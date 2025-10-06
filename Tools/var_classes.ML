signature VAR_CLASSES = sig

val get_class_for_bound: term -> local_theory -> class option

val get_class_assumption: class -> string -> local_theory -> thm
val get_local_class_assumption: string -> local_theory -> thm
val get_bound_from_class: class -> local_theory -> term

val register_class_for_bound: string -> term -> local_theory -> local_theory
val mk_class_for_bound: binding -> term -> local_theory -> class * local_theory
val mk_comp_class: binding -> term -> thm list -> sort -> local_theory -> class * local_theory

val prove_class_theorems: bool -> bool -> class -> thm -> thm -> local_theory -> local_theory
val prove_subclass_of: class option -> class -> (Proof.context -> tactic) -> local_theory -> local_theory

end

structure Var_Classes : VAR_CLASSES = struct

open MRBNF_Util

structure Data = Generic_Data
(                  
  type T = (term * (class * bool)) Item_Net.T;
  val empty = Item_Net.init ((op=) o apply2 fst) (single o fst);
  val merge = Item_Net.merge;
);

fun get_class_for_bound' bound lthy =
  case Item_Net.lookup (Data.get (Context.Proof lthy)) (bound, ("", false)) of
    [(_, x)] => SOME x
    | _::_ => error "more than one class found for bound"
    | [] => NONE

fun get_class_for_bound bound lthy =
  case get_class_for_bound' bound lthy of
    SOME (x, true) => SOME x
    | SOME (x, false) => error ("class " ^ x ^ " is not initialized, use prove_class_theorems first")
    | NONE => NONE

fun short_type_name full_name = String.tokens (fn c => c = #".") full_name |> List.last;

fun get_class_assumption' class assN lthy =
  let
    val local_class = null class;
    val thmN = if local_class then assN else short_type_name (the_single class) ^ "_class." ^ assN;
    val (context, facts) = (if local_class then `Context.Proof else Proof_Context.theory_of #>
      `Context.Theory ##> Proof_Context.init_global) lthy ||> Proof_Context.facts_of;

    val class' = case class of [] => "local" | _ => hd class;

    fun the_error (SOME x) = x
      | the_error _ = error ("Class `" ^ class' ^ "` does not have assumption `" ^ assN ^ "`")
  in
    Facts.intern facts thmN
      |> Facts.lookup context facts
      |> the_error
      |> #thms
      |> the_single
      |> Thm.transfer' lthy
  end;
val get_class_assumption = get_class_assumption' o single;
val get_local_class_assumption = get_class_assumption' [];

fun register_class_for_bound name bound lthy =
  if not (Class.is_class (Proof_Context.theory_of lthy) name) then
    error (name ^ " is not a defined class")
  else
    let
      val b = Option.isSome (try (get_class_assumption name "large'") lthy);
    in Local_Theory.declaration {syntax = false, pos = Position.none, pervasive = true}
      (fn phi => Data.map (Item_Net.update (Morphism.term phi bound, (name, b)))) lthy
    end;

fun mk_class_for_bound b bound lthy =
  if Class.is_class (Proof_Context.theory_of lthy) (Local_Theory.full_name lthy b) then
    (Local_Theory.full_name lthy b, lthy)
  else case get_class_for_bound' bound lthy of
    SOME (class, _) => (class, lthy)
    | _ =>
    let
      val (class, lthy) = Local_Theory.background_theory_result (fn thy =>
        let
          fun mk_assumption name term = ((Binding.name name, []), single (term, []));
          val large = mk_assumption "large" (HOLogic.mk_Trueprop (mk_ordLeq
            (mk_card_of (mk_Field bound))
            (mk_card_of (HOLogic.mk_UNIV (Term.aT @{sort type})))
          ));
          val regular = mk_assumption "regular" (HOLogic.mk_Trueprop (
            mk_regularCard (mk_card_of (HOLogic.mk_UNIV (Term.aT @{sort type})))
          ))
      
          val (class, lthy) = Class_Declaration.class b [] [] [
            Element.Assumes [large, regular]
          ] thy;
        in (class, Local_Theory.exit_global lthy) end
      ) lthy;
    in (class, register_class_for_bound class bound lthy) end

fun get_bound_from_class class lthy = 
  Thm.prop_of (get_class_assumption class "large" lthy)
  |> HOLogic.dest_Trueprop
  |> fst o HOLogic.dest_mem
  |> hd o snd o Term.strip_comb
  |> snd o Term.dest_comb
  |> snd o Term.dest_comb;

fun mk_comp_class b bound Cinfinites sort lthy = 
  let
    val (class, lthy) = mk_class_for_bound b bound lthy;
  in if [class] = sort then (class, lthy) else
    let
      val lthy = fold (fn super => Local_Theory.background_theory (fn thy =>
        let
          val lthy = Named_Target.init [] class thy;
  
          val lthy = Class_Declaration.prove_subclass (let val ctxt = lthy in EVERY1 [
            K (Class.intro_classes_tac ctxt []),
            rtac ctxt @{thm ordLeq_transitive[rotated]},
            rtac ctxt (get_local_class_assumption "large" lthy),
            rtac ctxt @{thm card_of_mono2},
            EVERY' [
              rtac ctxt @{thm ordLeq_cprod2},
              rtac ctxt @{thm Cinfinite_Cnotzero},
              TRY o (rtac ctxt @{thm Cinfinite_csum} THEN' rtac ctxt @{thm disjI1}),
              resolve_tac ctxt Cinfinites,
              resolve_tac ctxt (map (fn thm => thm RS conjunct2) Cinfinites)
            ] ORELSE' EVERY' [
              rtac ctxt @{thm ordLeq_transitive[OF _ ordLeq_cprod1]},
              REPEAT_DETERM o (EVERY' [
                resolve_tac ctxt @{thms ordLeq_csum1 ordLeq_refl},
                REPEAT_DETERM o resolve_tac ctxt (map (fn thm => thm RS conjunct2) Cinfinites)
              ] ORELSE' rtac ctxt @{thm ordLeq_transitive[OF _ ordLeq_csum2]}),
              rtac ctxt @{thm Card_order_csum},
              rtac ctxt @{thm Cinfinite_Cnotzero},
              resolve_tac ctxt Cinfinites
            ],
            rtac ctxt (get_local_class_assumption "regular" lthy)
          ] end) super lthy;
        in Local_Theory.exit_global lthy end
      )) sort lthy;
    in (class, lthy) end
  end

fun prove_subclass_of class_opt super tac lthy =
  let
    fun prove lthy = Class_Declaration.prove_subclass (let val ctxt = lthy in EVERY1 [
      K (Class.intro_classes_tac ctxt []),
      rtac ctxt @{thm ordLeq_transitive[rotated]},
      rtac ctxt (get_local_class_assumption "large" lthy),
      rtac ctxt @{thm card_of_mono2},
      SELECT_GOAL (tac ctxt),
      rtac ctxt (get_local_class_assumption "regular" lthy)
    ] end) super lthy;
  in case class_opt of
    NONE => prove lthy
    | SOME class => if class = super orelse Sign.subsort (Proof_Context.theory_of lthy) ([class], [super]) then lthy else
      Local_Theory.background_theory (fn thy =>
        let
          val lthy = Named_Target.init [] class thy;
          val lthy = prove lthy;
        in Local_Theory.exit_global lthy end
      ) lthy
  end

fun prove_class_theorems add_wit var_class class bd_Cinfinite bd_regularCard lthy =
  let
    val bound = get_bound_from_class class lthy;

    fun add_class_witness class lthy = if not add_wit then lthy else
      let
        val ((wit_name, wit), lthy) = new_typedef (Binding.prefix_name "wit_" (Binding.name (short_type_name class)))
          (mk_Field bound) (fn ctxt => EVERY1 [
            rtac ctxt @{thm cinfinite_wit},
            rtac ctxt (bd_Cinfinite RS conjunct1)
          ]) lthy;

        val lthy = Local_Theory.background_theory (
          Class.instantiation ([wit_name], [], [class])
          #> Class.prove_instantiation_exit (fn ctxt => EVERY1 [
            K (Class.intro_classes_tac ctxt []),
            rtac ctxt (@{thm ordLeq_ordIso_trans} OF [@{thm _},
              @{thm type_definition_card_UNIV} OF [#type_definition (snd wit)]
            ]),
            rtac ctxt @{thm ordLeq_refl},
            rtac ctxt @{thm card_of_Card_order},
            rtac ctxt (@{thm regularCard_ordIso[OF ordIso_transitive[OF ordIso_symmetric[OF card_of_Field_ordIso]]]} OF [
              @{thm _}, @{thm type_definition_card_UNIV} OF [#type_definition (snd wit)]
            ]),
            rtac ctxt (bd_Cinfinite RS conjunct2),
            rtac ctxt bd_Cinfinite,
            rtac ctxt bd_regularCard
          ])
        ) lthy;
      in lthy end

    fun prove_class class lthy = Local_Theory.background_theory (fn thy =>
      let
        val lthy = Named_Target.init [] class thy;

        val large' = Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (mk_ordLeq
          bound (mk_card_of (HOLogic.mk_UNIV (Term.aT @{sort type})))
        )) (fn {context=ctxt, ...} => EVERY1 [
          rtac ctxt @{thm ordIso_ordLeq_trans},
          rtac ctxt @{thm ordIso_symmetric},
          rtac ctxt @{thm card_of_Field_ordIso},
          rtac ctxt (bd_Cinfinite RS conjunct2),
          rtac ctxt (get_local_class_assumption "large" lthy)
        ]);
        
        val notes = [
          ("large'", [large'])
        ] |> (map (fn (thmN, thms) => (((Binding.name thmN), []), [(thms, [])])))
        val (_, lthy) = Local_Theory.notes notes lthy;
  
        val lthy = if not var_class then lthy else
          prove_subclass_of NONE @{class var} (fn ctxt => EVERY1 [
            rtac ctxt @{thm natLeq_ordLeq_cinfinite},
            rtac ctxt bd_Cinfinite
          ]) lthy;
      in Local_Theory.exit_global lthy end
    ) lthy
      |> add_class_witness class
      |> register_class_for_bound class bound;

  in case get_class_for_bound' bound lthy of
    SOME (_, true) => lthy
  | SOME (x, _) => prove_class x lthy
  | NONE => prove_class class lthy
    
  end

end