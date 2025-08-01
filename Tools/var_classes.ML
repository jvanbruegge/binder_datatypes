signature VAR_CLASSES = sig

val get_class_for_bound: term -> local_theory -> class option

val register_class_for_bound: string -> term -> local_theory -> local_theory
val mk_class_for_bound: string -> term -> thm -> local_theory -> class * local_theory

end

structure Var_Classes : VAR_CLASSES = struct

open BNF_Util

structure Data = Generic_Data
(                  
  type T = (term * class) Item_Net.T;
  val empty = Item_Net.init ((op=) o apply2 fst) (single o fst);
  val merge = Item_Net.merge;
);

fun get_class_for_bound bound lthy =
  case Item_Net.lookup (Data.get (Context.Proof lthy)) (bound, "") of
    [(_, x)] => SOME x
    | _::_ => error "more than one class found for bound"
    | [] => NONE

fun register_class_for_bound name bound lthy =
  if not (Class.is_class (Proof_Context.theory_of lthy) name) then
    error (name ^ " is not a defined class")
  else Local_Theory.declaration {syntax = false, pos = Position.none, pervasive = true}
    (fn phi => Data.map (Item_Net.update (Morphism.term phi bound, name))) lthy

fun short_type_name full_name = String.tokens (fn c => c = #".") full_name |> List.last;

fun get_class_assumption class assN lthy =
  let
    val local_class = null class;
    val thmN = if local_class then assN else short_type_name (the_single class) ^ "_class." ^ assN;
    val (context, facts) = (if local_class then `Context.Proof else Proof_Context.theory_of #>
      `Context.Theory ##> Proof_Context.init_global) lthy ||> Proof_Context.facts_of;
  in
    Facts.intern facts thmN
      |> Facts.lookup context facts
      |> the
      |> #thms
      |> the_single
      |> Thm.transfer' lthy
  end;
val get_local_class_assumption = get_class_assumption [];

fun mk_class_for_bound name bound Cinfinite_bound lthy =
  Local_Theory.background_theory_result (fn thy =>
    let
      fun mk_assumption name term = ((Binding.name name, []), single (term, []));
      val large = mk_assumption "large" (HOLogic.mk_Trueprop (mk_ordLeq
        (mk_card_of (mk_Field bound))
        (mk_card_of (HOLogic.mk_UNIV (Term.aT @{sort type})))
      ));
      val regular = mk_assumption "regular" (HOLogic.mk_Trueprop (
        mk_regularCard (mk_card_of (HOLogic.mk_UNIV (Term.aT @{sort type})))
      ))

      val (class, lthy) = Class_Declaration.class (Binding.name name) [] [] [
        Element.Assumes [large, regular]
      ] thy;

      val large' = Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (mk_ordLeq
        bound (mk_card_of (HOLogic.mk_UNIV (Term.aT @{sort type})))
      ))

      val _ = Class_Declaration.prove_subclass (let val ctxt = lthy in EVERY1 [
        K (Class.intro_classes_tac ctxt []),
        rtac ctxt @{thm ordLeq_transitive},
        rtac ctxt @{thm Cinfinite_ordLeq_natLeq},
        rtac ctxt Cinfinite_bound,
        rtac ctxt @{thm ordIso_ordLeq_trans},
        rtac ctxt @{thm card_of_Field_ordIso[THEN ordIso_symmetric]},
        rtac ctxt (Cinfinite_bound RS conjunct2),
        rtac ctxt (get_local_class_assumption "large" ctxt),
        rtac ctxt (get_local_class_assumption "regular" ctxt)
      ] end) @{class var} lthy;

    in error "TODO" end
  ) lthy

end