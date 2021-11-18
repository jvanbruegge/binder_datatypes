signature MRBNF_COMP =
sig
  type vars = {
    lives: (string * sort) list,
    frees: (string * sort) list,
    bounds: (string * sort) list,
    deads: (string * sort) list
  }

  val ID_mrbnf: MRBNF_Def.mrbnf
  val DEADID_mrbnf: MRBNF_Def.mrbnf

  val mrbnf_of_typ: vars -> typ -> local_theory -> MRBNF_Def.mrbnf * local_theory
  val as_mrbnf: string -> local_theory -> (MRBNF_Def.mrbnf * local_theory) option

  type unfold_set =
    {map_unfolds: thm list,
     set_unfoldss: thm list list,
     rel_unfolds: thm list}
  val clean_compose_mrbnf: MRBNF_Def.inline_policy -> (binding -> binding) -> binding -> MRBNF_Def.mrbnf ->
    MRBNF_Def.mrbnf list -> unfold_set * local_theory -> MRBNF_Def.mrbnf * (unfold_set * local_theory)
end;

structure MRBNF_Comp : MRBNF_COMP =
struct

open MRBNF_Def

type vars = {
  lives: (string * sort) list,
  frees: (string * sort) list,
  bounds: (string * sort) list,
  deads: (string * sort) list
}

type unfold_set =
    {map_unfolds: thm list,
     set_unfoldss: thm list list,
     rel_unfolds: thm list}

val ID_mrbnf = the (mrbnf_of \<^context> "BNF_Composition.ID");
val DEADID_mrbnf = the (mrbnf_of \<^context> "BNF_Composition.DEADID");

fun as_mrbnf name lthy' =
  (case mrbnf_of lthy' name of
    SOME mrbnf => SOME (mrbnf, lthy')
    | NONE =>
      (case BNF_Def.bnf_of lthy' name of
        SOME bnf => SOME (register_bnf_as_mrbnf NONE bnf lthy')
        | NONE => NONE
      )
  )

(* Checks if the cardinal is composed of sums and producs of "natLeq" only. *)
fun is_sum_prod_natLeq (Const (@{const_name BNF_Cardinal_Arithmetic.csum}, _) $ t $ u) = forall is_sum_prod_natLeq [t, u]
  | is_sum_prod_natLeq (Const (@{const_name BNF_Cardinal_Arithmetic.cprod}, _) $ t $ u) = forall is_sum_prod_natLeq [t, u]
  | is_sum_prod_natLeq t = t aconv @{term natLeq};

(*
 * Instantiates the live variables of an outer MRBNF with several inner MRBNFs and returns a composed MRBNF.
 * The composed MRBNF will have:
 *   - The union of the dead variables of the outer and the inner MRBNFs
 *   - The live variables of the inner MRBNFs (which are the same for all inner MRBNFs by invariant)
 *   - The free and bound variables of the outer MRBNF (which are the same as those of all inner MRBNFs by invariant)
 *
 * INVARIANTS:
 *   - All inner MRBNFs have the same live variables in the same order
 *   - Outer and all inner MRBNFs have the same bound and free variables in the same order (the live variables are ignored while checking the order)
 *   - There are as many inner MRBNFs as there are live variables on the outer MRBNF
 *)
fun clean_compose_mrbnf const_policy qualify binding outer inners (unfold_set, lthy) =
  let
    val num_ilives = live_of_mrbnf (hd inners);
    val num_inondead = num_ilives + free_of_mrbnf outer + bound_of_mrbnf outer;
    val ivar_types = var_types_of_mrbnf (hd inners);

    (* Combine variable type classes of outer and inners into a single sort *)
    val sort = fold (curry (Sign.inter_sort (Proof_Context.theory_of lthy))) (map class_of_mrbnf inners) (class_of_mrbnf outer);
    val cosort = fold (curry (Sign.inter_sort (Proof_Context.theory_of lthy))) (map coclass_of_mrbnf inners) (coclass_of_mrbnf outer);

    (* Invent variable names for deads of outer and inner *)
    val (oDs, lthy1) = apfst (map TFree) (Variable.invent_types (map Type.sort_of_atyp (deads_of_mrbnf outer)) lthy);
    val (iDss, lthy2) = apfst (map (map TFree)) (fold_map Variable.invent_types (map (map Type.sort_of_atyp) (map deads_of_mrbnf inners)) lthy1);

    (* Invent variable names for bounds and frees (by invariant the same on outer and all inners) *)
    val (Fs, lthy3) = apfst (map TFree) (Variable.invent_types (map (K sort) (frees_of_mrbnf outer)) lthy2);
    val (Bs, lthy4) = apfst (map TFree) (Variable.invent_types (map (K sort) (bounds_of_mrbnf outer)) lthy3);

    (* Invent variable names for lives of inners (by invariant all inners have the same lives)
     * Live variables of outer are instantiated by the composition, so no variables names are needed.
     * The code invents two lists of names because of map: e.g. for "('a \<rightarrow> 'b) \<rightarrow> 'a F \<rightarrow> 'b F" As = ['a] and As' = ['b]
     * names_lthy is the local context after new variable names have been invented *)
    val (As, lthy5) = apfst (map TFree) (Variable.invent_types (replicate num_ilives @{sort type}) lthy4);
    val (As', names_lthy) = apfst (map TFree) (Variable.invent_types (replicate num_ilives @{sort type}) lthy5);

    (* Create the types of the inners, the only thing that is not the same by invariant are the dead variables.
     * This is dones once for the As and once for the As' of the live variables *)
    val iTs = map2 (fn deads => mk_T_of_mrbnf deads As Bs Fs) iDss inners;
    val iTs' = map2 (fn deads => mk_T_of_mrbnf deads As' Bs Fs) iDss inners;

    (* Create the type of the outer, this will replace the live variables of the outer with the types of the inners *)
    val oT = mk_T_of_mrbnf oDs iTs Bs Fs outer;

    (* Create the composed bound (bd) for the new MRBNF: bd = (inner_1.bd +c inner_2.bd +c ... +c inner_m.bd) *c outer.bd *)
    val bd = BNF_Util.mk_cprod (foldr1 (uncurry BNF_Util.mk_csum) (map bd_of_mrbnf inners)) (bd_of_mrbnf outer)

    (* In case the composed bound only consists of sums and products of "natLeq", simplify the bound to just "natLeq" *)
    val (bd', bd_ordIso_natLeq_thm_opt) =
      if is_sum_prod_natLeq bd then
        let
          val bd' = @{term natLeq};
          val bd_bd' = HOLogic.mk_prod (bd, bd');
          val ordIso = Const (@{const_name ordIso}, HOLogic.mk_setT (fastype_of bd_bd'));
          val goal = BNF_Util.mk_Trueprop_mem (bd_bd', ordIso)
        in (bd', SOME (Goal.prove_sorry lthy [] [] goal (BNF_Comp_Tactics.bd_ordIso_natLeq_tac o #context) |> Thm.close_derivation \<^here>))
        end
      else (bd, NONE);

    (* Define the map function of the composed MRBNF. It instantiates the map function of outer with the map functions of the inners:
     * \<forall>f1 ... fn v1 ... vm u1 ... ul. outer.map (inner_1.map f1 ... fn v1 ... vm u1 ... ul) ... (inner_m.map f1 ... fn v1 ... vm u1 ... ul) v1 ... vm u1 ... ul
     * Although in the example above the map function first takes all of the live variable functions, then all the bound variable function and
     * lastly the free variable functions, this does NOT have to be the case. Lives, bounds and frees can be interleaved in any order.
     * Additionally, the inners are only instanciated as the live variables of the outer, so the map function retains the functions for bounds and frees *)
    val (mapx, map_lthy) =
      let
        (* Create new variables for the different variable kinds and give them the types:
         *  - live: f1 ... fn : As\<^sub>i \<Rightarrow> As'\<^sub>i
         *  - bound: v1 ... vm : Bs\<^sub>j \<Rightarrow> Bs\<^sub>j
         *  - free: u1 ... ul : Fs\<^sub>k \<Rightarrow> Fs\<^sub>k *)
        val (((fs, vs), us), lthy) = names_lthy
          |> apfst snd o BNF_Util.mk_Frees' "f" (map2 (curry op -->) As As')
          ||>> apfst snd o BNF_Util.mk_Frees' "v" (map2 (curry op -->) Bs Bs)
          ||>> apfst snd o BNF_Util.mk_Frees' "u" (map2 (curry op -->) Fs Fs)

        (* Define a function that takes a list of variable types and interlaces the other arguments according to that list
         * and use it to put the variables created earlier in the correct order based of the variable types from the inners *)
        fun interlace _ _ _ [] = []
          | interlace (a :: als) bs fs (Live_Var::ts) = a :: interlace als bs fs ts
          | interlace als (b::bs) fs (Bound_Var::ts) = b :: interlace als bs fs ts
          | interlace als bs (f::fs) (Free_Var::ts) = f :: interlace als bs fs ts
        val fn_vars = interlace fs vs us ivar_types;

        (* Create a list of the de Bruijn indices of the forall-bound function variables, and one list with only the frees and bounds *)
        val fn_vars_ids = map Bound (num_inondead - 1 downto 0);
        val fn_bounds_frees_ids = map fst (filter (fn x => snd x <> Live_Var) (fn_vars_ids ~~ ivar_types))

        (* As the forall-bound function variables over live, bound and free variables are already in the correct order,
         * the inner maps can be applied directly to those function variables *)
        val innermaps = map2 (fn deads => fn inner => Term.list_comb (mk_map_of_mrbnf deads As As' Bs Fs inner, fn_vars_ids)) iDss inners

        (* The outer map function needs to be applied with the inner map functions for all its live variable functions,
         * and with the forall-bound bound and free variable function variables in the correct order.
         * For this, we need to interlace the inner map function with the function variables according to the variable types of the outer *)
        fun interlace_maps _ _ [] = []
          | interlace_maps ids (f::maps) (Live_Var::ts) = f :: interlace_maps ids maps ts
          | interlace_maps (i::ids) maps (_::ts) = i :: interlace_maps ids maps ts
        val body = Term.list_comb (mk_map_of_mrbnf oDs iTs iTs' Bs Fs outer, interlace_maps fn_bounds_frees_ids innermaps (var_types_of_mrbnf outer))

      in (fold_rev Term.abs fn_vars body, lthy)
      end;

    (* TODO: Create real map, sets, rel, pred, bd, wits *)
    val sets = []
    val rel = @{term "()"}
    val pred = @{term "()"}
    val wits = []

    (* TODO: Use real tacs here *)
    val tacs = {
      map_id0 = fn ctxt => print_tac ctxt "map_id0",
      map_comp0 = fn ctxt => print_tac ctxt "map_comp0",
      map_cong0 = fn ctxt => print_tac ctxt "map_cong0",
      set_map0 = replicate num_ilives (fn ctxt => print_tac ctxt "set_map0"),
      infinite_regular_card_order = fn ctxt => print_tac ctxt "infinite_regular_card_order",
      set_bd = replicate num_ilives (fn ctxt => print_tac ctxt "set_bd"),
      le_rel_OO = fn ctxt => print_tac ctxt "le_rel_OO",
      in_rel = fn ctxt => print_tac ctxt "in_rel",
      pred_set = fn ctxt => print_tac ctxt "pred_set",
      wit = fn ctxt => print_tac ctxt "wit"
    };

    val (mrbnf, lthy') = mrbnf_def Smart_Inline (K Dont_Note) true qualify tacs (SOME (oDs @ flat iDss)) (SOME (sort, cosort))
              Binding.empty Binding.empty Binding.empty [] (((((((binding, oT), mapx), sets), bd'), wits), SOME rel), SOME pred) map_lthy

  in (mrbnf, (unfold_set, lthy'))
  end;

fun mrbnf_of_typ vars T lthy =
  let val _ = ""
  in (case T of
    Type (name, args) =>
      (case as_mrbnf name lthy of
        SOME (outer_mrbnf, lthy') => (
          writeln ("success: " ^ Pretty.string_of (Syntax.pretty_typ lthy T));
          let val (inner_mrbnfs, lthy'') = List.foldr (fn (t, (xs, lthy1)) => mrbnf_of_typ vars t lthy1 |>> (fn x => x::xs)) ([], lthy') args
          in (outer_mrbnf, lthy'') end (* TODO: Actually compose and don't just return the outer mrbnf *)
        )
        | NONE => (writeln ("TODO: dead type: " ^ Pretty.string_of (Syntax.pretty_typ lthy T)) ; (DEADID_mrbnf, lthy))
      )
    | TVar (i, s) => (error "foo bound", lthy)
    | TFree T' => if member (op =) (#deads vars) T' then
        (DEADID_mrbnf, lthy)
        else
      (ID_mrbnf, lthy)
  ) end;

end;