signature EQUIVARIANCE =
sig
  val equiv_thms': Context.generic -> thm list
  val equiv_sym_thms': Context.generic -> thm list
  val equiv_forward_thms': Context.generic -> (thm * int) list

  val equiv_thms: local_theory -> thm list
  val equiv_sym_thms: local_theory -> thm list
  val equiv_forward_thms: local_theory -> (thm * int) list

  val get_mr_bnfs: local_theory -> typ -> (string * (MRBNF_Def.mrbnf, (BNF_Def.bnf, MRBNF_FP_Def_Sugar.quotient_result MRBNF_FP_Def_Sugar.fp_result_T) MRBNF_Util.either) MRBNF_Util.either) list
end

structure Equivariance : EQUIVARIANCE =
struct

open MRBNF_Util

structure Equiv_Data = Generic_Data
(
  type T = thm Item_Net.T;
  val empty: T = Thm.item_net_intro;
  val merge : T * T -> T = Item_Net.merge;
)
structure Equiv_Sym_Data = Generic_Data
(
  type T = thm Item_Net.T;
  val empty: T = Thm.item_net_intro;
  val merge : T * T -> T = Item_Net.merge;
)
structure Equiv_Forward_Data = Generic_Data
(
  type T = (thm * int) Item_Net.T;
  val empty: T = Item_Net.init (Thm.eq_thm_prop o apply2 fst) (single o Thm.concl_of o fst);
  val merge: T * T -> T = Item_Net.merge;
)

fun equiv_thms' context =
  rev (map (Thm.transfer'' context) (Item_Net.content (Equiv_Data.get context)));
fun equiv_sym_thms' context =
  rev (map (Thm.transfer'' context) (Item_Net.content (Equiv_Sym_Data.get context)));
fun equiv_forward_thms' context =
  rev (map (apfst (Thm.transfer'' context)) (Item_Net.content (Equiv_Forward_Data.get context)));

val equiv_thms = equiv_thms' o Context.Proof
val equiv_sym_thms = equiv_sym_thms' o Context.Proof
val equiv_forward_thms = equiv_forward_thms' o Context.Proof

fun get_mr_bnfs lthy (Type (s, Ts)) = (case MRBNF_FP_Def_Sugar.fp_result_of lthy s of
  SOME sugar => [(s, Inr (Inr (hd (filter (curry (op=) s o fst o dest_Type o #T) (#quotient_fps sugar)))))]
  | NONE => (case MRBNF_Def.mrbnf_of lthy s of
    SOME mrbnf => (s, MRBNF_Util.Inl mrbnf) :: maps (get_mr_bnfs lthy) Ts
    | NONE => (case BNF_Def.bnf_of lthy s of
      SOME bnf => (s, Inr (MRBNF_Util.Inl bnf)) :: maps (get_mr_bnfs lthy) Ts
      | NONE => maps (get_mr_bnfs lthy) Ts
  )))
  | get_mr_bnfs _ _ = [];

val _ = Theory.local_setup (fn lthy =>
  let
    val add = Thm.declaration_attribute (fn thm => fn context =>
      let
        val is_eq = Option.mapPartial (fn x =>
          let
            val b = forall (fn t => case HOLogic.dest_Trueprop t of
              (Const (@{const_name bij_betw}, _) $ _ $ _ $ _) => true
              | (Const (@{const_name Set.member}, _) $ _ $ Const (@{const_name ordLess}, _)) => true
              | _ => false
            ) (Thm.prems_of thm);
          in if b then SOME x else NONE end
        ) (Option.mapPartial (try HOLogic.dest_eq) (
          try HOLogic.dest_Trueprop (Thm.concl_of thm)
        ));
        val (thm'_opt, commute_opt) = case is_eq of
          SOME (lhs, rhs) =>
            let
              val prems = Thm.prems_of thm
              val fs = fold Term.add_vars prems [];
              val vars_lhs = Term.add_vars lhs [];
              val vars_rhs = Term.add_vars rhs [];
              fun inter' (xs, ys) = not (null (inter (op=) xs ys));
              val commute = if inter' (vars_lhs, vars_rhs) andalso inter' (vars_lhs, fs) andalso inter' (vars_rhs, fs) then
                SOME (thm RS sym)
              else NONE
            in (SOME thm, commute) end
          | NONE =>
            let
              open MRBNF_Util
              val lthy = Context.proof_of context;
              val prop = Thm.full_prop_of (Variable.import_vars lthy thm);
              val (f_prems, rhs) = split_last (Logic.strip_imp_prems prop);
              val lhs = Logic.strip_imp_concl prop;
              val goal = fold_rev (curry Logic.mk_implies) f_prems (HOLogic.mk_Trueprop (HOLogic.mk_eq (
                apply2 HOLogic.dest_Trueprop (lhs, rhs)
              )));
              val fs = rev (fold_rev Term.add_frees f_prems []);
              val vars = rev (Term.add_frees goal []);
              val params = subtract (op=) (map Free fs) (map Free vars);

              val mr_bnfs = map snd (
                distinct ((op=) o apply2 fst) (maps (get_mr_bnfs lthy o fastype_of) params)
              );
              fun map_comps_of_mr_bnf (Inl mrbnf) = [MRBNF_Def.map_comp_of_mrbnf mrbnf, MRBNF_Def.map_comp0_of_mrbnf mrbnf RS sym]
                | map_comps_of_mr_bnf (Inr (Inl bnf)) = [BNF_Def.map_comp_of_bnf bnf, BNF_Def.map_comp0_of_bnf bnf RS sym]
                | map_comps_of_mr_bnf (Inr (Inr quot)) = [#permute_comp quot, #permute_comp0 quot]
              val map_comps = maps map_comps_of_mr_bnf mr_bnfs;
              fun map_id0s_of_mr_bnf (Inl mrbnf) = MRBNF_Def.map_id0_of_mrbnf mrbnf
                | map_id0s_of_mr_bnf (Inr (Inl bnf)) = BNF_Def.map_id0_of_bnf bnf
                | map_id0s_of_mr_bnf (Inr (Inr quot)) = #permute_id0 quot

              val thm' = try (Goal.prove lthy (map fst vars) [] goal) (fn {context=ctxt, ...} => EVERY1 [
                rtac ctxt iffI,
                defer_tac,
                etac ctxt (Drule.rotate_prems ~1 thm),
                REPEAT_DETERM o assume_tac ctxt,
                dtac ctxt (Drule.rotate_prems ~1 thm),
                K (prefer_tac (length f_prems + 1)),
                SELECT_GOAL (REPEAT_DETERM (SOMEGOAL (EVERY' [
                  EqSubst.eqsubst_asm_tac ctxt [0] (@{thms inv_o_simp1 inv_o_simp2 image_inv_f_f[OF bij_is_inj]} @ map_comps),
                  REPEAT_DETERM o eq_assume_tac
                ]))),
                K (Local_Defs.unfold0_tac ctxt (@{thms id_apply id_o o_id inv_simp1 inv_simp2 image_inv_f_f[OF bij_is_inj]} @ map map_id0s_of_mr_bnf mr_bnfs)),
                REPEAT_DETERM o (assume_tac ctxt ORELSE' resolve_tac ctxt @{thms bij_id supp_id_bound bij_imp_bij_inv supp_inv_bound})(*,*)
                (*IF_UNSOLVED o (K (print_tac ctxt "strengthening failed:"))*)
              ])
            in (thm', NONE) end
        val context = the_default context (Option.map (fn thm => Equiv_Data.map (Item_Net.update (Thm.trim_context thm)) context) thm'_opt);
      in the_default context (Option.map (fn thm => Equiv_Sym_Data.map (
        Item_Net.update (Thm.trim_context thm)
      ) context) commute_opt) end);
    val del = Thm.declaration_attribute (fn thm => fn context =>
      let
        val concl2 = HOLogic.dest_Trueprop (Thm.concl_of thm);
        val context = Equiv_Data.map (Item_Net.filter (fn thm' =>
          let
            val concl1 = HOLogic.dest_Trueprop (Thm.concl_of thm')
          in case try HOLogic.dest_eq concl1 of
            SOME _ => not (concl1 aconv concl2)
            | NONE => not (concl1 aconv fst (HOLogic.dest_eq concl2))
           end
        )) context;
      in Equiv_Sym_Data.map (Item_Net.remove (thm RS sym)) context end)

    val lthy' = lthy
      |> Local_Theory.add_thms_dynamic (@{binding equiv}, equiv_thms')
      |> Local_Theory.add_thms_dynamic (@{binding equiv_sym}, equiv_sym_thms')
      |> Attrib.local_setup @{binding equiv} (Attrib.add_del add del) "Register equivariance theorems"
  in lthy' end
)

val _ = Theory.local_setup (fn lthy =>
  let
    fun add idx = Thm.declaration_attribute (fn thm => Equiv_Forward_Data.map (Item_Net.update (Thm.trim_context thm, idx)));
    val del = Thm.declaration_attribute (fn thm => Equiv_Forward_Data.map (Item_Net.filter (fn (thm', _) =>
      not (Thm.concl_of thm aconv Thm.concl_of thm')
    )))

    val attr = Scan.lift (Scan.optional Parse.nat 0 :-- (fn idx =>
      Args.add >> K (add idx) || Args.del >> K del || Scan.succeed (add idx)
    )) >> snd;
  in lthy
    |> Local_Theory.add_thms_dynamic (@{binding equiv_forward}, map fst o equiv_forward_thms')
    |> Attrib.local_setup @{binding equiv_forward} attr "Register forward theorems for equivariance proofs"
  end
);

end
