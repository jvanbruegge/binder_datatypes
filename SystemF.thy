theory SystemF
  imports "thys/MRBNF_Recursor"
begin

datatype \<kappa> = Star ("\<star>") | Arrow \<kappa> \<kappa> (infixr "\<rightarrow>" 40)

(* binder_datatype 'a \<tau> =
  TyVar 'a
  | Arrow "'a \<tau>" "'a \<tau>" (infixr "\<rightarrow>" 40)
  | TyApp "'a \<tau>" "'a \<tau>" (infixr "@" 40)
  | TyAll \<alpha>::'a bound::"'a \<tau>" tybody::"'a \<tau>" binds \<alpha> in tybody (infixr "\<forall>_<_._" 30)

*)
ML \<open>
val tyctors = [
  (("TyVar", (NONE : mixfix option)), [@{typ 'var}]),
  (("TyArr", NONE), [@{typ 'rec}, @{typ 'rec}]),
  (("TyAll", NONE), [@{typ 'bvar}, @{typ 'brec}])
]
val tyspec = {
  fp_b = @{binding "\<tau>"},
  vars = [
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[0]],
  rec_vars = 2,
  ctors = tyctors,
  map_b = @{binding ty_vvsubst},
  tvsubst_b = @{binding ty_tvsubst}
}
\<close>
declare [[mrbnf_internals]]
local_setup \<open>fn lthy =>
let
  val lthy' = MRBNF_Sugar.create_binder_datatype tyspec lthy
in lthy' end\<close>
print_theorems
print_mrbnfs

thm \<tau>.strong_induct
thm \<tau>.set
thm \<tau>.map
thm \<tau>.subst

(* binder_datatype ('a,'b) term =
  Var 'b
| App "('a,'b) term" "('a,'b) term"
| Lam x::'b ty::"'a \<tau>" t::"('a,'b) term" binds x in t
| TyApp "('a,'b) term" "'a \<tau>"
| TyLam \<alpha>::'a body::"('a,'b) term" binds \<alpha> in body
*)

ML \<open>
val ctors = [
  (("Var", (NONE : mixfix option)), [@{typ 'var}]),
  (("App", NONE), [@{typ 'rec}, @{typ 'rec}]),
  (("Lam", NONE), [@{typ 'bvar}, @{typ "'tyvar \<tau>"}, @{typ 'brec}]),
  (("TyApp", NONE), [@{typ 'rec}, @{typ "'tyvar \<tau>"}]),
  (("TyLam", NONE), [@{typ 'btyvar}, @{typ 'brec}])
]

val spec = {
  fp_b = @{binding "term"},
  vars = [
    (dest_TFree @{typ 'tyvar}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'btyvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[0], [0]],
  rec_vars = 2,
  ctors = ctors,
  map_b = @{binding vvsubst},
  tvsubst_b = @{binding tvsubst}
}
\<close>

declare [[ML_print_depth=10000]]
declare [[mrbnf_internals]]
ML \<open>Multithreading.parallel_proofs := 0\<close>
local_setup \<open>fn lthy =>
let
  val lthy' = MRBNF_Sugar.create_binder_datatype spec lthy
in lthy' end\<close>
print_theorems
print_mrbnfs

(* ??.SystemF.FFVars_term2 (??.SystemF.tvsubst f2 t) =
 (SUP a\<in>??.SystemF.FFVars_term2 t. ??.SystemF.FFVars_term2 (f2 a) *)

thm term.strong_induct
thm term.set
thm term.map
thm term.subst

lemma FFVars_tvsubst:
  fixes t::"('a::var_term_pre, 'b::var_term_pre) term"
  assumes "|tvSSupp_tvsubst f2| <o cmin |UNIV::'a set| |UNIV::'b set|"
    shows "FFVars_term2 (tvsubst f2 t) = (\<Union>a\<in>FFVars_term2 t. FFVars_term2 (f2 a))"
  apply (rule term.TT_fresh_co_induct[of "tvIImsupp1_tvsubst f2" "tvIImsupp2_tvsubst f2" _ t])
    apply (unfold tvIImsupp1_tvsubst_def comp_def)[1]
    apply ((rule assms term_pre.Un_bound term_pre.UNION_bound term.set_bd_UNIV ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)[1]
   apply (unfold tvIImsupp2_tvsubst_def comp_def)[1]
   apply ((rule assms term_pre.Un_bound term_pre.UNION_bound term.set_bd_UNIV ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)[1]
  subgoal for v
    apply (rule case_split[of "tvisVVr_tvsubst (term_ctor v)"])
     apply (unfold tvisVVr_tvsubst_def)[1]
     apply (erule exE)
    subgoal premises prems for a
      apply (subst prems(9))+
      apply (subst term.tvsubst_VVr)
       apply (rule assms)
      apply (subst term.FVars_VVr)
      apply (unfold UN_single)[1]
      apply (rule refl)
      done
    apply (subst term.tvsubst_cctor_not_isVVr)
         apply (rule assms)
      (* REPEAT_DETERM *)
        apply (rule iffD2[OF disjoint_iff])
        apply (rule allI)
        apply (rule impI)
        apply assumption
      (* copied from above *)
       apply (rule iffD2[OF disjoint_iff])
       apply (rule allI)
       apply (rule impI)
       apply assumption
    (* copied from above *)
      apply (rule iffD2[OF meta_eq_to_obj_eq[OF noclash_term_def]])
      apply (unfold Int_Un_distrib Un_empty)[1]
      apply (rule conjI)+
       apply (rule iffD2[OF disjoint_iff])
       apply (rule allI)
        apply (rule impI)
        apply assumption
       apply (rule iffD2[OF disjoint_iff])
       apply (rule allI)
       apply (rule impI)
       apply (unfold UN_iff Set.bex_simps)
       apply (rule ballI)
       apply assumption
    apply (rule conjI)+
       apply (rule iffD2[OF disjoint_iff])
       apply (rule allI)
        apply (rule impI)
       apply assumption
       apply (rule iffD2[OF disjoint_iff])
       apply (rule allI)
        apply (rule impI)
       apply (unfold UN_iff Set.bex_simps)
       apply (rule ballI)
      apply assumption
  (* END REPEAT_DETERM *)
     apply assumption
    apply (unfold term.FFVars_cctors)
    apply (subst term_pre.set_map, (rule supp_id_bound bij_id)+)+
    apply (unfold image_id image_comp[unfolded comp_def] UN_Un term.not_isVVr_free UN_empty Un_empty_left)
    apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])+
      (* REPEAT_DETERM *)
     apply (rule trans[rotated])
      apply (rule sym)
      apply (rule term.IImsupp_Diff)
      apply (rule iffD2[OF disjoint_iff])
      apply (rule allI)
      apply (rule impI)
      apply assumption
     apply (rule arg_cong2[OF _ refl, of _ _ minus])
     apply (unfold UN_simps)
     apply (rule UN_cong)
     apply assumption
  (* copied from above *)
     apply (rule UN_cong)
    apply assumption
    done
  done



end