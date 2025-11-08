theory Linearize_alist
  imports "Binders.MRBNF_Composition" "Binders.MRBNF_Recursor"
  keywords "linearize_mrbnf" :: thy_goal
begin

ML_file "../Tools/mrbnf_linearize_tactics.ML"
ML_file "../Tools/mrbnf_linearize.ML"

declare [[mrbnf_internals]]

section "command"
linearize_mrbnf ('k::var,'v) alist' = "('k::var \<times> 'v) list" on 'k for nonrep: list_distinct eq_shape: length_eq morphisms to_alist of_alist
  apply (auto simp: list_eq_iff_nth_eq map_prod_def split_beta prod_eq_iff)
  done

thm of_alist_inverse[unfolded list_distinct_def]
thm to_alist

thm map_alist'_def

binder_datatype 'a lc = Var 'a | Abs x::'a t::"'a lc" binds x in t | App "'a lc" "'a lc"
  | Let "(fs::'a, t::'a lc) alist'" u::"'a lc" binds fs in t u

section "manual"
typedef ('k, 'v) pre_alist = "UNIV :: ('k \<times> 'v) list set" by auto

setup_lifting type_definition_pre_alist

copy_bnf (keys: 'k, vals: 'v) pre_alist for map: map_pre_alist rel: rel_pre_alist
print_theorems


definition eq_shape :: "('k, 'v) pre_alist \<Rightarrow> ('k, 'v) pre_alist \<Rightarrow> bool" where 
  "eq_shape x x' \<equiv> rel_pre_alist top (=) x x'"

definition nonrep :: "('k, 'v) pre_alist \<Rightarrow> bool" where 
  "nonrep x \<equiv> \<forall> x'. eq_shape x x' \<longrightarrow> (\<exists> f. x' = map_pre_alist f id x)"

typedef ('k,'v) alist = "{x :: ('k, 'v) pre_alist. nonrep x}"
  apply (rule exI[of _ "Abs_pre_alist []"])
  apply (unfold mem_Collect_eq nonrep_def eq_shape_def pre_alist.map_id rel_pre_alist_def vimage2p_def 
      map_pre_alist_def o_apply Abs_pre_alist_inverse[simplified])
  apply (auto)
    apply (drule arg_cong[where f = Abs_pre_alist])
    by (auto simp add: Rep_pre_alist_inverse[simplified])

definition map_alist :: "('v \<Rightarrow> 'v') \<Rightarrow> ('k, 'v) alist \<Rightarrow> ('k, 'v') alist" where
  "map_alist f \<equiv> Abs_alist o (map_pre_alist id f) o Rep_alist"

definition set_alist :: "('k, 'v) alist \<Rightarrow> 'v set" where
  "set_alist \<equiv> vals o Rep_alist"

definition rel_alist :: "('v \<Rightarrow> 'v' \<Rightarrow> bool) \<Rightarrow> ('k, 'v) alist \<Rightarrow> ('k, 'v') alist \<Rightarrow> bool" where
  "rel_alist R x y \<equiv> rel_pre_alist (=) R (Rep_alist x) (Rep_alist y)"


bnf "('k, 'v) alist"
  map: "map_alist"
  sets: "set_alist"
  bd: natLeq
  rel: "rel_alist"
  sorry

print_bnfs


mrbnf pre_alist: "('k, 'v) pre_alist"
  map: map_pre_alist
  sets:
    live: keys live: vals
  bd: "natLeq"
  rel: rel_pre_alist
  pred: pred_pre_alist
  apply (auto simp add: pre_alist.map_id pre_alist.map_comp pre_alist.set_map pre_alist.set_bd
  pre_alist.bd_card_order pre_alist.bd_cinfinite pre_alist.bd_regularCard infinite_regular_card_order_def
  pre_alist.rel_compp pre_alist.in_rel pre_alist.pred_set)
  using pre_alist.map_cong0
   apply blast
  done

linearize_mrbnf ('k::var,'v) alisttt = "('k::var, 'v) pre_alist" on 'k
  oops

axiomatization where
  (* The next property assumes preservation of pullbacks on the third position. 
   NB: All MRBNFs already preserve _weak_ pullbacks, i.e., they satisfy the following property 
   without uniqueness.  *)
  pre_alist_strong_pullback: 
  "\<And> R S (x :: (('k, 'v) pre_alist)) y.
    rel_pre_alist R S x y =
      (\<exists>!z. keys z \<subseteq> {(x, y). R x y} \<and>
            vals z \<subseteq> {(x, y). S x y} \<and> map_pre_alist fst fst z = x \<and> map_pre_alist snd snd z = y)"
  and
  (* The next property assumes that nonrepetitive elements exist: *)
  ex_nonrep: "\<exists>x. \<forall>x'. rel_pre_alist top (=) x x' \<longrightarrow> (\<exists> f. x' = map_pre_alist f id x)"

(* Important consequence of preservation of pullbacks (which is actually equivalent to it): 
The relator is closed under intersections. *)

lemma pre_alist_strong:
  "mr_rel_pre_alist R3 R4 x y \<Longrightarrow> mr_rel_pre_alist Q3 Q4 x y \<Longrightarrow> mr_rel_pre_alist (inf R3 Q3) (inf R4 Q4) x y"
  apply (frule pre_alist.mr_rel_mono_strong0;
      ((rule ballI, rule ballI refl)?, 
        (rule impI, rule trans[OF top_apply[THEN fun_cong] trans[OF top_apply top_bool_def]])?))
  apply (unfold pre_alist.map_id mr_rel_pre_alist_def eq_True)
  apply (rotate_tac 2)
  apply (drule pre_alist_strong_pullback[THEN iffD1])
  apply (unfold top_apply top_bool_def Collect_const_case_prod if_True eqTrueI[OF subset_UNIV] simp_thms(22))
  apply (unfold pre_alist.in_rel[unfolded id_apply pre_alist.map_id OO_Grp_alt]
      id_def[symmetric] mem_Collect_eq)
  apply (elim exE alt_ex1E conjE)
  subgoal premises prems for z l r
    apply (insert spec2[OF prems(1), of r z])
    apply (insert spec2[OF prems(1), of l z])
    apply (erule impE, intro conjI prems)
    apply (erule impE, intro conjI prems)
    apply (rule exI)
    apply (unfold inf_fun_def inf_bool_def)
    apply (rule conjI)
     apply (insert prems) []
     apply (hypsubst_thin)
     apply ((rule conjI)?,
        rule subrelI, 
        rule CollectI, 
        rule case_prodI, 
        (rule conjI; erule rev_subsetD[THEN iffD1[OF prod_in_Collect_iff]]),
        assumption, assumption)+
    apply (rule conjI; rule prems)
    done
  done

(* Another important consequence: the following "exchange"-property, which could be read: 
Since the atoms have a fixed position, we can permute the relations: *)
lemma rel_F_exchange: 
  fixes x :: "('k, 'v) pre_alist" and x' :: "('k', 'v') pre_alist"
  assumes "mr_rel_pre_alist Rk Rv x x'" and "mr_rel_pre_alist Qk Qv x x'"
  shows "mr_rel_pre_alist Rk Qv x x'" 
    apply (rule pre_alist.mr_rel_mono_strong0)
    apply (rule pre_alist_strong[OF assms])
       apply (unfold id_apply eqTrueI[OF refl] ball_triv inf_apply inf_bool_def)
     apply (intro ballI impI; erule conjunct1 conjunct2)+
  done

(* Then notion of two items having the same shape (w.r.t. the 3rd position): *)
(* these definitions are lin_pos dependent *)
definition eq_shape :: "('k, 'v) pre_alist \<Rightarrow> ('k, 'v) pre_alist \<Rightarrow> bool" where 
  "eq_shape x x' \<equiv> mr_rel_pre_alist top (=) x x'"

definition nonrep :: "('k, 'v) pre_alist \<Rightarrow> bool" where 
  "nonrep x \<equiv> \<forall> x'. eq_shape x x' \<longrightarrow> (\<exists> f. x' = map_pre_alist f id x)"

lemma nonrep_map_F:
  fixes x :: "('k, 'v) pre_alist" and g :: "'v \<Rightarrow> 'v"
  assumes "nonrep x"
  shows "nonrep (map_pre_alist id g x)"
  apply (unfold nonrep_def eq_shape_def)
  apply (rule allI)
  apply (rule impI)
  apply (subst pre_alist.map_comp; (rule assms bij_id supp_id_bound)?)
  apply (unfold o_id id_o)
  apply (drule iffD1[OF pre_alist.mr_rel_map(1), rotated -1])
  apply (unfold trans[OF id_o o_id[symmetric]] Grp_UNIV_id trans[OF OO_eq eq_OO[symmetric]])
  apply (unfold trans[OF eq_OO OO_eq[symmetric], of top])
  apply (unfold eq_alt)
  apply (subst Grp_UNIV_id)
  apply (unfold mr_rel_pre_alist_def o_id pre_alist.rel_compp pre_alist.rel_Grp)
  apply (unfold eqTrueI[OF subset_UNIV] simp_thms(21) UNIV_def[symmetric] id_o)
  apply (unfold Grp_UNIV_id OO_def Grp_def eqTrueI[OF UNIV_I] simp_thms(21) id_apply)
  apply (unfold id_def[THEN sym])
  apply (erule exE)
  apply (erule conjE)
  apply (drule pre_alist.in_rel[THEN iffD1, rotated -1])
  apply (erule exE)
  apply (erule conjE)
  apply (erule CollectE)
  apply (erule conjE)
  apply (erule conjE)
  apply (insert assms(1)[unfolded nonrep_def eq_shape_def mr_rel_pre_alist_def pre_alist.map_id])
  apply (rotate_tac -1)
  apply (hypsubst_thin)
  subgoal premises prems for x' y z
    apply (insert prems(1))
    apply (erule allE)
    apply (erule impE)
     apply (subst pre_alist.rel_map)
     apply (subst pre_alist.rel_map)
     apply (rule pre_alist.rel_refl_strong)
      apply (drule subsetD[OF prems(2), THEN Collect_case_prodD] 
        subsetD[OF prems(3), THEN Collect_case_prodD]; 
        (assumption)?; (rule sym; assumption)?)+
    apply (elim exE)
    apply (subst pre_alist.map_comp[unfolded trans[OF id_o o_id[symmetric]]])
    apply (subst pre_alist.map_comp[THEN sym]; (rule prems bij_id supp_id_bound)?)
    subgoal premises subprems for f
      apply (rule exI[of _ f]) (* instantiation not necessary but easy *)
      apply (subst subprems)
      apply (subst pre_alist.map_comp; (rule prems bij_id supp_id_bound)?)
      apply (unfold o_id id_o)
      apply (rule refl)
      done
    done
  done


(* Here we need pullback preservation: *)
lemma nonrep_map_F_rev:
  fixes x :: "('k, 'v) pre_alist" and g :: "'v \<Rightarrow> 'v'"
  assumes "nonrep (map_pre_alist id g x)"
  shows "nonrep x"
  using assms apply -
  subgoal premises prems
    apply (unfold nonrep_def eq_shape_def)
    apply (rule allI)
    apply (rule impI)

(* alt *)
    apply (insert prems(1)[unfolded nonrep_def eq_shape_def])
    apply (elim allE impE)
     apply (rule pre_alist.mr_rel_map(1)[THEN iffD2]; (rule prems supp_id_bound bij_id)?)
     apply (drule pre_alist.mr_rel_map(2)[rotated -1, of _ _ _ _ id])
     apply (unfold o_id id_o Grp_UNIV_id eq_OO OO_eq)
     apply (assumption)

    apply (erule exE)
    apply (subst (asm) pre_alist.map_comp; (rule prems supp_id_bound bij_id)?)
    apply (unfold o_id id_o)

    apply (subst (asm) pre_alist.rel_eq[symmetric])
    apply (unfold pre_alist.mr_rel_id)
    apply (drule iffD1[OF pre_alist.mr_rel_map(1), rotated -1]; (rule prems supp_id_bound bij_id)?)
    apply (unfold id_o OO_eq)
    apply (drule rel_F_exchange[rotated])
     apply (rule iffD1[OF pre_alist.mr_rel_flip])
     apply (subst (asm) pre_alist.mr_rel_map(3))
     apply (unfold Grp_def)
     apply (tactic \<open>Ctr_Sugar_Tactics.unfold_thms_tac @{context} @{thms eqTrueI[OF UNIV_I] simp_thms(21) id_apply}\<close>)
     apply (subst (asm) eq_commute) (*lin_live_pos*)
     apply (unfold eq_OO conversep_def)
     apply (elim pre_alist.mr_rel_mono_strong0) (*- len vartypes - 1*)
      (*left subtactic is for frees and bounds, right subtactic for lives*)
    apply ((rule ballI,rule refl)?; (rule ballI,rule ballI,rule impI,rotate_tac 2,subst (asm) eq_commute,assumption))+

    apply (erule thin_rl)
    apply (subst (asm) Grp_UNIV_def[symmetric]) (*lin_live_pos*)
    apply (rule exI)
    apply (subst (asm) eq_alt) (* repeat lives - 1 *)
    apply (subst (asm) pre_alist.mr_rel_Grp)
    apply (unfold eqTrueI[OF subset_UNIV] eqTrueI[OF UNIV_I] UNIV_def[THEN sym] simp_thms(21) Grp_def)
    apply (assumption)
    done
  done

lemma nonrep_mapF_bij:
  fixes x :: "('k, 'v) pre_alist" and g::"'k \<Rightarrow> 'k"
  assumes g: "bij g" and x: "nonrep x"
  shows "nonrep (map_pre_alist g id x)"
  using assms apply -
  subgoal premises prems
    apply (unfold nonrep_def eq_shape_def)
    apply (rule allI)
    apply (rule impI)
    apply (drule pre_alist.mr_rel_map(1)[THEN iffD1, rotated -1]; (rule supp_id_bound bij_id)?)
    apply (unfold o_id Grp_UNIV_id eq_OO Grp_OO_top)
    apply (drule x[unfolded nonrep_def eq_shape_def, rule_format])
    apply (erule exE conjE)+
    apply hypsubst_thin
    subgoal for _ f
      apply (rule exI[of _ "f o inv g"])
      apply (rule sym)
      apply (rule trans)
       apply (rule pre_alist.map_comp; (rule supp_id_bound bij_id)?)
      apply (unfold id_o o_id inv_o_simp1[OF g] o_assoc[symmetric])
      apply (rule refl)
      done
    done
  done

lemma nonrep_mapF_bij_2:
  fixes x :: "('k, 'v) pre_alist" and g::"'k \<Rightarrow> 'k" and f::"'v \<Rightarrow> 'v"
  assumes g: "bij g" and x: "nonrep x"
  shows "nonrep (map_pre_alist g f x)" 
  using assms apply -
  subgoal premises prems
    apply (rule nonrep_mapF_bij[OF prems(1) nonrep_map_F[OF prems(2)], 
          unfolded pre_alist.map_comp id_o o_id])
    done
  done


typedef ('k::var,'v) alist = "{x :: ('k, 'v) pre_alist. nonrep x}"
  apply (unfold mem_Collect_eq nonrep_def eq_shape_def mr_rel_pre_alist_def pre_alist.map_id)
  by (rule ex_nonrep)

definition keys' :: "('k::var, 'v) alist \<Rightarrow> 'k set" where "keys' = keys o Rep_alist"
definition vals' :: "('k::var, 'v) alist \<Rightarrow> 'v set" where "vals' = vals o Rep_alist"

definition map_alist :: "('k::var \<Rightarrow> 'k) \<Rightarrow> ('v \<Rightarrow> 'v') \<Rightarrow> ('k, 'v) alist \<Rightarrow> ('k, 'v') alist"
  where "map_alist f g = Abs_alist o map_pre_alist (asBij f) g o Rep_alist"

definition rrel_alist :: "('v \<Rightarrow> 'v' \<Rightarrow> bool) \<Rightarrow> ('k::var, 'v) alist \<Rightarrow> ('k::var, 'v') alist \<Rightarrow> bool"
  where "rrel_alist R x x' = rel_pre_alist (=) R (Rep_alist x) (Rep_alist x')"

(* Verifying the axioms of a MRBNF for F':  *)
lemma F'_map_id: "map_alist id id = id"
  apply (unfold map_alist_def asSS_def asBij_def 
      eqTrueI[OF bij_id] eqTrueI[OF supp_id_bound] if_True)
  apply (rule ext)
  apply (unfold o_apply pre_alist.map_id Rep_alist_inverse)
  apply (unfold id_def)
  apply (rule refl)
  done

lemma F'_map_comp1_:
  fixes u1 v1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 v2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 v3 :: "'a3::var \<Rightarrow> 'a3"
  assumes "|supp u1| <o |UNIV :: 'a1 set|" "|supp v1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|" "bij v2" "|supp v2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|" "bij v3" "|supp v3| <o |UNIV :: 'a3 set|"
  shows "map_F' (v1 o u1) (v2 o u2) (v3 o u3) (g o f) = map_F' v1 v2 v3 g o map_F' u1 u2 u3 f"
  using assms apply -
  subgoal premises prems
    apply (unfold map_F'_def asBij_def asSS_def)
    apply (unfold eqTrueI[OF bij_comp[OF prems (3, 5)]] eqTrueI[OF bij_comp[OF prems (7, 9)]] 
        eqTrueI[OF supp_comp_bound[OF prems(1,2) infinite_UNIV]] eqTrueI[OF supp_comp_bound[OF prems(4,6) infinite_UNIV]]
        if_True)
    apply (unfold 
        eqTrueI[OF assms(1)] eqTrueI[OF assms(2)] eqTrueI[OF assms(3)] eqTrueI[OF assms(4)] eqTrueI[OF assms(5)] eqTrueI[OF assms(6)]
        eqTrueI[OF assms(7)] eqTrueI[OF assms(8)] eqTrueI[OF assms(9)] eqTrueI[OF assms(10)]
        if_True)
    apply (rule ext)
    apply (subst F.map_comp0; (rule prems)?)
    apply (unfold o_apply)
    apply (subst Abs_F'_inverse[unfolded mem_Collect_eq])
     apply (rule nonrep_mapF_bij_2; (rule prems Rep_F'[unfolded mem_Collect_eq])?)
    apply (rule refl)
    done
  done


(* This tactic is applicable to all 4 of the following <F'_setx_map_> lemmas*)
ML \<open>
open BNF_Util BNF_Tactics

fun mk_set_map_tac set_F'_def map_F'_def Abs_F'_inverse Rep_F' nonrep_mapF_bij_2 F_set_map ctxt =
  HEADGOAL (Subgoal.FOCUS
    (fn {prems = prems, context = ctxt, ...} =>
      unfold_thms_tac ctxt ([set_F'_def, map_F'_def] @ map (fn thm => thm RS eqTrueI) prems @
        @{thms asSS_def asBij_def if_True o_apply}) THEN
      HEADGOAL (EVERY' [EqSubst.eqsubst_tac ctxt [0] [Abs_F'_inverse],
        rtac ctxt nonrep_mapF_bij_2 THEN_ALL_NEW resolve_tac ctxt (Rep_F' :: prems),
        rtac ctxt F_set_map THEN_ALL_NEW
          resolve_tac ctxt prems])
    ) ctxt)
\<close>

lemma F'_set1_map_:
  fixes u1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  assumes "|supp u1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  shows "set1_F' (map_F' u1 u2 u3 f b) = u1 ` set1_F' b"
  using assms apply -
  apply (tactic \<open>mk_set_map_tac @{thm set1_F'_def} @{thm map_F'_def} @{thm Abs_F'_inverse[unfolded mem_Collect_eq]}
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep_mapF_bij_2} @{thm F.set_map(1)} @{context} 
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  subgoal premises prems
    apply (unfold set1_F'_def map_F'_def asSS_def asBij_def
        eqTrueI[OF prems(1)] eqTrueI[OF prems(2)] eqTrueI[OF prems(3)] eqTrueI[OF prems(4)] eqTrueI[OF prems(5)] o_apply if_True)
    apply (subst Abs_F'_inverse[unfolded mem_Collect_eq])
     apply (rule nonrep_mapF_bij_2; (rule prems Rep_F'[unfolded mem_Collect_eq])?)
    apply (rule F.set_map(1); (rule prems))
    done
  done

lemma F'_set2_map_:
  fixes u1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  assumes "|supp u1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  shows "set2_F' (map_F' u1 u2 u3 f b) = u2 ` set2_F' b"
  using assms apply -
  apply (tactic \<open>mk_set_map_tac @{thm set2_F'_def} @{thm map_F'_def} @{thm Abs_F'_inverse[unfolded mem_Collect_eq]}
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep_mapF_bij_2} @{thm F.set_map(2)} @{context}\<close>)
  done

lemma F'_set3_map_:
  fixes u1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  assumes "|supp u1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  shows "set3_F' (map_F' u1 u2 u3 f b) = u3 ` set3_F' b"
  using assms apply -
  apply (tactic \<open>mk_set_map_tac @{thm set3_F'_def} @{thm map_F'_def} @{thm Abs_F'_inverse[unfolded mem_Collect_eq]}
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep_mapF_bij_2} @{thm F.set_map(3)} @{context}\<close>)
  done

lemma F'_set4_map_:
  fixes u1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  assumes "|supp u1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  shows "set4_F' (map_F' u1 u2 u3 f b) = f ` set4_F' b"
  using assms apply -
  apply (tactic \<open>mk_set_map_tac @{thm set4_F'_def} @{thm map_F'_def} @{thm Abs_F'_inverse[unfolded mem_Collect_eq]}
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep_mapF_bij_2} @{thm F.set_map(4)} @{context}\<close>)
  done

lemma F'_map_cong_[fundef_cong]:
  fixes u1 v1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 v2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 v3 :: "'a3::var \<Rightarrow> 'a3"
  assumes "|supp u1| <o |UNIV :: 'a1 set|" "|supp v1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|" "bij v2" "|supp v2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|" "bij v3" "|supp v3| <o |UNIV :: 'a3 set|"
    and "\<forall> a \<in> set1_F' x. u1 a = v1 a"
    and "\<forall> a \<in> set2_F' x. u2 a = v2 a"
    and "\<forall> a \<in> set3_F' x. u3 a = v3 a"
    and "\<forall> a \<in> set4_F' x. f a = g a"
  shows "map_F' u1 u2 u3 f x = map_F' v1 v2 v3 g x"
  using assms apply -
  subgoal premises prems
    apply (unfold map_F'_def asSS_def asBij_def 
        eqTrueI[OF assms(1)] eqTrueI[OF assms(2)] eqTrueI[OF assms(3)] eqTrueI[OF assms(4)] eqTrueI[OF assms(5)] 
        eqTrueI[OF assms(6)] eqTrueI[OF assms(7)] eqTrueI[OF assms(8)] eqTrueI[OF assms(9)] eqTrueI[OF assms(10)]
        eqTrueI[OF assms(11)] eqTrueI[OF assms(12)] eqTrueI[OF assms(13)] eqTrueI[OF assms(14)] if_True o_apply)
    apply (subst F.map_cong; (rule prems(14,13,12,11,10,9,8,7,6,5,4,3,2,1))?) (*reverse prems so that the v-prems apply before the u-prems*)
         apply (rule refl)
         apply (erule bspec[OF prems(11)[unfolded set1_F'_def o_apply]] 
        bspec[OF prems(12)[unfolded set2_F'_def o_apply]]
        bspec[OF prems(13)[unfolded set3_F'_def o_apply]]
        bspec[OF prems(14)[unfolded set4_F'_def o_apply]])+
    apply (rule refl)
    done
  done

lemma F'_set1_bd: "\<And>b. |set1_F' b| <o natLeq"
  apply (unfold set1_F'_def o_apply)
  by (rule F.set_bd(1))

lemma F'_set2_bd: "\<And>b. |set2_F' b| <o natLeq"
  apply (unfold set2_F'_def o_apply)
  by (rule F.set_bd(2))

lemma F'_set3_bd: "\<And>b. |set3_F' b| <o natLeq"
  apply (unfold set3_F'_def o_apply)
  by (rule F.set_bd(3))

lemma F'_set4_bd: "\<And>b. |set4_F' b| <o natLeq"
  apply (unfold set4_F'_def o_apply)
  by (rule F.set_bd(4))

lemma F'_rel_comp_leq_: "rrel_F' Q OO rrel_F' R \<le> rrel_F' (Q OO R)"
  apply (rule predicate2I)
  apply (erule relcomppE)
  apply (unfold rrel_F'_def)
  subgoal premises prems for x y b
    apply (insert prems(1))
    apply (drule relcomppI[of _ "Rep_F' x" "Rep_F' b" _ "Rep_F' y"])
     apply (rule prems(2))
    apply (unfold F.rel_compp[symmetric] eq_OO)
    apply (assumption)
    done
  done

lemma rrel_F_map_F3:
  fixes x :: "('a :: var,'b :: var,'c,'d) F"
  shows "rrel_F (Grp (f :: 'c \<Rightarrow> 'c)) R x y = rrel_F (=) R (map_F id id f id x) y"
  apply (unfold F.rel_map(1) Grp_def id_apply eqTrueI[OF UNIV_I] simp_thms(21))
  apply (rule iffI)
   apply (erule F.rel_mono_strong; (assumption?, (erule sym)?))+
  done

lemma F'_in_rel:
  fixes u1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var \<Rightarrow> 'a3"
  assumes u1: "|supp u1| <o |UNIV :: 'a1 set|"
    and u2: "bij u2" "|supp u2| <o |UNIV :: 'a2 set|" 
    and u3: "bij u3" "|supp u3| <o |UNIV :: 'a3 set|"
  shows "rrel_F' R (map_F' u1 u2 u3 id x) y =
    (\<exists>z. set4_F' z \<subseteq> {(x, y). R x y} \<and> map_F' id id id fst z = x \<and> map_F' u1 u2 u3 snd z = y)"
  using assms apply -
  subgoal premises prems
    apply (unfold rrel_F'_def set4_F'_def map_F'_def asSS_def asBij_def if_True 
        eqTrueI[OF prems(1)] eqTrueI[OF prems(2)] eqTrueI[OF prems(3)] eqTrueI[OF prems(4)] 
        eqTrueI[OF prems(5)]
        eqTrueI[OF supp_id_bound] eqTrueI[OF bij_id] o_apply)
    apply (subst Abs_F'_inverse[unfolded mem_Collect_eq])
     apply (rule nonrep_mapF_bij_2; (rule prems Rep_F'[unfolded mem_Collect_eq])?)

(* instantiation for bounds B, frees F, lives A: [_ * nr_BFs @ id * nr_BFs @ _ * nr_As @ id * nr_As] *)
    apply (subst F.map_comp[of _ _ id id _ _ id id, unfolded o_id id_o, symmetric]; (rule prems bij_id supp_id_bound)?)
    apply (subst rrel_F_map_F3[symmetric])
    apply (subst F.in_rel; (rule prems)?)

    apply (rule iffI)
    apply (unfold Grp_def eqTrueI[OF UNIV_I] simp_thms(21))
     apply (erule exE)
     apply (erule conjE)
     apply (erule conjE)
     apply (erule CollectE)
     apply (erule conjE)
    subgoal premises subprems for z
   apply (rule exI[of _ "(Abs_F' (map_F id id fst id z))"])
      apply ((subst Abs_F'_inverse[unfolded mem_Collect_eq]), (tactic \<open>defer_tac 1\<close>))+ 
         apply (tactic \<open>distinct_subgoals_tac\<close>)
      prefer 2
       apply (rule nonrep_map_F_rev; (rule bij_id supp_id_bound)?)
       apply (subst F.map_comp; (rule bij_id supp_id_bound)?)
       apply (unfold o_id id_o)
       apply (subst subprems)
      apply (rule Rep_F'[unfolded mem_Collect_eq])

      apply (subst (1 2) F.map_comp; (rule supp_id_bound bij_id prems)?)
      apply (unfold o_id id_o)
      apply (rule conjI)
      apply ((rule conjI)?,
        (subst F.set_map; (rule supp_id_bound bij_id)?),
        subst image_id,
        rule subprems)+
      apply (rule conjI)
       apply (subst subprems)
       apply (rule Rep_F'_inverse[unfolded mem_Collect_eq])

      apply (subst (2) Rep_F'_inverse[symmetric])
      apply (subst subprems(2)[symmetric])
      apply (rule F.map_cong[THEN arg_cong]; (rule prems refl)?)
      apply (drule rev_subsetD[THEN Collect_case_prodD])
       apply (rule subprems)
      apply (rule sym)
      apply (subst o_apply)
      apply (assumption)
      done
    apply (erule exE)
    apply (erule conjE)
    apply (erule conjE)
    apply (hypsubst_thin)
    subgoal premises subprems for z
      apply (rule exI)
      apply (subst Abs_F'_inverse[unfolded mem_Collect_eq])
       apply (rule nonrep_mapF_bij_2; (rule supp_id_bound bij_id Rep_F'[unfolded mem_Collect_eq])?)
      apply (rule conjI; (rule conjI)?)

        prefer 3(* subgoal 3 is solvable without the exI instantiation and it "instantiates" ?z 
          so that the other 2 subgoals are solvable as well*)
        apply (subst Abs_F'_inverse[unfolded mem_Collect_eq])
         apply (rule nonrep_mapF_bij_2; (rule prems Rep_F'[unfolded mem_Collect_eq])?)
        apply (subst F.map_comp; (rule bij_id supp_id_bound prems)?) (*having the id prems before the actual prems is important!*)
        apply (unfold o_id)
        apply (unfold o_def)
        apply (rule F.map_cong; (rule prems refl)?)
        apply (rule snd_conv)

       apply (rule CollectI)
       apply (subst F.set_map; (rule bij_id supp_id_bound)?)+
       apply (unfold image_ident)
       apply (rule conjI; (rule subprems)?)+
        apply (rule subsetI)
        apply (erule imageE)
        apply (rule CollectI)
       apply (rule case_prodI2)
        apply (drule trans[OF sym, THEN iffD1[OF prod.inject]])
         apply (assumption)
        apply (erule conjE)
        apply (rule trans[OF sym])
         apply (assumption)
        apply (erule arg_cong)

      apply (subst F.map_comp; (rule supp_id_bound bij_id)?)
      apply (unfold o_def fst_conv id_def)
      apply (rule refl)
      done
    done
  done

ML \<open>
open BNF_Util BNF_Tactics

fun mk_strong_tac rrel_F'_def mr_rel_F_def F_strong F_map_id ctxt =
  HEADGOAL (Subgoal.FOCUS
    (fn {prems, context = ctxt, ...} => 
    let
      val _ = prems |> map @{print tracing}
    in
      unfold_thms_tac ctxt [rrel_F'_def] THEN
      HEADGOAL (rtac ctxt (unfold_thms ctxt @{thms inf.idem} 
        (unfold_thms ctxt [mr_rel_F_def, F_map_id] F_strong
         OF (map (fn prem => unfold_thms ctxt [rrel_F'_def] prem) prems))))
    end) ctxt)
\<close>

lemma F'_strong:
  assumes "rrel_F' R x x'" 
    and "rrel_F' Q x x'"
  shows "rrel_F' (inf R Q) x x'" 
  using assms apply -
  apply (tactic \<open>mk_strong_tac @{thm rrel_F'_def} @{thm mr_rel_F_def} @{thm F_strong} @{thm F.map_id} @{context} 
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  subgoal premises prems
    apply (unfold rrel_F'_def)
    apply (rule F_strong[unfolded mr_rel_F_def F.map_id, 
          OF prems(1)[unfolded rrel_F'_def] prems(2)[unfolded rrel_F'_def], 
          unfolded inf.idem])
    done
  done

mrbnf "('a::var, 'b::var, 'c::var, 'd) F'"
  map: map_F'
  sets: free: set1_F' bound: set2_F' bound: set3_F' live: set4_F'
  bd: natLeq
  rel: rrel_F'
  var_class: var

  subgoal by (rule F'_map_id)
  subgoal premises prems by (rule F'_map_comp1_; (rule prems))
  subgoal premises prems 
    apply (rule F'_map_cong_; (rule prems ballI)?)
    by (rule prems, assumption)+
  subgoal premises prems 
    apply (rule ext)
    apply (unfold o_apply)
    by(rule F'_set1_map_[OF prems])
  subgoal premises prems
    apply (rule ext)
    apply (unfold o_apply F'_set2_map_[OF prems]) 
    by(rule refl)
  subgoal premises prems 
    apply (rule ext)
    apply (unfold o_apply F'_set3_map_[OF prems]) 
    by(rule refl)
  subgoal premises prems 
    apply (rule ext)
    apply (unfold o_apply F'_set4_map_[OF prems]) 
    by(rule refl)
  subgoal by (rule infinite_regular_card_order_natLeq)
  subgoal by (rule F'_set1_bd)
  subgoal by (rule F'_set2_bd)
  subgoal by (rule F'_set3_bd)
  subgoal by (rule F'_set4_bd)
  subgoal by (rule F'_rel_comp_leq_)
  subgoal premises prems by (rule F'_in_rel[OF prems])
  done        

end