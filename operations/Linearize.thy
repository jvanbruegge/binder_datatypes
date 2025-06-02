theory Linearize
  imports "Binders.MRBNF_Composition" "Binders.MRBNF_Recursor"
begin

(* This theory we start with an MRBNF F, which is assumed (in the imported theory 
Common_Data_Codata_Bindings) to have the following characteristics:
  ** is map-constrained to small-support endofunctions in the 1st position, 
  ** is map-constrained to small-support endobijections in the 2nd position,  
  ** is unconstrained in the 3rd and 4th position.   
We show that applying the nonrepetitiveness construction at the 3rd position (on which F is assumed 
to be pullback-preserving), we transform it into an MRBNF F' that has the same characteristics 
as F except that the 3rd position becomes map-constrained to small-support endobijections.  
*)

typedecl ('a, 'b, 'c, 'd) F
consts map_F :: "('a :: var \<Rightarrow> 'a) \<Rightarrow> ('b :: var \<Rightarrow> 'b) \<Rightarrow>
  ('c \<Rightarrow> 'c') \<Rightarrow> ('d \<Rightarrow> 'd') \<Rightarrow> ('a, 'b, 'c, 'd) F \<Rightarrow> ('a, 'b, 'c', 'd') F"
consts set1_F :: "('a :: var, 'b :: var, 'c, 'd) F \<Rightarrow> 'a set"
consts set2_F :: "('a :: var, 'b :: var, 'c, 'd) F \<Rightarrow> 'b set"
consts set3_F :: "('a :: var, 'b :: var, 'c, 'd) F \<Rightarrow> 'c set"
consts set4_F :: "('a :: var, 'b :: var, 'c, 'd) F \<Rightarrow> 'd set"
consts rrel_F :: "('c \<Rightarrow> 'c' \<Rightarrow> bool) \<Rightarrow> ('d \<Rightarrow> 'd' \<Rightarrow> bool) \<Rightarrow> ('a :: var, 'b :: var, 'c, 'd) F \<Rightarrow> ('a, 'b, 'c', 'd') F \<Rightarrow> bool"

declare [[mrbnf_internals]]
declare [[typedef_overloaded]]
mrbnf "('a :: var, 'b :: var, 'c, 'd) F"
  map: map_F
  sets: free: set1_F bound: set2_F live: set3_F live: set4_F
  bd: natLeq
  rel: rrel_F
  var_class: var
  sorry

ML \<open>map (fn x => x+1) [1, 2, 3] \<close>

ML \<open>@{term "map (\<lambda>x. x+1) [(1::int), 2, 3]"} \<close>
ML \<open>Const ("List.list.Nil", @{typ"int list"})\<close>

print_mrbnfs
declare [[ML_print_depth=10000]]
ML \<open>MRBNF_Def.mrbnf_of @{context} @{type_name F} |> the \<close>

axiomatization where
  (* The next property assumes preservation of pullbacks on the third position. 
   NB: All MRBNFs already preserve _weak_ pullbacks, i.e., they satisfy the following property 
   without uniqueness.  *)
  F_rel_map_set2_strong: 
  "\<And> R S (x :: ('a :: var,'b :: var,'c,'d) F) y.
    rrel_F R S x y =
      (\<exists>!z. set3_F z \<subseteq> {(x, y). R x y} \<and>
            set4_F z \<subseteq> {(x, y). S x y} \<and> map_F id id fst fst z = x \<and> map_F id id snd snd z = y)"
  and
  (* The next property assumes that nonrepetitive elements exist: *)
  ex_nonrep: "\<exists>x. \<forall>x'. (\<exists> R. rrel_F R (=) x x') \<longrightarrow> (\<exists> f. x' = map_F id id f id x)"

abbreviation "rel_F \<equiv> mr_rel_F"

(* Important consequence of preservation of pullbacks (which is actually equivalent to it): 
The relator is closed under intersections. *)
lemma F_strong:
  "rel_F id id R3 R4 x y \<Longrightarrow> rel_F id id Q3 Q4 x y \<Longrightarrow> rel_F id id (inf R3 Q3) (inf R4 Q4) x y"
  apply (unfold F.map_id mr_rel_F_def)
  apply (frule F.mr_rel_mono_strong0[OF supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound,
        of _ _ _ _ top top, unfolded mr_rel_F_def F.map_id])
      apply (rule ballI)
      apply (rule refl)
     apply (rule ballI)
     apply (rule refl)
    apply (unfold top_apply)
    apply (intro ballI impI)
    apply (subst (1) top_bool_def)
    apply(rule TrueI)
   apply (intro ballI impI)
   apply (subst (1) top_bool_def)
   apply(rule TrueI)
  apply(rotate_tac 2)
  apply (drule F_rel_map_set2_strong[THEN iffD1, unfolded top_apply])
  apply (unfold top_bool_def Collect_const_case_prod if_True eqTrueI[OF subset_UNIV] simp_thms(22))
  apply (unfold F.in_rel[OF supp_id_bound bij_id supp_id_bound, unfolded id_apply F.map_id OO_Grp_alt]
      id_def[symmetric])
  apply (elim exE alt_ex1E)
  subgoal for z l r
    apply (unfold conj_assoc)
    apply (frule spec2[of _ l z])
    apply (drule spec2[of _ r z])
    apply (elim impE conjE)
       apply (intro conjI; assumption)
      apply (intro conjI; assumption)
     apply (intro conjI; assumption)
    apply (unfold mem_Collect_eq conj_assoc top_apply top_bool_def Collect_const_case_prod if_True)
    apply (elim conjE)
    apply (rule exI[of _ z])
    apply (unfold inf_apply inf_bool_def)
    apply (intro conjI) 
       apply (rule subrelI)
       apply (rule CollectI)
       apply (rule case_prodI)
       apply (rule conjI)
        apply (drule rev_subsetD[THEN Collect_case_prodD])
         apply (assumption)
        apply (unfold prod.sel(1,2))
        apply (assumption)
       apply (drule rev_subsetD[THEN Collect_case_prodD, of _ _ Q3])
        apply (rule subst[of "set3_F l" "set3_F z"])
         apply (rule arg_cong[of l z])
         apply (assumption)
        apply (assumption)
       apply (unfold prod.sel(1,2))
       apply (assumption)
      apply (rule subrelI)
      apply (rule CollectI)
      apply (rule case_prodI)
      apply (rule conjI)
       apply (drule rev_subsetD[THEN Collect_case_prodD])
        apply (assumption)
       apply (unfold prod.sel(1,2))
       apply (assumption)
      apply (drule rev_subsetD[THEN Collect_case_prodD, of _ _ Q4])
       apply (rule subst[of "set4_F l" "set4_F z"])
        apply (rule arg_cong[of l z])
        apply (assumption)
       apply (assumption)
      apply (unfold prod.sel(1,2))
      apply (assumption)
     apply (assumption)
    apply (assumption)
    done
  done

(* Another important consequence: the following "exchange"-property, which could be read: 
Since the atoms have a fixed position, we can permute the relations: *)
lemma rel_F_exchange: 
  fixes x :: "('a1::var,'a2::var,'a3,'a4) F" and x' :: "('a1,'a2,'a3','a4') F"
  assumes "rel_F id id R2 R3 x x'" and "rel_F id id Q2 Q3 x x'"
  shows "rel_F id id R2 Q3 x x'" 
  using assms apply -
  subgoal premises prems
    apply (rule F.mr_rel_mono_strong0[OF supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound F_strong[OF assms]])
       apply (unfold id_apply eqTrueI[OF refl] ball_triv simp_thms(17) inf_apply inf_bool_def)
       apply (rule TrueI)+
     apply (intro ballI impI)
     apply (erule conjunct1)
    apply (intro ballI impI)
    apply (erule conjunct2)
    done
  done


(* Then notion of two items having the same shape (w.r.t. the 3rd position): *)
definition sameShape1 :: "('a1::var,'a2::var,'a3,'a4) F \<Rightarrow> ('a1,'a2,'a3,'a4) F \<Rightarrow> bool" where 
  "sameShape1 x x' \<equiv> \<exists> R. rel_F id id R (=) x x'"

definition nonrep2 :: "('a1::var,'a2::var,'a3,'a4) F \<Rightarrow> bool" where 
  "nonrep2 x \<equiv> \<forall> x'. sameShape1 x x' \<longrightarrow> (\<exists> f. x' = map_F id id f id x)"

lemma op_eq_triv_sym: "(\<lambda>x. (=) (g x)) = (\<lambda>x z. z = g x)"
  apply (intro ext)
  apply (rule eq_commute)
  done

lemma nonrep2_map_F:
  fixes x :: "('a1::var,'a2::var,'a3,'a4) F"
    and v :: "'a1 \<Rightarrow> 'a1" and u :: "'a2\<Rightarrow>'a2" and g :: "'a4 \<Rightarrow> 'b4"
  assumes v: "|supp v| <o |UNIV :: 'a1 set|"  and u: "bij u" "|supp u| <o |UNIV :: 'a2 set|" 
  assumes "nonrep2 x"
  shows "nonrep2 (map_F v u id g x)"
  using assms apply -
  subgoal premises prems
    apply (unfold nonrep2_def sameShape1_def)
    apply (intro allI impI)
    apply (elim exE)
    subgoal for y' R
      apply (unfold F.map_comp[OF v u(1,2) supp_id_bound bij_id supp_id_bound])
      apply (subst (1) trans[OF o_id id_o[symmetric]])
      apply (subst (1 2 4) trans[OF id_o o_id[symmetric]])
      apply (fold F.map_comp[OF supp_id_bound bij_id supp_id_bound v u(1,2)])
      apply (drule iffD1[OF F.mr_rel_map(1)[OF v u(1,2) supp_id_bound bij_id supp_id_bound]])
      apply (unfold trans[OF id_o o_id[symmetric]])
      apply (unfold Grp_UNIV_id)
      apply (subst (asm) trans[OF OO_eq eq_OO[symmetric]])
      apply (subst (asm) trans[OF eq_OO OO_eq [symmetric]])
      apply (subst (asm) (1 2) eq_alt)
      apply (unfold mr_rel_F_def o_id F.rel_compp F.rel_Grp F.map_id)
      apply (unfold eqTrueI[OF subset_UNIV] simp_thms(21) UNIV_def[symmetric] id_o)
      apply (unfold Grp_UNIV_id OO_def Grp_def)
      apply (unfold eqTrueI[OF UNIV_I] simp_thms(21))
      apply (subst (asm) id_apply)
      apply (elim exE conjE)
      apply (drule iffD1[OF F.in_rel[OF v u(1,2)]])
      apply (elim exE conjE CollectE)

      subgoal premises subprems for y z
        thm subprems
          (* now show this (xx'): 
     rel_F id id R (=) x x'
  \<equiv> rel_F id id R (=) (map_F id id fst fst z) (map_F id id snd snd z)                     (mr_rel_F_def)
  \<equiv> rrel_F R (=) (map_F id id id id (map_F id id fst fst z)) (map_F id id snd snd z)      (F.map_id) 
  \<equiv> rrel_F R (=) (map_F id id fst fst z) (map_F id id snd snd z)
*)
        apply (insert F.rel_refl_strong[of z "\<lambda>a b. R (fst a) (snd b)" "\<lambda>a b. (snd b) = (fst a)"])
        apply (unfold eqTrueI[OF subsetD[OF subprems(4), THEN Collect_case_prodD]])
        apply (unfold eqTrueI[OF subsetD[OF subprems(5), THEN Collect_case_prodD]])
        apply (unfold implies_True_equals triv_forall_equality True_implies_equals) 
        apply (subst (asm) F.rel_map(2)[symmetric])
        apply (subst (asm) F.rel_map(1)[symmetric])
        apply (subst (asm) subprems(2))
        apply (subst (asm) eq_commute) (*this is xx'*)


        apply (insert prems(4)[unfolded nonrep2_def sameShape1_def])
        apply (unfold mr_rel_F_def F.map_id)
        apply (elim allE impE)
         apply (rule exI)
         apply (assumption) (* this is x'*)
        apply (elim exE)
        apply (subst subprems(1))
        apply (subst subprems(3)[symmetric])
        apply (subst F.map_comp[OF v u(1,2) supp_id_bound bij_id supp_id_bound])
        apply (subst (1 2) trans[OF id_o o_id[symmetric]])
        apply (subst F.map_comp[OF supp_id_bound bij_id supp_id_bound v u(1,2), symmetric])
        apply (rule exI)
        apply (rule arg_cong[of _ _ "map_F v u id g"])
        apply (assumption)
        done
      done
    done
  done


(* Here we need pullback preservation: *)
lemma nonrep2_map_F_rev:
  fixes x :: "('a1::var,'a2::var,'a3,'a4) F" and u :: "'a2\<Rightarrow>'a2" and g :: "'a4 \<Rightarrow> 'b4"
  assumes u: "bij u" "|supp u| <o |UNIV :: 'a2 set|" 
  assumes "nonrep2 (map_F id u id g x)"
  shows "nonrep2 x"
  using assms apply -
  subgoal premises prems
    apply (unfold nonrep2_def sameShape1_def)
    apply (intro allI impI)
    apply (elim exE)
    subgoal for x' R
      apply (frule F.mr_rel_map(2)[OF supp_id_bound bij_id supp_id_bound supp_id_bound u, of R "(=)" x x' id g])
      apply (rotate_tac) (*maybe we can later make that a drule and remove the rotate*)
      apply (subst (asm) (2) trans[OF o_id id_o[symmetric]])
      apply (subst (asm) Grp_UNIV_id)
      apply (subst (asm) trans[OF eq_OO OO_eq[symmetric]])
      apply (subst (asm) trans[OF OO_eq eq_OO[symmetric]])
      apply (subst (asm) eq_alt)
      apply (fold F.mr_rel_map(1)[OF supp_id_bound u supp_id_bound bij_id supp_id_bound])

      apply (insert assms(3)[unfolded nonrep2_def sameShape1_def])
      apply (elim allE impE)
       apply (rule exI)
       apply (assumption)
      apply (erule thin_rl)
      apply (erule exE)
      apply (unfold F.map_comp[OF supp_id_bound u(1,2) supp_id_bound bij_id supp_id_bound] o_id id_o)

      apply (drule conjI[OF sym UNIV_I[of x']])
        (* maybe this can be shortened *)
      apply (drule iffD1[OF Grp_def[symmetric, of "map_F id u id g" UNIV, THEN fun_cong, THEN fun_cong]])
      apply (drule iffD2[OF F.mr_rel_Grp[OF supp_id_bound u(1,2), of UNIV id UNIV g, unfolded Grp_def
              eqTrueI[OF subset_UNIV] simp_thms(21) UNIV_def[symmetric], 
              folded Grp_def, THEN fun_cong, THEN fun_cong]])



(*     
    map_F id u id g x' = map_F id u f g x    
    rel_F id u (Grp id) (Grp g) x' (map_F id u f g x)         (here)
    rel_F id id (Grp f) (Grp g OO conversep (Grp g)) x x'
    rel_F id id (Grp f) (=) x x'
*)

      apply (drule rel_F_exchange[of "Grp _" "(Grp g OO conversep (Grp g))", rotated])

       prefer 2
      subgoal for f
        apply(intro exI) 
        apply (unfold eq_alt)
        apply (unfold F.mr_rel_Grp[OF supp_id_bound bij_id supp_id_bound])
        apply (unfold eqTrueI[OF subset_UNIV] simp_thms(21))
        apply (fold UNIV_def)
        apply (unfold Grp_def eqTrueI[OF UNIV_I] simp_thms(21))
        apply (subst id_apply)
        apply (rule sym)
        apply (assumption)
        done

      apply (subst F.mr_rel_flip[OF bij_id supp_id_bound bij_id supp_id_bound, simplified, symmetric])
      apply (unfold F.mr_rel_map(3)[OF supp_id_bound u bij_id supp_id_bound u] Grp_def)
      apply (subst (asm) inv_o_simp1[OF bij_id])
      apply (subst (asm) inv_o_simp1[OF u(1)])
      apply (subst (asm) id_apply)
      apply (unfold eqTrueI[OF UNIV_I] simp_thms(21))
      apply (subst (asm) eq_commute)
      apply (subst (asm) eq_OO)
      apply (unfold conversep_def) 
      apply (elim F.mr_rel_mono_strong0[rotated 6]; (rule supp_id_bound bij_id)?)
         apply (rule ballI; rule refl)
        apply (rule ballI; rule refl)
       apply (intro ballI impI)
       apply (assumption)
      apply (intro ballI impI)
      apply (unfold OO_def)
      apply (elim exE conjE)
      apply (intro exI conjI; assumption)
      done

    done
  done

lemma nonrep2_map_F_rev_orig:
  fixes x :: "('a1::var,'a2::var,'a3,'a4) F" and u :: "'a2\<Rightarrow>'a2" and g :: "'a4 \<Rightarrow> 'b4"
  assumes u: "bij u" "|supp u| <o |UNIV :: 'a2 set|" 
  assumes "nonrep2 (map_F id u id g x)"
  shows "nonrep2 x"
  apply (unfold nonrep2_def sameShape1_def)
  apply (intro allI impI)
  apply (elim exE)
  subgoal for x' R
  proof -
    let ?y = "map_F id u id g x"  let ?y' = "map_F id u id g x'"
    assume r: "rel_F id id R (=) x x'"
    hence "rel_F id id R (=) ?y ?y'" 
      apply -
      apply (drule F.mr_rel_map(2)[OF supp_id_bound bij_id supp_id_bound supp_id_bound u, of R "(=)" x x' id g])
      apply (subst (asm) (2) trans[OF o_id id_o[symmetric]])
      apply (subst (asm) Grp_UNIV_id)
      apply (subst (asm) trans[OF eq_OO OO_eq[symmetric]])
      apply (subst (asm) trans[OF OO_eq eq_OO[symmetric]])
      apply (subst (asm) eq_alt)
      apply (fold F.mr_rel_map(1)[OF supp_id_bound u supp_id_bound bij_id supp_id_bound])
      apply (assumption)
      done
    then obtain f where "?y' = map_F id id f id ?y" 
      apply (atomize_elim)
      apply (insert assms(3)[unfolded nonrep2_def sameShape1_def])
      apply (elim allE impE)
       apply (rule exI)
       apply (assumption)
      apply (erule exE)
      apply (unfold F.map_comp[OF supp_id_bound u(1,2) supp_id_bound bij_id supp_id_bound] o_id id_o)
      apply (rule exI)
      apply (assumption)
      done
    hence y':"?y' = map_F id u f g x"
      apply -
      apply (unfold F.map_comp[OF supp_id_bound u(1,2) supp_id_bound bij_id supp_id_bound] o_id id_o)
      apply (assumption)
      done
    hence "rel_F id u (Grp id) (Grp g) x' (map_F id u f g x)"
      apply -
      apply (unfold F.mr_rel_Grp[OF supp_id_bound u(1,2), of UNIV id UNIV g, unfolded Grp_def
            eqTrueI[OF subset_UNIV] simp_thms(21) UNIV_def[symmetric], folded Grp_def])
      apply (unfold Grp_def)
      apply (rule conjI)
       apply (drule sym)
       apply (assumption)
      apply (rule UNIV_I)
      done
    hence "rel_F id id (Grp f) (Grp g OO conversep (Grp g)) x x'" (* We are here*)
      apply (subst F.mr_rel_flip[OF bij_id supp_id_bound bij_id supp_id_bound, simplified, symmetric])
      apply (unfold F.mr_rel_map(3)[OF supp_id_bound u bij_id supp_id_bound u] Grp_def)
      apply (subst (asm) inv_o_simp1[OF bij_id])
      apply (subst (asm) inv_o_simp1[OF u(1)])
      apply (subst (asm) id_apply)
      apply (unfold eqTrueI[OF UNIV_I] simp_thms(21))
      apply (subst (asm) eq_commute)
      apply (subst (asm) eq_OO)
      apply (unfold conversep_def) 
      apply (elim F.mr_rel_mono_strong0[rotated 6]; (rule supp_id_bound bij_id)?)
         apply (rule ballI; rule refl)
        apply (rule ballI; rule refl)
       apply (intro ballI impI)
       apply (assumption)
      apply (intro ballI impI)
      apply (unfold OO_def)
      apply (elim exE conjE)
      apply (intro exI conjI; assumption)
      done
    thm rel_F_exchange[OF this r]  rel_F_exchange[rotated, OF r, of "Grp f" "(Grp g OO conversep (Grp g))"] this r
    from this (*rel_F_exchange[OF this r]*)
    have "rel_F id id (Grp f) (=) x x'"
      by (rule rel_F_exchange[rotated, OF r, of "Grp f" "(Grp g OO conversep (Grp g))"] )
    thus "\<exists>f. x' = map_F id id f id x"
      apply(intro exI) 
      apply (unfold eq_alt F.mr_rel_Grp[OF supp_id_bound bij_id supp_id_bound])
      apply (unfold eqTrueI[OF subset_UNIV] simp_thms(21))
      apply (fold UNIV_def)
      apply (unfold Grp_def eqTrueI[OF UNIV_I] simp_thms(21) id_apply)
      apply (rule sym)
      apply (assumption)
      done
  qed
  done


lemma nonrep2_mapF_bij:
  fixes x :: "('a1::var,'a2::var,'a3,'a4) F" and g::"'a3\<Rightarrow>'a3"
  assumes g: "bij g" and x: "nonrep2 x"
  shows "nonrep2 (map_F id id g id x)" (is "nonrep2 ?x'")
  apply (unfold nonrep2_def sameShape1_def)
  apply (intro allI impI)
  apply (erule exE)
  subgoal for y' R'
    apply (drule iffD1[OF F.mr_rel_map(1)[OF supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound, of R' "(=)" g id x y']])
    apply (unfold o_id Grp_UNIV_id eq_OO)
    apply (drule iffD1[OF F.mr_rel_map(3)[OF supp_id_bound bij_id supp_id_bound bij_id supp_id_bound bij_id supp_id_bound,
            of "Grp g OO R' OO conversep (Grp g)" "(=)" x "inv g" id y', symmetric,
            unfolded Grp_UNIV_id conversep_eq OO_eq inv_id comp_id relcompp_assoc converse_relcompp[symmetric] Grp_o[symmetric]
            inv_o_simp2[OF g]]])
    apply (drule x[unfolded nonrep2_def sameShape1_def, rule_format, OF exI])
    apply (erule exE)
    apply (unfold F.map_comp[OF supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound])
    apply (unfold o_id)
    apply (drule arg_cong[of "map_F id id (inv g) id y'" _ "map_F id id g id", 
          unfolded F.map_comp[OF supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound] o_id])
    apply (unfold inv_o_simp2[OF g] F.map_id)
    apply (unfold F.map_comp[OF supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound])
    apply (unfold o_id)
    apply (rule exI[of "_" "g o _ o inv g"])
    apply (unfold o_assoc[symmetric] inv_o_simp1[OF g] o_id)
    apply (assumption)
    done
  done


lemma nonrep2_mapF_bij_2:
  fixes x :: "('a1::var,'a2::var,'a3,'a4) F"
    and v :: "'a1 \<Rightarrow> 'a1" and u :: "'a2\<Rightarrow>'a2" and g::"'a3\<Rightarrow>'a3" and f::"'a4\<Rightarrow>'a4'"
  assumes v: "|supp v| <o |UNIV :: 'a1 set|" and u: "bij u" "|supp u| <o |UNIV :: 'a2 set|"
    and g: "bij g" and x: "nonrep2 x"
  shows "nonrep2 (map_F v u g f x)" 
  using assms apply -
  subgoal premises prems
    apply (subst F.map_comp[OF prems(1,2,3) supp_id_bound bij_id supp_id_bound, of g, unfolded id_apply o_apply, symmetric])
    apply (rule nonrep2_mapF_bij[OF prems(4) nonrep2_map_F[OF prems(1,2,3,5)], unfolded id_apply])
      (*apply (subst F.map_comp[OF supp_id_bound bij_id supp_id_bound prems(1,2,3), of _ f, unfolded id_apply o_apply, symmetric])
    apply (rule nonrep2_map_F[OF prems(1,2,3) nonrep2_mapF_bij[OF prems(4,5)], unfolded id_apply])*)
    done
  done


typedef ('a1::var,'a2::var,'a3::var,'a4) F' = "{x :: ('a1,'a2,'a3,'a4) F. nonrep2 x}"
  apply (unfold mem_Collect_eq nonrep2_def sameShape1_def mr_rel_F_def F.map_id id_apply)
  apply (unfold id_def[symmetric])
  by (rule ex_nonrep)

definition set1_F' :: "('a1::var,'a2::var,'a3::var,'a4) F' \<Rightarrow> 'a1 set" where "set1_F' = set1_F o Rep_F'"
definition set2_F' :: "('a1::var,'a2::var,'a3::var,'a4) F' \<Rightarrow> 'a2 set" where "set2_F' = set2_F o Rep_F'"
definition set3_F' :: "('a1::var,'a2::var,'a3::var,'a4) F' \<Rightarrow> 'a3 set" where "set3_F' = set3_F o Rep_F'"
definition set4_F' :: "('a1::var,'a2::var,'a3::var,'a4) F' \<Rightarrow> 'a4 set" where "set4_F' = set4_F o Rep_F'"

definition asSS :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "asSS f \<equiv> if |supp f| <o |UNIV :: 'a set| then f else id"

definition map_F' :: "('a1::var \<Rightarrow> 'a1) \<Rightarrow> ('a2::var \<Rightarrow> 'a2) \<Rightarrow> ('a3::var \<Rightarrow> 'a3) \<Rightarrow> ('a4 \<Rightarrow> 'a4') 
  \<Rightarrow> ('a1,'a2,'a3,'a4) F' \<Rightarrow> ('a1,'a2,'a3,'a4') F'"
  where "map_F' v u f g = Abs_F' o map_F (asSS v) (asSS (asBij u)) (asBij f) g o Rep_F'"

definition rrel_F' :: "('a4 \<Rightarrow> 'a4' \<Rightarrow> bool) \<Rightarrow> ('a1::var,'a2::var,'a3::var,'a4) F' \<Rightarrow> ('a1,'a2,'a3,'a4') F' \<Rightarrow> bool"
  where "rrel_F' R x x' = rrel_F (=) R (Rep_F' x) (Rep_F' x')"

(* Verifying the axioms of a MRBNF for F':  *)
ML \<open>
open BNF_Util BNF_Tactics

fun mk_map_id_tac map_F'_def F_map_id Rep_F'_inverse ctxt =
  HEADGOAL (Subgoal.FOCUS
    (fn {context = ctxt, ...} =>
      unfold_thms_tac ctxt ([map_F'_def, 
        @{thm eqTrueI} OF @{thms bij_id}, @{thm eqTrueI} OF @{thms supp_id_bound}] @ 
        @{thms asSS_def asBij_def if_True}) THEN
      HEADGOAL (rtac ctxt ext) THEN
      unfold_thms_tac ctxt [F_map_id, Rep_F'_inverse, @{thm o_apply}] THEN
      unfold_thms_tac ctxt @{thms id_def} THEN
      HEADGOAL (rtac ctxt refl)
     ) ctxt)
\<close>

lemma F'_map_id: "map_F' id id id id = id"
  apply (tactic \<open>mk_map_id_tac @{thm map_F'_def} @{thm F.map_id} @{thm Rep_F'_inverse} @{context} 
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  apply (unfold map_F'_def asSS_def asBij_def 
      eqTrueI[OF bij_id] eqTrueI[OF supp_id_bound] if_True)
  apply (rule ext)
  apply (unfold o_apply F.map_id Rep_F'_inverse)
  apply (unfold id_def)
  apply (rule refl)
  done


ML \<open>
open BNF_Util BNF_Tactics

fun mk_map_comp_tac map_F'_def Abs_F'_inverse Rep_F' nonrep2_mapF_bij_2 F_map_comp0 ctxt =
  HEADGOAL (Subgoal.FOCUS
    (fn {prems = prems as [supp_u1, supp_v1, bij_u2, supp_u2, bij_v2, supp_v2, bij_u3, _, bij_v3, _],
      context = ctxt, ...} =>
    let
      val _ = prems |> map @{print tracing}
      val supp_comp = @{thm eqTrueI[OF supp_comp_bound[OF _ _ infinite_UNIV]]}
      val bij_comp = @{thm eqTrueI[OF bij_comp]}
    in
      unfold_thms_tac ctxt ([map_F'_def,
        supp_comp OF [supp_u1, supp_v1],
        supp_comp OF [supp_u2, supp_v2],
        bij_comp OF [bij_u2, bij_v2],
        bij_comp OF [bij_u3, bij_v3]] @ map (fn thm => thm RS @{thm eqTrueI}) prems @
        @{thms asSS_def asBij_def if_True}) THEN
      HEADGOAL (rtac ctxt ext) THEN
      unfold_thms_tac ctxt [F_map_comp0 OF [supp_u1, bij_u2, supp_u2, supp_v1, bij_v2, supp_v2]] THEN
      unfold_thms_tac ctxt [o_apply] THEN
      HEADGOAL (EVERY' [EqSubst.eqsubst_tac ctxt [0] [Abs_F'_inverse],
        rtac ctxt nonrep2_mapF_bij_2 THEN_ALL_NEW resolve_tac ctxt (Rep_F' :: prems),
        rtac ctxt refl])
    end) ctxt)
\<close>

lemma F'_map_comp1_:
  fixes u1 v1 :: "'a1::var \<Rightarrow> 'a1"
  fixes u2 v2 :: "'a2::var \<Rightarrow> 'a2"
  fixes u3 v3 :: "'a3::var \<Rightarrow> 'a3"
  assumes "|supp u1| <o |UNIV :: 'a1 set|" "|supp v1| <o |UNIV :: 'a1 set|"
  assumes "bij u2" "|supp u2| <o |UNIV :: 'a2 set|" "bij v2" "|supp v2| <o |UNIV :: 'a2 set|"
  assumes "bij u3" "|supp u3| <o |UNIV :: 'a3 set|" "bij v3" "|supp v3| <o |UNIV :: 'a3 set|"
  shows "map_F' (v1 o u1) (v2 o u2) (v3 o u3) (g o f) = map_F' v1 v2 v3 g o map_F' u1 u2 u3 f"
  using assms apply -
  apply (tactic \<open>mk_map_comp_tac @{thm map_F'_def} @{thm Abs_F'_inverse[unfolded mem_Collect_eq]}
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep2_mapF_bij_2} @{thm F.map_comp0} @{context} 
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  subgoal premises prems
    apply (unfold map_F'_def asBij_def asSS_def
        eqTrueI[OF supp_comp_bound[OF assms(1,2) infinite_UNIV]]
        eqTrueI[OF supp_comp_bound[OF assms(4,6) infinite_UNIV]]
        eqTrueI[OF bij_comp[OF assms(3,5)]]
        eqTrueI[OF bij_comp[OF assms(7,9)]]
        eqTrueI[OF assms(5)] eqTrueI[OF assms(2)] eqTrueI[OF assms(3)] eqTrueI[OF assms(1)] eqTrueI[OF assms(4)] eqTrueI[OF assms(6)]
        eqTrueI[OF assms(7)] eqTrueI[OF assms(9)]
        if_True)
    apply (rule ext)
    apply (unfold F.map_comp0[OF assms(1,3,4,2,5,6)])
    apply (unfold o_apply)
    apply (subst Abs_F'_inverse[unfolded mem_Collect_eq])
      (*apply (rule  nonrep2_mapF_bij_2[OF assms(1,3,4,7)])*)
     apply (rule nonrep2_mapF_bij_2; (rule prems Rep_F'[unfolded mem_Collect_eq])?)
    apply (rule refl)
    done
  done


(* This tactic is applicable to all 4 of the following <F'_setx_map_> lemmas*)
ML \<open>
open BNF_Util BNF_Tactics

fun mk_set_map_tac set_F'_def map_F'_def Abs_F'_inverse Rep_F' nonrep2_mapF_bij_2 F_set_map ctxt =
  HEADGOAL (Subgoal.FOCUS
    (fn {prems = prems as [supp_u1, bij_u2, supp_u2, _, _],
      context = ctxt, ...} =>
    let
      val _ = prems |> map @{print tracing}
    in
      unfold_thms_tac ctxt ([set_F'_def, map_F'_def] @ map (fn thm => thm RS @{thm eqTrueI}) prems @
        @{thms asSS_def asBij_def if_True o_apply}) THEN
      HEADGOAL (EVERY' [EqSubst.eqsubst_tac ctxt [0] [Abs_F'_inverse],
        rtac ctxt nonrep2_mapF_bij_2 THEN_ALL_NEW resolve_tac ctxt (Rep_F' :: prems),
        rtac ctxt (F_set_map OF [supp_u1, bij_u2, supp_u2])])
    end) ctxt)
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
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep2_mapF_bij_2} @{thm F.set_map(1)} @{context} 
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  subgoal premises prems
    apply (unfold set1_F'_def map_F'_def asSS_def asBij_def
        eqTrueI[OF assms(1)] eqTrueI[OF assms(2)] eqTrueI[OF assms(3)] eqTrueI[OF assms(4)] o_apply if_True)
    apply (subst Abs_F'_inverse[unfolded mem_Collect_eq])
      (*apply (rule nonrep2_mapF_bij_2[OF assms(1,2,3,4)])*)
     apply (rule nonrep2_mapF_bij_2; (rule assms Rep_F'[unfolded mem_Collect_eq])?)
    apply (rule F.set_map(1)[OF assms(1,2,3)])
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
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep2_mapF_bij_2} @{thm F.set_map(2)} @{context}\<close>)
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
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep2_mapF_bij_2} @{thm F.set_map(3)} @{context}\<close>)
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
    @{thm Rep_F'[unfolded mem_Collect_eq]} @{thm nonrep2_mapF_bij_2} @{thm F.set_map(4)} @{context}\<close>)
  done


ML \<open>
open BNF_Util BNF_Tactics

fun mk_map_cong_tac map_F'_def set1_F'_def set2_F'_def set3_F'_def set4_F'_def  F_map_cong ctxt =
  HEADGOAL (Subgoal.FOCUS
    (fn {prems = prems as [supp_u1, supp_v1, bij_u2, supp_u2, bij_v2, supp_v2, _, _, _, _,
      eq_set1, eq_set2, eq_set3, eq_set4],
      context = ctxt, ...} =>
    let
      val _ = prems |> map @{print tracing}
    in
      unfold_thms_tac ctxt ([map_F'_def] @ map (fn thm => thm RS @{thm eqTrueI}) prems @
        @{thms asSS_def asBij_def if_True o_apply}) THEN
      HEADGOAL (EVERY' [
        EqSubst.eqsubst_tac ctxt [0] [F_map_cong OF [supp_u1, bij_u2, supp_u2, supp_v1, bij_v2, supp_v2]],
        rtac ctxt refl,
        etac ctxt (bspec OF [unfold_thms ctxt [set1_F'_def, @{thm o_apply}] eq_set1]),
        etac ctxt (bspec OF [unfold_thms ctxt [set2_F'_def, @{thm o_apply}] eq_set2]),
        etac ctxt (bspec OF [unfold_thms ctxt [set3_F'_def, @{thm o_apply}] eq_set3]),
        etac ctxt (bspec OF [unfold_thms ctxt [set4_F'_def, @{thm o_apply}] eq_set4]),
        rtac ctxt refl])
    end) ctxt)
\<close>

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
  apply (tactic \<open>mk_map_cong_tac @{thm map_F'_def} @{thm set1_F'_def} @{thm set2_F'_def} 
    @{thm set3_F'_def} @{thm set4_F'_def} @{thm F.map_cong} @{context} 
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  subgoal premises prems
    apply (unfold map_F'_def asSS_def asBij_def 
        eqTrueI[OF assms(1)] eqTrueI[OF assms(2)] eqTrueI[OF assms(3)] eqTrueI[OF assms(4)] eqTrueI[OF assms(5)] 
        eqTrueI[OF assms(6)] eqTrueI[OF assms(7)] eqTrueI[OF assms(9)] if_True o_apply)
    apply (subst F.map_cong[OF prems(1,3,4,2,5,6)])
         apply (rule refl)
        apply (erule bspec[OF prems(11)[unfolded set1_F'_def o_apply]])
       apply (erule bspec[OF prems(12)[unfolded set2_F'_def o_apply]])
      apply (erule bspec[OF prems(13)[unfolded set3_F'_def o_apply]])
     apply (erule bspec[OF prems(14)[unfolded set4_F'_def o_apply]])
    apply (rule refl)
    done
  done


(* This tactic is applicable to all 4 of the following <F'_setx_bd> lemmas*)
ML \<open>
open BNF_Util BNF_Tactics

fun mk_set_bd_tac set_F'_def F_set_bd ctxt =
    unfold_thms_tac ctxt [set_F'_def, o_apply] THEN
    HEADGOAL (rtac ctxt F_set_bd)
\<close>

lemma F'_set1_bd: "\<And>b. |set1_F' b| <o natLeq"
  apply (tactic \<open>mk_set_bd_tac @{thm set1_F'_def} @{thm F.set_bd(1)} @{context}
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  apply (unfold set1_F'_def o_apply)
  apply (rule F.set_bd(1))
  done
lemma F'_set2_bd: "\<And>b. |set2_F' b| <o natLeq"
  apply (tactic \<open>mk_set_bd_tac @{thm set2_F'_def} @{thm F.set_bd(2)} @{context}\<close>)
  done
lemma F'_set3_bd: "\<And>b. |set3_F' b| <o natLeq"
  apply (tactic \<open>mk_set_bd_tac @{thm set3_F'_def} @{thm F.set_bd(3)} @{context}\<close>)
  done
lemma F'_set4_bd: "\<And>b. |set4_F' b| <o natLeq"
  apply (tactic \<open>mk_set_bd_tac @{thm set4_F'_def} @{thm F.set_bd(4)} @{context}\<close>)
  done

ML \<open>
open BNF_Util BNF_Tactics

fun mk_rel_comp_leq_tac rrel_F'_def F_rel_compp ctxt =
 HEADGOAL (Subgoal.FOCUS
    (fn {context = ctxt, ...} => print_tac @{context} "0" THEN
      HEADGOAL (rtac ctxt @{thm predicate2I}) THEN print_tac @{context} "1" THEN
      HEADGOAL (etac ctxt @{thm relcomppE}) THEN print_tac @{context} "2" THEN
      unfold_thms_tac ctxt [rrel_F'_def] THEN print_tac @{context} "3" THEN
      HEADGOAL (EqSubst.eqsubst_tac ctxt [1] (@{thms eq_OO[symmetric]})) THEN print_tac @{context} "4" THEN
      HEADGOAL (EqSubst.eqsubst_tac ctxt [1] ([F_rel_compp])) THEN print_tac @{context} "5" THEN
      unfold_thms_tac ctxt [rrel_F'_def] THEN print_tac @{context} "6" THEN
      HEADGOAL (rtac ctxt @{thm relcomppI} THEN_ALL_NEW assume_tac ctxt)
    ) ctxt)
  
\<close>

lemma F'_rel_comp_leq_: "rrel_F' Q OO rrel_F' R \<le> rrel_F' (Q OO R)"
  apply (tactic \<open>mk_rel_comp_leq_tac @{thm rrel_F'_def} @{thm F.rel_compp} @{context}
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  subgoal premises prems
    apply (rule predicate2I)
    apply (erule relcomppE)
    apply (unfold rrel_F'_def) (* Somehow this only unfolds the goal in the tactic *)
    apply (subst (1) eq_OO[symmetric])
    apply (subst (1) F.rel_compp)
      (*apply (unfold rrel_F'_def)*)
    apply (rule relcomppI; (assumption))
    done
  done

ML \<open>
open BNF_Util BNF_Tactics

fun mk_rrel_F_map_F3_tac F_rel_map F_rel_mono_strong Grp_def ctxt =
  HEADGOAL (Subgoal.FOCUS
    (fn {context = ctxt, ...} =>
      unfold_thms_tac ctxt ([F_rel_map, Grp_def, eqTrueI OF @{thms UNIV_I}] @ @{thms id_apply simp_thms(21)}) THEN
      HEADGOAL (rtac ctxt @{thm iffI}) THEN
      ALLGOALS (EVERY' [etac ctxt F_rel_mono_strong, etac ctxt sym, assume_tac ctxt])
    ) ctxt)
\<close>

lemma rrel_F_map_F3:
  fixes x :: "('a :: var,'b :: var,'c,'d) F"
  shows "rrel_F (Grp (f :: 'c \<Rightarrow> 'c)) R x y = rrel_F (=) R (map_F id id f id x) y"
  apply (tactic \<open>mk_rrel_F_map_F3_tac @{thm F.rel_map(1)} @{thm F.rel_mono_strong} @{thm Grp_def} @{context} 
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  subgoal premises prems
    apply (unfold F.rel_map(1) Grp_def id_apply eqTrueI[OF UNIV_I] simp_thms(21))
    apply (rule iffI)
     apply (erule F.rel_mono_strong, erule sym, assumption)+
    done
  done


ML \<open>
open BNF_Util BNF_Tactics

fun mk_asSS_tac ctxt =
  HEADGOAL (Subgoal.FOCUS
    (fn {prems, context = ctxt, ...} =>
      unfold_thms_tac ctxt @{thms asSS_def} THEN
      HEADGOAL (rtac ctxt @{thm if_P}) THEN
      HEADGOAL (rtac ctxt (nth prems 0))
    ) ctxt)
\<close>

lemma asSS: "|supp u| <o |UNIV :: 'a set| \<Longrightarrow> asSS (u :: 'a \<Rightarrow> 'a) = u"
  apply (tactic \<open>mk_asSS_tac @{context} 
    THEN print_tac @{context} "done" THEN no_tac\<close>)
  subgoal premises prems
    apply (unfold asSS_def)
    apply (rule if_P) 
    apply (rule prems)
    done
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
        eqTrueI[OF supp_id_bound] eqTrueI[OF bij_id] o_apply)
    apply (subst Abs_F'_inverse[unfolded mem_Collect_eq])
      (*apply (rule nonrep2_mapF_bij_2[OF assms(1,2,3,4)])*)
     apply (rule nonrep2_mapF_bij_2; (rule prems Rep_F'[unfolded mem_Collect_eq])?)
    apply (subst trans[OF rrel_F_map_F3[symmetric] F.in_rel[OF prems(1,2,3)],
          simplified F.map_comp u1 u2 u3 supp_id_bound bij_id o_id True_implies_equals id_o])
    apply (rule iffI)
     apply (unfold Grp_def eqTrueI[OF UNIV_I] simp_thms(21))
     apply (elim exE CollectE conjE)
    subgoal for z
      apply (tactic \<open>
        let
          val ctxt = @{context};
          val cz = @{cterm z};
          val z = Thm.term_of cz;
          val zT = fastype_of z;
          val which = 0;
          val Abs_F' = @{term Abs_F'}
          val mrbnf = MRBNF_Def.mrbnf_of ctxt @{type_name F} |> the;
          val subst = Sign.typ_match (Proof_Context.theory_of ctxt)
            (MRBNF_Def.T_of_mrbnf mrbnf, zT) Vartab.empty;
          val deads = MRBNF_Def.deads_of_mrbnf mrbnf |> map (Envir.subst_type subst) |> @{print};
          val frees = MRBNF_Def.frees_of_mrbnf mrbnf |> map (Envir.subst_type subst) |> @{print};
          val bounds = MRBNF_Def.bounds_of_mrbnf mrbnf |> map (Envir.subst_type subst) |> @{print};
          val lives = MRBNF_Def.lives_of_mrbnf mrbnf |> map (Envir.subst_type subst) |> @{print};
          val map_F = MRBNF_Def.mk_map_comb_of_mrbnf deads
            (map_index (uncurry (fn i => if i = which then BNF_Util.fst_const else HOLogic.id_const)) lives)
            (map HOLogic.id_const bounds) (map HOLogic.id_const frees)
            mrbnf $ z |> @{print};
          val Ts = fastype_of map_F |> dest_Type |> snd;
          val Us = domain_type (fastype_of Abs_F') |> dest_Type |> snd;
          val ct = Thm.cterm_of ctxt (subst_atomic_types (Us ~~ Ts) Abs_F' $ map_F) |> @{print};
        in
          HEADGOAL (BNF_Util.rtac ctxt (infer_instantiate' ctxt [NONE, SOME ct] exI))
        end
        \<close>)
          (*
      apply (rule exI[of _ "Abs_F' (map_F id id fst id z)"])
*)
          (*apply (simp only: F.map_comp[OF supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound]
          nonrep2_map_F_rev[OF bij_id supp_id_bound, of fst] Abs_F'_inverse[unfolded mem_Collect_eq] Rep_F'[unfolded mem_Collect_eq, of x] 
mem_Collect_eq comp_id id_comp)*)

      apply (frule arg_cong[of _ "(Rep_F' x)" nonrep2, unfolded eqTrueI[OF Rep_F'[unfolded mem_Collect_eq]]])
      apply (drule eqTrueE)
      apply (frule nonrep2_map_F_rev[OF bij_id supp_id_bound, of fst "(map_F id id fst id z)", unfolded 
            F.map_comp[OF supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound] 
            comp_id id_comp])
      apply (subst Abs_F'_inverse[unfolded mem_Collect_eq]; (assumption)?)
      apply (subst Abs_F'_inverse[unfolded mem_Collect_eq]; (assumption)?)
      apply (subst Abs_F'_inverse[unfolded mem_Collect_eq]; (assumption)?)

      apply (subst F.map_comp[OF supp_id_bound bij_id supp_id_bound supp_id_bound bij_id supp_id_bound])
      apply (unfold comp_id id_comp)
      apply (intro conjI)
      subgoal
        apply (subst F.set_map(4)[OF supp_id_bound bij_id supp_id_bound])
        apply (unfold id_apply image_ident)
        apply (assumption)
        done
      subgoal
        apply (erule trans[OF arg_cong, of "map_F id id fst fst z" "Rep_F' x" Abs_F', unfolded Rep_F'_inverse])
        apply (rule refl)
        done
      subgoal
        apply (subst F.map_comp; (rule supp_id_bound bij_id prems(1,2,3))?)
        apply (unfold o_id o_apply)
        apply (frule arg_cong[of _ "Rep_F' y" Abs_F', unfolded Rep_F'_inverse])
        apply (rule trans[OF arg_cong[of "(map_F u1 u2 (\<lambda>x. u3 (fst x)) snd z)" _ "Abs_F'"]]; (assumption)?)
        apply (rule F.map_cong; (rule prems(1,2,3) refl)?)
        apply (drule rev_subsetD[THEN Collect_case_prodD])
         apply (assumption)
        apply (erule sym[OF asm_rl])
        done
      done
    apply (elim exE conjE)
    subgoal for z
      apply (rule exI[of _ "map_F id id (\<lambda>x. (x, u3 x)) id (Rep_F' z)"])
      apply (subst arg_cong[THEN sym, of _ x Rep_F']; (assumption)?)
      apply (subst arg_cong[THEN sym, of _ y Rep_F']; (assumption)?)
      thm Abs_F'_inverse[unfolded mem_Collect_eq]
      apply (subst Abs_F'_inverse[unfolded mem_Collect_eq])
        (*apply (rule nonrep2_mapF_bij_2[OF assms(1,2,3,4)])*)
       apply (rule nonrep2_mapF_bij_2; (rule supp_id_bound bij_id Rep_F'[unfolded mem_Collect_eq])?)
      apply (intro conjI)
      subgoal     
        apply (rule CollectI)
        apply (unfold 
            F.set_map(3)[OF supp_id_bound bij_id supp_id_bound] 
            F.set_map(4)[OF supp_id_bound bij_id supp_id_bound])
        apply (unfold id_apply image_ident)
        apply (rule conjI; (assumption)?) 
        apply (rule subsetI)
        apply (erule imageE)
        apply (rule CollectI)
        apply (rule case_prodI2)
        apply (drule trans[OF sym, THEN iffD1[OF prod.inject]]; (assumption)?)
        apply (erule conjE)
        apply (rule trans[OF sym]; (assumption)?)
        apply (erule arg_cong)
        done
      subgoal
        apply (subst F.map_comp; (rule supp_id_bound bij_id prems(1,2,3))?)
        apply (unfold o_id o_apply fst_conv id_apply)
        apply (rule refl)
        done
      subgoal
        apply (subst Abs_F'_inverse[unfolded mem_Collect_eq])
         apply (rule nonrep2_mapF_bij_2; (rule prems Rep_F'[unfolded mem_Collect_eq])?)
        apply (subst F.map_comp; (rule supp_id_bound bij_id prems(1,2,3))?)
        apply (unfold o_id o_apply)
        apply (rule F.map_cong; (rule prems(1,2,3) refl)?)
        apply (rule snd_conv)
        done
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

ML \<open>
open BNF_Util BNF_Tactics

fun mk_is_mrbnf_tac F'_map_id F'_map_comp1 F'_map_cong F'_set1_map F'_set2_map F'_set3_map F'_set4_map
    F'_set1_bd F'_set2_bd F'_set3_bd F'_set4_bd F'_rel_comp_leq F'_in_rel ctxt = 
  HEADGOAL (rtac ctxt F'_map_id) THEN
  HEADGOAL (Subgoal.FOCUS
    (fn {prems, context = ctxt, ...} => 
      HEADGOAL (rtac ctxt F'_map_comp1 THEN_ALL_NEW resolve_tac ctxt prems)
    ) ctxt) THEN
  HEADGOAL (Subgoal.FOCUS
    (fn {prems, context = ctxt, ...} => 
      HEADGOAL (rtac ctxt F'_map_cong THEN_ALL_NEW resolve_tac ctxt (ballI :: prems)) THEN
      ALLGOALS (resolve_tac ctxt prems) THEN
      ALLGOALS (assume_tac ctxt) 
    ) ctxt) THEN
  (* 4 time the same except for the F'_setX_map. Maybe can be compacted *)
  HEADGOAL (Subgoal.FOCUS
    (fn {prems, context = ctxt, ...} => 
      HEADGOAL (rtac ctxt ext) THEN
      unfold_thms_tac ctxt [o_apply] THEN
      HEADGOAL (rtac ctxt (F'_set1_map OF prems))
    ) ctxt) THEN
  HEADGOAL (Subgoal.FOCUS
    (fn {prems, context = ctxt, ...} => 
      HEADGOAL (rtac ctxt ext) THEN
      unfold_thms_tac ctxt [o_apply] THEN
      HEADGOAL (rtac ctxt (F'_set2_map OF prems))
    ) ctxt) THEN
  HEADGOAL (Subgoal.FOCUS
    (fn {prems, context = ctxt, ...} => 
      HEADGOAL (rtac ctxt ext) THEN
      unfold_thms_tac ctxt [o_apply] THEN
      HEADGOAL (rtac ctxt (F'_set3_map OF prems))
    ) ctxt) THEN
  HEADGOAL (Subgoal.FOCUS
    (fn {prems, context = ctxt, ...} => 
      HEADGOAL (rtac ctxt ext) THEN
      unfold_thms_tac ctxt [o_apply] THEN
      HEADGOAL (rtac ctxt (F'_set4_map OF prems))
    ) ctxt) THEN
  HEADGOAL (rtac ctxt @{thm infinite_regular_card_order_natLeq}) THEN
  HEADGOAL (rtac ctxt F'_set1_bd) THEN
  HEADGOAL (rtac ctxt F'_set2_bd) THEN
  HEADGOAL (rtac ctxt F'_set3_bd) THEN
  HEADGOAL (rtac ctxt F'_set4_bd) THEN
  HEADGOAL (rtac ctxt F'_rel_comp_leq) THEN
  HEADGOAL (Subgoal.FOCUS
    (fn {prems, context = ctxt, ...} => 
      HEADGOAL (rtac ctxt (F'_in_rel OF prems))
    ) ctxt)
\<close>



mrbnf "('a::var, 'b::var, 'c::var, 'd) F'"
  map: map_F'
  sets: free: set1_F' bound: set2_F' bound: set3_F' live: set4_F'
  bd: natLeq
  rel: rrel_F'
  var_class: var
               apply (tactic \<open>mk_is_mrbnf_tac 
  @{thm F'_map_id} @{thm F'_map_comp1_} @{thm F'_map_cong_}
  @{thm F'_set1_map_} @{thm F'_set2_map_} @{thm F'_set3_map_} @{thm F'_set4_map_}
  @{thm F'_set1_bd} @{thm F'_set2_bd} @{thm F'_set3_bd} @{thm F'_set4_bd}
  @{thm F'_rel_comp_leq_} @{thm F'_in_rel} @{context}
   THEN print_tac @{context} "done" THEN no_tac\<close>)
  subgoal by (rule F'_map_id)
  subgoal premises prems by (rule F'_map_comp1_; (rule prems))
  subgoal premises prems 
    apply (rule F'_map_cong_; (rule prems ballI))
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