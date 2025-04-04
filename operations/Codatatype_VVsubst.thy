theory Codatatype_VVsubst
imports Greatest_Fixpoint
begin


typedef 'a :: covar ssfun = "{f :: 'a \<Rightarrow> 'a. |supp f| <o |UNIV::'a set|}"
  by (auto intro!: exI[of _ id] simp: supp_id_bound)

setup_lifting type_definition_ssfun

lift_definition idSS :: "'a :: covar ssfun" is id
  by (simp add: supp_id_bound)

context
  fixes u :: "'a :: covar \<Rightarrow> 'a"
  assumes u: "bij u" "|supp u| <o |UNIV::'a set|"
begin

lift_definition compSS :: "'a :: covar ssfun \<Rightarrow> 'a ssfun" is "\<lambda>p. u o p o inv u"
  by (simp add: supp_comp_bound supp_inv_bound u infinite_UNIV)

end

context
  fixes u :: "'a :: covar \<Rightarrow> 'a"
  assumes u[transfer_rule, simp]: "bij u" "|supp u| <o |UNIV::'a set|"
begin

lemma compSS_inv_compSS[simp]: "compSS (inv u) (compSS u p) = p"
  supply bij_imp_bij_inv[transfer_rule] supp_inv_bound[transfer_rule]
  apply transfer
  apply auto
  done

end

context
  fixes u v :: "'a :: covar \<Rightarrow> 'a"
  assumes [transfer_rule, simp]: "bij u" "|supp u| <o |UNIV::'a set|" "bij v" "|supp v| <o |UNIV::'a set|"
begin

lemma compSS_o[simp]: "compSS (u o v) p = compSS u (compSS v p)"
  supply bij_comp[transfer_rule] supp_comp_bound[OF _ _ infinite_UNIV, transfer_rule]
  apply transfer
   apply (auto simp: o_inv_distrib)
  done

end

lemma compSS_id[simp]: "compSS id = id"
  supply supp_id_bound[transfer_rule] bij_id[transfer_rule] by (rule ext, transfer) auto

theorem TT_fresh_inject:
  fixes x x' :: "('a::covar, 'a, 'a term,'a term) term_pre" and A :: "'a set"
  assumes "|A| <o |UNIV::'a set|" "set2_term_pre x \<inter> A = {}" "set2_term_pre x' \<inter> A = {}"
  shows "term_ctor x = term_ctor x' \<longleftrightarrow>
   (\<exists>f. bij f \<and> |supp f| <o |UNIV::'a set| \<and> id_on (\<Union>(FVars_term ` set3_term_pre x) - set2_term_pre x) f \<and>
        A \<inter> imsupp f = {} \<and> map_term_pre id f (permute_term f) id x = x')" (is "_ \<longleftrightarrow> (\<exists>f. ?renaming f)")
proof
  assume "term_ctor x = term_ctor x'"
  then obtain f where "bij f" "|supp f| <o |UNIV::'a set|" "id_on (\<Union>(FVars_term ` set3_term_pre x) - set2_term_pre x) f" "map_term_pre id f (permute_term f) id x = x'"
    unfolding TT_inject0s by blast
  then show "\<exists>f. ?renaming f"
    apply -
    apply (rule exE[OF ex_avoiding_bij])
            apply assumption+
          apply (rule infinite_UNIV)
         prefer 2
         apply assumption
        apply (rule ordLeq_ordLess_trans[OF card_of_diff])
        apply (rule var_class.UN_bound)
         apply (rule ordLess_ordLeq_trans)
          apply (rule term_pre.set_bd)
         apply (rule var_class.large')
        apply (rule FVars_bd_UNIVs)
    prefer 2
      apply (rule assms)
      apply (rule term_pre.set_bd_UNIV)
    apply (rule assms)
    subgoal for g
      apply (rule exI[of _ g])
      apply (auto intro!: term_pre.map_cong0 simp: supp_id_bound)
        apply (metis IntI assms(3) empty_iff imageI supp_id_bound term_pre.set_map(2))
       apply (rule sym)
       apply (rule permute_congs)
          apply assumption+
      by (smt (verit, best) DiffI UN_I assms(3) disjoint_iff id_on_def imageI supp_id_bound term_pre.set_map(2))
    done
qed (auto simp add: TT_inject0s)

(* Term-like structures: *)
definition termLikeStr :: "(('a::covar \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> 'a set) \<Rightarrow> bool" where 
  "termLikeStr swp fcovars \<equiv>
  swp id = id \<and> 
  (\<forall> u v. bij u \<and> |supp u| <o |UNIV::'a set| \<and> bij v \<and> |supp v| <o |UNIV::'a set|
      \<longrightarrow> swp (u o v) = swp u o swp v) \<and> 
  (\<forall> u c. bij u \<and> |supp u| <o |UNIV::'a set| \<and>
      (\<forall> a. a \<in> fcovars c \<longrightarrow> u a = a) \<longrightarrow> swp u c = c) \<and>
  (\<forall> u c a. bij u \<and> |supp u| <o |UNIV::'a set| 
     \<longrightarrow> (u a \<in> fcovars (swp u c) \<longleftrightarrow> a \<in> fcovars c))"

(* A restricted version of "termLikeStr" to be used for the comodels -- it only 
assums small-support bijection functoriality and nothing else, 
in particular nothing about freshness.  *)
abbreviation termLikeStrD :: "(('a::covar \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> bool" where 
  "termLikeStrD swp  \<equiv>
  (\<forall> c. swp id c = c) \<and> 
  (\<forall> u v c. bij u \<and> |supp u| <o |UNIV::'a set| \<and> bij v \<and> |supp v| <o |UNIV::'a set|
    \<longrightarrow>  swp (u o v) c = swp u (swp v c))"

(* The following definition and three properties will not be used in the development, but motivate the 
chosen axioms for DDTOR by showing that the terms satisfy them for their natural destructor:  *)
definition ddtor :: "'a::covar term \<Rightarrow> ('a, 'a, 'a term, 'a term) term_pre set" where 
  "ddtor t \<equiv> {x . t = term_ctor x}"

lemma ddtor_ne:  
  "ddtor t \<noteq> {}"  
  unfolding ddtor_def
  by (metis (mono_tags, lifting) Collect_empty_eq_bot empty_def fresh_cases supp_id_bound)

lemma ddtor_permute_term:
  assumes "{x,x'} \<subseteq> ddtor t"
  shows "\<exists>u. bij (u::'a\<Rightarrow>'a) \<and> |supp u| <o |UNIV::'a::covar set| \<and> id_on (\<Union>(FVars_term ` set3_term_pre x) - set2_term_pre x) u \<and> map_term_pre id u (permute_term u) id x = x'"
  using assms TT_inject0s by (auto simp: ddtor_def) 

lemma FVars_term_ddtor: 
  assumes "x \<in> ddtor t"
  shows "FVars_term t = set1_term_pre x \<union> (\<Union>(FVars_term ` set3_term_pre x) - set2_term_pre x) \<union> \<Union>(FVars_term ` set4_term_pre x) "
  using assms by (auto simp: ddtor_def FVars_ctors)
(****)

datatype 'a D = D "'a term" "'a ssfun"

definition DDTOR :: "('a::covar D \<Rightarrow> ('a, 'a, 'a term + 'a D , 'a term + 'a D) term_pre set)" where
  "DDTOR = (\<lambda>d. case d of D t f \<Rightarrow> {map_term_pre (Rep_ssfun f) id (\<lambda>x. Inr (D x f)) (\<lambda>x. Inr (D x f)) x | x.
        t = term_ctor x \<and> set2_term_pre x \<inter> imsupp (Rep_ssfun f) = {}})"
definition mmapD :: "('a::covar \<Rightarrow> 'a) \<Rightarrow> 'a D \<Rightarrow> 'a D" where
  "mmapD = (\<lambda>u d. case d of D x f \<Rightarrow> D (permute_term u x) (compSS u f))"
definition FVars_termD :: "'a::covar D \<Rightarrow> 'a set" where
  "FVars_termD = (\<lambda>d. case d of D x f \<Rightarrow> FVars_term x \<union> imsupp (Rep_ssfun f))"

declare D.splits[split]

lemmas comodel_defs = DDTOR_def mmapD_def FVars_termD_def

(* Comodel properties: *)
lemma
  (* Full-corecursion version of the clauses (Dne), (MD), (VD) and (DRen) from the paper: *)
  DDTOR_ne: "DDTOR d \<noteq> {}"
  and 
  DDTOR_mmapD0: "{X,X'} \<subseteq> DDTOR d \<Longrightarrow> 
\<exists>u. bij (u::'a \<Rightarrow> 'a) \<and> |supp u| <o |UNIV::'a::covar set| \<and> id_on (\<Union>(case_sum FVars_term FVars_termD ` set3_term_pre X) - set2_term_pre X) u \<and> 
     map_term_pre id u (map_sum (permute_term u) (mmapD u)) id X = X'" 
  and   
  FVars_termD_DDTOR0: 
  "X \<in> DDTOR d \<Longrightarrow> 
  set1_term_pre X  \<union>    (\<Union>(case_sum FVars_term FVars_termD ` set3_term_pre X) - set2_term_pre X)
   \<union> \<Union>(case_sum FVars_term FVars_termD ` set4_term_pre X) \<subseteq> 
  FVars_termD d"  
  and  
  mmapD_DDTOR: "bij (u::'a\<Rightarrow>'a) \<Longrightarrow> |supp u| <o |UNIV::'a::covar set| \<Longrightarrow> 
  DDTOR (mmapD u d) \<subseteq>
  image 
    (map_term_pre u u (map_sum (permute_term u) (mmapD u)) (map_sum (permute_term u) (mmapD u))) 
    (DDTOR d)"
  and 
  (* Comodels are a restricted term-like structure: *)
  termLikeStr_mmapD_FVars_termD: "termLikeStrD mmapD"
  unfolding comodel_defs
      apply -
  subgoal
    apply (auto split: prod.splits simp: imsupp_supp_bound Rep_ssfun[simplified])
    subgoal for x1 x2
      apply (rule fresh_cases[of "imsupp (Rep_ssfun x2)" x1])
      using Greatest_Fixpoint.infinite_UNIV Rep_ssfun imsupp_supp_bound apply blast
      by blast
    done
  subgoal
    apply clarsimp
    subgoal for p x y
      apply (subst (asm) TT_fresh_inject[of "imsupp (Rep_ssfun p)"])
         apply (auto simp: imsupp_supp_bound Rep_ssfun[simplified]) [3]
      using Greatest_Fixpoint.infinite_UNIV Rep_ssfun imsupp_supp_bound apply blast
      apply safe
      subgoal for u
        apply (auto simp: supp_inv_bound supp_id_bound supp_comp_bound Rep_ssfun[simplified]
        term_pre.set_map FVars_permutes term_pre.map_comp id_on_def
            permute_ids permute_comps[symmetric] bij_imp_inv
            intro!: exI[of _ "u"] term_pre.map_cong)
         apply (auto simp: imsupp_def supp_def) []
        subgoal premises prems
          supply prems(6,7)[transfer_rule] supp_inv_bound[transfer_rule] bij_imp_bij_inv[transfer_rule]
          using prems(4,5,8,9)
          apply (transfer fixing: u)
          apply (auto simp: prems(6,7) fun_eq_iff)
          subgoal for x p a
            apply (auto simp: imsupp_commute[THEN fun_cong, simplified, of p u "inv u a", symmetric] prems(6))
            done
          done
        done
      done
    done
  subgoal
    apply (auto simp: term_pre.set_map supp_id_bound Rep_ssfun[simplified] FVars_ctors)
     apply (auto simp: imsupp_def supp_def)
    done
  subgoal
    apply (simp split: prod.splits, safe)
    subgoal for t p _ x
      apply (drule arg_cong[of _ _ "permute_term (inv u)"])
      apply (auto simp: image_iff permute_comps supp_inv_bound permute_ids permute_simps)
      apply (rule exI conjI refl)+
       apply (auto simp: term_pre.map_comp supp_id_bound Rep_ssfun[simplified]
          image_iff map_sum_def compSS.rep_eq supp_comp_bound[OF _ _ infinite_UNIV] supp_inv_bound term_pre.set_map
          inv_o_simp1[THEN rewriteR_comp_comp] permute_comps permute_ids
          split: sum.splits intro!: term_pre.map_cong0)
      apply (frule (1) imsupp_empty_IntD2)
      apply (auto simp: imsupp_def supp_def bij_inv_rev bij_imp_inv disjoint_iff_not_equal
          ball_Un)
      apply (drule bspec, assumption)
      apply (auto simp: bij_imp_inv[symmetric, of u])
      subgoal for x
        apply (auto dest!: spec[of _ "u x"])
        by (meson bij_implies_inject)
      done
    done
  subgoal
    apply (auto simp: permute_ids permute_comps)
    done
  done

(* Defined analogously to the FVarsB: *)
definition FVars_termBD :: "('a::covar, 'a, 'a term + 'a D, 'a term + 'a D) term_pre \<Rightarrow> 'a set" where
  "FVars_termBD X \<equiv> \<Union>(case_sum FVars_term FVars_termD ` set3_term_pre X) - set2_term_pre X"

lemmas DDTOR_mmapD = DDTOR_mmapD0[folded FVars_termBD_def]
lemmas FVars_termD_DDTOR = FVars_termD_DDTOR0[folded FVars_termBD_def]

(*  *)
lemma mmapD_id[simp,intro!]: "mmapD id d = d"
  using termLikeStr_mmapD_FVars_termD by auto

lemma mmapD_comp: 
  "bij (u::'a\<Rightarrow>'a) \<Longrightarrow> |supp u| <o |UNIV::'a::covar set| \<Longrightarrow> bij v \<Longrightarrow> |supp v| <o |UNIV::'a set| \<Longrightarrow> 
 mmapD (u o v) d = mmapD u (mmapD v d)"
  using termLikeStr_mmapD_FVars_termD by auto

(*  *)

lemma mmapD_DDTOR_strong: 
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a::covar set|"
  shows
    "DDTOR (mmapD u d) =
 image 
   (map_term_pre u u (map_sum (permute_term u) (mmapD u)) (map_sum (permute_term u) (mmapD u))) 
   (DDTOR d)" (is "?L = ?R")
proof
  show "?L \<subseteq> ?R" using mmapD_DDTOR[OF assms] .
next
  have iu: "bij (inv u)" "|supp (inv u)| <o |UNIV::'a set|" using u by(simp_all add: supp_inv_bound) 
  define dd where "dd \<equiv> mmapD u d"
  have d: "d = mmapD (inv u) dd" 
    using u unfolding dd_def by(simp add: mmapD_comp[symmetric] supp_inv_bound) 
  have [simp]: "mmapD u \<circ> (mmapD (inv u)) = id" unfolding fun_eq_iff
    by (simp add: u iu mmapD_comp[symmetric])
  show "?R \<subseteq> ?L" unfolding dd_def[symmetric] d using mmapD_DDTOR[OF iu, of dd] 
    apply (auto simp: u iu term_pre.map_comp 
        map_sum.comp permute_comps permute_ids mmapD_comp[symmetric] map_sum.id term_pre.map_id) 
    apply (drule subsetD)
     apply assumption
    apply (erule imageE)
    apply hypsubst
    apply (auto simp: term_pre.map_comp supp_inv_bound assms sum.map_comp comp_def permute_comps mmapD_comp[symmetric])
    apply (unfold id_def[symmetric] mmapD_id permute_id0s sum.map_id term_pre.map_id)
    apply (unfold id_def)
    apply assumption
    done
qed


(*************************************)
(* The raw-term-based model infrastructure *)  

definition DTOR :: "'a::covar D \<Rightarrow> ('a, 'a, 'a raw_term + 'a D, 'a raw_term + 'a D) term_pre set" where 
  "DTOR d \<equiv>  map_term_pre id id (map_sum TT_rep id) (map_sum TT_rep id) ` (DDTOR d)"

abbreviation mapD :: "('a::covar \<Rightarrow> 'a) \<Rightarrow> 'a D \<Rightarrow> 'a D" where 
  "mapD \<equiv> mmapD"  

abbreviation FVarsD :: "'a::covar D \<Rightarrow> 'a set" where 
  "FVarsD \<equiv> FVars_termD" 

definition FVarsBD :: "('a::covar, 'a, 'a raw_term + 'a D, 'a raw_term + 'a D) term_pre \<Rightarrow> 'a set" where 
  "FVarsBD X \<equiv> \<Union>(case_sum FVars_raw_term FVarsD ` set3_term_pre X) - set2_term_pre X"

lemmas FVars_def2 = trans[OF meta_eq_to_obj_eq[OF FVars_term_def[of "TT_abs _"]] alpha_FVars[OF TT_rep_abs], symmetric]


(* Raw-term-based version of the assumptions: *)

(*  *)
lemmas mapD_id = mmapD_id 

lemmas mapD_comp = mmapD_comp 

lemma FVarsBD_FVars_termBD: 
  "FVarsBD X = FVars_termBD (map_term_pre id id (map_sum TT_abs id) (map_sum TT_abs id) X)"
  unfolding FVarsBD_def FVars_termBD_def FVars_def2   
  apply(simp add: term_pre.set_map FVars_def2 case_sum_map_sum supp_id_bound) 
  unfolding o_def id_def ..

definition asSS :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "asSS f \<equiv> if |supp f| <o |UNIV::'a set| then f else id"

lemma DTOR_mapD: 
  assumes "{X,X'} \<subseteq> DTOR d"
  shows "\<exists>u. bij (u::'a\<Rightarrow>'a) \<and> |supp u| <o |UNIV::'a::covar set| \<and> id_on (FVarsBD X) u \<and> 
     mr_rel_term_pre id u 
       (rel_sum (\<lambda> t t'. alpha_term (permute_raw_term u t) t') (\<lambda> d d'. mapD u d = d')) 
       (rel_sum alpha_term (=)) 
     X X'"  
proof-
  define XX XX' where 
    "XX \<equiv> map_term_pre id id (map_sum TT_abs id) (map_sum TT_abs id) X" and 
    "XX' \<equiv> map_term_pre id id (map_sum TT_abs id) (map_sum TT_abs id) X'" 
  have 0: "{XX,XX'} \<subseteq> DDTOR d" using assms unfolding XX_def XX'_def DTOR_def
    by (auto simp: term_pre.map_comp sum.map_comp TT_abs_rep map_sum.id term_pre.map_id sum.map_ident term_pre.map_ident comp_def supp_id_bound)       
  then obtain u where u: "bij u" "|supp u| <o |UNIV::'a set|" "id_on (FVars_termBD XX) u"
    and m: "map_term_pre id u (map_sum (permute_term u) (mmapD u)) id XX = XX'"
    using DDTOR_mmapD[OF 0] by auto 
  have [simp]: "asSS (asBij u) = u"  "asSS u = u" using u unfolding asSS_def by auto
  show ?thesis
  proof(rule exI[of _ u], safe )
    show "id_on (FVarsBD X) u"  
      using u(3) unfolding id_on_def XX_def FVarsBD_FVars_termBD by auto
    show "mr_rel_term_pre id u (rel_sum (\<lambda>t. alpha_term (permute_raw_term u t)) (\<lambda>d d'. mapD u d = d')) (rel_sum alpha_term (=)) X X'"
      using m unfolding XX_def XX'_def
      apply(simp add: u term_pre.map_comp term_pre.map_id map_sum.comp permute_term_def term_pre.rel_eq[symmetric]
      term_pre.mr_rel_map term_pre.mr_rel_id supp_id_bound)
      apply(erule term_pre.mr_rel_mono_strong[rotated -3]) apply (auto simp: u supp_id_bound)
      unfolding Grp_def apply auto
      subgoal for d1 d2
        apply(cases d1) apply (cases d2) apply auto
        using TT_total_abs_eq_iffs permute_abs u(1,2) apply fastforce
        by (smt (z3) id_def map_sum.simps(2) rel_sum.intros(2) rel_sum_simps(3) sum.exhaust sum.rel_map(2))
      subgoal for d1 d2
        apply(cases d1) apply(cases d2) apply auto
        using TT_total_abs_eq_iffs apply fastforce
        apply(cases d2) by auto .
  qed(insert u, auto)
qed

lemma DTOR_ne: 
  "DTOR d \<noteq> {}"
  unfolding DTOR_def using DDTOR_ne by auto

lemma FVarsD_DTOR: 
  assumes "X \<in> DTOR d"
  shows "set1_term_pre X \<union> \<Union>(case_sum FVars_raw_term FVarsD ` set4_term_pre X) \<union> FVarsBD X \<subseteq> FVarsD d"
proof-
  define XX where "XX \<equiv> map_term_pre id id (map_sum TT_abs id) (map_sum TT_abs id) X"  
  have 0: "XX \<in> DDTOR d" using assms unfolding XX_def DTOR_def 
    by (auto simp: term_pre.map_comp map_sum.comp TT_abs_rep map_sum.id term_pre.map_id supp_id_bound comp_def sum.map_comp sum.map_ident term_pre.map_ident) 
  show ?thesis using FVars_termD_DDTOR[OF 0] unfolding FVarsBD_FVars_termBD XX_def
    apply (simp add: term_pre.set_map FVars_def2 case_sum_map_sum supp_id_bound) unfolding FVars_def2 o_def 
      map_sum.simps id_def by simp
qed

lemma rel_set_reflI: 
  assumes "\<And>a. a \<in> A \<Longrightarrow> r a a"
  shows "rel_set r A A"
  using assms unfolding rel_set_def by auto

lemma mapD_DTOR: 
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a::covar set|"
  shows 
    "rel_set
  (mr_rel_term_pre u u 
     (rel_sum (\<lambda> t t'. alpha_term (permute_raw_term u t) t') (\<lambda> d d'. mapD u d = d'))
     (rel_sum (\<lambda> t t'. alpha_term (permute_raw_term u t) t') (\<lambda> d d'. mapD u d = d')))
 (DTOR d)
 (DTOR (mapD u d))" 
  unfolding DTOR_def  
  by (auto intro!: rel_set_reflI term_pre.rel_refl_strong sum.rel_refl_strong 
      simp: mmapD_DDTOR_strong[OF u, of d] rel_set_image u term_pre.mr_rel_map OO_def Grp_def sum.rel_map 
      permute_term_def asSS_def alpha_syms term_pre.mr_rel_id[symmetric] TT_rep_abs
      image_comp map_sum.comp supp_id_bound)  

(*    *)

definition suitable ::  "('a::covar D \<Rightarrow> ('a,'a,'a raw_term + 'a D,'a raw_term + 'a D) term_pre) \<Rightarrow> bool" where
  "suitable pick \<equiv> \<forall> d. pick d \<in> DTOR d"

definition f :: "('a::covar D \<Rightarrow> ('a,'a,'a raw_term + 'a D,'a raw_term + 'a D) term_pre) \<Rightarrow> 'a D => 'a raw_term" where
  "f pick \<equiv> corec_raw_term pick"
thm raw_term.corec[of "pick o DTOR", unfolded f_def[symmetric]]

lemma f_simps: 
  "f pick d = raw_term_ctor (map_term_pre id id (case_sum id (f pick)) (case_sum id (f pick)) (pick d))"
  apply(subst raw_term.corec[of pick, unfolded f_def[symmetric]]) unfolding id_def ..

lemma f_ctor: 
  "raw_term_ctor x = f pick d \<Longrightarrow> 
 x = map_term_pre id id (case_sum id (f pick)) (case_sum id (f pick)) (pick d)"
  using f_simps[of pick d] by simp

lemma suitable_FVarsD:
  assumes "suitable pick"  
  shows "set1_term_pre (pick d) \<union> \<Union>(case_sum FVars_raw_term FVarsD ` set4_term_pre (pick d)) \<union> FVarsBD (pick d)
       \<subseteq> FVarsD d"
  using FVarsD_DTOR[of "pick d"] using assms[unfolded suitable_def] by auto

(*  *)

lemma f_FVarsD: 
  assumes p: "suitable pick"  
  shows "FVars_raw_term (f pick d) \<subseteq> FVarsD d"
proof safe
  fix a assume aa: "a \<in> FVars_raw_term (f pick d)"  
  define t where "t = f pick d"
  show "a \<in> FVarsD d" using aa[unfolded t_def[symmetric]] using t_def unfolding FVars_raw_term_def mem_Collect_eq
  proof(induction arbitrary: d)
    case (1 a x)
    note x = f_ctor[OF `raw_term_ctor x = f pick d`] 
    note fvd = suitable_FVarsD[OF assms, of d]
    show ?case using 1 fvd unfolding x by (auto simp add: term_pre.set_map supp_id_bound)
  next
    case (2 t x a d)
    note x = f_ctor[OF `raw_term_ctor x = f pick d`]  
    note fvd = suitable_FVarsD[OF assms, of d]
    from `t \<in> set3_term_pre x` obtain td where t: "t = case_sum id (f pick) td" 
      and td: "td \<in> set3_term_pre (pick d)" unfolding x by (auto simp add: term_pre.set_map supp_id_bound)
    have a: "a \<in> case_sum FVars_raw_term FVarsD td"
      using 2 unfolding t by(cases td) (auto simp: FVars_raw_term_def)
    have "a \<notin> set2_term_pre (pick d)" using `a \<notin> set2_term_pre x` unfolding x by(auto simp: term_pre.set_map supp_id_bound)
    thus ?case using a td apply (intro rev_subsetD[OF _ fvd]) unfolding FVarsBD_def by auto 
  next
    case (3 t x a)
    note x = f_ctor[OF `raw_term_ctor x = f pick d`]  
    note fvd = suitable_FVarsD[OF assms, of d]
    from `t \<in> set4_term_pre x` obtain td where t: "t = case_sum id (f pick) td" 
      and td: "td \<in> set4_term_pre (pick d)" unfolding x by (auto simp add: term_pre.set_map supp_id_bound)
    have a: "a \<in> case_sum FVars_raw_term FVarsD td"
      using 3 unfolding t apply (cases td) by (auto simp: FVars_raw_term_def)
    show ?case using a td by (intro rev_subsetD[OF _ fvd]) auto
  qed
qed


lemma mr_rel_term_pre_suitable_mapD: 
  assumes pp': "suitable pick" "suitable pick'"
    and u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a::covar set|"
  shows "\<exists> v. bij v \<and> |supp v| <o |UNIV::'a set| \<and> id_on (FVarsBD (pick d)) v \<and> 
 mr_rel_term_pre u (u o v)
   (rel_sum (\<lambda>t t'. alpha_term (permute_raw_term (u o v) t) t') 
            (\<lambda>d d'. mapD (u o v) d = d'))
   (rel_sum (\<lambda>t t'. alpha_term (permute_raw_term u t) t') 
            (\<lambda>d d'. d' = mapD u d))
 (pick d)  
 (pick' (mapD u d))" 
proof- 
  have p: "pick d \<in> DTOR d" and p': "pick' (mapD u d) \<in> DTOR (mapD u d)" 
    using pp' unfolding suitable_def by auto
  obtain X where X: "X \<in> DTOR d" and 0: 
    "mr_rel_term_pre u u 
       (rel_sum (\<lambda>t. alpha_term (permute_raw_term u t)) (\<lambda>d. (=) (mapD u d)))
       (rel_sum (\<lambda>t. alpha_term (permute_raw_term u t)) (\<lambda>d. (=) (mapD u d)))
     X (pick' (mapD u d))"
    using mapD_DTOR[OF u, of d] p' unfolding rel_set_def by auto
  obtain v where v: "bij v" "|supp v| <o |UNIV::'a set|" "id_on (FVarsBD (pick d)) v" 
    and 2: 
    "mr_rel_term_pre id v
      (rel_sum (\<lambda>t. alpha_term (permute_raw_term v t)) (\<lambda>d. (=) (mapD v d)))
      (rel_sum alpha_term (=)) 
   (pick d) X" using DTOR_mapD[of "pick d" X d] using pp' X unfolding suitable_def by auto
  show ?thesis apply(rule exI[of _ v], simp add: v)
    apply(rule term_pre.mr_rel_mono_strong0[rotated -5])
    apply (rule term_pre.mr_rel_OO[THEN fun_cong, THEN fun_cong, THEN iffD2, rotated -1, OF relcomppI, OF 2 0])
              apply(auto simp: u v supp_comp_bound[OF _ _ infinite_UNIV] supp_inv_bound supp_id_bound)
    subgoal for td1 td3 td2 using alpha_refls
      apply(cases td1) apply auto 
       apply(cases td2) apply auto  apply(cases td3) apply (auto  simp: u v permute_raw_comps supp_inv_bound 
          ) using alpha_bij_eqs alpha_trans  using u(1) u(2)
      apply (smt (verit, best) permute_raw_comps v(1,2))
      apply(cases td2) apply auto  apply(cases td3) 
      by (auto simp: u v permute_raw_comps mapD_comp[symmetric])
    subgoal for td1 td3 td2 using alpha_refls
      apply(cases td1) apply auto 
       apply(cases td2) apply auto  apply(cases td3) apply auto
       apply (smt alpha_bij_eqs alpha_trans rel_sum_simps(1) u(1) u(2))
      apply(cases td2) apply auto  apply(cases td3) by auto . 
qed

(* The "monster lemma": termLikeStr and "pick"-irrelevance covered in one shot: *)

lemma f_swap_alpha_term: 
  assumes p: "suitable pick" and p': "suitable pick'"
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a::covar set|" 
  shows "alpha_term (permute_raw_term u (f pick d)) (f pick' (mapD u d))"
proof- 
  let ?\<phi> = "\<lambda> tL tR. \<exists> u d. bij u \<and> |supp u| <o |UNIV::'a set| \<and> 
   tL = permute_raw_term u (f pick d) \<and> tR = f pick' (mapD u d)"
  {fix tL tR assume "?\<phi> tL tR"
    hence "alpha_term tL tR"
    proof(induction rule: alpha_term_coinduct2)
      case (C xL xR)  
      then obtain u d
        where u: "bij u" "|supp u| <o |UNIV::'a set|"  
          and "raw_term_ctor xL = permute_raw_term u (f pick d)" "raw_term_ctor xR = f pick' (mapD u d)" by auto
      hence xL: "xL = map_term_pre u u (permute_raw_term u \<circ> case_sum id (f pick)) (permute_raw_term u\<circ> case_sum id (f pick)) (pick d)" 
        and xR: "xR = map_term_pre id id (case_sum id (f pick')) (case_sum id (f pick')) (pick' (mapD u d))"
        using f_simps[of "pick"] f_simps[of "pick'"] 
        by (auto simp: u permute_raw_term_simps term_pre.map_comp supp_id_bound)
          (*  *)
      obtain v where v: "bij v" "|supp v| <o |UNIV::'a set|" and iv: "id_on (FVarsBD (pick d)) v"
        and rv:   
        "mr_rel_term_pre u (u \<circ> v) 
       (rel_sum (\<lambda>t. alpha_term (permute_raw_term u t)) (\<lambda>d d'. d' = mapD u d))
       (rel_sum (\<lambda>t. alpha_term (permute_raw_term (u \<circ> v) t)) (\<lambda>d. (=) (mapD (u \<circ> v) d))) 
     (pick d) (pick' (mapD u d)) " 
        using mr_rel_term_pre_suitable_mapD[OF p p' u(1,2)] by blast 
      define w where "w \<equiv> u o v o inv u" 
      have w: "bij w" "|supp w| <o |UNIV::'a set|" by (simp_all add: w_def u v supp_comp_bound supp_inv_bound)
      have fv_xL: "FVarsB xL \<subseteq> u ` (FVarsBD (pick d))" 
        using f_FVarsD[OF p] unfolding xL apply (auto simp: u term_pre.set_map FVars_permute_raw_term FVarsBD_def)
        subgoal for td a apply (cases td) by fastforce+ . 
      have fv_p'd: "FVarsBD (pick d) \<subseteq> FVarsD d" 
        using FVarsD_DTOR[of "pick d"] p unfolding suitable_def by auto
      have "id_on (u ` (FVarsBD (pick d))) w"
        using iv fv_p'd unfolding id_on_def xL w_def eq_on_def id_on_def by (auto simp: term_pre.set_map u) 
      hence iw: "id_on (FVarsB xL) w" using fv_xL unfolding id_on_def by auto 
      show ?case proof(rule exI[of _ w], safe)
        show "mr_rel_term_pre id w
      (\<lambda>t t'. (\<exists>u d. bij u \<and> |supp u| <o |UNIV::'a set| \<and>   
                     t = permute_raw_term u (f pick d) \<and> t' = f pick' (mapD u d))
              \<or> alpha_term t t')
      (\<lambda>t t'. (\<exists>u d. bij u \<and> |supp u| <o |UNIV::'a set| \<and> 
                     permute_raw_term w t = permute_raw_term u (f pick d)  \<and> t' = f pick' (mapD u d))
              \<or> alpha_term (permute_raw_term w t) t')
      xL xR" unfolding xL xR  
          apply(simp add: w u F_rel_map Grp_def OO_def supp_comp_bound supp_inv_bound permute_raw_comps[symmetric] supp_id_bound)
        proof(rule F_rel_mono_strong0[OF _ _ _ _ _ _ rv], auto)  
          fix a assume "a \<in> set2_term_pre (pick d)"
          thus "u (v a) = w (u a)"  
            unfolding w_def by (simp add: u v)
        next
          fix ttdL ttdR assume ttdLin: "ttdL \<in> set3_term_pre (pick d)"
            and ttdRin: "ttdR \<in> set3_term_pre (pick' (mapD u d))"
            and r: "rel_sum (\<lambda>t. alpha_term (permute_raw_term u t)) (\<lambda>d d'. d' = mapD u d) ttdL ttdR"
            and na: "\<not> alpha_term (permute_raw_term u (case_sum id (f pick) ttdL)) (case_sum id (f pick') ttdR)"
          {fix tL assume 000: "ttdL = Inl tL" 
            then obtain tR where "ttdR = Inl tR"
              and  "alpha_term (permute_raw_term u tL) tR" "\<not> alpha_term (permute_raw_term u tL) tR" using r na by (cases ttdR, auto)
            moreover have "alpha_term (permute_raw_term u tL) (permute_raw_term u tL)" 
              apply(rule alpha_term_cong) by (auto simp: u)  
            ultimately have False using alpha_trans alpha_term_sym by blast
          }
          then obtain dd where ttdL: "ttdL = Inr dd" by (cases ttdL, auto)
          hence ttdR: "ttdR = Inr (mapD u dd)" using r by(cases ttdR, auto)
          have fv_dd: "FVarsD dd \<subseteq> FVarsD d" using ttdLin unfolding ttdL 
            using FVarsD_DTOR p unfolding suitable_def by force        
          show "\<exists>uu. bij uu \<and> |supp uu| <o |UNIV::'a set| \<and>
             (\<exists> dd. permute_raw_term u (case_sum id (f pick) ttdL) = permute_raw_term uu (f pick dd) \<and>
                    case_sum id (f pick') ttdR = f pick' (mapD uu dd))"
            by (auto simp: u ttdL ttdR intro: exI[of _ u] exI[of _ dd])
        next
          fix ttdL ttdR assume ttdLin: "ttdL \<in> set4_F (pick d)"
            and ttdRin: "ttdR \<in> set4_F (pick' (mapD u d))"
            and r: "rel_sum (\<lambda>t. alpha_term (permute_raw_term (u \<circ> v) t)) (\<lambda>d. (=) (mapD (u \<circ> v) d)) ttdL ttdR"
            and na: "\<not> alpha_term (permute_raw_term (w \<circ> u) (case_sum id (f pick) ttdL)) (case_sum id (f pick') ttdR)"
          have uvw: "u \<circ> v = w \<circ> u" unfolding w_def by (auto simp: u)
          {fix tL assume 000: "ttdL = Inl tL" 
            then obtain tR where "ttdR = Inl tR"
              and  "alpha_term (permute_raw_term (u \<circ> v) tL) tR" "\<not> alpha_term (permute_raw_term (w \<circ> u) tL) tR" 
              using r na by (cases ttdR, auto)
            moreover have "alpha_term (permute_raw_term (u \<circ> v) tL) (permute_raw_term (w \<circ> u) tL)" 
              unfolding uvw using alpha_refls .   
            ultimately have False using alpha_trans alpha_term_sym by blast
          }
          then obtain dd where ttdL: "ttdL = Inr dd" by (cases ttdL, auto)
          hence ttdR: "ttdR = Inr (mapD (u \<circ> v) dd)" using r by (cases ttdR, auto)        
          show "\<exists>uu. bij uu \<and> |supp uu| <o |UNIV::'a set| \<and>
              (\<exists> dd. permute_raw_term (w \<circ> u) (case_sum id (f pick) ttdL) = permute_raw_term uu (f pick dd) \<and>
                     case_sum id (f pick') ttdR = f pick' (mapD uu dd))"  
            by (auto simp: u w supp_comp_bound ttdL ttdR uvw intro: exI[of _ "w o u"] exI[of _ dd]) 
        qed(simp_all add: w u v supp_comp_bound)
      qed(simp_all add: w iw)
    qed 
  }
  thus ?thesis using assms by blast
qed

lemma f_alpha_term: 
  assumes p: "suitable pick" and p': "suitable pick'" 
  shows "alpha_term (f pick d) (f pick' d)"
  using f_swap_alpha_term[OF assms bij_id supp_id_bound, of d] by (simp add: T_map_id) 

(*******************************)
(* Committing to a particular pick function: *)

definition pick0 :: "'a::covar D \<Rightarrow> ('a, 'a, 'a raw_term + 'a D, 'a raw_term + 'a D) F" where
  "pick0 \<equiv> SOME pick. suitable pick"

lemma exists_suitable: 
  "\<exists> pick. suitable pick" 
proof-
  have "\<forall>d. \<exists> X. X \<in> DTOR d" using DTOR_ne by auto
  thus ?thesis unfolding suitable_def by metis
qed

lemma suitable_pick0:
  "suitable pick0"
  using someI_ex[OF exists_suitable] unfolding pick0_def[symmetric] .

definition f0 where "f0 \<equiv> f pick0"

lemmas f0_low_level_simps = f_simps[of pick0, unfolded f0_def[symmetric]]

lemma f0_DTOR: 
  assumes "X \<in> DTOR d"
  shows "alpha_term (f0 d) (ctor (map_term_pre id id (case_sum id f0) (case_sum id f0) X))"
proof-  
  define pick1 where "pick1 \<equiv> \<lambda> d'. if d' = d then X else pick0 d'"
  have 1: "suitable pick1" using suitable_pick0 assms unfolding suitable_def pick1_def by auto
  have 2: "pick1 d = X" unfolding pick1_def by auto
  have 3: "\<And> dd. alpha_term (f0 dd) (f pick1 dd)" using f_alpha_term[OF suitable_pick0 1, of ] 
    unfolding f0_def[symmetric] .
  have 4: "f pick1 d = raw_term_ctor (map_term_pre id id (case_sum id (f pick1)) (case_sum id (f pick1)) X)"
    apply(subst f_simps) unfolding 2 ..
  have 5: "alpha_term (ctor (map_term_pre id id (case_sum id (f pick1)) (case_sum id (f pick1)) X)) 
                       (ctor (map_term_pre id id (case_sum id f0) (case_sum id f0) X))"
    apply(rule alpha_term.intros[of id]) apply (auto simp: F_rel_map simp: Grp_def OO_def supp_id_bound)
    apply(rule term_pre.rel_refl_strong)
    subgoal for td by (cases td, auto simp: alpha_refls alpha_term_sym[OF 3])
    subgoal for td by (cases td, auto simp: T_map_id alpha_refls alpha_term_sym[OF 3]) .
  show ?thesis using 3[of d] 5 unfolding 4[symmetric] using alpha_trans by blast
qed

lemma f0_mapD: 
  assumes "bij (u::'a\<Rightarrow>'a)" and "|supp u| <o |UNIV::'a::covar set|"  
  shows "alpha_term (f0 (mapD u d)) (permute_raw_term u (f0 d))" 
  using alpha_term_sym[OF f_swap_alpha_term[OF suitable_pick0 suitable_pick0 assms, unfolded f0_def[symmetric]]] .

lemmas f0_FVarsD = f_FVarsD[OF suitable_pick0, unfolded f0_def[symmetric]]


(* The following theorems for raw terms will now be lifted to quotiented terms: *)
thm f0_DTOR f0_mapD f0_FVarsD 

(*******************)
(* End product: *)
definition ff0 :: "'a::covar D \<Rightarrow> 'a term" where "ff0 d = TT_abs (f0 d)" 

theorem ff0_DDTOR: 
  assumes "X \<in> DDTOR d"
  shows "ff0 d = term_ctor (map_term_pre id id (case_sum id ff0) (case_sum id ff0) X)"
  using assms using DTOR_def
proof-
  define XX where "XX \<equiv> map_term_pre id id (map_sum TT_rep id) (map_sum TT_rep id) X"
  have XX: "XX \<in> DTOR d" using assms unfolding XX_def DTOR_def by auto
  have 0: "alpha_term 
    (ctor (map_term_pre id id (case_sum TT_rep f0) (case_sum TT_rep f0) X))
    (ctor (map_term_pre id id (case_sum TT_rep (TT_rep \<circ> (TT_abs \<circ> f0))) 
                       (case_sum TT_rep (TT_rep \<circ> (TT_abs \<circ> f0))) X))" 
    apply(rule alpha_term.intros[of id]) apply (auto simp: F_rel_map Grp_def OO_def supp_id_bound)
    apply(rule term_pre.rel_refl_strong)
    subgoal for td by (cases td) (auto simp add: alpha_refls alpha_term_rep_TT_abs alpha_term_sym)  
    subgoal for td by (cases td) (auto simp add: alpha_refls alpha_term_rep_TT_abs alpha_term_sym T_map_id) .
  show ?thesis using f0_DTOR[OF XX] unfolding ff0_def term_ctor_def 
    apply(auto simp: term_pre.map_comp supp_id_bound id_def[symmetric] XX_def  
        TT.abs_eq_iff o_case_sum case_sum_o_map_sum)   
    unfolding o_def[symmetric] using alpha_trans[OF _ 0] by auto
qed

lemma ff0_mmapD: 
  assumes "bij (u::'a\<Rightarrow>'a)" and "|supp u| <o |UNIV::'a::covar set|"  
  shows "ff0 (mmapD u d) = permute_term u (ff0 d)" 
proof-
  {assume "alpha_term (f0 (mmapD u d)) (permute_raw_term u (f0 d))"
    moreover have "alpha_term (permute_raw_term u (f0 d)) (permute_raw_term u (TT_rep (TT_abs (f0 d))))" 
      unfolding alpha_bij_eqs[OF assms] by (simp add: alpha_term_rep_TT_abs alpha_term_sym)
    ultimately have "alpha_term (f0 (mmapD u d)) (permute_raw_term u (TT_rep (TT_abs (f0 d))))" 
      using alpha_trans by blast
  }
  thus ?thesis using f0_mapD[OF assms, of d]
    unfolding ff0_def permute_term_def by(auto simp: TT.abs_eq_iff asSS_def asBij_def assms)
qed

theorem ff0_FVars_termD: 
  "FVars_term (ff0 d) \<subseteq> FVars_termD d"
  using f0_FVarsD[of d] alpha_term_FVars_raw_term alpha_term_rep_TT_abs 
  unfolding ff0_def FVars_term_def by fastforce

hide_const f

context
  fixes f :: "'a :: covar \<Rightarrow> 'a"
  assumes f: "|supp f| <o bound (any :: 'a)"
begin

lift_definition fSS :: "'a ssfun" is f by (rule f)

definition vvsubst where "vvsubst x = ff0 (D x fSS)"

lemma vvsubst_term_ctor: "set2_term_pre x \<inter> imsupp f = {} \<Longrightarrow>
  vvsubst (term_ctor x) = term_ctor (map_term_pre f id vvsubst vvsubst x)"
  unfolding vvsubst_def
  by (subst ff0_DDTOR[unfolded comodel_defs])
    (auto simp: term_pre.map_comp f supp_id_bound o_def id_def[symmetric] Rep_ssfun fSS.rep_eq)

lemma FVars_term_vvsubst_weak: "FVars_term (vvsubst t) \<subseteq> FVars_term t \<union> imsupp f"
  unfolding vvsubst_def
  by (rule order_trans[OF ff0_FVars_termD[unfolded comodel_defs]])
    (auto simp: term_pre.map_comp f supp_id_bound o_def id_def[symmetric] Rep_ssfun fSS.rep_eq)

end

thm vvsubst_term_ctor FVars_term_vvsubst_weak

lemma permute_term_vvsubst:
  fixes f u :: "'a :: covar \<Rightarrow> 'a"
  assumes f: "|supp f| <o bound (any :: 'a)" and u: "bij u" "|supp u| <o bound (any :: 'a)"
  shows "permute_term u (vvsubst f t) = vvsubst (u o f o inv u) (permute_term u t)"
  unfolding vvsubst_def[OF f] ff0_mmapD[unfolded comodel_defs, OF u, symmetric]
  by (auto simp: vvsubst_def assms ff0_mmapD[unfolded comodel_defs, symmetric] supp_comp_bound supp_inv_bound
    fSS_def compSS_def Abs_ssfun_inverse)

lemma FVars_term_vvsubst_le:
  "a \<in> FVars_term u \<Longrightarrow> \<forall>x (f :: 'a::covar \<Rightarrow> 'a).
   u = vvsubst f (term_ctor x) \<longrightarrow> |supp f| <o |UNIV::'a set| \<longrightarrow> set2_term_pre x \<inter> imsupp f = {} \<longrightarrow>
   a \<in> f ` FVars_term (term_ctor x)"
  apply (induct a u rule: FVars_term_induct[rule_format, consumes 1]; (rule allI impI)+)
  subgoal for a fx x f
    apply (auto simp only: term_pre.set_map vvsubst_term_ctor
        bij_id supp_id_bound imsupp_supp_bound TT_inject0s image_id id_apply
        dest!: arg_cong[of _ _ set1_term_pre]
        intro!: imageI FVars_term_intros(1))
    done
  subgoal for fx u a x f
    apply (auto simp only: term_pre.set_map TT_inject0s vvsubst_term_ctor
        supp_id_bound bij_id image_id id_apply dest!: arg_cong[of _ _ set3_term_pre])
    subgoal for v y
      apply (rule fresh_cases[of "imsupp f" y])
       apply (simp only: imsupp_supp_bound)
      apply (drule spec2, drule mp, hypsubst, rule refl)
      apply (auto simp only: intro!: imageI FVars_term_intros(2))
      done
    done
  subgoal for fx u a x f
    apply (auto simp only: term_pre.set_map TT_inject0s vvsubst_term_ctor
        supp_id_bound bij_id image_id id_apply)
    apply (frule arg_cong[of _ _ set2_term_pre, symmetric])
    apply (drule arg_cong[of _ _ set4_F])
    apply (auto simp only: term_pre.set_map TT_inject0s vvsubst_term_ctor
        supp_id_bound bij_id image_id id_apply)
    subgoal for v
      apply (drule arg_cong[of _ _ "image (permute_term (inv v))"])
      apply (auto simp: image_image permute_term_comp[symmetric] permute_term_id supp_inv_bound
          permute_term_vvsubst)
      subgoal for y
        apply (rule fresh_cases[of "imsupp f" y])
         apply (simp only: imsupp_supp_bound)
        apply (hypsubst)
        apply (auto simp: permute_term_term_ctor supp_inv_bound)
        apply (drule spec2, drule mp, rule refl)
        apply (drule mp)
         apply (simp only: supp_comp_bound supp_inv_bound)
        apply (drule mp)
         apply (auto simp: term_pre.set_map supp_inv_bound) []
         apply (auto simp: imsupp_def supp_def bij_imp_inv') []
        apply (auto simp: permute_term_term_ctor[symmetric] supp_inv_bound FVars_term_permute_term)
        apply (auto intro!: image_eqI[rotated, OF FVars_term_intros(3)])
        using imsupp_empty_IntD2 apply fastforce
        apply (auto simp: id_on_def)
        done
      done
    done
  done

lemma FVars_term_vvsubst_ge:
  fixes f::"'a::covar\<Rightarrow>'a"
  assumes "|supp f| <o |UNIV::'a set|"
  shows "a \<in> FVars_term t \<Longrightarrow>  \<forall>x g. |supp g| <o |UNIV::'a set| \<longrightarrow> bij g  \<longrightarrow> g a = a \<longrightarrow>
    t = permute_term (inv g) (term_ctor x) \<longrightarrow> set2_term_pre x \<inter> imsupp f = {} \<longrightarrow>
    f a \<in> FVars_term (vvsubst f (term_ctor x))"
  apply (induct rule: FVars_term_induct[rule_format, consumes 1]; (rule allI impI)+)
  subgoal
    apply (auto simp: vvsubst_term_ctor assms term_pre.set_map supp_id_bound supp_inv_bound TT_inject0s
        permute_term_term_ctor image_iff bij_inv_rev dest!: arg_cong[of _ _ set1_term_pre] intro!: FVars_term_intros(1))
    done
  subgoal for fx t a x g
    apply (auto simp: vvsubst_term_ctor assms term_pre.set_map supp_id_bound supp_inv_bound imsupp_supp_bound
        TT_inject0s permute_term_term_ctor FVars_term_permute_term dest!: arg_cong[of _ _ set3_term_pre])
    subgoal for v u
      apply (rule fresh_cases[of "imsupp f" u])
       apply (simp only: imsupp_supp_bound assms)
      subgoal for y
        apply (drule spec2[of _ y g])
        apply (auto simp: vvsubst_term_ctor bij_inv_rev permute_term_term_ctor supp_id_bound supp_inv_bound term_pre.set_map assms
            intro!: FVars_term_intros(2))
        done
      done
    done
  subgoal for fx t a x g
    apply (auto simp: vvsubst_term_ctor assms term_pre.set_map supp_id_bound supp_inv_bound imsupp_supp_bound
        TT_inject0s permute_term_term_ctor FVars_term_permute_term)
    apply (frule arg_cong[of _ _ set2_term_pre])
    apply (drule arg_cong[of _ _ set4_F])
    apply (auto simp: vvsubst_term_ctor assms term_pre.set_map supp_id_bound supp_inv_bound imsupp_supp_bound
        TT_inject0s permute_term_term_ctor FVars_term_permute_term)
    subgoal for h
      apply (drule id_onD[of _ h a])
       apply auto []
      apply (drule arg_cong[of "h ` _" _ "image (inv h)"])
      apply (drule arg_cong[of "permute_term h ` _" _ "image (permute_term (inv h))"])
      apply (auto simp: image_image permute_term_comp[symmetric] permute_term_id supp_inv_bound
          FVars_term_permute_term)
      subgoal for u
        apply (rule fresh_cases[of "imsupp f" u])
         apply (simp only: imsupp_supp_bound assms)
        subgoal for y
          apply (drule spec2[of _ y "g o h"])
          apply (simp only: supp_comp_bound bij_comp simp_thms permute_term_term_ctor
              o_inv_distrib supp_inv_bound bij_imp_bij_inv o_apply[of g h a])
          apply (auto simp: term_pre.set_map supp_id_bound assms vvsubst_term_ctor
              imsupp_empty_IntD1 image_iff bij_inv_rev bij_imp_inv
              dest!: bspec[of _ _ a] intro!: FVars_term_intros(3))
          done
        done
      done
    done
  done

(* fresnness versus vsubst: *)
theorem FVars_term_vvsubst:
  fixes t :: "('a::covar)TT" and f :: "'a \<Rightarrow> 'a"
  assumes supp: "|supp f| <o |UNIV::'a set|"
  shows "FVars_term (vvsubst f t) = f ` FVars_term t"
  using imsupp_supp_bound[THEN iffD2, OF supp]
proof (cases rule: fresh_cases[of _ t])
  case (1 x)
  show ?thesis
    unfolding \<open>t = term_ctor x\<close>
    apply (rule set_eqI iffI)+
     apply (erule FVars_term_vvsubst_le[rule_format, OF _ refl, of _ f x];
        simp only: supp imsupp_supp_bound 1)
    apply (erule imageE)
    apply hypsubst
    apply (rule FVars_term_vvsubst_ge[rule_format, of f _ t id])
         apply (auto simp: 1 supp_id_bound supp permute_term_id)
    done
qed

theorem vvsubst_permute_term:
  fixes t :: "('a::covar)TT"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "vvsubst f t = permute_term f t"
  apply (coinduction arbitrary: t rule: TT_existential_coinduct)
  subgoal for x y t
    apply (rule fresh_cases[of "imsupp f" t])
     apply (simp only: imsupp_supp_bound assms)
    apply (simp only: imsupp_supp_bound assms vvsubst_term_ctor permute_term_term_ctor)
    apply (rule exI conjI refl)+
      apply (auto simp only: F_rel_map assms supp_inv_bound bij_imp_bij_inv inv_o_simp1
      bij_id supp_id_bound image_id id_apply o_id permute_term_id imsupp_inv bij_inv_rev relcompp_apply Grp_def
      elim!: imsupp_empty_IntD2[symmetric] intro!: exI[of _ id]
      F_rel_mono_strong0[rotated 6, OF F.rel_eq[THEN predicate2_eqD, THEN iffD2], OF refl])
    done
  done

theorem vvsubst_id: "vvsubst id t = t"
  unfolding vvsubst_permute_term[OF bij_id supp_id_bound] permute_term_id id_apply ..

(* Compositonality (bound-restricted functoriality) of vsubst: *)
theorem vvsubst_o:
  fixes t :: "('a::covar)TT"
  assumes supp: "|supp g| <o |UNIV::'a set|" "|supp f| <o |UNIV::'a set|"
  shows "vvsubst (g o f) t = vvsubst g (vvsubst f t)"
  apply (coinduction arbitrary: t rule: TT_existential_coinduct)
  subgoal for x y t
    apply (rule fresh_cases[of "imsupp f \<union> imsupp g" t])
     apply (auto simp only: Un_bound imsupp_supp_bound assms vvsubst_term_ctor
        imsupp_disj_comp Int_Un_distrib term_pre.set_map bij_id supp_id_bound supp_comp_bound
        image_id id_apply)
    apply (rule exI conjI refl)+
    apply (auto simp only: F_rel_map term_pre.map_comp
        assms bij_id supp_id_bound supp_comp_bound id_o)
    apply (rule F_rel_mono_strong0[rotated 6, OF F_rel_map_right[rotated 6, OF F.rel_refl[of "(=)" "(=)"]]])
                     apply (auto simp only: o_apply id_apply id_def[symmetric] supp_comp_bound supp_id_bound bij_id assms term_pre.set_map Grp_def id_o)
    done
  done

(* Obliviousness of ssubst w.r.t. fresh covariables: *)
theorem vvsubst_cong:
  fixes t :: "('a::covar)TT"
  assumes supp: "|supp f| <o |UNIV::'a set|" "|supp g| <o |UNIV::'a set|"
    and fr: "\<And> a. a \<in> FVars_term t \<Longrightarrow> f a = g a"
  shows "vvsubst f t = vvsubst g t"
  using fr
  apply (coinduction arbitrary: t rule: TT_existential_coinduct)
  subgoal for x y t
    apply (rule fresh_cases[of "imsupp f \<union> imsupp g" t])
     apply (auto simp only: Un_bound imsupp_supp_bound assms vvsubst_term_ctor Int_Un_distrib)
    apply (rule exI conjI refl)+
    apply (auto simp only: F_rel_map term_pre.map_comp
        assms bij_id supp_id_bound supp_comp_bound id_o)
    apply (rule F_rel_mono_strong0[rotated 6, OF F_rel_map_right[rotated 6, OF F.rel_refl[of "(=)" "(=)"]]])
                     apply (auto simp only: o_apply id_apply id_def[symmetric] supp_comp_bound supp_id_bound bij_id
        assms term_pre.set_map FVars_ctors relcompp_apply id_o Un_iff UN_iff imp_disjL all_conj_distrib)
    subgoal
      apply (simp only: Grp_def simp_thms UNIV_I)
      apply (rule disjI1 exI conjI refl)+
      apply (auto simp only:)
      done
    subgoal
      apply (simp only: Grp_def simp_thms UNIV_I)
      apply (rule disjI1 exI conjI refl)+
      apply (auto simp only: dest!: imsupp_empty_IntD2)
      done
    done
  done

(* Unary covar-substitution: *)
definition vusubst :: "('a::covar) \<Rightarrow> 'a \<Rightarrow> 'a term \<Rightarrow> 'a term" where
  "vusubst a a' t \<equiv> vvsubst (id(a:=a')) t"

(* The next is the simplification rule working with the covariable convention: *)
theorem vusubst_term_ctor:
  assumes "set2_term_pre x \<inter> {a,a'} = {}"
  shows "vusubst a a' (term_ctor x) =  term_ctor (map_term_pre (id(a := a')) id (vusubst a a') (vusubst a a') x)"
  unfolding vusubst_def using assms
  apply (force simp only: supp_id_upd imsupp_id_fun_upd intro!: vvsubst_term_ctor split: if_splits)
  done

theorem FVars_term_vusubst:
  fixes t :: "('a::covar)TT"
  shows "FVars_term (vusubst a1 a2 t) = (if a1 \<in> FVars_term t then FVars_term t - {a1} \<union> {a2} else FVars_term t)"
  unfolding vusubst_def
  apply (auto simp only: FVars_term_vvsubst supp_id_upd fun_upd_apply id_apply split: if_splits)
  done

theorem vusubst_comp_same:
  fixes t :: "('a::covar)TT"
  shows "vusubst a a2 (vusubst a a1 t) = vusubst a ((id(a:=a2)) a1) t"
  unfolding vusubst_def
  apply (auto simp only: vvsubst_o[symmetric] supp_id_upd supp_comp_bound
      o_apply fun_upd_apply id_apply intro!: vvsubst_cong split: if_splits)
  done

theorem vusubst_comp_diff:
  fixes t :: "('a::covar)TT"
  assumes diff: "a1 \<noteq> a2" "a1 \<noteq> a2'"
  shows "vusubst a2 a2' (vusubst a1 a1' t) = vusubst a1 ((id(a2:=a2')) a1') (vusubst a2 a2' t)"
  unfolding vusubst_def using diff
  apply (auto simp only: vvsubst_o[symmetric] supp_id_upd supp_comp_bound
      o_apply fun_upd_apply id_apply intro!: vvsubst_cong split: if_splits)
  done

theorem vusubst_idle:
  fixes t :: "('a::covar)TT"
  assumes "a \<notin> FVars_term t"
  shows "vusubst a a' t = t"
  unfolding vusubst_def using assms
  apply (auto simp only: supp_id_bound supp_id_upd
      fun_upd_apply id_apply intro!: trans[OF vvsubst_cong vvsubst_id] split: if_splits)
  done

definition rel_TT where "rel_TT f = Grp (vvsubst f)"

lemma rel_TT_eq: "rel_TT id = (=)"
  unfolding rel_TT_def vvsubst_id id_def[symmetric] eq_alt[symmetric] ..

lemma TT_rel_compp_le:
  fixes f g :: "'a::covar \<Rightarrow> 'a"
  shows "|supp f| <o |UNIV::'a set| \<Longrightarrow> |supp g| <o |UNIV::'a set| \<Longrightarrow> rel_TT f OO rel_TT g \<le> rel_TT (g o f)"
  unfolding rel_TT_def by (auto simp: Grp_def vvsubst_o)

lemma TT_inject:
  fixes x x' :: "('a::covar, 'a, 'a term, 'a term) F"
  shows "(term_ctor x = term_ctor x') =
  (\<exists>f. bij f \<and>
       |supp f| <o |UNIV::'a set| \<and>
       id_on ((\<Union>t\<in>set4_F x. FVars_term t) - set2_term_pre x) f \<and>
       map_term_pre id f id (vvsubst f) x = x')"
  unfolding TT_inject0s
  apply (rule ex_cong conj_cong refl iffI F_map_cong | erule trans[rotated]
      | auto simp only: supp_id_bound bij_id id_apply vvsubst_permute_term)+
  done

thm \<comment> \<open>MRBNF properties\<close>
  vvsubst_id
  vvsubst_o
  FVars_term_vvsubst
  vvsubst_cong
  card_of_FVars_term_bound
  bound_card_order
  bound_cinfinite
  rel_TT_def
  rel_TT_eq
  TT_rel_compp_le

end