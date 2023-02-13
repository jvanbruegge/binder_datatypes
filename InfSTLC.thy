theory InfSTLC
  imports "./thys/MRBNF_Recursor" "./DALList"
begin

datatype \<tau> = Unit | Arrow \<tau> \<tau> (infix "\<rightarrow>" 60)

(*
binder_datatype 'var terms =
  Var 'var
| App "'var terms" "'var terms"
| Lam x::'var \<tau> t::"'var terms" binds x in t
| LetRec "(xs::'var, (\<tau> * ts::"'var terms")) dallist" t::"'var terms" binds xs in t ts
*)

ML \<open>
val name = "terms"
val T = @{typ "'var + 'rec * 'rec + 'bvar * \<tau> * 'brec + ('bvar, (\<tau> * 'brec)) dallist * 'brec"}
\<close>

declare [[mrbnf_internals]]
local_setup \<open>fn lthy =>
let
  val Xs = map dest_TFree [@{typ 'bvar}, @{typ 'brec}, @{typ 'rec}]
  val resBs = map dest_TFree [@{typ 'var}]
  val rel = [[0]]

  fun flatten_tyargs Ass = subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;
  val qualify = Binding.prefix_name (name ^ "_pre_")

  (* Step 1: Create pre-MRBNF *)
  val ((mrbnf, tys), (accum, lthy)) = MRBNF_Comp.mrbnf_of_typ true MRBNF_Def.Smart_Inline qualify flatten_tyargs Xs []
    [(dest_TFree @{typ 'var}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var)] T
    ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy)

  (* Step 2: Seal the pre-MRBNF with a typedef *)
  val ((mrbnf, (Ds, info)), lthy) = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name (name ^ "_pre")) true (fst tys) [] mrbnf lthy

  (* Step 3: Register the pre-MRBNF as a BNF in its live variables *)
  val (bnf, lthy) = MRBNF_Def.register_mrbnf_as_bnf mrbnf lthy

  (* Step 4: Create fixpoint of pre-MRBNF *)
  val (res, lthy) = MRBNF_FP.construct_binder_fp MRBNF_Util.Least_FP [((name, mrbnf), 2)] rel lthy;

  (* Step 5: Create recursor and create fixpoint as MRBNF *)
  val (rec_mrbnf, lthy) = MRBNF_VVSubst.mrbnf_of_quotient_fixpoint @{binding vvsubst} I (hd res) lthy;

  (* Step 6: Register fixpoint MRBNF *)
  val lthy = MRBNF_Def.register_mrbnf_raw (fst (dest_Type (#T (#quotient_fp (hd res))))) rec_mrbnf lthy;

  (* Step 7: Also register the DALList MRBNF as a BNF in its live variables *)
  val (bnf, lthy) = MRBNF_Def.register_mrbnf_as_bnf (the (MRBNF_Def.mrbnf_of lthy "DALList.dallist")) lthy
in lthy end\<close>
print_theorems
print_mrbnfs
print_bnfs

thm terms.TT_fresh_nchotomys
lemma TT_fresh_nchotomys: "|A::'a::var_terms_pre set| <o |UNIV::'a set| \<Longrightarrow> \<exists>v. w = terms_ctor v \<and> set2_terms_pre v \<inter> A = {} \<and> noclash_terms v"
  apply (rule mp[OF bspec[OF terms.TT_fresh_co_induct_param[of _ "\<lambda>x. FFVars_terms x \<union> A" "\<lambda>e \<rho>. e = \<rho> \<longrightarrow> (\<exists>v. e = terms_ctor v \<and> set2_terms_pre v \<inter> A = {} \<and> noclash_terms v)" w] UNIV_I]])
   apply (rule terms.Un_bound)
    apply (rule terms.set_bd_UNIV)
    apply assumption

   apply (rule impI)
   apply hypsubst
   apply (rule exI)
   apply (rule conjI)
    apply (rule refl)
  subgoal premises prems for v x
   apply (rule conjI)
    apply (rule iffD2[OF disjoint_iff])
    apply (rule allI)
     apply (rule impI)
     apply (drule prems)
     apply (unfold Un_iff de_Morgan_disj terms.FFVars_cctors)
    apply (erule conjE)+
    apply assumption
   apply (subst noclash_terms_def)
    apply (rule iffD2[OF disjoint_iff])
    apply (rule allI impI)+
    apply (drule prems)
    apply (unfold Un_iff de_Morgan_disj terms.FFVars_cctors)
    apply (erule conjE)+
    apply (rule conjI)
     apply assumption
    apply assumption
    done
  apply (rule refl)
  done

(* obtain a term-for-variable substitution function, \<eta> is the free variable injection *)
definition "\<eta> \<equiv> Abs_terms_pre \<circ> Inl"
lemma \<eta>_free: "set1_terms_pre (\<eta> a) = {a}"
  unfolding set1_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I] \<eta>_def
  by auto
lemma \<eta>_inj: "\<eta> a = \<eta> b \<Longrightarrow> a = b"
  unfolding Abs_terms_pre_inject[OF UNIV_I UNIV_I] sum.inject comp_def \<eta>_def
  by assumption
lemma \<eta>_compl_free: "x \<notin> range \<eta> \<Longrightarrow> set1_terms_pre x = {}"
  unfolding set1_terms_pre_def comp_def Un_empty sum.set_map UN_singleton UN_empty2
  apply (rule conjI)
   apply (rule Abs_terms_pre_cases[of x])
  apply hypsubst_thin
  unfolding Abs_terms_pre_inverse[OF UNIV_I] Abs_terms_pre_inject[OF UNIV_I UNIV_I] image_iff bex_UNIV comp_def \<eta>_def
   apply (erule contrapos_np)
   apply (drule iffD2[OF ex_in_conv])
   apply (erule exE)
   apply (erule setl.cases)
   apply hypsubst
   apply (rule exI)
   apply (rule refl)
  apply (rule refl)
  done
lemma \<eta>_natural: "|supp (f::'a::var_terms_pre \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> bij g \<Longrightarrow> |supp (g::'b::var_terms_pre \<Rightarrow> 'b)| <o |UNIV::'b set|
  \<Longrightarrow> map_terms_pre f g h i \<circ> \<eta> = \<eta> \<circ> f"
  unfolding comp_def map_terms_pre_def Abs_terms_pre_inverse[OF UNIV_I] map_sum.simps  \<eta>_def
  by (rule refl)

local_setup \<open>fn lthy =>
let
  val fp_result = the (MRBNF_FP_Def_Sugar.fp_result_of lthy "InfSTLC.terms")

  val axioms = {
    eta_free = fn ctxt => resolve_tac ctxt @{thms \<eta>_free} 1,
    eta_inj = fn ctxt => resolve_tac ctxt @{thms \<eta>_inj} 1 THEN assume_tac ctxt 1,
    eta_compl_free = fn ctxt => resolve_tac ctxt @{thms \<eta>_compl_free} 1 THEN assume_tac ctxt 1,
    eta_natural = fn ctxt => resolve_tac ctxt @{thms \<eta>_natural} 1 THEN ALLGOALS (assume_tac ctxt)
  };

  val model = {
    fp_result = fp_result,
    etas = [SOME (
      @{term "\<eta>::'a::var_terms_pre \<Rightarrow> ('a, 'b::var_terms_pre, 'c, 'd) terms_pre"},
      axioms
    )]
  };
  val lthy = MRBNF_TVSubst.create_tvsubst_of_mrbnf @{binding tvsubst} (Binding.prefix_name "tv") model lthy
in lthy end
\<close>
print_theorems

lemma disjoint_single: "{x} \<inter> A = {} \<longleftrightarrow> x \<notin> A"
  by simp
lemma UN_snds_eq_snd: "\<Union>(Basic_BNFs.snds ` A) = snd ` A" by force

(* Better syntax *)
definition Var :: "'a \<Rightarrow> 'a::var_terms_pre terms" where
  "Var a \<equiv> terms_ctor (Abs_terms_pre (Inl a))"
definition App :: "'a terms \<Rightarrow> 'a terms \<Rightarrow> 'a::var_terms_pre terms" where
  "App e1 e2 \<equiv> terms_ctor (Abs_terms_pre (Inr (Inl (e1, e2))))"
definition Lam :: "'a \<Rightarrow> \<tau> \<Rightarrow> 'a terms \<Rightarrow> 'a::var_terms_pre terms" where
  "Lam x \<tau> e \<equiv> terms_ctor (Abs_terms_pre (Inr (Inr (Inl (x, \<tau>, e)))))"
definition LetRec :: "('a, (\<tau> * 'a terms)) dallist \<Rightarrow> 'a terms \<Rightarrow> 'a::var_terms_pre terms" where
  "LetRec xs e \<equiv> terms_ctor (Abs_terms_pre (Inr (Inr (Inr (xs, e)))))"

lemma terms_inject_plain[simp]:
  "Var a = Var b \<longleftrightarrow> a = b"
  "App e1 e2 = App t1 t2 \<longleftrightarrow> e1 = t1 \<and> e2 = t2"
  unfolding Var_def App_def terms.TT_injects0 map_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I] Abs_terms_pre_inject[OF UNIV_I UNIV_I] map_sum_def sum.case prod.map_id
  by (auto simp: supp_id_bound)

thm terms.TT_injects0

lemma terms_distinct[simp]:
  "Var a \<noteq> App e1 e2"
  "Var a \<noteq> Lam x \<tau> e"
  "Var a \<noteq> LetRec xs e"
  "App e1 e2 \<noteq> Var a"
  "App e1 e2 \<noteq> Lam x \<tau> e"
  "App e1 e2 \<noteq> LetRec xs e"
  "Lam x \<tau> e \<noteq> Var a"
  "Lam x \<tau> e \<noteq> App e1 e2"
  "Lam x \<tau> e \<noteq> LetRec xs e2"
  "LetRec xs e \<noteq> Var a"
  "LetRec xs e \<noteq> App e1 e2"
  "LetRec xs e \<noteq> Lam x \<tau> e2"
  unfolding Var_def App_def Lam_def LetRec_def terms.TT_injects0 map_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I] Abs_terms_pre_inject[OF UNIV_I UNIV_I] map_sum_def sum.case
  by auto

lemma rrename_simps:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows
    "rrename_terms f (Var x) = Var (f x)"
    "rrename_terms f (App e1 e2) = App (rrename_terms f e1) (rrename_terms f e2)"
    "rrename_terms f (Lam x \<tau> e) = Lam (f x) \<tau> (rrename_terms f e)"
    "rrename_terms f (LetRec xs e) = LetRec (map_dallist f (map_prod id (rrename_terms f)) xs) (rrename_terms f e)"
     apply (unfold Var_def App_def Lam_def LetRec_def terms.rrename_cctors[OF assms])
     apply (unfold map_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I] map_sum.simps map_prod_simp id_def)
     apply (rule refl)+
  done

lemma vvsubst_simps:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a"
  assumes "|supp f| <o |UNIV::'a set|"
  shows
    "vvsubst f (Var x) = Var (f x)"
    "vvsubst f (App e1 e2) = App (vvsubst f e1) (vvsubst f e2)"
    "x \<notin> imsupp f \<Longrightarrow> vvsubst f (Lam x \<tau> e) = Lam x \<tau> (vvsubst f e)"
    "keys_dallist xs \<inter> imsupp f = {} \<Longrightarrow> vvsubst f (LetRec xs e) = LetRec (map_dallist id (map_prod id (vvsubst f)) xs) (vvsubst f e)"
     apply (unfold Var_def App_def Lam_def LetRec_def)

     apply (subst terms_cctor)
       apply (rule assms)
  apply (unfold noclash_terms_def set2_terms_pre_def sum.set_map prod.set_map UN_empty2 comp_def Un_empty_left Abs_terms_pre_inverse[OF UNIV_I] sum_set_simps UN_empty UN_single)
      apply (rule Int_empty_left)+
    apply (unfold map_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I] map_sum.simps map_prod_simp)[1]
  apply (rule refl)

    (* repeat *)
     apply (subst terms_cctor)
       apply (rule assms)
  apply (unfold noclash_terms_def set2_terms_pre_def sum.set_map prod.set_map UN_empty2 comp_def Un_empty_left Abs_terms_pre_inverse[OF UNIV_I] sum_set_simps UN_empty UN_single)
      apply (rule Int_empty_left)+
    apply (unfold map_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I] map_sum.simps map_prod_simp)[1]
    apply (rule refl)


     apply (subst terms_cctor)
       apply (rule assms)
     apply (unfold noclash_terms_def set2_terms_pre_def set1_terms_pre_def set4_terms_pre_def sum.set_map prod.set_map UN_empty2 comp_def Un_empty_right Un_empty_left Abs_terms_pre_inverse[OF UNIV_I] sum_set_simps UN_empty UN_single UN_singleton prod_set_simps)
     apply (rule iffD2[OF disjoint_iff])
     apply (rule allI)
     apply (rule impI)
     apply (drule singletonD)
     apply hypsubst
     apply assumption
  apply (rule Int_empty_right)
    apply (unfold map_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I] map_sum.simps map_prod_simp id_def)[1]
   apply (rule refl)

     apply (subst terms_cctor)
       apply (rule assms)
     apply (unfold dallist.set_map[OF bij_id supp_id_bound] noclash_terms_def set2_terms_pre_def set1_terms_pre_def set4_terms_pre_def sum.set_map prod.set_map UN_empty2 comp_def Un_empty_right Un_empty_left Abs_terms_pre_inverse[OF UNIV_I] sum_set_simps UN_empty UN_single UN_singleton prod_set_simps)
     apply assumption
  apply (rule Int_empty_right)
    apply (unfold map_terms_pre_def comp_def Abs_terms_pre_inverse[OF UNIV_I] map_sum.simps map_prod_simp)[1]
  apply (rule refl)
  done

lemma Var_is_VVr: "Var x = VVr x"
  unfolding Var_def VVr_def \<eta>_def comp_def by (rule refl)

lemma not_VVr:
  "\<not>isVVr (App e1 e2)"
  "\<not>isVVr (Lam x \<tau> e)"
  "\<not>isVVr (LetRec xs e)"
    apply (unfold isVVr_def VVr_def \<eta>_def comp_def App_def Lam_def LetRec_def)
    apply (rule ccontr)
    apply (unfold not_not)
    apply (erule exE)
    apply (drule iffD1[OF terms.TT_injects0])
    apply (erule exE conjE)+
    apply (unfold map_terms_pre_def comp_def map_sum.simps prod.map_id Abs_terms_pre_inverse[OF UNIV_I]
      Abs_terms_pre_inject[OF UNIV_I UNIV_I] Inr_Inl_False
    )
    apply assumption
apply (rule ccontr)
    apply (unfold not_not)
    apply (erule exE)
    apply (drule iffD1[OF terms.TT_injects0])
    apply (erule exE conjE)+
    apply (unfold map_terms_pre_def comp_def map_sum.simps prod.map_id Abs_terms_pre_inverse[OF UNIV_I]
      Abs_terms_pre_inject[OF UNIV_I UNIV_I] Inr_Inl_False
    )
   apply assumption
apply (rule ccontr)
    apply (unfold not_not)
    apply (erule exE)
    apply (drule iffD1[OF terms.TT_injects0])
    apply (erule exE conjE)+
    apply (unfold map_terms_pre_def comp_def map_sum.simps prod.map_id Abs_terms_pre_inverse[OF UNIV_I]
      Abs_terms_pre_inject[OF UNIV_I UNIV_I] Inr_Inl_False
    )
  apply assumption
  done

lemma tvsubst_simps:
  assumes "|SSupp (f::'a::var_terms_pre \<Rightarrow> 'a terms)| <o |UNIV::'a set|"
  shows
    "tvsubst f (Var x) = f x"
    "tvsubst f (App e1 e2) = App (tvsubst f e1) (tvsubst f e2)"
    "x \<notin> IImsupp f \<Longrightarrow> tvsubst f (Lam x \<tau> e) = Lam x \<tau> (tvsubst f e)"
    "keys_dallist xs \<inter> IImsupp f = {} \<Longrightarrow> tvsubst f (LetRec xs e) = LetRec (map_dallist id (map_prod id (tvsubst f)) xs) (tvsubst f e)"
     apply (unfold Var_is_VVr App_def Lam_def LetRec_def)
     apply (rule tvsubst_VVr)
     apply (rule assms)
    apply (rule trans)
     apply (rule tvsubst_cctor_not_isVVr)
        apply (rule assms)
       apply (unfold set2_terms_pre_def sum.set_map UN_empty2 Un_empty_left prod.set_map Un_empty_right
        UN_singleton dallist.set_map[OF bij_id supp_id_bound] comp_def Abs_terms_pre_inverse[OF UNIV_I]
        sum_set_simps UN_single UN_empty tvnoclash_terms_def map_terms_pre_def map_sum.simps map_prod_simp
      )
       apply (rule Int_empty_left)+
     apply (unfold App_def[symmetric])[1]
     apply (rule not_VVr)
    apply (rule refl)

   apply (rule trans)
    apply (rule tvsubst_cctor_not_isVVr)
        apply (rule assms)
       apply (unfold set2_terms_pre_def sum.set_map UN_empty2 Un_empty_left prod.set_map Un_empty_right
        UN_singleton dallist.set_map[OF bij_id supp_id_bound] comp_def Abs_terms_pre_inverse[OF UNIV_I]
        sum_set_simps UN_single UN_empty tvnoclash_terms_def map_terms_pre_def map_sum.simps map_prod_simp
        prod_set_simps disjoint_single set1_terms_pre_def set4_terms_pre_def empty_iff not_False_eq_True
      )
      apply assumption
     apply (rule TrueI)
    apply (unfold Lam_def[symmetric])[1]
    apply (rule not_VVr)
   apply (unfold id_def)[1]
   apply (rule refl)

   apply (rule trans)
    apply (rule tvsubst_cctor_not_isVVr)
        apply (rule assms)
       apply (unfold set2_terms_pre_def sum.set_map UN_empty2 Un_empty_left prod.set_map Un_empty_right
        UN_singleton dallist.set_map[OF bij_id supp_id_bound] comp_def Abs_terms_pre_inverse[OF UNIV_I]
        sum_set_simps UN_single UN_empty tvnoclash_terms_def map_terms_pre_def map_sum.simps map_prod_simp
        prod_set_simps disjoint_single set1_terms_pre_def set4_terms_pre_def empty_iff not_False_eq_True
      )
      apply assumption
     apply (rule Int_empty_right)
    apply (unfold LetRec_def[symmetric])[1]
    apply (rule not_VVr)
   apply (unfold id_def)[1]
   apply (rule refl)
  done

lemma FFVars_simps:
  "FFVars_terms (Var x) = {x}"
  "FFVars_terms (App e1 e2) = FFVars_terms e1 \<union> FFVars_terms e2"
  "FFVars_terms (Lam x \<tau> e) = FFVars_terms e - {x}"
  "FFVars_terms (LetRec xs e) = (\<Union>(FFVars_terms ` snd ` vals_dallist xs) \<union> FFVars_terms e) - keys_dallist xs"
     apply (unfold Var_def App_def Lam_def LetRec_def terms.FFVars_cctors
      set1_terms_pre_def comp_def prod.set_map sum.set_map Abs_terms_pre_inverse[OF UNIV_I] UN_singleton
      sum_set_simps prod_set_simps UN_empty Un_empty_right set3_terms_pre_def UN_empty2 empty_Diff
      set4_terms_pre_def Un_empty_left UN_single UN_Un set2_terms_pre_def dallist.set_map[OF bij_id supp_id_bound]
      UN_snds_eq_snd image_comp snd_conv
    )
     apply (rule refl)+
  done

lemma Lam_avoid: "|A::'a::var_terms_pre set| <o |UNIV::'a set| \<Longrightarrow> \<exists>x' e'. Lam x \<tau> e = Lam x' \<tau> e' \<and> x' \<notin> A"
  apply (rule exE[OF terms.TT_fresh_nchotomys[of _ "Lam x \<tau> e"]])
   apply assumption
  apply (erule conjE)
  apply (unfold Lam_def terms.TT_injects0)
  apply (erule exE)
  apply (erule conjE)+
  apply hypsubst
  apply (unfold map_terms_pre_def comp_def map_sum.id map_prod.id Abs_terms_pre_inverse[OF UNIV_I] map_sum.simps map_prod_simp set3_terms_pre_def
    prod_set_simps UN_empty UN_empty2 Union_empty sum_set_simps Un_empty_left Un_empty_right cSup_singleton UN_single
    set2_terms_pre_def
  )
  apply (rule exI)+
  apply (rule conjI[rotated])
   apply (drule iffD1[OF disjoint_single])
   apply assumption
  apply (rule exI)
  apply (rule conjI, assumption)+
  apply (unfold id_def)
  apply (rule refl)
  done

lemma LetRec_avoid: "|A::'a::var_terms_pre set| <o |UNIV::'a set| \<Longrightarrow> \<exists>ys e'. LetRec xs e = LetRec ys e' \<and> keys_dallist ys \<inter> A = {}"
  apply (rule exE[OF terms.TT_fresh_nchotomys[of _ "LetRec xs e"]])
   apply assumption
  apply (erule conjE)
  apply (unfold LetRec_def terms.TT_injects0)
  apply (erule exE conjE)+
  apply hypsubst
  apply (unfold map_terms_pre_def comp_def map_sum.id map_prod.id Abs_terms_pre_inverse[OF UNIV_I] map_sum.simps map_prod_simp set3_terms_pre_def
    prod_set_simps UN_empty UN_empty2 Union_empty sum_set_simps Un_empty_left Un_empty_right cSup_singleton UN_single
    set2_terms_pre_def dallist.set_map[OF bij_id supp_id_bound] prod.set_map UN_singleton
  )
  apply (rule exI)+
  apply (rule conjI[rotated])
   apply assumption
  apply (rule exI)
  apply (rule conjI, assumption)+
  apply (rule refl)
  done

thm terms.TT_injects0

lemma Lam_inject: "Lam x \<tau> e = Lam y \<tau>' e' \<longleftrightarrow> (\<exists>(f::'a::var_terms_pre \<Rightarrow> 'a). bij f \<and> |supp f| <o |UNIV::'a set|
  \<and> id_on (FFVars_terms e - {x}) f \<and> f x = y \<and> \<tau> = \<tau>' \<and> vvsubst f e = e')"
  apply (unfold Lam_def terms.TT_injects0 set3_terms_pre_def map_sum.simps map_prod_simp Abs_terms_pre_inverse[OF UNIV_I]
    sum_set_simps prod_set_simps prod.set_map sum.set_map UN_empty2 Un_empty_left UN_singleton comp_def
    dallist.set_map[OF bij_id supp_id_bound] UN_single UN_empty Un_empty_right set2_terms_pre_def
    map_terms_pre_def id_def Abs_terms_pre_inject[OF UNIV_I UNIV_I] sum.inject prod.inject
  )
  apply (rule iffI)
   apply (erule exE conjE)+
   apply (rule exI)
   apply (rule conjI, assumption)+
   apply (unfold terms_vvsubst_rrename)
   apply assumption
  apply (erule exE conjE)+
  apply (rule exI)
  apply (rule conjI, assumption)+
  apply (unfold terms_vvsubst_rrename)
  apply assumption
  done

lemma LetRec_inject: "LetRec xs e = LetRec ys e' \<longleftrightarrow> (\<exists>(f::'a::var_terms_pre \<Rightarrow> 'a).
  bij f \<and> |supp f| <o |UNIV::'a set| \<and> id_on ((\<Union>(FFVars_terms ` snd ` vals_dallist xs) \<union> FFVars_terms e) - keys_dallist xs) f
  \<and> map_dallist f (map_prod id (vvsubst f)) xs = ys \<and> vvsubst f e = e')"
  apply (unfold LetRec_def terms.TT_injects0 set3_terms_pre_def map_sum.simps map_prod_simp Abs_terms_pre_inverse[OF UNIV_I]
    sum_set_simps prod_set_simps prod.set_map sum.set_map UN_empty2 Un_empty_left UN_singleton comp_def
    dallist.set_map[OF bij_id supp_id_bound] UN_single UN_empty Un_empty_right set2_terms_pre_def
    map_terms_pre_def Abs_terms_pre_inject[OF UNIV_I UNIV_I] sum.inject prod.inject
    UN_snds_eq_snd UN_Un
  )
  apply (rule iffI)
   apply (erule exE conjE)+
   apply (rule exI)
   apply (rule conjI, assumption)+
   apply (unfold terms_vvsubst_rrename)
   apply (rule conjI)
    apply assumption+
  apply (erule exE conjE)+
  apply (unfold terms_vvsubst_rrename)
  apply (rule exI)
  apply ((rule conjI)?, assumption)+
  done

lemma TT_fresh_induct_param[case_names Bound Var App Lam LetRec]:
  fixes x::"'a::var_terms_pre terms" and K::"'b \<Rightarrow> 'a set"
  assumes "\<forall>\<rho>. |K \<rho>| <o |UNIV::'a set|"
  and Var: "\<And>a \<rho>. P (Var a) \<rho>"
  and App: "\<And>e1 e2 \<rho>. \<lbrakk> \<forall>\<rho>. P e1 \<rho> ; \<forall>\<rho>. P e2 \<rho> \<rbrakk> \<Longrightarrow> P (App e1 e2) \<rho>"
  and Lam: "\<And>x \<tau> e \<rho>. \<lbrakk> x \<notin> K \<rho> ; \<forall>\<rho>. P e \<rho> \<rbrakk> \<Longrightarrow> P (Lam x \<tau> e) \<rho>"
  and LetRec: "\<And>xs e \<rho>. \<lbrakk> keys_dallist xs \<inter> K \<rho> = {} ; pred_dallist (\<lambda>(_, e). \<forall>\<rho>. P e \<rho>) xs ; \<forall>\<rho>. P e \<rho> \<rbrakk> \<Longrightarrow> P (LetRec xs e) \<rho>"
shows "\<forall>\<rho>. P x \<rho>"
  apply (rule allI)
  apply (rule spec[OF terms.TT_fresh_co_induct_param[of UNIV K, unfolded ball_UNIV]])
   apply (rule spec[OF assms(1)])
  subgoal for \<rho>1 v \<rho>2
    apply (rule Abs_terms_pre_cases[of v])
    apply hypsubst_thin
    subgoal for y
      apply (rule sum.exhaust[of y])
       apply hypsubst
       apply (unfold Var_def[symmetric])
       apply (rule Var)
      subgoal for x2
        apply (rule sum.exhaust[of x2])
         apply hypsubst_thin
        subgoal for x1
          apply (rule prod.exhaust[of x1])
          apply hypsubst_thin
          apply (unfold App_def[symmetric])
          apply (rule App)
           apply (rule allI)
           apply (unfold set4_terms_pre_def comp_def prod.set_map sum.set_map UN_empty2 Un_empty_left Abs_terms_pre_inverse[OF UNIV_I] sum_set_defs sum.case UN_single UN_empty map_sum_def Union_empty Un_empty_right UN_singleton prod_set_defs map_prod_simp fst_conv snd_conv cSup_singleton)
          subgoal premises IH
            apply (rule IH(2))
             apply (rule UnI1)
             apply (rule singletonI)
            apply (rule UNIV_I)
            done
          apply (rule allI)
          subgoal premises IH
            apply (rule IH(2))
             apply (rule UnI2)
             apply (rule singletonI)
            apply (rule UNIV_I)
            done
          done
        subgoal for x3
          apply (rule sum.exhaust[of x3])
          subgoal for x4
            apply (rule prod.exhaust[of x4])
            subgoal for x5 x6
              apply (rule prod.exhaust[of x6])
              apply hypsubst_thin
              apply (unfold Lam_def[symmetric])
              apply (unfold set2_terms_pre_def set3_terms_pre_def comp_def prod.set_map sum.set_map UN_empty2 Un_empty_left Abs_terms_pre_inverse[OF UNIV_I] sum_set_defs sum.case UN_single UN_empty map_sum_def Union_empty Un_empty_right UN_singleton prod_set_defs map_prod_simp fst_conv snd_conv cSup_singleton)
              subgoal premises IHs
                apply (rule Lam)
                 apply (rule IHs)
                 apply (rule singletonI)
                apply (rule allI)
                apply (rule IHs(1))
                 apply (rule singletonI)
                apply (rule UNIV_I)
                done
              done
            done
          subgoal for x4
            apply (rule prod.exhaust[of x4])
            apply hypsubst_thin
            apply (unfold LetRec_def[symmetric])
            apply (unfold UNION_singleton_eq_range dallist.set_map[OF bij_id supp_id_bound] fst_map_prod snd_map_prod set2_terms_pre_def set3_terms_pre_def comp_def prod.set_map sum.set_map UN_empty2 Un_empty_left Abs_terms_pre_inverse[OF UNIV_I] sum_set_defs sum.case UN_single UN_empty map_sum_def Union_empty Un_empty_right UN_singleton prod_set_defs map_prod_simp fst_conv snd_conv cSup_singleton)
            subgoal premises IHs
            apply (rule LetRec)
              apply (rule iffD2[OF disjoint_iff])
              apply (rule allI)
              apply (rule impI)
                apply (rule IHs(3))
              apply assumption
             apply (unfold dallist.pred_set)
             apply (rule ballI)
             apply (unfold case_prod_beta)
               apply (rule allI)
               apply (rule IHs(1))
                apply (rule UnI1)
                apply (rule imageI)
                apply assumption
               apply (rule UNIV_I)
              apply (rule allI)
              apply (rule IHs(1))
               apply (rule UnI2)
               apply (rule singletonI)
              apply (rule UNIV_I)
              done
            done
          done
        done
      done
    done
  done

lemma TT_fresh_induct[case_names Bound Var App Lam LetRec]:
  fixes x::"'a::var_terms_pre terms"
  assumes "|A| <o |UNIV::'a set|"
  and Var: "\<And>a. P (Var a)"
  and App: "\<And>e1 e2. \<lbrakk> P e1 ; P e2 \<rbrakk> \<Longrightarrow> P (App e1 e2)"
  and Lam: "\<And>x \<tau> e. \<lbrakk> x \<notin> A ; P e \<rbrakk> \<Longrightarrow> P (Lam x \<tau> e)"
  and LetRec: "\<And>xs e. \<lbrakk> keys_dallist xs \<inter> A = {} ; pred_dallist (\<lambda>(_, e). P e) xs ; P e \<rbrakk> \<Longrightarrow> P (LetRec xs e)"
shows "P x"
  apply (rule spec[OF TT_fresh_induct_param[of "\<lambda>(x::unit). A" "\<lambda>x _. P x" x]])
      apply (rule allI)
      apply (rule assms(1))
     apply (rule Var)
    apply (rule App)
     apply (erule allE)
     apply assumption
    apply (erule allE)+
    apply assumption
   apply (rule Lam)
    apply assumption
   apply (erule allE)
   apply assumption
  apply (rule LetRec)
    apply assumption
   apply (rule dallist.pred_mono_strong)
    apply assumption
   apply (unfold case_prod_beta)
   apply (erule allE)+
   apply assumption
  apply (erule allE)
  apply assumption
  done

lemmas TT_induct = TT_fresh_induct[OF emp_bound, case_names Var App Lam LetRec]

partial_function (option) llookup :: "'k \<Rightarrow> ('k \<times> 'v) llist \<Rightarrow> 'v option" where
  "llookup k xs = (case xs of LNil \<Rightarrow> None | LCons (k', v) ys \<Rightarrow> if k = k' then Some v else llookup k ys)"
print_theorems

lemma llookup_LNil[simp]: "llookup k LNil = None"
  by (subst llookup.simps) auto
lemma llookup_LCons[simp]: "llookup k (LCons (k', v) xs) = (if k = k' then Some v else llookup k xs)"
  by (subst llookup.simps) auto

lift_definition dallookup :: "'k \<Rightarrow> ('k, 'v) dallist \<Rightarrow> 'v option" is "llookup" .

lift_definition DALNil :: "('k, 'v) dallist" is "LNil" by simp
lift_definition DALCons :: "'k \<Rightarrow> 'v \<Rightarrow> ('k, 'v) dallist \<Rightarrow> ('k, 'v) dallist" is
  "\<lambda>x v xs. if x \<in> fst ` lset xs then xs else LCons (x, v) xs"
  by (auto simp: llist.set_map intro: ldistinct.intros)

lemma notin_DALNil[simp]: "k \<notin> keys_dallist DALNil"
  by transfer auto

lemma dallookup_DALNil[simp]: "dallookup k DALNil = None"
  by transfer auto
lemma dallookup_DALCons[simp]: "k' \<notin> keys_dallist xs \<Longrightarrow> dallookup k (DALCons k' v xs) = (if k = k' then Some v else dallookup k xs)"
  by (transfer fixing: k k' v) auto

lemma llookup_SomeI': "kv \<in> lset xs \<Longrightarrow> ldistinct (lmap fst xs) \<Longrightarrow> llookup (fst kv) xs = Some (snd kv)"
  apply (induct rule: llist.set_induct)
   apply auto
   apply (metis fst_conv image_eqI ldistinct.cases llist.distinct(1) llist.sel(1) llist.sel(3) llist.set_map)
  apply (metis ldistinct.cases llist.distinct(1) llist.sel(3))
  done

lemma llookup_SomeI: "(k, v) \<in> lset xs \<Longrightarrow> ldistinct (lmap fst xs) \<Longrightarrow> llookup k xs = Some v"
  by (rule llookup_SomeI'[of "(k, v)", unfolded fst_conv snd_conv])

lemma llookup_NoneI: "k \<notin> fst ` lset xs \<Longrightarrow> ldistinct (lmap fst xs) \<Longrightarrow> llookup k xs = None"
  apply (induct arbitrary: xs rule: llookup.fixp_induct)
    apply (auto elim: ldistinct.cases intro!: ccpo.admissibleI split: llist.splits)
  apply (smt (verit) chain_fun flat_lub_in_chain fun_lub_def mem_Collect_eq option.discI)
  done

lemma llookup_SomeD: "llookup k xs = Some v \<Longrightarrow> (k, v) \<in> lset xs"
  apply (rule llookup.raw_induct[of "\<lambda>k xs v. (k, v) \<in> lset xs", rotated])
   apply assumption
  apply (auto split: llist.splits)
  apply metis
  by (metis option.inject)

lemma llookup_NoneD: "llookup k xs = None \<Longrightarrow> ldistinct (lmap fst xs) \<Longrightarrow> k \<notin> fst ` lset xs"
  apply (erule contrapos_pp)
  apply (unfold not_not)
  apply (erule imageE)
  apply hypsubst
  apply (drule llookup_SomeI')
   apply assumption
  apply (rule iffD2[OF arg_cong[of _ _ Not]])
   apply (rule arg_cong2[OF _ refl, of _ _ "(=)"])
   apply assumption
  apply (rule option.distinct)
  done

lemma inj_is_inj_on: "inj f \<Longrightarrow> inj_on f A"
  by (simp add: inj_def inj_onI)

lemma llookup_lmap_SomeD:
  fixes f::"'a \<Rightarrow> 'a" and xs::"('a \<times> 'v) llist"
  assumes "bij f"
  shows "llookup (f k) xs = Some v \<Longrightarrow> llookup k (lmap (map_prod (inv f) id) xs) = Some v"
  apply (rule llookup.raw_induct[of "\<lambda>k xs v. llookup (inv f k) (lmap (map_prod (inv f) id) xs) = Some v" "f k" xs v, unfolded inv_simp1[OF assms]])
  subgoal for g k2 xs2 v2
    apply (cases xs2)
    by (auto simp: assms)
  apply assumption
  done

lemma dallookup_map_SomeD: "bij f \<Longrightarrow> dallookup (f k) xs = Some v \<Longrightarrow> dallookup k (map_dallist (inv f) id xs) = Some v"
  apply transfer
  apply (subst if_P)
   apply (rule inj_is_inj_on)
   apply (rule bij_is_inj)
   apply (rule bij_imp_bij_inv)
   apply assumption
  apply (rule llookup_lmap_SomeD)
   apply assumption+
  done

lemma dallookup_SomeD: "dallookup k xs = Some v \<Longrightarrow> (k, v) \<in> lset (Rep_dallist xs)"
  by transfer (auto intro: llookup_SomeD)

lemma dallookup_SomeI: "(k, v) \<in> lset (Rep_dallist xs) \<Longrightarrow> dallookup k xs = Some v"
  by transfer (auto intro: llookup_SomeI)

lemma dallookup_SomeI': "k \<in> keys_dallist xs \<Longrightarrow> \<exists>v. dallookup k xs = Some v"
  by (transfer fixing: k) (auto intro: llookup_SomeI')

lemma dallookup_NoneI: "k \<notin> keys_dallist xs \<Longrightarrow> dallookup k xs = None"
  by (transfer fixing: k) (auto intro: llookup_NoneI)

lemma dallookup_NoneD: "dallookup k xs = None \<Longrightarrow> k \<notin> keys_dallist xs"
  by transfer (auto dest: llookup_NoneD)

lemma lset_DALNil[simp]: "lset (Rep_dallist DALNil) = {}"
  unfolding DALNil_def by (subst Abs_dallist_inverse) auto

primcorec linterleave where
  "linterleave xs ys = (case xs of DALList.LNil \<Rightarrow> ys | DALList.LCons x xs \<Rightarrow> DALList.LCons x (linterleave ys xs))"

lemma in_set_linterleaveD: "x \<in> lset (linterleave xs ys) \<Longrightarrow> x \<in> lset xs \<or> x \<in> lset ys"
proof (induct "linterleave xs ys" arbitrary: xs ys rule: llist.set_induct)
  case (LCons1 z1 z2)
  then show ?case
    by (subst (asm) linterleave.code) (auto split: llist.splits)
next
  case (LCons2 z1 z2 zs)
  then show ?case
    by (subst (asm) linterleave.code) (auto split: llist.splits)
qed

lemma ldistinct_linterleave: "ldistinct (lmap fst xs) \<Longrightarrow> ldistinct (lmap fst ys) \<Longrightarrow> fst ` lset xs \<inter> fst ` lset ys = {} \<Longrightarrow> ldistinct (lmap fst (linterleave xs ys))"
  apply (coinduction arbitrary: xs ys)
  apply (subst disj_commute)
  apply (rule disjCI)
  subgoal for xs ys
    apply (cases xs)
       apply auto
     apply (metis ldistinct.cases linterleave.code llist.simps(4))
    apply (subst linterleave.code)
    apply (auto simp: llist.set_map dest!: in_set_linterleaveD)
    apply (metis fst_conv image_eqI ldistinct.cases llist.distinct(1) llist.sel(1) llist.sel(3) llist.set_map)
    apply (metis inf_commute ldistinct.cases llist.distinct(1) llist.sel(3))
    done
  done

lemma lmap_linterleave: "lmap f (linterleave xs ys) = linterleave (lmap f xs) (lmap f ys)"
  apply (coinduction arbitrary: xs ys)
  subgoal for xs ys
    apply (cases xs)
     apply (auto simp: llist.map_sel linterleave.code)
    by (metis llist.simps(12) llist.simps(4))
  done

lift_definition dainterleave :: "('k, 'v) dallist \<Rightarrow> ('k, 'v) dallist \<Rightarrow> ('k, 'v) dallist" is "\<lambda>xs ys. if fst ` lset xs \<inter> fst ` lset ys = {} then linterleave xs ys else DALList.LNil"
  by (auto simp: ldistinct_linterleave)

lemma dainterleave_DALNil1[simp]: "dainterleave DALNil xs = xs"
  by transfer (auto simp: linterleave.code)
lemma linterleave_LNil2[simp]: "linterleave xs LNil = xs"
  by (cases xs) (auto simp: linterleave.code)
lemma dainterleave_DALNil2[simp]: "dainterleave xs DALNil = xs"
  apply transfer
  subgoal for ys
    apply (cases ys)
     apply (auto simp: linterleave.code)
    done
  done
lemma dainterleave_DALCons[simp]: "\<lbrakk> k \<notin> keys_dallist xs ; keys_dallist (DALCons k v xs) \<inter> keys_dallist ys = {} \<rbrakk> \<Longrightarrow> dainterleave (DALCons k v xs) ys = DALCons k v (dainterleave ys xs)"
  apply transfer
  apply (subst if_not_P, assumption)+
  apply (subst (asm) if_not_P, assumption)+
  apply (unfold llist.set image_insert fst_conv insert_disjoint(1))
  apply (subst if_P, assumption)
  apply (erule conjE)
  apply (subst if_P, rule trans[OF Int_commute], assumption)+
  apply (subst if_not_P)
   apply (rotate_tac)
   apply (drule conjI)
    apply rotate_tac
    apply assumption
   apply (rotate_tac -1)
   apply (unfold de_Morgan_disj[symmetric])
   apply (erule contrapos_nn)
   apply (rule iffD2[OF disj_commute])
   apply (erule imageE)
   apply hypsubst
   apply (drule in_set_linterleaveD)
   apply (erule disjE)
    apply (rule disjI1)
    apply (rule imageI)
    apply assumption
   apply (rule disjI2)
   apply (rule imageI)
   apply assumption
  by (auto simp: linterleave.code)

lemma lset_DALCons[simp]: "x \<notin> keys_dallist xs \<Longrightarrow> lset (Rep_dallist (DALCons x v xs)) = insert (x, v) (lset (Rep_dallist xs))"
  apply transfer
  apply (subst if_not_P)
   apply assumption
  by simp

lemma lset_linterleaveD:
  "x \<in> lset zs \<Longrightarrow> zs = linterleave xs ys \<Longrightarrow> x \<in> lset xs \<union> lset ys"
  by (induct zs arbitrary: xs ys rule: llist.set_induct)
    (subst (asm) linterleave.code; auto split: llist.splits)+

lemma lset_linterleaveI1: "x \<in> lset xs \<Longrightarrow> x \<in> lset (linterleave xs ys)"
  apply (induct xs arbitrary: ys rule: llist.set_induct)
  apply (subst linterleave.code; auto split: llist.splits)
  apply (subst linterleave.code; subst linterleave.code; auto split: llist.splits)
  done

lemma lset_linterleaveI2: "x \<in> lset ys \<Longrightarrow> x \<in> lset (linterleave xs ys)"
  apply (induct ys arbitrary: xs rule: llist.set_induct)
  apply (subst linterleave.code; subst linterleave.code; auto split: llist.splits)
  apply (subst linterleave.code; subst linterleave.code; auto split: llist.splits)
  done

lemma lset_linterleave: "lset (linterleave xs ys) = lset xs \<union> lset ys"
  by (auto intro: lset_linterleaveI1 lset_linterleaveI2 dest: lset_linterleaveD)

lemma lset_dainterleave[simp]: "keys_dallist xs \<inter> keys_dallist ys = {} \<Longrightarrow> lset (Rep_dallist (dainterleave xs ys)) = lset (Rep_dallist xs) \<union> lset (Rep_dallist ys)"
  by transfer (auto simp: lset_linterleave)

lemma in_dainterleave1: "\<lbrakk> x \<in> lset (Rep_dallist xs) ; keys_dallist xs \<inter> keys_dallist ys = {} \<rbrakk> \<Longrightarrow> x \<in> lset (Rep_dallist (dainterleave xs ys))"
  by transfer (auto intro: lset_linterleaveI1)
lemma in_dainterleave2: "\<lbrakk> x \<in> lset (Rep_dallist ys) ; keys_dallist xs \<inter> keys_dallist ys = {} \<rbrakk> \<Longrightarrow> x \<in> lset (Rep_dallist (dainterleave xs ys))"
  by transfer (auto intro: lset_linterleaveI2)

lemma dallookup_dainterleave1: "\<lbrakk> dallookup k xs = Some v ; keys_dallist xs \<inter> keys_dallist ys = {} \<rbrakk> \<Longrightarrow> dallookup k (dainterleave xs ys) = Some v"
  apply (drule dallookup_SomeD)
  apply (rule dallookup_SomeI)
  apply (rule in_dainterleave1)
   apply assumption+
  done

lemma llookup_lmapD: "llookup k xs = Some a \<Longrightarrow> ldistinct (lmap fst xs) \<Longrightarrow> llookup k (lmap (map_prod id f) xs) = Some (f a)"
  apply (rule llookup_SomeI)
   apply (unfold llist.set_map)
   apply (unfold image_iff)
   apply (rule bexI)
    apply (rule sym)
    apply (rule trans)
     apply (rule map_prod_simp)
    apply (unfold id_def)[1]
    apply (rule refl)
   apply (drule llookup_SomeD)
   apply assumption
  apply (unfold llist.map_comp Product_Type.fst_comp_map_prod id_o)
  apply assumption
  done

lemma dallookup_dallmapD: "dallookup k xs = Some v \<Longrightarrow> dallookup k (map_dallist id f xs) = Some (f v)"
  by transfer (auto dest: llookup_lmapD)

lemma map_dallist_DALNil[simp]: "map_dallist f1 f2 DALNil = DALNil"
  by transfer auto

lemma map_dallist_DALCons: "\<lbrakk> |supp (f1::'a \<Rightarrow> 'a)| <o |UNIV::'a set| ; bij f1 ; x \<notin> keys_dallist xs \<rbrakk> \<Longrightarrow> map_dallist f1 f2 (DALCons x v xs) = DALCons (f1 x) (f2 v) (map_dallist f1 f2 xs)"
  apply transfer
  apply (subst if_not_P, assumption)+
  apply (subst if_P, rule inj_is_inj_on, rule bij_is_inj, assumption)+
  apply (unfold llist.set_map image_comp Product_Type.fst_comp_map_prod)
  apply (unfold image_comp[symmetric])
  apply (subst if_not_P)
   apply (rule not_imageI)
    apply assumption+
  apply (unfold llist.map map_prod_simp)
  apply (rule refl)
  done

lemma keys_dallist_DALNil[simp]: "keys_dallist DALNil = {}"
  by transfer auto
lemma keys_dallist_DALCons[simp]: "x \<notin> keys_dallist xs \<Longrightarrow> keys_dallist (DALCons x v xs) = insert x (keys_dallist xs)"
  by transfer auto

lemma pred_dallist_DALNil[simp]: "pred_dallist R DALNil"
  unfolding dallist.pred_rel by transfer auto
lemma pred_dallist_DALCons[simp]: "x \<notin> keys_dallist xs \<Longrightarrow> pred_dallist R (DALCons x v xs) \<longleftrightarrow> R v \<and> pred_dallist R xs"
  unfolding dallist.pred_rel by transfer (auto simp: eq_onp_def)

(* Definitions *)
inductive stuck_aux :: "'a::var_terms_pre terms \<Rightarrow> bool" where
  "stuck_aux (Var x)"
| "stuck_aux t \<Longrightarrow> stuck_aux (App t _)"

definition stuck :: "'a::var_terms_pre terms \<Rightarrow> bool" where
  "stuck t \<equiv> stuck_aux t \<or> (\<exists>x \<tau> e. t = Lam x \<tau> e)"

coinductive Step :: "'a::var_terms_pre terms \<Rightarrow> 'a terms \<Rightarrow> bool" ("_ \<^bold>\<longrightarrow> _" 25)  where
  ST_Beta: "App (Lam x \<tau> e) e2 \<^bold>\<longrightarrow> tvsubst (VVr(x:=e2)) e"
| ST_App: "e1 \<^bold>\<longrightarrow> e1' \<Longrightarrow> App e1 e2 \<^bold>\<longrightarrow> App e1' e2"
| ST_Let: "e \<^bold>\<longrightarrow> e' \<Longrightarrow> LetRec xs e \<^bold>\<longrightarrow> LetRec xs e'"
| ST_DropLet: "\<lbrakk> stuck e ; keys_dallist xs \<inter> FFVars_terms e = {} \<rbrakk> \<Longrightarrow> LetRec xs e \<^bold>\<longrightarrow> e"
| ST_LetBeta: "\<lbrakk> stuck e ; keys_dallist xs \<inter> FFVars_terms e \<noteq> {} \<rbrakk> \<Longrightarrow> LetRec xs e \<^bold>\<longrightarrow> LetRec xs (tvsubst (\<lambda>k. case dallookup k xs of None \<Rightarrow> VVr k | Some v \<Rightarrow> snd v) e)"
print_theorems

no_notation Set.member  ("(_/ : _)" [51, 51] 50)
inductive Ty :: "('a::var_terms_pre, \<tau>) dallist \<Rightarrow> 'a terms \<Rightarrow> \<tau> \<Rightarrow> bool" ("_ \<turnstile> _ : _" [55,55,55] 60) where
  Ty_Var: "dallookup x \<Gamma> = Some \<tau> \<Longrightarrow> \<Gamma> \<turnstile> Var x : \<tau>"
| Ty_App: "\<lbrakk> \<Gamma> \<turnstile> e1 : \<tau>1 \<rightarrow> \<tau>2 ; \<Gamma> \<turnstile> e2 : \<tau>1 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App e1 e2 : \<tau>2"
| Ty_Lam: "\<lbrakk> x \<notin> keys_dallist \<Gamma> ; DALCons x \<tau> \<Gamma> \<turnstile> e : \<tau>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam x \<tau> e : \<tau> \<rightarrow> \<tau>2"
| Ty_LetRec: "\<lbrakk> keys_dallist \<Gamma> \<inter> keys_dallist xs = {} ; \<Gamma>' = dainterleave \<Gamma> (map_dallist id fst xs) ;
    pred_dallist (\<lambda>(\<tau>', e). \<Gamma>' \<turnstile> e : \<tau>') xs ; \<Gamma>' \<turnstile> e : \<tau>
  \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> LetRec xs e : \<tau>"
monos dallist.pred_mono

definition cl :: "(('a::var_terms_pre, \<tau>) dallist \<Rightarrow> 'a terms \<Rightarrow> \<tau> \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a, \<tau>) dallist \<Rightarrow> 'a terms \<Rightarrow> \<tau> \<Rightarrow> 'b \<Rightarrow> bool" where
  "cl P \<Gamma> e \<tau> \<rho> \<equiv> (\<forall>f. bij f \<and> |supp f| <o |UNIV::'a set| \<longrightarrow> P (map_dallist f id \<Gamma>) (vvsubst f e) \<tau> \<rho>)"

lemmas clI = allI[THEN iffD2[OF meta_eq_to_obj_eq[OF cl_def]], unfolded atomize_imp[symmetric]]

lemma clD:
  fixes e::"'a::var_terms_pre terms" and f::"'a \<Rightarrow> 'a"
assumes "cl P \<Gamma> e \<tau> \<rho>" and "bij f" "|supp f| <o |UNIV::'a set|"
shows "P (map_dallist f id \<Gamma>) (vvsubst f e) \<tau> \<rho>"
  apply (rule mp[OF spec[OF assms(1)[unfolded cl_def]]])
  apply (rule conjI)
   apply (rule assms)+
  done

lemma cl_ext: "cl P \<Gamma> e \<tau> \<rho> \<Longrightarrow> P \<Gamma> e \<tau> \<rho>"
  unfolding cl_def
  apply (erule allE)
  apply (erule impE)
   apply (rule conjI)
    apply (rule bij_id)
   apply (rule supp_id_bound)
  unfolding dallist.map_id terms.map_id
  apply assumption
  done

lemma cl_vvsubst:
  fixes e::"'a::var_terms_pre terms"
  assumes f: "bij f" "|supp f| <o |UNIV::'a set|" and cl: "cl P \<Gamma> e \<tau> \<rho>"
  shows "cl P (map_dallist f id \<Gamma>) (vvsubst f e) \<tau> \<rho>"
  unfolding cl_def
  apply (rule allI impI)+
  apply (erule conjE)
  unfolding dallist.map_comp[OF assms(1,2)] terms.map_comp[OF f(2)] id_o
  apply (rule clD[OF cl])
   apply (rule bij_comp)
    apply (rule f)
   apply assumption
  apply (rule supp_comp_bound)
    apply (rule f)
   apply assumption
  apply (rule cinfinite_imp_infinite[OF terms_pre.UNIV_cinfinite])
  done

lemma cl_cl: "cl (cl P) = cl P"
  unfolding cl_def
  apply (rule ext)+
  apply (rule iffI)
   apply (rule allI)
   apply (rule impI)
   apply (erule allE)
   apply (erule conjE)
   apply (erule impE)
    apply (rule conjI)
     apply assumption+
   apply (erule allE)
   apply (erule impE)
    apply (rule conjI)
     apply (rule bij_id)
    apply (rule supp_id_bound)
  unfolding dallist.map_id terms.map_id
   apply assumption
  apply (rule allI impI)+
  apply (erule allE conjE)+
  apply (erule impE)
   defer
  unfolding dallist.map_comp id_o terms.map_comp
   apply assumption
  apply (rule conjI)
   apply (rule bij_comp)
    apply assumption+
  apply (rule supp_comp_bound)
    apply assumption+
  apply (rule cinfinite_imp_infinite[OF terms_pre.UNIV_cinfinite])
  done

lemma dallookup_eqvt: "bij f \<Longrightarrow> dallookup k xs = Some v \<Longrightarrow> dallookup (f k) (map_dallist f id xs) = Some v"
  apply transfer
  apply (subst if_P)
   apply (rule inj_is_inj_on)
  apply (rule bij_is_inj)
   apply assumption
  apply (rule llookup_SomeI)
   apply (unfold llist.set_map image_iff)
   apply (rule bexI)
    apply (rule sym)
  apply (rule trans)
     apply (rule map_prod_simp)
    apply (unfold id_def)[1]
    apply (rule refl)
   apply (erule llookup_SomeD)
  apply (unfold llist.map_comp Product_Type.fst_comp_map_prod)
  apply (unfold llist.map_comp[symmetric])
  apply (erule ldistinct_lmap)
  apply (rule inj_is_inj_on)
  apply (rule bij_is_inj)
  apply assumption
  done

lemma dainterleave_eqvt: "bij f \<Longrightarrow> keys_dallist xs \<inter> keys_dallist ys = {} \<Longrightarrow> map_dallist f id (dainterleave xs ys) = dainterleave (map_dallist f id xs) (map_dallist f id ys)"
  apply transfer
  apply (subst if_P, assumption)+
  apply (subst if_P, rule inj_is_inj_on, rule bij_is_inj, assumption)+
  apply (subst if_P)
   apply (unfold llist.set_map image_comp Product_Type.fst_comp_map_prod)
   apply (unfold image_comp[symmetric])
   apply (rule trans[OF image_Int[symmetric]])
    apply (rule bij_is_inj)
  apply assumption
   apply (rule iffD2[OF image_is_empty])
   apply assumption
  apply (rule lmap_linterleave)
  done

lemma Ty_eqvt:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|" "\<Gamma> \<turnstile> e : \<tau>"
  shows "map_dallist f id \<Gamma> \<turnstile> vvsubst f e : \<tau>"
  apply (rule Ty.induct[OF assms(3)])
     apply (unfold terms_vvsubst_rrename[OF assms(1,2)] rrename_simps[OF assms(1,2)])
     apply (rule Ty_Var)
     apply (rule dallookup_eqvt)
      apply (rule assms)
     apply assumption
    apply (rule Ty_App)
     apply assumption+
   apply (rule Ty_Lam)
    apply (unfold dallist.set_map[OF assms(1,2)])
    apply (rule not_imageI)
     apply (rule assms)
    apply assumption
   apply (subst (asm) map_dallist_DALCons)
      apply (rule assms)+
    apply assumption
   apply (unfold id_def)[1]
   apply assumption
  apply (rule Ty_LetRec)
     apply (unfold dallist.set_map[OF assms(1,2)])
     apply (rule trans[OF image_Int[symmetric]])
      apply (rule bij_is_inj)
      apply (rule assms)
     apply (rule iffD2[OF image_is_empty])
     apply assumption
    apply (unfold dallist.map_comp[OF assms(1,2) bij_id supp_id_bound] id_o_commute)
    apply (unfold Product_Type.fst_comp_map_prod)
    apply (unfold dallist.map_comp[OF bij_id supp_id_bound assms(1,2), symmetric])
    apply (rule trans[rotated])
     apply (rule dainterleave_eqvt)
      apply (rule assms)
     apply (unfold dallist.set_map[OF bij_id supp_id_bound] image_id)
     apply assumption
    apply (rule arg_cong[of _ _ "map_dallist f id"])
    apply assumption
   apply (rule iffD2[OF dallist.pred_map])
     apply (rule assms)+
   apply (erule dallist.pred_mono_strong)
   apply (unfold case_prod_beta comp_def snd_map_prod fst_map_prod id_def)
   apply (erule conjE)
   apply assumption+
  done

lemma image_not_in_imsupp: "x \<notin> imsupp f \<Longrightarrow> x \<in> f ` A \<longleftrightarrow> x \<in> A"
  unfolding imsupp_def supp_def by force

lemma ex_avoiding_bij:
  fixes f :: "'a \<Rightarrow> 'a" and I D A :: "'a set"
  assumes  "|supp f| <o |UNIV :: 'a set|" "bij f" "infinite (UNIV :: 'a set)"
    "|I| <o |UNIV :: 'a set|" "id_on I f"
    "|D| <o |UNIV :: 'a set|" "D \<inter> A = {}" "|A| <o |UNIV :: 'a set|"
  shows "\<exists>(g::'a \<Rightarrow> 'a). bij g \<and> |supp g| <o |UNIV::'a set| \<and> imsupp g \<inter> A = {} \<and>
    (\<forall>a. a \<in> (imsupp f - A) \<union> D \<and> f a \<notin> A \<longrightarrow> g a = f a) \<and> id_on I g"
  apply (rule exI[of _ "avoiding_bij f I D A"])
  apply (rule conjI avoiding_bij assms)+
  done

lemma single_bound: "|{a}| <o |UNIV::'a::var_terms_pre set|"
  by (rule finite_ordLess_infinite2[OF finite_singleton cinfinite_imp_infinite[OF terms_pre.UNIV_cinfinite]])

lemma Ty_strong_induct[consumes 1, case_names Bound Var App Lam LetRec]:
  fixes K::"'b \<Rightarrow> 'a::var_terms_pre set" and e::"'a terms"
  assumes x: "\<Gamma> \<turnstile> e : \<tau>" and bound: "\<forall>\<rho>. |K \<rho>| <o |UNIV::'a set|"
  and Var: "\<And>x \<Gamma> \<tau> \<rho>. dallookup x \<Gamma> = Some \<tau> \<Longrightarrow> P \<Gamma> (Var x) \<tau> \<rho>"
  and App: "\<And>\<Gamma> e1 \<tau>1 \<tau>2 e2 \<rho>. \<lbrakk> \<Gamma> \<turnstile> e1 : \<tau>1 \<rightarrow> \<tau>2 ; \<forall>\<rho>. P \<Gamma> e1 (\<tau>1 \<rightarrow> \<tau>2) \<rho> ; \<Gamma> \<turnstile> e2 : \<tau>1 ; \<forall>\<rho>. P \<Gamma> e2 \<tau>1 \<rho> \<rbrakk> \<Longrightarrow> P \<Gamma> (App e1 e2) \<tau>2 \<rho>"
  and Lam: "\<And>x \<Gamma> \<tau> e \<tau>2 \<rho>. \<lbrakk> x \<notin> K \<rho> ; x \<notin> keys_dallist \<Gamma> ; DALCons x \<tau> \<Gamma> \<turnstile> e : \<tau>2 ; \<forall>\<rho>. P (DALCons x \<tau> \<Gamma>) e \<tau>2 \<rho> \<rbrakk> \<Longrightarrow> P \<Gamma> (Lam x \<tau> e) (\<tau> \<rightarrow> \<tau>2) \<rho>"
  and LetRec: "\<And>\<Gamma> xs \<Gamma>' e \<tau> \<rho>. \<lbrakk> keys_dallist xs \<inter> K \<rho> = {} ;  keys_dallist \<Gamma> \<inter> keys_dallist xs = {} ; \<Gamma>' = dainterleave \<Gamma> (map_dallist id fst xs) ;
    pred_dallist (\<lambda>(\<tau>', e). \<Gamma>' \<turnstile> e : \<tau>' \<and> (\<forall>\<rho>. P \<Gamma>' e \<tau>' \<rho>)) xs ; \<Gamma>' \<turnstile> e : \<tau> ; \<forall>\<rho>. P \<Gamma>' e \<tau> \<rho> \<rbrakk> \<Longrightarrow> P \<Gamma> (LetRec xs e) \<tau> \<rho>"
shows "\<forall>\<rho>. P \<Gamma> e \<tau> \<rho>"
  apply (rule allI)
  apply (rule cl_ext[of P])
  apply (rule spec[OF Ty.induct[OF x, of "\<lambda>\<Gamma> e \<tau>. \<forall>\<rho>. cl P \<Gamma> e \<tau> \<rho>"]])
  (* Var *)
     apply (rule allI)
     apply (rule clI)
     apply (erule conjE)
     apply (subst vvsubst_simps)
      apply assumption
     apply (rule Var)
     apply (rule dallookup_eqvt)
      apply assumption
     apply assumption
    (* App *)
    apply (rule allI)
    apply (rule clI)
    apply (erule conjE)
    apply (subst vvsubst_simps)
     apply assumption
    apply (rule App)
       apply (rule Ty_eqvt)
         apply assumption+
      apply (rule allI)
      apply (erule allE)+
      apply (rule clD[of P])
        apply assumption+
     apply (rule Ty_eqvt)
       apply assumption+
    apply (rule allI)
    apply (erule allE)+
    apply (rule clD[of P])
      apply assumption+
  (* Lam *)
   apply (rule allI)
   apply (rule clI)
   apply (erule conjE)
  subgoal for \<rho> x \<Gamma> \<tau> e \<tau>2 \<rho>' f
    apply (rule exE[OF Lam_avoid[of "imsupp f \<union> K \<rho>' \<union> f ` keys_dallist \<Gamma>" x \<tau> e]])
     apply (rule terms.Un_bound)+
      apply (rule iffD2[OF imsupp_supp_bound])
       apply (rule cinfinite_imp_infinite[OF terms.UNIV_cinfinite])
      apply assumption
      apply (rule spec[OF bound])
     apply (rule ordLeq_ordLess_trans)
      apply (rule card_of_image)
     apply (rule ordLess_ordLeq_trans)
    apply (rule dallist.set_bd)
    using Card_order_iff_ordLeq_card_of llist.bd_Card_order ordLeq_transitive var_dallist_class.large apply blast
     apply (erule exE conjE)+
     apply (tactic \<open>resolve_tac @{context} [iffD2 OF [infer_instantiate' @{context} (replicate 8 NONE @ [SOME @{cterm P}]) (MRBNF_Util.mk_arg_cong (Proof_Context.init_global @{theory}) 4 @{term P})]] 1\<close>)
         apply (rule arg_cong2[OF refl, of _ _ vvsubst] | assumption | rule refl)+
     apply (subst vvsubst_simps)
       apply assumption
      apply (unfold Un_iff de_Morgan_disj)
      apply (erule conjE)+
    apply assumption
    apply (rule Lam)
       apply (erule conjE)+
       apply assumption
      apply (subst dallist.set_map)
        apply assumption+
      apply (erule conjE)+
      apply assumption
     apply (unfold Lam_inject)[1]
     apply (erule exE conjE)+
    subgoal for y e' g
     apply hypsubst
     apply (rule iffD2[OF arg_cong3[OF _ refl refl, of _ _ Ty]])
    apply (rule trans)
      apply (rule arg_cong3[OF _ refl refl, of _ _ DALCons])
       prefer 2
       apply (rule map_dallist_DALCons[of _ "g x" _ id, unfolded id_def, unfolded id_def[symmetric], symmetric])
          apply assumption+
        apply (rotate_tac 5)
        apply (erule contrapos_nn)
        apply (rule iffD2[OF image_not_in_imsupp])
         apply assumption+
       apply (rule sym)
       apply (rule not_in_imsupp_same)
       apply assumption
      apply (rule Ty_eqvt)
        apply assumption+
      apply (rule exE[OF ex_avoiding_bij])
              prefer 5
              apply assumption
             apply assumption
            apply assumption
           apply (rule cinfinite_imp_infinite[OF terms.UNIV_cinfinite])
          apply (rule ordLeq_ordLess_trans)
           apply (rule card_of_diff)
          apply (rule terms.set_bd_UNIV)
         apply (rule single_bound[of x])
        apply (rule iffD2[OF disjoint_single])
        apply assumption
      apply (rule ordLess_ordLeq_trans)
    apply (rule dallist.set_bd)
      using Card_order_iff_ordLeq_card_of llist.bd_Card_order ordLeq_transitive var_dallist_class.large apply blast
      apply (erule conjE)+
      apply (rule iffD2[OF arg_cong3[OF _ refl refl, of _ _ Ty]])
      apply (rule trans)
        apply (rule arg_cong3[OF _ refl, of _ _ _ _ DALCons])
         apply (erule allE)+
         apply (erule impE)
          prefer 2
          apply (rule sym)
          apply (rotate_tac -1)
          apply assumption
         apply (rule conjI)
          apply (rule UnI2)
          apply (rule singletonI)
         apply (rotate_tac 4)
         apply (erule contrapos_nn)
         apply (erule iffD2[OF image_not_in_imsupp])
         apply assumption
        prefer 2
        apply (rule map_dallist_DALCons[of _ x _ id, unfolded id_def, unfolded id_def[symmetric], symmetric])
          apply assumption+
       apply (rule sym)
       apply (rule trans)
        apply (rule dallist.map_cong[rotated -3])
              apply (rule refl)
      apply (drule trans[OF Int_commute])
             apply (drule iffD1[OF disjoint_iff])
      apply (rotate_tac -1)
             apply (erule allE)
             apply (erule impE)
              apply assumption
             apply (erule not_in_imsupp_same)
            apply (rule refl)
           apply assumption+
         apply (unfold id_def[symmetric])
         apply (rule bij_id supp_id_bound)+
       apply (unfold dallist.map_id)
       apply (rule refl)
      apply (rule iffD2[OF arg_cong3[OF refl _ refl, of _ _ Ty]])
       apply (rule terms.map_cong[rotated -2])
          apply (rule refl)
         apply (rule case_split[of "_ \<in> _", rotated])
          apply (drule id_onD)
           apply (rule DiffI)
            apply assumption
           apply assumption
          apply (rule trans)
           apply assumption
          apply (rule sym)
          apply (drule id_onD)
           apply (rule DiffI)
            apply assumption
           apply assumption
          apply (rotate_tac -1)
          apply assumption
         apply (rotate_tac -4)
         apply (erule allE)
         apply (erule impE)
          prefer 2
          apply (rule sym)
          apply assumption
         apply (rule conjI)
          apply (rule UnI2)
          apply assumption
         apply (drule singletonD)
         apply hypsubst
         apply (rotate_tac 7)
         apply (erule contrapos_nn)
         apply (erule iffD2[OF image_not_in_imsupp])
         apply assumption+
      apply (rule Ty_eqvt)
        apply assumption+
      done
    apply (rule allI)
    apply (unfold Lam_inject)
    apply (erule exE conjE)+
    apply hypsubst

    apply (rule exE[OF ex_avoiding_bij])
              prefer 5
              apply assumption
             apply assumption
            apply assumption
           apply (rule cinfinite_imp_infinite[OF terms.UNIV_cinfinite])
          apply (rule ordLeq_ordLess_trans)
           apply (rule card_of_diff)
          apply (rule terms.set_bd_UNIV)
         apply (rule single_bound[of x])
        apply (rule iffD2[OF disjoint_single])
        apply assumption
      apply (rule ordLess_ordLeq_trans)
    apply (rule dallist.set_bd)
      using Card_order_iff_ordLeq_card_of llist.bd_Card_order ordLeq_transitive var_dallist_class.large apply blast
      apply (erule conjE)+
    apply (subst terms.map_comp)
        apply assumption+

      apply (tactic \<open>resolve_tac @{context} [iffD2 OF [infer_instantiate' @{context} (replicate 8 NONE @ [SOME @{cterm P}]) (MRBNF_Util.mk_arg_cong (Proof_Context.init_global @{theory}) 4 @{term P})]] 1\<close>)
      apply (rule trans)
          apply (rule arg_cong3[OF _ refl _, of _ _ _ _ DALCons])
           apply (rule trans)
            apply (rule sym)
            apply (erule not_in_imsupp_same[of _ f])
           apply (rule arg_cong[of _ _ f])
           apply (rule sym)
           apply (rotate_tac -2)
           apply (erule allE)
           apply (erule impE)
            prefer 2
            apply assumption
           apply (rule conjI)
            apply (rule UnI2)
            apply (rule singletonI)
           apply (rotate_tac 6)
           apply (erule contrapos_nn)
           apply (erule iffD2[OF image_not_in_imsupp])
           apply assumption
          apply (rule dallist.map_cong[rotated -3])
                apply (rule refl)
               apply (rule arg_cong[of _ _ f])
               apply (rule sym)
               apply (drule trans[OF Int_commute])
               apply (drule iffD1[OF disjoint_iff])
               apply (rotate_tac -1)
               apply (erule allE)
               apply (erule impE)
                apply (rotate_tac -1)
                apply assumption
               apply (erule not_in_imsupp_same)
              apply (rule refl)
             apply assumption+
           apply (unfold comp_def[symmetric])
            apply (rule bij_comp supp_comp_bound cinfinite_imp_infinite[OF terms.UNIV_cinfinite] | assumption)+
          apply (unfold comp_def)[1]
          apply (rule map_dallist_DALCons[of _ x _ id, unfolded id_def, unfolded id_def[symmetric], symmetric])
            apply (unfold comp_def[symmetric])
            apply (rule bij_comp supp_comp_bound cinfinite_imp_infinite[OF terms.UNIV_cinfinite] | assumption)+
         apply (rule terms.map_cong[rotated -2])
            apply (rule refl)
           apply (rule trans[OF comp_apply])
           apply (rule arg_cong[of _ _ f])
           apply (rule case_split[of "_ \<in> _"])
            apply (rotate_tac -4)
            apply (erule allE)
            apply (erule impE)
             prefer 2
             apply (rule sym)
             apply assumption
            apply (rule conjI)
             apply (rule UnI2)
             apply assumption
            apply (drule singletonD)
            apply hypsubst
      apply (rotate_tac 7)
            apply (erule contrapos_nn)
           apply (erule iffD2[OF image_not_in_imsupp])
            apply assumption
           apply (rule trans)
            apply (drule id_onD)
             apply (rule DiffI)
              apply assumption
             apply assumption
            apply assumption
           apply (rule sym)
           apply (erule id_onD)
           apply (rule DiffI)
            apply assumption+
          apply (unfold comp_def[symmetric])
           apply (rule bij_comp supp_comp_bound cinfinite_imp_infinite[OF terms.UNIV_cinfinite] | assumption)+
        apply (rule refl)
      apply (rule refl)
    apply (erule allE)
    apply (drule clD[of P])
        prefer 3
      apply assumption
       apply (rule bij_comp supp_comp_bound cinfinite_imp_infinite[OF terms.UNIV_cinfinite] | assumption)+
      done
  (* LetRec *)
    apply (rule allI)
    apply (rule clI)
    apply (erule conjE)
    subgoal for \<rho> \<Gamma> xs \<Gamma>' e \<tau> \<rho>' f
      apply (rule exE[OF LetRec_avoid[of "imsupp f \<union> K \<rho>' \<union> keys_dallist \<Gamma> \<union> f ` keys_dallist \<Gamma>" xs e]])
       prefer 2
       apply (erule exE conjE)+
     apply (tactic \<open>resolve_tac @{context} [iffD2 OF [infer_instantiate' @{context} (replicate 8 NONE @ [SOME @{cterm P}]) (MRBNF_Util.mk_arg_cong (Proof_Context.init_global @{theory}) 4 @{term P})]] 1\<close>)
           apply (rule refl)
          apply (rule arg_cong2[OF refl, of _ _ vvsubst])
          apply assumption
         apply (rule refl)
        apply (rule refl)
       apply (subst vvsubst_simps)
         apply assumption
        apply (unfold Int_Un_distrib Un_empty)[1]
        apply (erule conjE)+
        apply assumption

 apply (drule iffD1[OF LetRec_inject])
       apply (erule exE conjE)+
       apply hypsubst
       apply (rule exE[OF ex_avoiding_bij, rotated 4])
               apply assumption
              prefer 2
              apply (drule trans[OF Int_commute])
      apply (rotate_tac -1)
              apply assumption
      apply (rule ordLess_ordLeq_trans)
    apply (rule dallist.set_bd)
    using Card_order_iff_ordLeq_card_of llist.bd_Card_order ordLeq_transitive var_dallist_class.large apply blast
     apply (rule ordLess_ordLeq_trans)
    apply (rule dallist.set_bd)
    using Card_order_iff_ordLeq_card_of llist.bd_Card_order ordLeq_transitive var_dallist_class.large apply blast
    apply (erule conjE)+

       apply (rule LetRec)
            apply (subst dallist.set_map)
              apply (rule bij_id)
             apply (rule supp_id_bound)
            apply (unfold image_id)
            apply (unfold Int_Un_distrib Un_empty)[1]
            apply (erule conjE)+
            apply assumption
           apply (subst dallist.set_map)
             apply assumption+
           apply (subst dallist.set_map)
             apply (rule bij_id)
            apply (rule supp_id_bound)
           apply (unfold image_id Int_Un_distrib Un_empty)[1]
           apply (erule conjE)+
           apply (rule trans[OF Int_commute])
             apply assumption
            apply (rule refl)
         apply (subst dallist.map_comp, (assumption | rule bij_id supp_id_bound)+, unfold id_o o_id)+
         apply (unfold id_o o_id Product_Type.fst_comp_map_prod)
         apply (unfold comp_def prod.map_comp id_def)
         apply (unfold id_def[symmetric])
         apply (subst terms.map_comp)
      apply assumption+
         apply (rule iffD2[OF dallist.pred_map])
           apply (assumption | rule bij_id supp_id_bound)+
         apply (erule dallist.pred_mono_strong)
         apply (unfold case_prod_beta)
         apply (erule conjE)+
         apply (unfold comp_def fst_map_prod snd_map_prod id_def)[1]
         apply (unfold comp_def[symmetric] id_def[symmetric])
         apply (rule conjI)
          apply (rule iffD2[OF arg_cong3[OF _ _ refl, of _ _ _ _ Ty]])
           apply (rule trans)
            apply (rule arg_cong2[of _ _ _ _ dainterleave])
             apply (rule dallist.map_cong[rotated -3])
                   apply (rule refl)
                  apply (rule arg_cong[of _ _ f])
                    apply (rule sym)
                    apply (rotate_tac -7)
                    apply (drule trans[OF Int_commute])
                    apply (rotate_tac -1)
                    apply (drule iffD1[OF disjoint_iff])
                    apply (rotate_tac -1)
                    apply (erule allE)
                    apply (erule impE)
                     apply assumption
                    apply (erule not_in_imsupp_same)
                   apply (rule refl)
                  apply assumption+
                apply (unfold comp_def[symmetric])
                apply (rule bij_comp supp_comp_bound cinfinite_imp_infinite[OF terms.UNIV_cinfinite] | assumption)+
              apply (rule trans)
              apply (rule dallist.map_comp[OF bij_id supp_id_bound, of _ id, unfolded id_o o_id, symmetric])
                apply assumption+
              apply (rule dallist.map_cong[rotated -3])
                    apply (rule refl)
                   apply (rule trans)
                    apply (rule sym)
                    apply (rule not_in_imsupp_same)
                    apply (subst (asm) dallist.set_map)
                 apply assumption
                apply assumption
               apply (unfold Int_Un_distrib Un_empty)[1]
                    apply (erule conjE)+
                    apply (subst (asm) dallist.set_map)
                      apply (rule supp_id_bound bij_id)+
                    apply (unfold image_id)
                    apply (rotate_tac -2)
                    apply (drule iffD1[OF disjoint_iff])
                    apply (rotate_tac -1)
                    apply (erule allE)
                    apply (erule impE)
                     apply (rule imageI)
                     apply assumption
                    apply assumption
                   apply (rule arg_cong[of _ _ f])
                   apply (rotate_tac -6)
                   apply (erule allE)
                   apply (erule impE)
                    apply (rule conjI)
                     apply (rule UnI2)
                     apply (unfold dallist.set_map[OF bij_id supp_id_bound] image_id)
                     apply assumption
                    apply (subst (asm) dallist.set_map)
                 apply assumption
                apply assumption
               apply (unfold Int_Un_distrib Un_empty)[1]
                    apply (erule conjE)+
                    apply (rotate_tac -3)
                    apply (drule iffD1[OF disjoint_iff])
                    apply (rotate_tac -1)
                    apply (erule allE)
                    apply (erule impE)
                     apply (rule imageI)
                     apply assumption
                    apply assumption
                   apply (rule sym)
                   apply assumption
                  apply (rule refl)
                 apply assumption+
               apply (unfold comp_def[symmetric])
            apply (rule bij_comp supp_comp_bound cinfinite_imp_infinite[OF terms.UNIV_cinfinite] | assumption)+
             apply (rule dainterleave_eqvt[symmetric])
              apply (rule bij_comp supp_comp_bound cinfinite_imp_infinite[OF terms.UNIV_cinfinite] | assumption)+
             apply (subst dallist.set_map)
               apply (rule bij_id supp_id_bound)+
             apply (unfold image_id)
              apply assumption
             apply (rule terms.map_cong[rotated -2])
                apply (rule refl)
               apply (rule trans[OF comp_apply])
               apply (rule arg_cong[of _ _ f])
               apply (rule case_split[of "_ \<in> _"])
                apply (rotate_tac -7)
                apply (erule allE)
                apply (erule impE)
                 apply (rule conjI)
                  apply (rule UnI2)
                  apply assumption
                 apply (subst (asm) dallist.set_map)
                 apply assumption
                apply assumption
               apply (unfold Int_Un_distrib Un_empty)[1]
                 apply (erule conjE)+
                 apply (rotate_tac -3)
                    apply (drule iffD1[OF disjoint_iff])
                    apply (rotate_tac -1)
                    apply (erule allE)
                    apply (erule impE)
                     apply (rule imageI)
                     apply assumption
                 apply assumption
                apply (rule sym)
                apply assumption
               apply (rule trans)
                apply (erule id_onD)
                apply (rule DiffI)
                 apply (rule UnI1)
                 apply (rule UN_I)
                  apply (rule imageI)
                  apply assumption
                 apply assumption
                apply assumption
               apply (rule sym)
               apply (erule id_onD)
               apply (rule DiffI)
                apply (rule UnI1)
                apply (rule UN_I)
                 apply (rule imageI)
                 apply assumption
                apply assumption
               apply assumption
              apply (unfold comp_def[symmetric])
              apply (rule bij_comp supp_comp_bound cinfinite_imp_infinite[OF terms.UNIV_cinfinite] | assumption)+
            apply (rule Ty_eqvt)
              apply (rule bij_comp supp_comp_bound cinfinite_imp_infinite[OF terms.UNIV_cinfinite] | assumption)+

           apply (rule allI)
           apply (tactic \<open>resolve_tac @{context} [iffD2 OF [infer_instantiate' @{context} (replicate 8 NONE @ [SOME @{cterm P}]) (MRBNF_Util.mk_arg_cong (Proof_Context.init_global @{theory}) 4 @{term P})]] 1\<close>)
            (* copied *)
               apply (rule trans)
               apply (rule arg_cong2[of _ _ _ _ dainterleave])
                apply (rule dallist.map_cong[rotated -3])
                   apply (rule refl)
                  apply (rule arg_cong[of _ _ f])
                    apply (rule sym)
                    apply (rotate_tac -7)
                    apply (drule trans[OF Int_commute])
                    apply (rotate_tac -1)
                    apply (drule iffD1[OF disjoint_iff])
                    apply (rotate_tac -1)
                    apply (erule allE)
                    apply (erule impE)
                     apply assumption
                    apply (erule not_in_imsupp_same)
                   apply (rule refl)
                  apply assumption+
                apply (unfold comp_def[symmetric])
                apply (rule bij_comp supp_comp_bound cinfinite_imp_infinite[OF terms.UNIV_cinfinite] | assumption)+
              apply (rule trans)
              apply (rule dallist.map_comp[OF bij_id supp_id_bound, of _ id, unfolded id_o o_id, symmetric])
                 apply assumption+
               apply (rule dallist.map_cong[rotated -3])
                    apply (rule refl)
                   apply (rule trans)
                    apply (rule sym)
                    apply (rule not_in_imsupp_same)
                    apply (subst (asm) dallist.set_map)
                 apply assumption
                apply assumption
               apply (unfold Int_Un_distrib Un_empty)[1]
                    apply (erule conjE)+
                    apply (subst (asm) dallist.set_map)
                      apply (rule supp_id_bound bij_id)+
                    apply (unfold image_id)
                    apply (rotate_tac -2)
                    apply (drule iffD1[OF disjoint_iff])
                    apply (rotate_tac -1)
                    apply (erule allE)
                    apply (erule impE)
                     apply (rule imageI)
                     apply assumption
                    apply assumption
                   apply (rule arg_cong[of _ _ f])
                   apply (rotate_tac -6)
                   apply (erule allE)
                   apply (erule impE)
                    apply (rule conjI)
                     apply (rule UnI2)
                     apply (unfold dallist.set_map[OF bij_id supp_id_bound] image_id)
                     apply assumption
                    apply (subst (asm) dallist.set_map)
                 apply assumption
                apply assumption
               apply (unfold Int_Un_distrib Un_empty)[1]
                    apply (erule conjE)+
                    apply (rotate_tac -3)
                    apply (drule iffD1[OF disjoint_iff])
                    apply (rotate_tac -1)
                    apply (erule allE)
                    apply (erule impE)
                     apply (rule imageI)
                     apply assumption
                    apply assumption
                   apply (rule sym)
                   apply assumption
                  apply (rule refl)
                 apply assumption+
               apply (unfold comp_def[symmetric])
            apply (rule bij_comp supp_comp_bound cinfinite_imp_infinite[OF terms.UNIV_cinfinite] | assumption)+
             apply (rule dainterleave_eqvt[symmetric])
              apply (rule bij_comp supp_comp_bound cinfinite_imp_infinite[OF terms.UNIV_cinfinite] | assumption)+
             apply (subst dallist.set_map)
               apply (rule bij_id supp_id_bound)+
             apply (unfold image_id)
              apply assumption
             apply (rule terms.map_cong[rotated -2])
                apply (rule refl)
               apply (rule trans[OF comp_apply])
               apply (rule arg_cong[of _ _ f])
               apply (rule case_split[of "_ \<in> _"])
                apply (rotate_tac -7)
                apply (erule allE)
                apply (erule impE)
                 apply (rule conjI)
                  apply (rule UnI2)
                  apply assumption
                 apply (subst (asm) dallist.set_map)
                 apply assumption
                apply assumption
               apply (unfold Int_Un_distrib Un_empty)[1]
                 apply (erule conjE)+
                 apply (rotate_tac -3)
                    apply (drule iffD1[OF disjoint_iff])
                    apply (rotate_tac -1)
                    apply (erule allE)
                    apply (erule impE)
                     apply (rule imageI)
                     apply assumption
                 apply assumption
                apply (rule sym)
                apply assumption
               apply (rule trans)
                apply (erule id_onD)
                apply (rule DiffI)
                 apply (rule UnI1)
                 apply (rule UN_I)
                  apply (rule imageI)
                  apply assumption
                 apply assumption
                apply assumption
               apply (rule sym)
               apply (erule id_onD)
               apply (rule DiffI)
                apply (rule UnI1)
                apply (rule UN_I)
                 apply (rule imageI)
                 apply assumption
                apply assumption
               apply assumption
              apply (unfold comp_def[symmetric])
               apply (rule bij_comp supp_comp_bound cinfinite_imp_infinite[OF terms.UNIV_cinfinite] | assumption)+
(* end of copy *)
             apply (rule refl)
            apply (rule refl)
           apply (rotate_tac -1)
           apply (erule allE)
           apply (drule clD[of P])
             prefer 3
             apply assumption
            apply (rule bij_comp supp_comp_bound cinfinite_imp_infinite[OF terms.UNIV_cinfinite] | assumption)+

(* copied again *)
         apply (subst dallist.map_comp, (assumption | rule bij_id supp_id_bound)+, unfold id_o o_id)+
          apply (unfold id_o o_id Product_Type.fst_comp_map_prod)
         apply (unfold comp_def prod.map_comp id_def)
         apply (unfold id_def[symmetric])
         apply (subst terms.map_comp)
            apply assumption+
          apply (rule iffD2[OF arg_cong3[OF _ _ refl, of _ _ _ _ Ty]])
           apply (rule trans)
            apply (rule arg_cong2[of _ _ _ _ dainterleave])
             apply (rule dallist.map_cong[rotated -3])
                   apply (rule refl)
                  apply (rule arg_cong[of _ _ f])
                    apply (rule sym)
                    apply (rotate_tac -4)
                    apply (drule trans[OF Int_commute])
                    apply (rotate_tac -1)
                    apply (drule iffD1[OF disjoint_iff])
                    apply (rotate_tac -1)
                    apply (erule allE)
                    apply (erule impE)
                     apply assumption
                    apply (erule not_in_imsupp_same)
                   apply (rule refl)
                  apply assumption+
                apply (unfold comp_def[symmetric])
                apply (rule bij_comp supp_comp_bound cinfinite_imp_infinite[OF terms.UNIV_cinfinite] | assumption)+
              apply (rule trans)
              apply (rule dallist.map_comp[OF bij_id supp_id_bound, of _ id, unfolded id_o o_id, symmetric])
               apply assumption+
              apply (rule dallist.map_cong[rotated -3])
                    apply (rule refl)
                   apply (rule trans)
                    apply (rule sym)
                    apply (rule not_in_imsupp_same)
                    apply (subst (asm) dallist.set_map)
                 apply assumption
                apply assumption
               apply (unfold Int_Un_distrib Un_empty)[1]
                    apply (erule conjE)+
                    apply (subst (asm) dallist.set_map)
                      apply (rule supp_id_bound bij_id)+
                    apply (unfold image_id)
                    apply (rotate_tac -2)
                    apply (drule iffD1[OF disjoint_iff])
                    apply (rotate_tac -1)
                    apply (erule allE)
                    apply (erule impE)
                    apply (rule imageI)
                     apply assumption
                    apply assumption
                   apply (rule arg_cong[of _ _ f])
                   apply (rotate_tac -6)
                   apply (erule allE)
                   apply (erule impE)
                    apply (rule conjI)
                     apply (rule UnI2)
                     apply (unfold dallist.set_map[OF bij_id supp_id_bound] image_id)
                     apply assumption
                    apply (subst (asm) dallist.set_map)
                 apply assumption
                apply assumption
               apply (unfold Int_Un_distrib Un_empty)[1]
                    apply (erule conjE)+
                    apply (rotate_tac -3)
                    apply (drule iffD1[OF disjoint_iff])
                    apply (rotate_tac -1)
                    apply (erule allE)
                    apply (erule impE)
                     apply (rule imageI)
                     apply assumption
                    apply assumption
                   apply (rule sym)
                   apply assumption
                  apply (rule refl)
                 apply assumption+
               apply (unfold comp_def[symmetric])
            apply (rule bij_comp supp_comp_bound cinfinite_imp_infinite[OF terms.UNIV_cinfinite] | assumption)+
             apply (rule dainterleave_eqvt[symmetric])
              apply (rule bij_comp supp_comp_bound cinfinite_imp_infinite[OF terms.UNIV_cinfinite] | assumption)+
             apply (subst dallist.set_map)
               apply (rule bij_id supp_id_bound)+
             apply (unfold image_id)
              apply assumption
             apply (rule terms.map_cong[rotated -2])
                apply (rule refl)
               apply (rule trans[OF comp_apply])
               apply (rule arg_cong[of _ _ f])
               apply (rule case_split[of "_ \<in> _"])
                apply (rotate_tac -7)
                apply (erule allE)
                apply (erule impE)
                 apply (rule conjI)
                  apply (rule UnI2)
                  apply assumption
                 apply (subst (asm) dallist.set_map)
                 apply assumption
                apply assumption
               apply (unfold Int_Un_distrib Un_empty)[1]
                 apply (erule conjE)+
                 apply (rotate_tac -3)
                    apply (drule iffD1[OF disjoint_iff])
                    apply (rotate_tac -1)
                    apply (erule allE)
                    apply (erule impE)
                     apply (rule imageI)
                     apply assumption
                 apply assumption
                apply (rule sym)
                apply assumption
               apply (rule trans)
                apply (erule id_onD)
              apply (rule DiffI)
(* end of copy *)
               apply (rule UnI2)
               apply assumption+
             apply (rule sym)
             apply (erule id_onD)
             apply (rule DiffI)
              apply (rule UnI2)
              apply assumption+
            apply (unfold comp_def[symmetric])
            apply (rule bij_comp supp_comp_bound cinfinite_imp_infinite[OF terms.UNIV_cinfinite] | assumption)+
          apply (rule Ty_eqvt)
            apply (rule bij_comp supp_comp_bound cinfinite_imp_infinite[OF terms.UNIV_cinfinite] | assumption)+

         apply (rule allI)

apply (subst dallist.map_comp, (assumption | rule bij_id supp_id_bound)+, unfold id_o o_id)+
         apply (unfold id_o o_id Product_Type.fst_comp_map_prod)
         apply (unfold comp_def prod.map_comp id_def)
         apply (unfold id_def[symmetric])
         apply (subst terms.map_comp)
      apply assumption+
     apply (tactic \<open>resolve_tac @{context} [iffD2 OF [infer_instantiate' @{context} (replicate 8 NONE @ [SOME @{cterm P}]) (MRBNF_Util.mk_arg_cong (Proof_Context.init_global @{theory}) 4 @{term P})]] 1\<close>)
(* copied *)
 apply (rule trans)
               apply (rule arg_cong2[of _ _ _ _ dainterleave])
                apply (rule dallist.map_cong[rotated -3])
                   apply (rule refl)
                  apply (rule arg_cong[of _ _ f])
                    apply (rule sym)
                    apply (rotate_tac -7)
                    apply (drule trans[OF Int_commute])
                    apply (rotate_tac -1)
                    apply (drule iffD1[OF disjoint_iff])
                    apply (rotate_tac -1)
                    apply (erule allE)
                    apply (erule impE)
                     apply assumption
                    apply (erule not_in_imsupp_same)
                   apply (rule refl)
                  apply assumption+
                apply (unfold comp_def[symmetric])
                apply (rule bij_comp supp_comp_bound cinfinite_imp_infinite[OF terms.UNIV_cinfinite] | assumption)+
              apply (rule trans)
              apply (rule dallist.map_comp[OF bij_id supp_id_bound, of _ id, unfolded id_o o_id, symmetric])
                 apply assumption+
               apply (rule dallist.map_cong[rotated -3])
                    apply (rule refl)
                   apply (rule trans)
                    apply (rule sym)
                    apply (rule not_in_imsupp_same)
                    apply (subst (asm) dallist.set_map)
                 apply assumption
                apply assumption
               apply (unfold Int_Un_distrib Un_empty)[1]
                    apply (erule conjE)+
                    apply (subst (asm) dallist.set_map)
                      apply (rule supp_id_bound bij_id)+
                    apply (unfold image_id)
                    apply (rotate_tac -2)
                    apply (drule iffD1[OF disjoint_iff])
                    apply (rotate_tac -1)
                    apply (erule allE)
                    apply (erule impE)
                     apply (rule imageI)
                     apply assumption
                    apply assumption
                   apply (rule arg_cong[of _ _ f])
                   apply (rotate_tac -6)
                   apply (erule allE)
                   apply (erule impE)
                    apply (rule conjI)
                     apply (rule UnI2)
                     apply (unfold dallist.set_map[OF bij_id supp_id_bound] image_id)
                     apply assumption
                    apply (subst (asm) dallist.set_map)
                 apply assumption
                apply assumption
               apply (unfold Int_Un_distrib Un_empty)[1]
                    apply (erule conjE)+
                    apply (rotate_tac -3)
                    apply (drule iffD1[OF disjoint_iff])
                    apply (rotate_tac -1)
                    apply (erule allE)
                    apply (erule impE)
                     apply (rule imageI)
                     apply assumption
                    apply assumption
                   apply (rule sym)
                   apply assumption
                  apply (rule refl)
                 apply assumption+
               apply (unfold comp_def[symmetric])
            apply (rule bij_comp supp_comp_bound cinfinite_imp_infinite[OF terms.UNIV_cinfinite] | assumption)+
             apply (rule dainterleave_eqvt[symmetric])
              apply (rule bij_comp supp_comp_bound cinfinite_imp_infinite[OF terms.UNIV_cinfinite] | assumption)+
             apply (subst dallist.set_map)
               apply (rule bij_id supp_id_bound)+
             apply (unfold image_id)
              apply assumption
             apply (rule terms.map_cong[rotated -2])
                apply (rule refl)
               apply (rule trans[OF comp_apply])
               apply (rule arg_cong[of _ _ f])
               apply (rule case_split[of "_ \<in> _"])
                apply (rotate_tac -4)
                apply (erule allE)
                apply (erule impE)
                 apply (rule conjI)
                  apply (rule UnI2)
                  apply assumption
                 apply (subst (asm) dallist.set_map)
                 apply assumption
                apply assumption
               apply (unfold Int_Un_distrib Un_empty)[1]
                 apply (erule conjE)+
                 apply (rotate_tac -3)
                    apply (drule iffD1[OF disjoint_iff])
                    apply (rotate_tac -1)
                    apply (erule allE)
                    apply (erule impE)
                     apply (rule imageI)
                     apply assumption
                 apply assumption
                apply (rule sym)
                apply assumption
               apply (rule trans)
                apply (erule id_onD)
               apply (rule DiffI)
(* end of copy *)
                apply (rule UnI2)
                apply assumption+
              apply (rule sym)
              apply (erule id_onD)
              apply (rule DiffI)
               apply (rule UnI2)
               apply assumption+
             apply (unfold comp_def[symmetric])
             apply (rule bij_comp supp_comp_bound cinfinite_imp_infinite[OF terms.UNIV_cinfinite] | assumption)+

           apply (rule refl)
          apply (rule refl)
         apply (erule allE)
         apply (drule clD[of P])
           prefer 3
           apply assumption
            apply (rule bij_comp supp_comp_bound cinfinite_imp_infinite[OF terms.UNIV_cinfinite] | assumption)+

     apply (rule ordLeq_ordLess_trans)
      apply (rule card_of_diff)
     apply (rule terms.Un_bound)
      apply (rule terms.UNION_bound)
       apply (rule ordLeq_ordLess_trans)
        apply (rule card_of_image)
       apply (rule ordLess_ordLeq_trans)
        apply (rule dallist.set_bd)
    using Card_order_iff_ordLeq_card_of llist.bd_Card_order ordLeq_transitive var_dallist_class.large apply blast
      apply (rule terms.set_bd_UNIV)+

    apply (rule terms.Un_bound)+
       apply (rule iffD2[OF imsupp_supp_bound])
        apply (rule cinfinite_imp_infinite[OF terms.UNIV_cinfinite])
       apply assumption
      apply (rule spec[OF bound])
     apply (rule ordLess_ordLeq_trans)
      apply (rule dallist.set_bd)
    using Card_order_iff_ordLeq_card_of llist.bd_Card_order ordLeq_transitive var_dallist_class.large apply blast
    apply (rule ordLeq_ordLess_trans)
     apply (rule card_of_image)
    apply (rule ordLess_ordLeq_trans)
     apply (rule dallist.set_bd)
    using Card_order_iff_ordLeq_card_of llist.bd_Card_order ordLeq_transitive var_dallist_class.large apply blast
    done
  done

coinductive steps ("_ \<longrightarrow>* _" 25) where
  ST_refl: "x \<longrightarrow>* x"
| ST_trans: "\<lbrakk> Step e1 e2 ; e2 \<longrightarrow>* e3 \<rbrakk> \<Longrightarrow> e1 \<longrightarrow>* e3"

inductive_cases
  STE: "e \<^bold>\<longrightarrow> e2"
inductive_cases
  stuck_auxE: "stuck_aux e"
inductive_cases
  TyE: "\<Gamma> \<turnstile> e : \<tau>"
print_theorems

lemma no_step_imp_stuck: "\<nexists>e'. e \<^bold>\<longrightarrow> e' \<Longrightarrow> stuck e"
proof (induction e rule: TT_induct)
  case (Var a)
  then show ?case unfolding stuck_def using stuck_aux.intros by blast
next
  case (App e1 e2)
  then have "stuck e1" by (auto intro: Step.intros)
  moreover have "\<nexists>x \<tau> e. e1 = Lam x \<tau> e" using App(3) by (auto intro: Step.intros)
  ultimately have "stuck_aux e1" unfolding stuck_def by simp
  then show "stuck (App e1 e2)" unfolding stuck_def by (auto intro: stuck_aux.intros)
next
  case (Lam x \<tau> e)
  then show ?case unfolding stuck_def by blast
next
  case (LetRec xs e)
  then have 1: "stuck e" by (auto intro: Step.intros)
  then have "\<exists>a. LetRec xs e \<^bold>\<longrightarrow> a" by (cases "keys_dallist xs \<inter> FFVars_terms e = {}") (auto intro: Step.intros)
  then show ?case using \<open>\<nexists>a. LetRec xs e \<^bold>\<longrightarrow> a\<close> by blast
qed

theorem progress: "DALNil \<turnstile> e : \<tau> \<Longrightarrow> (\<exists>x \<tau>' e'. e = Lam x \<tau>' e') \<or> (\<exists>e'. e \<^bold>\<longrightarrow> e')"
proof (induction "DALNil :: ('a::var_terms_pre, \<tau>) dallist" e \<tau> rule: Ty.induct)
  case (Ty_Var x \<tau>)
  show ?case using Ty_Var by cases auto
next
  case (Ty_App e1 \<tau>1 \<tau>2 e2)
  then show ?case using Step.intros by blast
next
  case (Ty_Lam x \<tau> e \<tau>2)
  then show ?case by blast
next
  case (Ty_LetRec xs \<Gamma>' e \<tau>)
  then show ?case
  proof (cases "\<exists>e'. e \<^bold>\<longrightarrow> e'")
    case True
    then show ?thesis using ST_Let by blast
  next
    case False
    then have "stuck e" by (rule no_step_imp_stuck)
    then show ?thesis by (cases "keys_dallist xs \<inter> FFVars_terms e = {}") (auto intro: Step.intros)
  qed
qed

context begin
ML_file \<open>./Tools/binder_induction.ML\<close>
end

lemma rrename_tvsubst:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a" and g::"'a \<Rightarrow> 'a terms" and xs::"('a, 'v) dallist"
  assumes "bij f" "|supp f| <o |UNIV::'a set|" "|SSupp g| <o |UNIV::'a set|"
  shows "rrename_terms f (tvsubst g e) = tvsubst (rrename_terms f \<circ> g \<circ> inv f) (rrename_terms f e)"
proof (binder_induction e arbitrary: xs avoiding: "IImsupp g" rule: TT_fresh_induct_param)
  case Bound
  then show ?case
    unfolding IImsupp_def
    by (meson assms(3) terms.set_bd_UNIV type_copy_set_bd var_terms_pre_class.UN_bound var_terms_pre_class.Un_bound)
next
  case (Var a xs)
  show ?case
    apply (rule trans)
     apply (rule arg_cong[of _ _ "rrename_terms f"])
     apply (rule tvsubst_simps)
     apply (rule assms)
    apply (rule sym)
    apply (rule trans)
    apply (rule arg_cong[of _ _ "tvsubst _"])
     apply (rule rrename_simps)
      apply (rule assms)+
    apply (rule trans)
     apply (rule tvsubst_simps)
    apply (rule SSupp_comp_bound)
     apply (rule SSupp_comp_rename_bound)
        apply (rule assms supp_inv_bound)+
    apply (unfold comp_def)
    apply (subst inv_simp1)
     apply (rule assms)
    apply (rule refl)
    done
next
  case (App e1 e2 f)
  show ?case unfolding tvsubst_simps[OF assms(3)] rrename_simps[OF assms(1,2)]
    apply (rule sym)
    apply (rule trans)
     apply (rule tvsubst_simps)
     apply (rule SSupp_comp_bound)
      apply (rule SSupp_comp_rename_bound)
        apply (rule assms supp_inv_bound)+
    apply (rule iffD2[OF terms_inject_plain(2)])
    apply (rule conjI)
    apply (rule sym)
     apply (rule App)+
    apply (rule sym)
    apply (rule App)+
    done
next
  case (Lam x \<tau> e xs)
  show ?case
    apply (rule trans)
     apply (rule arg_cong[of _ _ "rrename_terms f"])
     apply (rule tvsubst_simps)
      apply (rule assms)
     apply (rule Lam)
    apply (rule trans)
     apply (rule rrename_simps)
      apply (rule assms)+
    apply (rule sym)
    apply (rule trans)
     apply (rule arg_cong[of _ _ "tvsubst _"])
     apply (rule rrename_simps)
      apply (rule assms)+
    apply (rule trans)
     apply (rule tvsubst_simps)
    apply (rule SSupp_comp_bound)
      apply (rule SSupp_comp_rename_bound)
         apply (rule assms supp_inv_bound)+
     apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<notin>)"]])
    apply (rule IImsupp_comp_image[OF assms(1,2), of "Abs_SSfun g", unfolded Abs_SSfun_inverse[unfolded mem_Collect_eq, OF assms(3)]])
     apply (rule not_imageI)
      apply (rule assms)
     apply (rule Lam)
    apply (rule arg_cong[of _ _ "Lam (f x) \<tau>"])
    apply (rule sym)
    apply (rule Lam)
    done
next
  case (LetRec xs e xs')
  show ?case
    apply (rule trans)
     apply (rule arg_cong[of _ _ "rrename_terms f"])
     apply (rule tvsubst_simps)
      apply (rule assms)
     apply (rule LetRec)
    apply (rule trans)
     apply (rule rrename_simps)
      apply (rule assms)+
    apply (subst dallist.map_comp)
        apply (rule bij_id supp_id_bound assms)+
    apply (unfold id_o o_id prod.map_comp trans[OF comp_apply[of "map_prod _ _" "map_prod _ _"] prod.map_comp, abs_def])
    apply (rule sym)
    apply (rule trans)
     apply (rule arg_cong[of _ _ "tvsubst _"])
     apply (rule rrename_simps)
      apply (rule assms)+
    apply (rule trans)
     apply (rule tvsubst_simps)
    apply (rule SSupp_comp_bound)
      apply (rule SSupp_comp_rename_bound)
         apply (rule assms supp_inv_bound)+
     apply (rule trans)
       apply (subst dallist.set_map)
    apply (rule assms)+
      apply (rule arg_cong2[OF refl, of _ _ "(\<inter>)"])
      apply (rule IImsupp_comp_image[OF assms(1,2), of "Abs_SSfun g", unfolded Abs_SSfun_inverse[unfolded mem_Collect_eq, OF assms(3)]])
     apply (rule trans)
      apply (rule image_Int[symmetric])
      apply (rule bij_is_inj)
      apply (rule assms)
     apply (unfold image_is_empty)
     apply (rule LetRec)
    apply (subst dallist.map_comp)
        apply (rule supp_id_bound bij_id assms)+
    apply (unfold id_o o_id prod.map_comp trans[OF comp_apply[of "map_prod _ _" "map_prod _ _"] prod.map_comp, abs_def])
    apply (rule arg_cong2[of _ _ _ _ LetRec])
     apply (rule dallist.map_cong)
           apply (rule assms refl)+
     apply (rule prod.map_cong)
       apply (rule refl)+
     apply (rule trans[OF comp_apply])
     apply (rule sym)
     apply (rule trans[OF comp_apply])
     apply (drule bspec[OF LetRec(2)[unfolded dallist.pred_set]])
     apply (unfold case_prod_beta snds.simps)
     apply hypsubst
     apply assumption
    apply (rule sym)
    apply (rule LetRec)
    done
qed

lemma SSupp_upd_bound:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a terms"
  shows "|SSupp (f (a:=t))| <o |UNIV::'a set| \<longleftrightarrow> |SSupp f| <o |UNIV::'a set|"
  unfolding SSupp_def
  apply (auto simp only: fun_upd_apply single_bound ordLeq_refl split: if_splits
      elim!: ordLeq_ordLess_trans[OF card_of_mono1 ordLess_ordLeq_trans[OF terms_pre.Un_bound], rotated]
      intro: card_of_mono1)
  done

corollary SSupp_upd_VVr_bound: "|SSupp (VVr(a:=(t::'a::var_terms_pre terms)))| <o |UNIV::'a set|"
  apply (rule iffD2[OF SSupp_upd_bound])
  apply (rule SSupp_VVr_bound)
  done

lemma VVr_comp:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "rrename_terms f \<circ> VVr(x := e2) \<circ> inv f = VVr(f x := rrename_terms f e2)"
  unfolding fun_upd_def comp_def
  apply (rule ext)
  subgoal for y
    apply (rule case_split[of "y = f x"])
     apply (subst if_P)
      apply (simp add: assms)
     apply (subst if_P)
      apply assumption
     apply (rule refl)
    apply (subst if_not_P)
    by (auto simp: assms Var_is_VVr[symmetric] rrename_simps)
  done

lemma stuck_aux_eqvt:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "stuck_aux e \<Longrightarrow> stuck_aux (rrename_terms f e)"
  by (induction e rule: stuck_aux.induct) (auto simp: rrename_simps[OF assms] intro: stuck_aux.intros)

lemma stuck_eqvt:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "stuck e \<Longrightarrow> stuck (rrename_terms f e)"
unfolding stuck_def proof (erule disjE, goal_cases)
  case 1
  then show ?case using stuck_aux_eqvt[OF assms] by simp
next
  case 2
  then show ?case using rrename_simps[OF assms] by blast
qed

lemma keys_dallist_bound: "|keys_dallist (xs::('a::var_terms_pre, 'v) dallist)| <o |UNIV::'a set|"
  apply (rule ordLess_ordLeq_trans)
   apply (rule dallist.set_bd)
  using Card_order_iff_ordLeq_card_of llist.bd_Card_order ordLeq_transitive var_dallist_class.large by blast

lemma vals_dallist_bound: "|vals_dallist (xs::('a::var_terms_pre, 'v) dallist)| <o |UNIV::'a set|"
  apply (rule ordLess_ordLeq_trans)
   apply (rule dallist.set_bd)
  using Card_order_iff_ordLeq_card_of llist.bd_Card_order ordLeq_transitive var_dallist_class.large by blast

lemma SSupp_bound: "|SSupp (\<lambda>k. case dallookup (k::'a::var_terms_pre) xs of None \<Rightarrow> VVr k | Some a \<Rightarrow> snd a)| <o |UNIV::'a set|" (is "|SSupp ?f| <o |?U|")
proof -
  have "SSupp ?f \<subseteq> keys_dallist xs" unfolding SSupp_def
    apply (rule subsetI)
    apply (drule iffD1[OF mem_Collect_eq])
    subgoal for x
      apply (cases "dallookup x xs")
      by (auto dest!: dallookup_SomeD simp: keys_dallist.rep_eq rev_image_eqI)
    done
  then show ?thesis by (rule card_of_subset_bound[OF _ keys_dallist_bound])
qed

lemma Step_eqvt:
  fixes f::"'a::var_terms_pre \<Rightarrow> 'a"
  assumes "bij f" "|supp f| <o |UNIV::'a set|"
  shows "e \<^bold>\<longrightarrow> e' \<Longrightarrow> vvsubst f e \<^bold>\<longrightarrow> vvsubst f e'"
unfolding terms_vvsubst_rrename[OF assms]
proof (coinduction arbitrary: e e')
  case Step
  then show ?case
  proof cases
    case (ST_Beta x \<tau> e1 e2)
    then have 1: "rrename_terms f e = App (Lam (f x) \<tau> (rrename_terms f e1)) (rrename_terms f e2)" using rrename_simps[OF assms] by simp
    from ST_Beta have "rrename_terms f e' = tvsubst (rrename_terms f \<circ> VVr(x := e2) \<circ> inv f) (rrename_terms f e1)"
      using rrename_tvsubst[OF assms SSupp_upd_VVr_bound] by auto
    also have "... = tvsubst (VVr (f x := rrename_terms f e2)) (rrename_terms f e1)" using VVr_comp[OF assms] by simp
    finally show ?thesis using 1 by auto
  next
    case (ST_App e1 e1' e2)
    then show ?thesis by (auto simp: rrename_simps assms)
  next
    case (ST_Let e1 e1' xs)
    then show ?thesis using assms rrename_simps(4) by blast
  next
    case (ST_DropLet xs)
    then have "rrename_terms f e = LetRec (map_dallist f (map_prod id (rrename_terms f)) xs) (rrename_terms f e')"
      by (simp add: rrename_simps assms)
    moreover have "stuck (rrename_terms f e')" using ST_DropLet stuck_eqvt[OF assms] by blast
    moreover have "keys_dallist (map_dallist f (map_prod id (rrename_terms f)) xs) \<inter> FFVars_terms (rrename_terms f e') = {}"
      using ST_DropLet by (auto simp: assms dallist.set_map terms.FFVars_rrenames)
    ultimately show ?thesis by blast
  next
    case (ST_LetBeta e1 xs)
    let ?g = "\<lambda>k. case dallookup k xs of None \<Rightarrow> VVr k | Some x \<Rightarrow> snd x"
    let ?xs = "map_dallist f (map_prod id (rrename_terms f)) xs"
    have "rrename_terms f \<circ> ?g \<circ> inv f = (\<lambda>k. case dallookup (inv f k) xs of None \<Rightarrow> VVr k | Some x \<Rightarrow> rrename_terms f (snd x))"
      apply (unfold comp_def)
      apply (rule ext)
      subgoal for k
        apply (cases "dallookup (inv f k) xs")
         apply simp
         apply (unfold Var_is_VVr[symmetric])
         apply (rule trans)
          apply (rule rrename_simps)
           apply (rule assms)+
         apply (subst inv_simp2[of f])
          apply (rule assms)
         apply (rule refl)
        by simp
      done
    also have "... = (\<lambda>k. case dallookup k ?xs of None \<Rightarrow> VVr k | Some x \<Rightarrow> snd x)"
      apply (rule ext)
      subgoal for k
        apply (cases "dallookup (inv f k) xs")
         apply simp
         apply (cases "dallookup k ?xs")
          apply simp
         apply (metis (mono_tags, lifting) assms(1) assms(2) bij_betw_imp_surj dallist.set_map(1) dallookup_NoneD dallookup_NoneI not_imageI option.discI surj_f_inv_f)
        apply simp
        apply (cases "dallookup k ?xs")
         apply simp
         apply (metis assms(1) assms(2) dallist.set_map(1) dallookup_NoneD dallookup_NoneI image_in_bij_eq option.discI)
        apply simp
        apply (rotate_tac -1)
        apply (drule dallookup_dallmapD[of _ _ _ "map_prod id (rrename_terms (inv f))"])
        apply (subst (asm) dallist.map_comp)
            apply (rule assms supp_id_bound bij_id)+
        apply (unfold id_o o_id prod.map_comp trans[OF comp_apply[of "map_prod _ _" "map_prod _ _"] prod.map_comp, abs_def])
        apply (subst (asm) terms.rrename_comp0s)
            apply (rule assms supp_inv_bound bij_imp_bij_inv)+
        apply (subst (asm) inv_o_simp1[of f])
         apply (rule assms)
        apply (unfold terms.rrename_id0s map_prod.id)
        subgoal for a b
          apply (rule prod.exhaust[of b])
          apply hypsubst_thin
          apply (unfold snd_conv map_prod_simp id_def)
          apply (unfold id_def[symmetric])
          apply (drule dallookup_map_SomeD[of "inv f", rotated])
           apply (rule bij_imp_bij_inv)
           apply (rule assms)
          apply (subst (asm) inv_inv_eq)
           apply (rule assms)
          apply simp
          apply (rule trans)
           apply (rule terms.rrename_comps)
              apply (rule assms bij_imp_bij_inv supp_inv_bound)+
          apply (subst inv_o_simp2)
           apply (rule assms)
          apply (rule terms.rrename_ids)
          done
        done
      done
    finally have 1: "rrename_terms f (tvsubst ?g e1)
    = tvsubst (\<lambda>k. case dallookup k ?xs of None \<Rightarrow> VVr k | Some x \<Rightarrow> snd x) (rrename_terms f e1)" (is "_ = ?e1'")
      unfolding rrename_tvsubst[OF assms SSupp_bound] by simp
    from ST_LetBeta have "rrename_terms f e = LetRec ?xs (rrename_terms f e1)"
      by (simp add: rrename_simps assms)
    moreover have "rrename_terms f e' = LetRec ?xs ?e1'" using 1 rrename_simps[OF assms] ST_LetBeta by auto
    moreover have "stuck (rrename_terms f e1)" using ST_LetBeta stuck_eqvt[OF assms] by blast
    moreover have "keys_dallist ?xs \<inter> FFVars_terms (rrename_terms f e1) \<noteq> {}"
      using ST_LetBeta by (auto simp: assms dallist.set_map terms.FFVars_rrenames)
    ultimately show ?thesis by blast
  qed
qed

lemma context_morph: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau> ; \<forall>(x, \<tau>)\<in>lset (Rep_dallist \<Gamma>). x \<in> FFVars_terms e \<longrightarrow> (x, \<tau>)\<in>lset (Rep_dallist \<Gamma>') \<rbrakk> \<Longrightarrow> \<Gamma>' \<turnstile> e : \<tau>"
proof (binder_induction \<Gamma> e \<tau> arbitrary: \<Gamma>' avoiding: \<Gamma>' rule: Ty_strong_induct)
  case (Var x \<Gamma> \<tau> \<Gamma>')
  then have "(x, \<tau>) \<in> lset (Rep_dallist \<Gamma>')" unfolding FFVars_simps using dallookup_SomeD by fastforce
  then show ?case using Ty_Var dallookup_SomeI by fast
next
  case (App \<Gamma> e1 \<tau>1 \<tau>2 e2 \<Gamma>')
  then show ?case unfolding FFVars_simps using Ty_App by blast
next
  case (Lam x \<Gamma> \<tau> e \<tau>2 \<Gamma>')
  then have "\<forall>(y, \<tau>')\<in>lset (Rep_dallist (DALCons x \<tau> \<Gamma>)). y \<in> FFVars_terms e \<longrightarrow> (y, \<tau>') \<in> lset (Rep_dallist (DALCons x \<tau> \<Gamma>'))"
    apply (unfold FFVars_simps case_prod_beta prod.collapse)
    apply (subst lset_DALCons, assumption)+
    by (metis DiffI empty_iff imageI insert_iff keys_dallist.rep_eq)
  then show ?case using Lam Ty_Lam by blast
next
  case (LetRec \<Gamma> xs \<Gamma>2 e \<tau> \<Gamma>')
  have 1: "keys_dallist \<Gamma> \<inter> keys_dallist (map_dallist id fst xs) = {}" "keys_dallist \<Gamma>' \<inter> keys_dallist (map_dallist id fst xs) = {}"
     apply (subst dallist.set_map, rule bij_id, rule supp_id_bound)
     apply (simp add: LetRec)
    apply (subst dallist.set_map, rule bij_id, rule supp_id_bound)
    apply (rule trans[OF Int_commute])
    by (simp add: LetRec)
  let ?\<Gamma>3 = "dainterleave \<Gamma>' (map_dallist id fst xs)"
  from LetRec(3,7) have x: "\<forall>a\<in>lset (Rep_dallist \<Gamma>2). fst a \<in> FFVars_terms (LetRec xs e) \<longrightarrow> a \<in> lset (Rep_dallist ?\<Gamma>3)"
    by (auto simp: lset_dainterleave[OF 1(1)] lset_dainterleave[OF 1(2)])
  then have "\<forall>a\<in>lset (Rep_dallist \<Gamma>2). fst a \<in> FFVars_terms e \<longrightarrow> a \<in> lset (Rep_dallist ?\<Gamma>3)" unfolding FFVars_simps
    using 1 LetRec.hyps(2,3) keys_dallist.rep_eq by fastforce
  then have 2: "?\<Gamma>3 \<turnstile> e : \<tau>" using LetRec(6) by fastforce
  have "\<forall>(\<tau>', e)\<in>vals_dallist xs. ((\<forall>a\<in>lset (Rep_dallist \<Gamma>2). case a of (x, \<tau>) \<Rightarrow> x \<in> FFVars_terms e \<longrightarrow> (x, \<tau>) \<in> lset (Rep_dallist ?\<Gamma>3)) \<longrightarrow> ?\<Gamma>3 \<turnstile> e : \<tau>')
    \<longrightarrow> ?\<Gamma>3 \<turnstile> e : \<tau>'"
    apply (rule ballI)
    apply (unfold case_prod_beta)
    apply (rule impI)
    apply (erule impE)
     prefer 2
    apply assumption
    using x unfolding FFVars_simps
    by (smt (verit, del_insts) 1 DiffI LetRec.hyps(2,3) UnCI UnE Union_iff disjoint_iff image_iff keys_dallist.rep_eq lset_dainterleave prod.collapse)
  then show ?case using Ty_LetRec[OF trans[OF Int_commute LetRec(1)] refl dallist.pred_mono_strong[OF LetRec(4)] 2]
    by blast
qed

lemma weaken:
  assumes "\<Gamma> \<turnstile> e : \<tau>" "keys_dallist \<Gamma> \<inter> keys_dallist xs = {}"
  shows "dainterleave \<Gamma> xs \<turnstile> e : \<tau>"
  using context_morph[OF assms(1)] in_dainterleave1[OF _ assms(2)] by blast

(*lemma substitution: "\<lbrakk> \<Gamma>' \<turnstile> e : \<tau> ; \<Gamma>' = dainterleave (map_dallist id fst xs) \<Gamma> ; pred_dallist (\<lambda>(\<tau>1, v). \<Gamma>' \<turnstile> v : \<tau>1 \<and> FFVars_terms v \<inter> keys_dallist xs = {}) xs; keys_dallist xs \<inter> keys_dallist \<Gamma> = {} \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> tvsubst (\<lambda>k. case dallookup k xs of None \<Rightarrow> VVr k | Some x \<Rightarrow> snd x) e : \<tau>"
proof (binder_induction \<Gamma>' e \<tau> arbitrary: \<Gamma> avoiding: \<Gamma> xs rule: Ty_strong_induct)
  case (Var x \<Gamma>' \<tau> \<Gamma>)
  then have 1: "keys_dallist (map_dallist id fst xs) \<inter> keys_dallist \<Gamma> = {}" by (simp add: dallist.set_map supp_id_bound)
  let ?e = "case dallookup x xs of None \<Rightarrow> VVr x | Some x \<Rightarrow> snd x"
  show ?case unfolding tvsubst_simps[OF SSupp_bound]
  proof (cases "dallookup x xs")
    case None
    have "dallookup x \<Gamma> = Some \<tau>" using None Var(1,2) 1
      apply (auto dest!: dallookup_NoneD dallookup_SomeD)
      apply (unfold lset_dainterleave[OF 1] id_def[symmetric])
      apply (drule imageI[of _ _ fst])
      apply (unfold fst_conv keys_dallist.rep_eq[symmetric] image_Un dallist.set_map[OF bij_id supp_id_bound] image_id)
      apply (auto intro!: dallookup_SomeI simp: keys_dallist.rep_eq)
      by (metis "1" Var.hyps dallookup_SomeD dallookup_SomeI in_dainterleave2)
    then show "\<Gamma> \<turnstile> ?e : \<tau>" using None Ty_Var unfolding Var_is_VVr by auto
  next
    case (Some a)
    then have 2: "dallookup x (map_dallist id fst xs) = Some \<tau>" using Var
      by (metis (no_types, lifting) "1" dallookup_dainterleave1 dallookup_dallmapD)
    from Var(3) have 3: "\<Gamma>' \<turnstile> snd a : fst a" unfolding dallist.pred_set vals_dallist.rep_eq using dallookup_SomeD[OF Some] by auto
    from Var(3) have "FFVars_terms (snd a) \<inter> keys_dallist xs = {}" unfolding dallist.pred_set vals_dallist.rep_eq using dallookup_SomeD[OF Some] by auto
    then show "\<Gamma> \<turnstile> ?e : \<tau>"  sorry
  qed
next
  case (App \<Gamma>' e1 \<tau>1 \<tau>2 e2 \<Gamma>)
  then show ?case sorry
next
  case (Lam x \<Gamma>' \<tau> e \<tau>2 \<Gamma>)
  then show ?case sorry
next
  case (LetRec \<Gamma>' xs \<Gamma>'' e \<tau> \<Gamma>)
  then show ?case sorry
qed*)

(*corollary substitution_single:
  assumes "DALCons x \<tau>1 \<Gamma> \<turnstile> e : \<tau>" "DALCons x \<tau>1 \<Gamma> \<turnstile> v : \<tau>1" "x \<notin> keys_dallist \<Gamma>"
  shows "\<Gamma> \<turnstile> tvsubst (VVr(x:=v)) e : \<tau>"
proof -
  let ?xs = "DALCons x (\<tau>1, v) DALNil"
  have 1: "(\<lambda>k. case dallookup k ?xs of None \<Rightarrow> VVr k | Some x \<Rightarrow> snd x) = (VVr(x:=v))" by auto
  have 2: "dainterleave (map_dallist id fst ?xs) \<Gamma> = DALCons x \<tau>1 \<Gamma>"
    using assms(3) by (auto simp: dainterleave_DALCons map_dallist_DALCons supp_id_bound)
  have 3: "pred_dallist (\<lambda>(\<tau>1, v). DALNil \<turnstile> v : \<tau>1) ?xs = DALNil \<turnstile> v : \<tau>1" by auto
  show ?thesis using substitution[of _ ?xs \<Gamma> e \<tau>, unfolded 1 2 3, OF assms(1,2)] assms(3) by simp
qed*)

lemma substitution_single:
  assumes "\<Gamma>' \<turnstile> e : \<tau>" "\<Gamma>' \<turnstile> v : \<tau>1" "\<Gamma>' = DALCons x \<tau>1 \<Gamma>" "x \<notin> keys_dallist \<Gamma>"
  shows "\<Gamma> \<turnstile> tvsubst (VVr(x:=v)) e : \<tau>"
using assms proof (binder_induction \<Gamma>' e \<tau> arbitrary: \<Gamma> avoiding: \<Gamma> v rule: Ty_strong_induct)
  case (Var y \<Gamma>' \<tau> \<Gamma>)
  then show ?case
    apply (subst tvsubst_simps)
     apply (rule SSupp_upd_VVr_bound)
    apply (unfold fun_upd_def Var_is_VVr[symmetric])
    apply (rule case_split[of "y = x"])
     apply (subst if_P)
      apply assumption

    sorry
next
  case (App \<Gamma>' e1 \<tau>1 \<tau>2 e2 \<Gamma>)
  then show ?case sorry
next
  case (Lam x \<Gamma>' \<tau> e \<tau>2 \<Gamma>)
  then show ?case sorry
next
  case (LetRec \<Gamma>' xs \<Gamma>' e \<tau> \<Gamma>)
  then show ?case sorry
qed

theorem preservation: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau> ; e \<^bold>\<longrightarrow> e' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> e' : \<tau>"
proof (binder_induction \<Gamma> e \<tau> arbitrary: e' avoiding: e' rule: Ty_strong_induct)
  case (App \<Gamma> e1 \<tau>1 \<tau>2 e2 e')
  from App.prems show ?case
  proof cases
    case (ST_Beta x \<tau> e1' e2')
    then show ?thesis using App sorry
  next
    case (ST_App e1 e1' e2)
    then show ?thesis using App by (auto intro: Ty.intros)
  qed simp_all
next
  case (LetRec \<Gamma> xs \<Gamma>' e \<tau> e')
  from LetRec.prems show ?case
  proof cases
    case (ST_Let e1 e1' ys)
    then show ?thesis using LetRec sorry
  next
    case (ST_DropLet ys)
    then obtain f where 1: "bij f" "|supp (f::'a::var_terms_pre \<Rightarrow> 'a)| <o |UNIV::'a set|"
      "map_dallist f (map_prod id (vvsubst f)) xs = ys" "vvsubst f e = e'"
      "id_on (\<Union> (FFVars_terms ` snd ` vals_dallist xs) \<union> FFVars_terms e - keys_dallist xs) f" using LetRec_inject by blast
    then have 2: "keys_dallist xs \<inter> FFVars_terms e = {}" using terms.set_map ST_DropLet(3)
      by (metis (no_types, lifting) bij_betw_apply bij_imp_bij_betw dallist.set_map(1) disjoint_iff)
    then have 3: "\<Gamma> \<turnstile> e : \<tau>" using LetRec(2,3) context_morph[OF LetRec(5)]
      by (smt (verit, ccfv_threshold) Int_emptyD Prelim.image_id UnE bij_id case_prodI2 dallist.set_map(1) fst_conv imageI keys_dallist.rep_eq lset_dainterleave supp_id_bound)
    have "id_on (FFVars_terms e) f" using 1 2 by (metis Diff_Un_disjunct id_on_Un)
    then have "e = e'" using 1 by (metis id_apply id_onD supp_id_bound terms.map_cong0 terms.map_id)
    then show ?thesis using 3 by blast
  next
    case (ST_LetBeta e1 ys)
    then show ?thesis using LetRec Ty_LetRec sorry
  qed simp_all
qed (auto elim: STE)


(*proof (induction \<Gamma> e \<tau> arbitrary: e' rule: Ty.induct)
  case (Ty_App \<Gamma> e1 \<tau>1 \<tau>2 e2)
  from Ty_App.prems show ?case
  proof cases
    case (ST_Beta x \<tau> e1' e2')
    then show ?thesis sorry
  next
    case (ST_App e1 e1' e2)
    then show ?thesis using Ty_App by (auto intro: Ty.intros)
  qed simp_all
next
  case (Ty_LetRec \<Gamma> xs \<Gamma>' e \<tau>)
  from Ty_LetRec.prems show ?case
  proof cases
    case (ST_Let e2 e1' ys)
    then obtain f::"'a::var_terms_pre \<Rightarrow> 'a" where 1: "bij f" "|supp f| <o |UNIV::'a set|"
      "map_dallist f (map_prod id (vvsubst f)) xs = ys" "vvsubst f e = e2"
      "id_on (\<Union>(FFVars_terms ` snd ` vals_dallist xs) \<union> FFVars_terms e - keys_dallist xs) f"
      using LetRec_inject by blast
    then have "map_dallist id fst xs = map_dallist id fst (map_dallist (inv f) id ys)"
      by (smt (verit) Product_Type.fst_comp_map_prod bij_id bij_imp_bij_inv dallist.map_comp dallist.map_id inv_id inv_o_simp1 supp_id_bound supp_inv_bound)

    have "vvsubst f e \<^bold>\<longrightarrow> e1'" using ST_Let(3) 1 by simp
    then have "vvsubst f e \<^bold>\<longrightarrow> vvsubst f (vvsubst (inv f) e1')" by (simp add: 1 supp_inv_bound terms.map_comp terms.map_id)
    then have "e \<^bold>\<longrightarrow> vvsubst (inv f) e1'" using Step_eqvt[of "inv f"]
      by (metis 1(1,2) bij_betw_inv_into inv_o_simp1 supp_inv_bound terms.map_comp terms.map_id)
    then have "\<Gamma>' \<turnstile> vvsubst (inv f) e1' : \<tau>" by (rule Ty_LetRec)
    then have "\<Gamma> \<turnstile> LetRec xs (vvsubst (inv f) e1') : \<tau>" (is "\<Gamma> \<turnstile> ?e : \<tau>") using Ty.Ty_LetRec[OF Ty_LetRec(1,2)] Ty_LetRec(4)
      by (simp add: dallist.pred_set split_beta)

    obtain g::"'a::var_terms_pre \<Rightarrow> 'a" where 3: "bij g" "|supp g| <o |UNIV::'a set|" "imsupp g \<inter> keys_dallist \<Gamma> = {}" "\<forall>a. a \<in> imsupp f - keys_dallist \<Gamma> \<union> keys_dallist xs \<and> f a \<notin> keys_dallist \<Gamma> \<longrightarrow> g a = f a"
      "id_on (\<Union> (FFVars_terms ` snd ` vals_dallist xs) \<union> FFVars_terms e - keys_dallist xs) g"
      apply atomize_elim
      apply (rule exE[OF ex_avoiding_bij[OF 1(2,1) cinfinite_imp_infinite[OF terms.UNIV_cinfinite] _ 1(5) _ trans[OF Int_commute Ty_LetRec(1)]]])
         apply (rule ordLeq_ordLess_trans[OF card_of_diff])
         apply (rule terms.Un_bound)
          apply (rule terms.UNION_bound)
           apply (rule ordLeq_ordLess_trans[OF card_of_image])
           apply (rule vals_dallist_bound keys_dallist_bound terms.set_bd_UNIV)+
      apply (erule conjE)+
      apply (rule exI)
      apply ((rule conjI)?, assumption)+
      done
  
    show ?thesis using 2  (* rename + induction *) sorry
  next
    case (ST_DropLet ys)
    then obtain f where 1: "bij f" "|supp (f::'a::var_terms_pre \<Rightarrow> 'a)| <o |UNIV::'a set|"
      "map_dallist f (map_prod id (vvsubst f)) xs = ys" "vvsubst f e = e'"
      "id_on (\<Union> (FFVars_terms ` snd ` vals_dallist xs) \<union> FFVars_terms e - keys_dallist xs) f" using LetRec_inject by blast
    then have 2: "keys_dallist xs \<inter> FFVars_terms e = {}" using terms.set_map ST_DropLet(3)
      by (metis (no_types, lifting) bij_betw_apply bij_imp_bij_betw dallist.set_map(1) disjoint_iff)
    then have 3: "\<Gamma> \<turnstile> e : \<tau>" using Ty_LetRec(1,2) context_morph[OF Ty_LetRec(3)]
      by (smt (verit, ccfv_threshold) Int_emptyD Prelim.image_id UnE bij_id case_prodI2 dallist.set_map(1) fst_conv imageI keys_dallist.rep_eq lset_dainterleave supp_id_bound)
    have "id_on (FFVars_terms e) f" using 1 2 by (metis Diff_Un_disjunct id_on_Un)
    then have "e = e'" using 1 by (metis id_apply id_onD supp_id_bound terms.map_cong0 terms.map_id)
    then show ?thesis using 3 by blast
  next
    case (ST_LetBeta e2 ys)
    then show ?thesis sorry
  qed simp_all
qed (auto elim: STE)*)

end