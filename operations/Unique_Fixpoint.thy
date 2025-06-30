theory Unique_Fixpoint
  imports "Binders.MRBNF_Recursor" "../operations/BMV_Monad"
begin


binder_datatype 'a expr =
    Var 'a
  | Lam x::'a t::"'a expr" binds x in t
  | App "'a expr" "'a expr"

thm subshape_expr_expr.intros

thm expr.strong_induct

(*
lemma tvsubst_expr_unique:
  assumes 
    B: "|- B| <o |UNIV :: 'a set|" and
    \<rho>: "|SSupp_expr (\<rho> :: 'a::var \<Rightarrow> 'a expr)| <o |UNIV :: 'a set|" and
    A: "|A| <o |UNIV :: 'a set|" and
    base: "\<And>a. a \<in> B \<Longrightarrow> h (Var a) = \<rho> a" and
    step: "\<And>u. FVars_expr (expr_ctor u) \<subseteq> B \<Longrightarrow>
       set2_expr_pre u \<inter> A = {} \<Longrightarrow>
       set2_expr_pre u \<inter> IImsupp_expr \<rho> = {} \<Longrightarrow>
       noclash_expr u \<Longrightarrow>
       (\<forall>a. expr_ctor u \<noteq> Var a) \<Longrightarrow>
       h (expr_ctor u) = expr_ctor (map_expr_pre id id h h u)"
  shows "FVars_expr e \<subseteq> B \<Longrightarrow> h e = tvsubst_expr \<rho> e"
  apply (binder_induction e avoiding: A "IImsupp_expr \<rho>" e "- B" rule: expr.strong_induct)
  subgoal
    apply (rule A)
    done
  subgoal
    apply (simp add: IImsupp_expr_def)
    apply (rule Un_bound[OF infinite_UNIV])
     apply (rule \<rho>)
    apply (rule UN_bound)
     apply (rule \<rho>)
    apply (rule expr.FVars_bd_UNIVs)
    done
  subgoal
    apply (rule B)
    done
  subgoal for x
    using expr.tvsubst_VVr[OF ordLess_ordLeq_trans[OF \<rho>], of x]
    apply (subst base)
    apply simp
    apply (simp add: tvVVr_tvsubst_expr_def Var_def tv\<eta>_expr_tvsubst_expr_def)
    done
  subgoal premises prems for x t
    using prems unfolding Lam_def
      apply (subst step)
      apply (simp_all add: expr.FVars_ctor noclash_expr_def Var_def expr.TT_inject0
        set1_expr_pre_def set2_expr_pre_def set3_expr_pre_def set4_expr_pre_def map_expr_pre_def
        Abs_expr_pre_inverse Abs_expr_pre_inject expr.FVars_permute infinite_UNIV)
    apply (subst expr.tvsubst_cctor_not_isVVr)
    apply (simp_all add: assms(1) noclash_expr_def expr.TT_inject0 tvisVVr_tvsubst_expr_def tvVVr_tvsubst_expr_def tv\<eta>_expr_tvsubst_expr_def
        set1_expr_pre_def set2_expr_pre_def set3_expr_pre_def set4_expr_pre_def map_expr_pre_def
        Abs_expr_pre_inverse Abs_expr_pre_inject \<rho>)
    apply (rule exI[of _ id]; simp add: expr.permute_id supp_id_bound)
    apply blast
    done
  subgoal for t u
    unfolding App_def
    apply (subst step)
    apply (simp_all add: expr.FVars_ctor noclash_expr_def Var_def expr.TT_inject0
        set1_expr_pre_def set2_expr_pre_def set3_expr_pre_def set4_expr_pre_def map_expr_pre_def
        Abs_expr_pre_inverse Abs_expr_pre_inject)
    apply (subst expr.tvsubst_cctor_not_isVVr)
    apply (simp_all add: assms(1) noclash_expr_def expr.TT_inject0 tvisVVr_tvsubst_expr_def tvVVr_tvsubst_expr_def tv\<eta>_expr_tvsubst_expr_def
        set1_expr_pre_def set2_expr_pre_def set3_expr_pre_def set4_expr_pre_def map_expr_pre_def
        Abs_expr_pre_inverse Abs_expr_pre_inject \<rho>)
    done
  done
*)

typedecl ('a1, 'a2, 'x1, 'x2) G
consts Gsub :: "('a1 :: var \<Rightarrow> 'a1) \<Rightarrow> ('a2 :: var \<Rightarrow> 'a2) \<Rightarrow> ('a1, 'a2, 'x1, 'x2) G \<Rightarrow> ('a1, 'a2, 'x1, 'x2) G"
consts GVrs1 :: "('a1 :: var, 'a2 :: var, 'x1, 'x2) G \<Rightarrow> 'a1 set"
consts GVrs2 :: "('a1 :: var, 'a2 :: var, 'x1, 'x2) G \<Rightarrow> 'a2 set"
consts Gmap :: "('x1 \<Rightarrow> 'x1') \<Rightarrow> ('x2 \<Rightarrow> 'x2') \<Rightarrow> ('a1, 'a2, 'x1, 'x2) G \<Rightarrow> ('a1, 'a2, 'x1', 'x2') G"
consts GSupp1 :: "('a1 :: var, 'a2 :: var, 'x1, 'x2) G \<Rightarrow> 'x1 set"
consts GSupp2 :: "('a1 :: var, 'a2 :: var, 'x1, 'x2) G \<Rightarrow> 'x2 set"

pbmv_monad "('a1::var, 'a2::var, 'x1, 'x2) G"
  Sbs: Gsub
  RVrs: GVrs1 GVrs2
  Maps: Gmap
  Supps: GSupp1 GSupp2
  bd: natLeq
  sorry

print_theorems

consts \<eta> :: "'a1 :: var \<Rightarrow> ('a1, 'a2 :: var, 'x1, 'x2) G"
consts \<eta>' :: "'a1 :: var \<Rightarrow> ('a1, 'a2 :: var, 'x1, 'x2) G"

lemma eta_natural: "Gsub \<delta>1 \<delta>2 (Gmap f1 f2 (\<eta> x)) = \<eta> (\<delta>1 x)"
  sorry
lemma eta'_natural: "Gsub \<delta>1 \<delta>2 (Gmap f1 f2 (\<eta>' x)) = \<eta>' (\<delta>1 x)"
  sorry

lemma eta_inj: "\<eta> a = \<eta> a' \<Longrightarrow> a = a'"
  sorry
lemma eta'_inj: "\<eta>' a = \<eta>' a' \<Longrightarrow> a = a'"
  sorry

lemma eta_distinct: "\<eta> a \<noteq> \<eta>' a'"
  sorry

typedecl 'a E

consts Ector :: "('a :: var, 'a, 'a E, 'a E) G \<Rightarrow> 'a E"
consts Eperm :: "('a :: var \<Rightarrow> 'a) \<Rightarrow> 'a E \<Rightarrow> 'a E"

lemma Eperm_id: "Eperm id = id"
  sorry

lemma Eperm_comp:
  "bij (\<sigma> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>
   bij (\<tau> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<tau>| <o |UNIV :: 'a set| \<Longrightarrow>
  Eperm \<sigma> o Eperm \<tau> = Eperm (\<sigma> o \<tau>)"
  sorry

inductive Efree for a where 
  "a \<in> GVrs1 u \<Longrightarrow> Efree a (Ector u)"
| "e \<in> GSupp1 u \<Longrightarrow> Efree a e \<Longrightarrow> a \<notin> GVrs2 u \<Longrightarrow> Efree a (Ector u)"
| "e \<in> GSupp2 u \<Longrightarrow> Efree a e \<Longrightarrow> Efree a (Ector u)"

definition "EFVars e = {a. Efree a e}"

lemma Ector_fresh_cases: "|A::'a set| <o |UNIV :: 'a ::var set| \<Longrightarrow> (\<And>u. e = Ector u \<Longrightarrow> GVrs2 u \<inter> A = {} \<Longrightarrow> P) \<Longrightarrow> P"
  sorry

lemma Ector_inject: "(Ector x = Ector y) =
(\<exists>\<sigma> :: 'a :: var \<Rightarrow> 'a. bij \<sigma> \<and>
     |supp \<sigma>| <o |UNIV :: 'a set| \<and>
     id_on (\<Union> (EFVars ` GSupp1 x) - GVrs2 x) \<sigma> \<and>
     Gsub id \<sigma> (Gmap (Eperm \<sigma>) id x) = y)"
  sorry

inductive Efreee for a where 
  "a \<in> GVrs1 u \<Longrightarrow> \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow> Efreee a (Ector u)"
| "e \<in> GSupp1 u \<Longrightarrow> Efreee a e \<Longrightarrow> a \<notin> GVrs2 u \<Longrightarrow> Efreee a (Ector u)"
| "e \<in> GSupp2 u \<Longrightarrow> Efreee a e \<Longrightarrow> Efreee a (Ector u)"

lemma Efreee_strong_induct: "|V| <o |UNIV :: 'a ::var set| \<Longrightarrow> Efreee a x \<Longrightarrow>
(\<And>u. GVrs2 u \<inter> V = {} \<Longrightarrow> a \<in> GVrs1 u \<Longrightarrow> \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow> P (Ector u)) \<Longrightarrow>
(\<And>e u. GVrs2 u \<inter> V = {} \<Longrightarrow> e \<in> GSupp1 u \<Longrightarrow> Efreee a e \<Longrightarrow> P e \<Longrightarrow> a \<notin> GVrs2 u \<Longrightarrow> P (Ector u)) \<Longrightarrow>
(\<And>e u. GVrs2 u \<inter> V = {} \<Longrightarrow> e \<in> GSupp2 u \<Longrightarrow> Efreee a e \<Longrightarrow> P e \<Longrightarrow> P (Ector u)) \<Longrightarrow> P x"
  sorry

inductive Efree\<eta> for a where 
  "Efree\<eta> a (Ector (\<eta> a))"
| "e \<in> GSupp1 u \<Longrightarrow> Efree\<eta> a e \<Longrightarrow> a \<notin> GVrs2 u \<Longrightarrow> Efree\<eta> a (Ector u)"
| "e \<in> GSupp2 u \<Longrightarrow> Efree\<eta> a e \<Longrightarrow> Efree\<eta> a (Ector u)"

lemma Efree\<eta>_strong_induct: "|V| <o |UNIV :: 'a ::var set| \<Longrightarrow> Efree\<eta> a x \<Longrightarrow>
P (Ector (\<eta> a)) \<Longrightarrow>
(\<And>e u. GVrs2 u \<inter> V = {} \<Longrightarrow> e \<in> GSupp1 u \<Longrightarrow> Efree\<eta> a e \<Longrightarrow> P e \<Longrightarrow> a \<notin> GVrs2 u \<Longrightarrow> P (Ector u)) \<Longrightarrow>
(\<And>e u. e \<in> GSupp2 u \<Longrightarrow> Efree\<eta> a e \<Longrightarrow> P e \<Longrightarrow> P (Ector u)) \<Longrightarrow> P x"
  sorry

inductive Efree\<eta>' for a where 
  "Efree\<eta>' a (Ector (\<eta>' a))"
| "e \<in> GSupp1 u \<Longrightarrow> Efree\<eta>' a e \<Longrightarrow> a \<notin> GVrs2 u \<Longrightarrow> Efree\<eta>' a (Ector u)"
| "e \<in> GSupp2 u \<Longrightarrow> Efree\<eta>' a e \<Longrightarrow> Efree\<eta>' a (Ector u)"

lemma Efree\<eta>'_strong_induct: "|V| <o |UNIV :: 'a ::var set| \<Longrightarrow> Efree\<eta>' a x \<Longrightarrow>
P (Ector (\<eta>' a)) \<Longrightarrow>
(\<And>e u. GVrs2 u \<inter> V = {} \<Longrightarrow> e \<in> GSupp1 u \<Longrightarrow> Efree\<eta>' a e \<Longrightarrow> P e \<Longrightarrow> a \<notin> GVrs2 u \<Longrightarrow> P (Ector u)) \<Longrightarrow>
(\<And>e u. e \<in> GSupp2 u \<Longrightarrow> Efree\<eta>' a e \<Longrightarrow> P e \<Longrightarrow> P (Ector u)) \<Longrightarrow> P x"
  sorry

definition "EFVrs e = {a. Efreee a e}"
definition "EFVrs\<eta> e = {a. Efree\<eta> a e}"
definition "EFVrs\<eta>' e = {a. Efree\<eta>' a e}"

consts Esub :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a ::var \<Rightarrow> 'a E) \<Rightarrow> ('a ::var \<Rightarrow> 'a E) \<Rightarrow> 'a E \<Rightarrow> 'a E"

lemma Eperm_Esub:
  "bij (\<sigma> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>
  |supp (\<delta> :: 'a \<Rightarrow> 'a :: var)| <o |UNIV::'a set| \<Longrightarrow>
  |SSupp (Ector o \<eta>) (\<rho>::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow>
  |SSupp (Ector o \<eta>') (\<rho>'::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow>
  Eperm \<sigma> o Esub \<delta> \<rho> \<rho>' = Esub (\<sigma> o \<delta> o inv \<sigma>) (Eperm \<sigma> o \<rho> o inv \<sigma>) (Eperm \<sigma> o \<rho>' o inv \<sigma>)"
  sorry

lemma EFVars_Esub:
  "|supp (\<delta> :: 'a \<Rightarrow> 'a :: var)| <o |UNIV::'a set| \<Longrightarrow>
  |SSupp (Ector o \<eta>) (\<rho>::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow>
  |SSupp (Ector o \<eta>') (\<rho>'::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow>
  EFVars (Esub \<delta> \<rho> \<rho>' x) \<subseteq> EFVars x \<union> supp \<delta> \<union> SSupp (Ector o \<eta>) \<rho>  \<union> SSupp (Ector o \<eta>') \<rho>'"
  sorry

lemma Esub_Ector:
  assumes
  "|supp (\<delta> :: 'a \<Rightarrow> 'a :: var)| <o |UNIV::'a set|"
  "|SSupp (Ector o \<eta>) (\<rho>::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set|"
  "|SSupp (Ector o \<eta>') (\<rho>'::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set|"
shows
   "Esub \<delta> \<rho> \<rho>' (Ector (\<eta> a)) = \<rho> a"
   "Esub \<delta> \<rho> \<rho>' (Ector (\<eta>' a)) = \<rho>' a"
   "GVrs2 u \<inter> imsupp \<delta> = {} \<Longrightarrow>
    GVrs2 u \<inter> IImsupp (Ector o \<eta>) EFVrs\<eta> \<rho> = {} \<Longrightarrow>
    GVrs2 u \<inter> IImsupp (Ector o \<eta>') EFVrs\<eta>' \<rho>' = {} \<Longrightarrow>
    \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow>
    Esub \<delta> \<rho> \<rho>' (Ector u) = Ector (Gsub \<delta> id (Gmap (Esub \<delta> \<rho> \<rho>') (Esub \<delta> \<rho> \<rho>') u))"
  sorry

(*
lemma Esub_unique:
  assumes
  "|supp (\<delta> :: 'a \<Rightarrow> 'a :: var)| <o |UNIV::'a set|"
  "|SSupp (Ector o \<eta>) (\<rho>::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set|"
  "|SSupp (Ector o \<eta>') (\<rho>'::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set|"
  "\<And>a. h (Ector (\<eta> a)) = \<rho> a"
  "\<And>a. h (Ector (\<eta>' a)) = \<rho>' a"
  "\<And>u.
   GVrs2 u \<inter> imsupp \<delta> = {} \<Longrightarrow>
   GVrs2 u \<inter> IImsupp (Ector o \<eta>) EFVrs\<eta> \<rho> = {} \<Longrightarrow>
   GVrs2 u \<inter> IImsupp (Ector o \<eta>') EFVrs\<eta>' \<rho>' = {} \<Longrightarrow>
   \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow>
   h (Ector u) = Ector (Gsub \<delta> id (Gmap h h u))"
  shows
   "h = Esub \<delta> \<rho> \<rho>'"
  sorry
*)

lemma Esub_unique_fresh_relativized:
  assumes
  "|- B| <o |UNIV :: 'a set|"
  "|- B\<eta>| <o |UNIV :: 'a set|"
  "|- B\<eta>'| <o |UNIV :: 'a set|"
  "|A| <o |UNIV::'a set|"
  "|supp (\<delta> :: 'a \<Rightarrow> 'a :: var)| <o |UNIV::'a set|"
  "|SSupp (Ector o \<eta>) (\<rho>::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set|"
  "|SSupp (Ector o \<eta>') (\<rho>'::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set|"
  "\<And>a. a \<in> B\<eta> \<Longrightarrow> h (Ector (\<eta> a)) = \<rho> a"
  "\<And>a. a \<in> B\<eta>' \<Longrightarrow> h (Ector (\<eta>' a)) = \<rho>' a"
  "\<And>u.
   EFVrs (Ector u) \<subseteq> B \<Longrightarrow>
   EFVrs\<eta> (Ector u) \<subseteq> B\<eta> \<Longrightarrow>
   EFVrs\<eta>' (Ector u) \<subseteq> B\<eta>' \<Longrightarrow>
   GVrs2 u \<inter> A = {} \<Longrightarrow>
   GVrs2 u \<inter> imsupp \<delta> = {} \<Longrightarrow>
   GVrs2 u \<inter> IImsupp (Ector o \<eta>) EFVrs\<eta> \<rho> = {} \<Longrightarrow>
   GVrs2 u \<inter> IImsupp (Ector o \<eta>') EFVrs\<eta>' \<rho>' = {} \<Longrightarrow>
   \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow>
   h (Ector u) = Ector (Gsub \<delta> id (Gmap h h u))"
  shows
   "EFVrs e \<subseteq> B \<Longrightarrow> EFVrs\<eta> e \<subseteq> B\<eta> \<Longrightarrow> EFVrs\<eta>' e \<subseteq> B\<eta>' \<Longrightarrow> h e = Esub \<delta> \<rho> \<rho>' e"
  sorry

lemma Esub_unique_fresh:
  assumes
  "|A| <o |UNIV::'a set|"
  "|supp (\<delta> :: 'a \<Rightarrow> 'a :: var)| <o |UNIV::'a set|"
  "|SSupp (Ector o \<eta>) (\<rho>::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set|"
  "|SSupp (Ector o \<eta>') (\<rho>'::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set|"
  "\<And>a. h (Ector (\<eta> a)) = \<rho> a"
  "\<And>a. h (Ector (\<eta>' a)) = \<rho>' a"
  "\<And>u.
   GVrs2 u \<inter> A = {} \<Longrightarrow>
   GVrs2 u \<inter> imsupp \<delta> = {} \<Longrightarrow>
   GVrs2 u \<inter> IImsupp (Ector o \<eta>) EFVrs\<eta> \<rho> = {} \<Longrightarrow>
   GVrs2 u \<inter> IImsupp (Ector o \<eta>') EFVrs\<eta>' \<rho>' = {} \<Longrightarrow>
   \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow>
   h (Ector u) = Ector (Gsub \<delta> id (Gmap h h u))"
  shows
   "h = Esub \<delta> \<rho> \<rho>'"
  apply (rule ext)
  apply (rule Esub_unique_fresh_relativized[where B=UNIV and B\<eta>=UNIV and B\<eta>'=UNIV and A=A])
  apply (auto intro!: assms)
  done
(*
  apply (rule Esub_unique[OF assms(2-6)])
  subgoal for u
    apply (subgoal_tac "\<exists>u'. Ector u = Ector u' \<and>
   GVrs2 u' \<inter> A = {} \<and>
   GVrs2 u' \<inter> imsupp \<delta> = {} \<and>
   GVrs2 u' \<inter> IImsupp (Ector o \<eta>) EFVrs\<eta> \<rho> = {} \<and>
   GVrs2 u' \<inter> IImsupp (Ector o \<eta>') EFVrs\<eta>' \<rho>' = {} \<and>
   (\<forall>a. u' \<noteq> \<eta> a) \<and> (\<forall>a'. u' \<noteq> \<eta>' a')")
     apply (auto simp: assms(7)) []
    apply (auto simp: Ector_inject)
    subgoal for \<sigma>
      apply (rule exI[of _ \<sigma>])
    apply (auto simp: assms(2-4) supp_id_bound id_on_def G.Map_comp[THEN fun_cong, simplified]
        G.Map_Sb[THEN fun_cong, simplified] G.Sb_comp[THEN fun_cong, simplified]
        G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map)

      find_theorems Gmap
      find_theorems GSupp1 Gmap
  sorry
*)

lemma EFVrs_bd:
  "|EFVars (x :: 'a :: var E)| <o natLeq"
  "|EFVrs (x :: 'a :: var E)| <o natLeq"
  "|EFVrs\<eta> (x :: 'a :: var E)| <o natLeq"
  "|EFVrs\<eta>' (x :: 'a :: var E)| <o natLeq"
  sorry

lemma EFVrs_bound[simp]:
  "|EFVars (x :: 'a :: var E)| <o |UNIV :: 'a set|"
  "|EFVrs (x :: 'a :: var E)| <o |UNIV :: 'a set|"
  "|EFVrs\<eta> (x :: 'a :: var E)| <o |UNIV :: 'a set|"
  "|EFVrs\<eta>' (x :: 'a :: var E)| <o |UNIV :: 'a set|"
  by (meson EFVrs_bd FType_pre.var_large ordLess_ordLeq_trans)+

lemma SSupp_comp_Esub_le:
  assumes "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
  shows "SSupp (Ector \<circ> \<eta>) (Esub \<delta> \<rho> \<rho>' \<circ> \<rho>'') \<subseteq>
     SSupp (Ector \<circ> \<eta>) \<rho>'' \<union> SSupp (Ector \<circ> \<eta>) \<rho>"
    "SSupp (Ector \<circ> \<eta>') (Esub \<delta> \<rho> \<rho>' \<circ> \<rho>'') \<subseteq>
     SSupp (Ector \<circ> \<eta>') \<rho>'' \<union> SSupp (Ector \<circ> \<eta>') \<rho>'"
  using assms
  by (auto simp: SSupp_def Esub_Ector)

lemma SSupp_comp_bound[simp]:
  "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set| \<Longrightarrow>
   |SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set| \<Longrightarrow>
   |SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set| \<Longrightarrow>
   |SSupp (Ector \<circ> \<eta>) \<rho>''| <o |UNIV :: 'a set| \<Longrightarrow>
   |SSupp (Ector \<circ> \<eta>) (Esub \<delta> \<rho> \<rho>' \<circ> \<rho>'')| <o |UNIV :: 'a set|"
  apply (rule ordLeq_ordLess_trans)
   apply (erule (2) card_of_mono1[OF SSupp_comp_Esub_le(1)])
  apply (auto simp: Un_bound infinite_UNIV)
  done

lemma SSupp_comp_bound'[simp]:
  "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set| \<Longrightarrow>
   |SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set| \<Longrightarrow>
   |SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set| \<Longrightarrow>
   |SSupp (Ector \<circ> \<eta>') \<rho>''| <o |UNIV :: 'a set| \<Longrightarrow>
   |SSupp (Ector \<circ> \<eta>') (Esub \<delta> \<rho> \<rho>' \<circ> \<rho>'')| <o |UNIV :: 'a set|"
  apply (rule ordLeq_ordLess_trans)
   apply (erule (2) card_of_mono1[OF SSupp_comp_Esub_le(2)])
  apply (auto simp: Un_bound infinite_UNIV)
  done

lemma IImsupp_bound[simp]:
  "|SSupp Inj (\<rho> :: 'a::var \<Rightarrow> _)| <o |UNIV :: 'a set| \<Longrightarrow> (\<And>x. |Vr (\<rho> x)| <o |UNIV :: 'a set| ) \<Longrightarrow>
   |IImsupp Inj (Vr :: _ \<Rightarrow> 'a set) \<rho>| <o |UNIV :: 'a set|"
  unfolding IImsupp_def
  apply (erule UN_bound)
  apply auto
  done

inductive Ele for z where
  "Ele z z"
| "Ele z y \<Longrightarrow> EFVars z \<inter> GVrs2 x = {} \<Longrightarrow> y \<in> GSupp1 x \<union> GSupp2 x \<Longrightarrow> Ele z (Ector x)"

lemma Ector_eta_inj: "Ector x = Ector (\<eta> a) \<longleftrightarrow> x = \<eta> a"
  unfolding Ector_inject
  apply safe
  subgoal for \<sigma>
    apply (drule arg_cong[where f = "Gsub id (inv \<sigma>) o Gmap (Eperm (inv \<sigma>)) id"])
    apply (auto simp: eta_natural supp_id_bound supp_inv_bound G.Map_comp[THEN fun_cong, simplified]
        G.Map_Sb[THEN fun_cong, simplified] G.Sb_comp[THEN fun_cong, simplified]
        G.Map_id G.Sb_Inj Eperm_comp Eperm_id)
    done
  subgoal
    apply (auto simp: eta_natural supp_id_bound)
    done
  done

lemma Ector_eta'_inj: "Ector x = Ector (\<eta>' a) \<longleftrightarrow> x = \<eta>' a"
  unfolding Ector_inject
  apply safe
  subgoal for \<sigma>
    apply (drule arg_cong[where f = "Gsub id (inv \<sigma>) o Gmap (Eperm (inv \<sigma>)) id"])
    apply (auto simp: eta'_natural supp_id_bound supp_inv_bound G.Map_comp[THEN fun_cong, simplified]
        G.Map_Sb[THEN fun_cong, simplified] G.Sb_comp[THEN fun_cong, simplified]
        G.Map_id G.Sb_Inj Eperm_comp Eperm_id)
    done
  subgoal
    apply (auto simp: eta'_natural supp_id_bound)
    done
  done

lemma Ector_eta_inj': "Ector (\<eta> a) = Ector x  \<longleftrightarrow> x = \<eta> a"
  using Ector_eta_inj by metis

lemma Ector_eta'_inj': "Ector (\<eta>' a) = Ector x  \<longleftrightarrow> x = \<eta>' a"
  using Ector_eta'_inj by metis

(*
lemma "Ele (Ector (\<eta> a)) x \<Longrightarrow> x = Ector (\<eta> a)"
  apply (induct x rule: Ele.induct)
  apply (auto simp: Ector_eta_inj)
*)

lemma GVrs_eta[simp]: "GVrs1 (\<eta> a) = {a}" "GVrs2 (\<eta> a) = {}"
  sorry

lemma GVrs_eta'[simp]: "GVrs1 (\<eta>' a) = {a}" "GVrs2 (\<eta>' a) = {}"
  sorry

lemma GSupp_eta[simp]: "GSupp1 (\<eta> a) = {}" "GSupp2 (\<eta> a) = {}"
  sorry

lemma GSupp_eta'[simp]: "GSupp1 (\<eta>' a) = {}" "GSupp2 (\<eta>' a) = {}"
  sorry

lemma EFVrs\<eta>_Ector_eta: "EFVrs\<eta> (Ector (\<eta> a)) = {a}"
  unfolding EFVrs\<eta>_def
  apply (auto intro: Efree\<eta>.intros)
  subgoal for x
    apply (induct "Ector (\<eta> a)" pred: Efree\<eta>)
      apply (auto simp: Ector_eta_inj dest: eta_inj)
    done
  done

lemma EFVrs\<eta>'_Ector_eta': "EFVrs\<eta>' (Ector (\<eta>' a)) = {a}"
  unfolding EFVrs\<eta>'_def
  apply (auto intro: Efree\<eta>'.intros)
  subgoal for x
    apply (induct "Ector (\<eta>' a)" pred: Efree\<eta>')
      apply (auto simp: Ector_eta'_inj dest: eta'_inj)
    done
  done

lemma Efree_alt:
  "Efreee a e \<longleftrightarrow> a \<in> EFVrs e"
  "Efree\<eta> a e \<longleftrightarrow> a \<in> EFVrs\<eta> e"
  "Efree\<eta>' a e \<longleftrightarrow> a \<in> EFVrs\<eta>' e"
  unfolding EFVrs_def EFVrs\<eta>_def EFVrs\<eta>'_def by auto

lemma Efreee_Efree: "Efreee a e \<Longrightarrow> Efree a e"
  by (induct e pred: Efreee) (auto intro: Efree.intros)

lemma Efree\<eta>_Efree: "Efree\<eta> a e \<Longrightarrow> Efree a e"
  by (induct e pred: Efree\<eta>) (auto intro: Efree.intros)

lemma Efree\<eta>'_Efree: "Efree\<eta>' a e \<Longrightarrow> Efree a e"
  by (induct e pred: Efree\<eta>') (auto intro: Efree.intros)

lemma Ele_EFVars: "Ele t u \<Longrightarrow> a \<in> EFVars t \<Longrightarrow> a \<in> EFVars u"
  unfolding EFVars_def mem_Collect_eq
  by (induct u pred: Ele) (auto simp: EFVars_def elim!: Efree.intros)

lemma Ele_EFVrs: "Ele t u \<Longrightarrow> a \<in> EFVrs t \<Longrightarrow> a \<in> EFVrs u"
  unfolding EFVrs_def mem_Collect_eq
  by (induct u pred: Ele) (auto simp: EFVars_def dest: Efreee_Efree elim!: Efreee.intros)

lemma Ele_EFVrs\<eta>: "Ele t u \<Longrightarrow> a \<in> EFVrs\<eta> t \<Longrightarrow> a \<in> EFVrs\<eta> u"
  unfolding EFVrs\<eta>_def mem_Collect_eq
  by (induct u pred: Ele) (auto simp: EFVars_def dest: Efree\<eta>_Efree elim!: Efree\<eta>.intros(2,3))

lemma Ele_EFVrs\<eta>': "Ele t u \<Longrightarrow> a \<in> EFVrs\<eta>' t \<Longrightarrow> a \<in> EFVrs\<eta>' u"
  unfolding EFVrs\<eta>'_def mem_Collect_eq
  by (induct u pred: Ele) (auto simp: EFVars_def dest: Efree\<eta>'_Efree elim!: Efree\<eta>'.intros(2,3))

lemma EFVrs_Ector: "\<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow>
  EFVrs (Ector u) = GVrs1 u \<union> ((\<Union>a \<in> GSupp1 u. EFVrs a) - GVrs2 u) \<union> (\<Union>a \<in> GSupp2 u. EFVrs a)"
  sorry

lemma G_Sb_cong:
  fixes f1 f2 g1 g2 :: "'a :: var \<Rightarrow> 'a"
  shows
  "|supp f1| <o |UNIV::'a set| \<Longrightarrow> |supp f2| <o |UNIV::'a set| \<Longrightarrow>
   |supp g1| <o |UNIV::'a set| \<Longrightarrow> |supp g2| <o |UNIV::'a set| \<Longrightarrow>
   x = y \<Longrightarrow>
   (\<And>a1. a1 \<in> GVrs1 x \<Longrightarrow> f1 a1 = g1 a1) \<Longrightarrow>
   (\<And>a2. a2 \<in> GVrs2 x \<Longrightarrow> f2 a2 = g2 a2) \<Longrightarrow> Gsub f1 f2 x = Gsub g1 g2 y"
  by hypsubst (rule G.Sb_cong)
(*
lemma
  assumes "|supp (\<delta>2 :: 'a::var \<Rightarrow> 'a)| <o |UNIV :: 'a set|"
  shows "\<forall>a. u \<noteq> \<eta> a \<Longrightarrow>
  \<forall>a. Gsub \<delta>2 id (Gmap (Esub \<delta>2 \<rho>2 \<rho>2') (Esub \<delta>2 \<rho>2 \<rho>2') u) \<noteq> \<eta> a"
  apply (erule contrapos_pp)
  apply auto
  subgoal premises prems for a
    apply (insert arg_cong[where f=GVrs1, OF prems])
    apply (auto simp: G.Vrs_Sb G.Vrs_Map supp_id_bound assms set_eq_iff)
    apply (drule spec[of _ a])
    apply simp
    apply (erule imageE)
    subgoal for x
      apply (rule exI[of _ x])
      using prems
  subgoal for a
*)

(*
lemma
  assumes
   "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
   "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
   "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
   "Gsub \<delta> id (Gmap \<rho> \<rho>' u) = \<eta> a"
  shows "\<exists>b. u = \<eta> b"
  apply (insert arg_cong[where f = GVrs1, OF assms(4)])
  apply (insert arg_cong[where f = GVrs2, OF assms(4)])
  apply (insert arg_cong[where f = GSupp1, OF assms(4)])
  apply (insert arg_cong[where f = GSupp2, OF assms(4)])
  apply (auto simp: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map assms(1-3) supp_id_bound)
*)
lemma 
  assumes
   "z \<in> EFVrs x"
   "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
   "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
   "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
  shows "\<delta> z \<in> EFVrs (Esub \<delta> \<rho> \<rho>' x)"
  using assms unfolding EFVrs_def mem_Collect_eq
  apply (induct x rule: Efreee_strong_induct[rotated, consumes 1, where V = "imsupp \<delta> \<union> IImsupp (Ector o \<eta>) EFVrs\<eta> \<rho> \<union> IImsupp (Ector o \<eta>') EFVrs\<eta>' \<rho>'"])
     apply (subst Esub_Ector; (simp add: Int_Un_distrib)?)
     apply (rule Efreee.intros)
       apply (simp add: G.Vrs_Sb G.Vrs_Map supp_id_bound)
  subgoal sorry
  subgoal sorry
    apply (subst Esub_Ector; (simp add: Int_Un_distrib)?)
  apply fastforce
  apply fastforce
     apply (rule Efreee.intros(2))
      apply (simp add: G.Supp_Sb G.Supp_Map supp_id_bound)
      apply (erule imageI)
     apply assumption
    apply (simp add: G.Vrs_Sb G.Vrs_Map supp_id_bound)
    apply (metis imsupp_empty_IntD1)
    apply (subst Esub_Ector; (simp add: Int_Un_distrib)?)
  apply fastforce
  apply fastforce
     apply (rule Efreee.intros(3))
      apply (simp add: G.Supp_Sb G.Supp_Map supp_id_bound)
      apply (erule imageI)
   apply assumption
  apply (auto intro!: infinite_UNIV imsupp_supp_bound[THEN iffD2] assms IImsupp_bound Un_bound EFVrs_bound)
  done

(*
lemma "GVrs2 u' \<inter> EFVars e = {} \<Longrightarrow> \<exists>u. e = Ector u \<and> GVrs2 u = GVrs2 u'"
*)

lemma Esub_inversion:
  assumes 
   "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
   "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
   "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
  shows
  "GVrs2 u \<inter> (imsupp \<delta> \<union> IImsupp (Ector o \<eta>) EFVrs\<eta> \<rho> \<union> IImsupp (Ector o \<eta>') EFVrs\<eta>' \<rho>' \<union> EFVars e) = {} \<Longrightarrow>
  Ector u = Esub \<delta> \<rho> \<rho>' e \<Longrightarrow> \<exists>u'. u = Gsub \<delta> id (Gmap \<rho> \<rho>' u') \<and> GVrs2 u' = GVrs2 u"
  sorry

lemma 
  assumes
   "z \<in> EFVrs (Esub \<delta> \<rho> \<rho>' e)"
   "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
   "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
   "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
  shows "
    z \<in> \<delta> ` EFVrs e \<union>
    ((\<Union>x\<in>EFVrs\<eta> e. EFVrs (\<rho> x)) \<union>
     (\<Union>x\<in>EFVrs\<eta>' e. EFVrs (\<rho>' x)))"
  using assms
  unfolding EFVrs_def EFVrs\<eta>_def EFVrs\<eta>'_def mem_Collect_eq Un_iff UN_iff bex_simps
  apply (induct "Esub \<delta> \<rho> \<rho>' e" arbitrary: e \<delta> \<rho> \<rho>' rule: Efreee_strong_induct[rotated, consumes 1])
  subgoal for u e \<delta> \<rho> \<rho>'
    apply (cases "\<exists>a. e = Ector (\<eta> a)")
     apply (auto simp: Esub_Ector) []
    apply (metis Efree\<eta>.intros(1) Efreee.intros(1))
    apply (cases "\<exists>a. e = Ector (\<eta>' a)")
     apply (auto simp: Esub_Ector) []
     apply (metis Efree\<eta>'.intros(1) Efreee.intros(1))
    apply (rule Ector_fresh_cases[of "imsupp \<delta> \<union> IImsupp (Ector o \<eta>) EFVrs\<eta> \<rho> \<union> IImsupp (Ector o \<eta>') EFVrs\<eta>' \<rho>'" e])
     apply (auto simp: infinite_UNIV Un_bound imsupp_supp_bound assms) []
     apply (hypsubst_thin)
    apply (subst (asm) Esub_Ector)
            apply (auto simp: Ector_eta_inj Ector_eta'_inj)
    apply (drule sym[of "Ector u"])
    apply (subst (asm) Ector_inject[of _ u])
    apply (auto simp: assms G.Vrs_Sb G.Vrs_Map supp_id_bound G.Map_comp[THEN fun_cong, simplified]
        G.Map_Sb[THEN fun_cong, simplified] G.Sb_comp[THEN fun_cong, simplified])
    apply (metis Efreee.intros(1) image_eqI mem_Collect_eq)
    done
  subgoal for e' u e \<delta> \<rho> \<rho>'
    apply (cases "\<exists>a. e = Ector (\<eta> a)")
     apply (auto simp: Esub_Ector assms) []
    apply (metis Efree\<eta>.intros(1) Efreee.intros(2))
    apply (cases "\<exists>a. e = Ector (\<eta>' a)")
     apply (auto simp: Esub_Ector assms) []
     apply (metis Efree\<eta>'.intros(1) Efreee.intros(2))
    apply (rule Ector_fresh_cases[of "imsupp \<delta> \<union> IImsupp (Ector o \<eta>) EFVrs\<eta> \<rho> \<union> IImsupp (Ector o \<eta>') EFVrs\<eta>' \<rho>' \<union> GVrs2 u" e])
     apply (auto simp: infinite_UNIV Un_bound imsupp_supp_bound assms G.Vrs_bd) []
    subgoal sorry
     apply (hypsubst_thin)
    apply (subst (asm) Esub_Ector)
            apply (auto simp: Ector_eta_inj Ector_eta'_inj) [8]
    apply (drule sym[of "Ector u"])
    apply (subst (asm) Ector_inject[of _ u])
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (simp add: G.Vrs_Sb G.Vrs_Map G.Supp_Sb G.Supp_Map supp_id_bound G.Map_comp[THEN fun_cong, simplified]
        G.Map_Sb[THEN fun_cong, simplified] G.Sb_comp[THEN fun_cong, simplified]
        Eperm_Esub Eperm_Esub[THEN fun_cong, simplified] Int_Un_distrib)
    apply (erule imageE conjE)+
    apply hypsubst_thin
    subgoal for u' \<sigma> e''
    apply (drule meta_spec)+
    apply (drule meta_mp)
    apply (rule refl)
    apply (drule meta_mp)
       apply (meson supp_comp_bound supp_inv_bound infinite_UNIV)
    apply (drule meta_mp)
      subgoal
      sorry
    apply (drule meta_mp)
    subgoal sorry
    apply (elim disj_forward)
    subgoal
      apply (erule imageE CollectE)+
      apply (unfold o_apply mem_Collect_eq image_iff Bex_def)
      subgoal for x
        apply (cases "inv \<sigma> x \<in> GVrs2 u'")
         apply (metis imsupp_empty_IntD1)
        apply (cases "\<delta> (inv \<sigma> x) \<in> GVrs2 u'")
         apply blast
        
         apply (rule exI conjI[rotated])+
         apply assumption
        
        sorry
      done
    apply (auto simp: id_on_def)
    oops

definition "restrict \<delta>1 \<delta>2 \<iota> a  = (if \<delta>1 a = \<delta>2 a then \<delta>1 a else \<iota> a)"

definition Ein where
  "Ein A B B' = {x. EFVrs x \<subseteq> A \<and> EFVrs\<eta> x \<subseteq> B \<and> EFVrs\<eta>' x \<subseteq> B'}"

lemma Ein_mono: "A1 \<subseteq> A2 \<Longrightarrow> B1 \<subseteq> B2 \<Longrightarrow> B1' \<subseteq> B2' \<Longrightarrow> Ein A1 B1 B1' \<subseteq> Ein A2 B2 B2'"
  unfolding Ein_def by auto

pbmv_monad "'a::var E"
  Sbs: Esub
  RVrs: EFVrs
  Injs: "Ector o \<eta>" "Ector o \<eta>'"
  Vrs: EFVrs\<eta> EFVrs\<eta>'
  bd: natLeq
  subgoal
    by (rule infinite_regular_card_order_natLeq)
  subgoal
    apply (rule Esub_unique_fresh[symmetric, where A="{}"])
         apply (simp_all add: supp_id_bound G.Sb_Inj G.Map_id)
    done
  subgoal for \<delta> \<rho> \<rho>'
    by (simp add: fun_eq_iff Esub_Ector)
  subgoal
    by (simp add: fun_eq_iff Esub_Ector)
  subgoal for \<delta>1 \<rho>1 \<rho>1' \<delta>2 \<rho>2 \<rho>2'
    apply (rule Esub_unique_fresh[where A = "imsupp \<delta>1 \<union> imsupp \<delta>2 \<union>
      IImsupp (Ector o \<eta>) EFVrs\<eta> \<rho>1 \<union> IImsupp (Ector o \<eta>) EFVrs\<eta> \<rho>2 \<union>
      IImsupp (Ector o \<eta>') EFVrs\<eta>' \<rho>1' \<union> IImsupp (Ector o \<eta>') EFVrs\<eta>' \<rho>2'"])
          apply (simp_all add: supp_comp_bound SSupp_comp_bound infinite_UNIV Esub_Ector Un_bound
            IImsupp_bound imsupp_supp_bound Int_Un_distrib)
    apply (subst Esub_Ector;
      (simp add: G.Vrs_Sb G.Vrs_Map supp_id_bound G.Map_comp[THEN fun_cong, simplified]
        G.Map_Sb[THEN fun_cong, simplified] G.Sb_comp[THEN fun_cong, simplified])?)
    subgoal sorry
    subgoal sorry
    done
  subgoal by (rule EFVrs_bd)
  subgoal by (rule EFVrs_bd)
  subgoal by (rule EFVrs_bd)
  subgoal for x
    by (auto simp: EFVrs_def Ector_eta_inj' elim: Efreee.cases)
  subgoal for x
    by (auto simp: EFVrs_def Ector_eta'_inj' elim: Efreee.cases)
  subgoal for x
    by (auto simp: EFVrs\<eta>_def Ector_eta_inj' eta_inj elim: Efree\<eta>.cases intro: Efree\<eta>.intros)
  subgoal for x
    by (auto simp: EFVrs\<eta>_def Ector_eta'_inj' eta_distinct elim: Efree\<eta>.cases)
  subgoal for x
    by (auto simp: EFVrs\<eta>'_def Ector_eta_inj' dest!: eta_distinct[THEN notE, OF sym] elim: Efree\<eta>'.cases)
  subgoal for x
    by (auto simp: EFVrs\<eta>'_def Ector_eta'_inj' eta'_inj elim: Efree\<eta>'.cases intro: Efree\<eta>'.intros)
  subgoal for \<delta> \<rho> \<rho>' x sorry
  subgoal for \<delta> \<rho> \<rho>' x sorry
  subgoal for \<delta> \<rho> \<rho>' x sorry
  subgoal for \<delta>1 \<rho>1 \<rho>1' \<delta>2 \<rho>2 \<rho>2' x
    apply (rule Esub_unique_fresh_relativized[where B = "{a. \<delta>1 a = \<delta>2 a}" and B\<eta> = "{a. \<rho>1 a = \<rho>2 a}" and B\<eta>' = "{a. \<rho>1' a = \<rho>2' a}" and
      A = "imsupp \<delta>2 \<union> IImsupp (Ector \<circ> \<eta>) EFVrs\<eta> \<rho>2 \<union> IImsupp (Ector \<circ> \<eta>') EFVrs\<eta>' \<rho>2'", symmetric
])
    subgoal sorry
    subgoal sorry
    subgoal sorry
    subgoal sorry
    subgoal sorry
    subgoal sorry
    subgoal sorry
    subgoal for a
      apply (subst Esub_Ector)
      subgoal sorry
      subgoal sorry
      subgoal sorry
      apply simp
      done
    subgoal for a
      apply (subst Esub_Ector)
      subgoal sorry
      subgoal sorry
      subgoal sorry
      apply simp
      done
    subgoal for u
       apply (subst Esub_Ector)
    subgoal sorry
    subgoal sorry
    subgoal sorry
    subgoal by (simp add: Int_Un_distrib)
    subgoal by (simp add: Int_Un_distrib)
    subgoal by (simp add: Int_Un_distrib)
    subgoal by assumption
    subgoal by assumption
    apply (rule arg_cong[where f = Ector])
    apply (rule G.Sb_cong)
    subgoal sorry
    subgoal sorry
    subgoal sorry
      apply (auto simp: supp_id_bound G.Vrs_Map)
    apply (simp add: Collect_mono_iff EFVrs_def Efreee.intros(1))
    done
    apply auto
  done
  done

(*
      apply (subst Ector_inject)
      apply (rule exI[of _ \<sigma>])
      apply (rule context_conjI)
      subgoal sorry
      apply (rule context_conjI)
      subgoal sorry
      apply (rule context_conjI)
      subgoal sorry
      apply (subst G.Map_Sb[THEN fun_cong, simplified]; (simp add: supp_id_bound)?)
      subgoal sorry
      apply (subst G.Sb_comp[THEN fun_cong, simplified]; (simp add: supp_id_bound)?)
      subgoal sorry
      apply (subst G.Map_comp[THEN fun_cong, simplified]; (simp add: supp_id_bound)?)
*)
      apply (rule G_Sb_cong; (simp add: supp_id_bound)?)
    subgoal sorry
    apply (subst (asm) G.Vrs_Map)
    apply (simp add: restrict_def)
    done
apply (rule Esub_unique_fresh[where A = "imsupp \<delta>2 \<union> IImsupp (Ector \<circ> \<eta>) EFVrs\<eta> \<rho>2 \<union> IImsupp (Ector \<circ> \<eta>') EFVrs\<eta>' \<rho>2' \<union> EFVars x" and
       h="\<lambda>y. Esub (restrict \<delta>2 \<delta>1)
                   (restrict \<rho>2 \<rho>1)
                   (restrict \<rho>2' \<rho>1') y", THEN fun_cong])
           apply (auto 0 0 simp: Esub_Ector imsupp_supp_bound infinite_UNIV IImsupp_bound Un_bound Int_Un_distrib
             EFVrs\<eta>_Ector_eta EFVrs\<eta>'_Ector_eta' supp_id_bound G.Vrs_Map restrict_def
             dest: Ele_EFVrs\<eta> Ele_EFVrs\<eta>')
    apply (subst Esub_Ector)
  subgoal sorry
  subgoal sorry
  subgoal sorry
    apply (simp add: restrict_def)

         apply (rule arg_cong2[THEN cong, THEN cong, where f2 = Esub])
        apply (auto simp: restrict_def fun_eq_iff)
        subgoal sorry
        subgoal for z a
      thm arg_cong2[THEN cong, THEN cong, where f2 = Esub]
(*
      apply (intro arg_cong[where f = Ector] G_Sb_cong G.Map_cong; (simp add: supp_id_bound)?)
        apply (safe; simp?)
*)

    subgoal for u a z
      apply (cases "z \<in> GVrs2 u")
      subgoal sorry
      subgoal by auto
      done
    done
    thm  G.Sb_cong[no_vars]
    
    thm EFVrs\<eta>_Ector_eta
    sorry
  sorry

end