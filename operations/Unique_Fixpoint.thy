theory Unique_Fixpoint
  imports "Binders.MRBNF_Recursor" "../operations/BMV_Monad"
begin

declare supp_id_bound[simp] supp_inv_bound[simp] infinite_UNIV[simp]

abbreviation "IImsupp' Inj Vr \<rho> \<equiv> SSupp Inj \<rho> \<union> IImsupp Inj Vr \<rho>"

(*
binder_datatype 'a expr =
  Var 'a
 | Lam x::'a t::"'a expr" binds x in t
 | App "'a expr" "'a expr"

thm subshape_expr_expr.intros

thm expr.strong_induct

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
  apply (rule Un_bound[OF ])
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
    Abs_expr_pre_inverse Abs_expr_pre_inject expr.FVars_permute)
  apply (subst expr.tvsubst_cctor_not_isVVr)
  apply (simp_all add: assms(1) noclash_expr_def expr.TT_inject0 tvisVVr_tvsubst_expr_def tvVVr_tvsubst_expr_def tv\<eta>_expr_tvsubst_expr_def
    set1_expr_pre_def set2_expr_pre_def set3_expr_pre_def set4_expr_pre_def map_expr_pre_def
    Abs_expr_pre_inverse Abs_expr_pre_inject \<rho>)
  apply (rule exI[of _ id]; simp add: expr.permute_id)
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

axiomatization where
  eta_inversion: "\<And>\<delta>1 f1 f2 u a. |supp \<delta>1| <o |UNIV::'a1 set| \<Longrightarrow>
   Gsub \<delta>1 id (Gmap f1 f2 u) = (\<eta> a :: ('a1::var, 'a2 :: var, 'x1, 'x2) G) \<Longrightarrow> \<exists>y. u = \<eta> y"
  and eta_natural: "\<And>\<delta>1 \<delta>2 f1 f2 a. |supp \<delta>1| <o |UNIV::'a1 set| \<Longrightarrow> |supp \<delta>2| <o |UNIV::'a2 set| \<Longrightarrow>
   Gsub \<delta>1 \<delta>2 (Gmap f1 f2 (\<eta> a :: ('a1::var, 'a2 :: var, 'x1, 'x2) G)) = \<eta> (\<delta>1 a)"
  and eta_mem: "\<And>a. a \<in> GVrs1 (\<eta> a :: ('a1::var, 'a2 :: var, 'x1, 'x2) G)"
  and eta'_inversion: "\<And>\<delta>1 f1 f2 u a. |supp \<delta>1| <o |UNIV::'a1 set| \<Longrightarrow>
   Gsub \<delta>1 id (Gmap f1 f2 u) = \<eta>' a \<Longrightarrow> \<exists>y. u = \<eta>' y"
  and eta'_natural: "\<And>\<delta>1 \<delta>2 f1 f2 a. |supp \<delta>1| <o |UNIV::'a1 set| \<Longrightarrow> |supp \<delta>2| <o |UNIV::'a2 set| \<Longrightarrow>
   Gsub \<delta>1 \<delta>2 (Gmap f1 f2 (\<eta>' a :: ('a1::var, 'a2 :: var, 'x1, 'x2) G)) = \<eta>' (\<delta>1 a)"
  and eta'_mem: "\<And>a. a \<in> GVrs1 (\<eta>' a :: ('a1::var, 'a2 :: var, 'x1, 'x2) G)"
  and eta_inj: "\<And>a a'. \<eta> a = \<eta> a' \<Longrightarrow> a = a'"
  and eta'_inj: "\<And>a a'. \<eta>' a = \<eta>' a' \<Longrightarrow> a = a'"
  and eta_distinct: "\<And>a a'. \<eta> a \<noteq> \<eta>' a'"

typedecl 'a E
consts Ector :: "('a :: var, 'a, 'a E, 'a E) G \<Rightarrow> 'a E"
consts Eperm :: "('a :: var \<Rightarrow> 'a) \<Rightarrow> 'a E \<Rightarrow> 'a E"
consts EFVars :: "'a::var E \<Rightarrow> 'a set"

lemma Eperm_id: "Eperm id = id"
  sorry

lemma Eperm_comp:
  "bij (\<sigma> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>
   bij (\<tau> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<tau>| <o |UNIV :: 'a set| \<Longrightarrow>
   Eperm \<sigma> o Eperm \<tau> = Eperm (\<sigma> o \<tau>)"
  sorry

lemma Ector_inject: "(Ector x = Ector y) =
(\<exists>\<sigma> :: 'a :: var \<Rightarrow> 'a. bij \<sigma> \<and>
   |supp \<sigma>| <o |UNIV :: 'a set| \<and>
   id_on (\<Union> (EFVars ` GSupp1 x) - GVrs2 x) \<sigma> \<and>
   Gsub id \<sigma> (Gmap (Eperm \<sigma>) id x) = y)"
  sorry

lemma EFVars_Ector:
  "EFVars (Ector u::('a::var) E) = GVrs1 u \<union> \<Union> {EFVars e | e .  e \<in> GSupp2 u} \<union> \<Union> {EFVars e - GVrs2 u | e .  e \<in> GSupp1 u}"
  sorry

consts Esub :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a ::var \<Rightarrow> 'a E) \<Rightarrow> ('a ::var \<Rightarrow> 'a E) \<Rightarrow> 'a E \<Rightarrow> 'a E"

lemma Esub_Ector:
  assumes
    "|supp (\<delta> :: 'a \<Rightarrow> 'a :: var)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>) (\<rho>::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set|"
    "|SSupp (Ector o \<eta>') (\<rho>'::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set|"
  shows
    "Esub \<delta> \<rho> \<rho>' (Ector (\<eta> a)) = \<rho> a"
    "Esub \<delta> \<rho> \<rho>' (Ector (\<eta>' a)) = \<rho>' a"
    "GVrs2 u \<inter> imsupp \<delta> = {} \<Longrightarrow>
  GVrs2 u \<inter> IImsupp' (Ector o \<eta>) EFVars \<rho> = {} \<Longrightarrow>
  GVrs2 u \<inter> IImsupp' (Ector o \<eta>') EFVars \<rho>' = {} \<Longrightarrow>
  \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow>
  Esub \<delta> \<rho> \<rho>' (Ector u) = Ector (Gsub \<delta> id (Gmap (Esub \<delta> \<rho> \<rho>') (Esub \<delta> \<rho> \<rho>') u))"
  sorry

lemma Esub_inversion:
  assumes 
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) (\<rho> :: 'a \<Rightarrow> 'a E)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') (\<rho>' :: 'a \<Rightarrow> 'a E)| <o |UNIV :: 'a set|"
  shows
    "GVrs2 u \<inter> (imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EFVars \<rho> \<union> IImsupp' (Ector o \<eta>') EFVars \<rho>') = {} \<Longrightarrow> Enoclash u \<Longrightarrow>
 Ector u = Esub \<delta> \<rho> \<rho>' e \<Longrightarrow> \<exists>u'. u = Gsub \<delta> id (Gmap (Esub \<delta> \<rho> \<rho>') (Esub \<delta> \<rho> \<rho>') u') \<and> GVrs2 u' = GVrs2 u \<and> e = Ector u'"
  sorry

lemma EFVars_bd:
  "|EFVars (x :: 'a :: var E)| <o natLeq"
  sorry

inductive Efreee for a where 
  "a \<in> GVrs1 u \<Longrightarrow> \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow> Efreee a (Ector u)"
| "e \<in> GSupp1 u \<Longrightarrow> Efreee a e \<Longrightarrow> a \<notin> GVrs2 u \<Longrightarrow> Efreee a (Ector u)"
| "e \<in> GSupp2 u \<Longrightarrow> Efreee a e \<Longrightarrow> Efreee a (Ector u)"

definition "Enoclash u = (GVrs2 u \<inter> EFVars (Ector u) = {})"

lemma Efreee_strong_induct: "|A::'a set| <o |UNIV :: 'a ::var set| \<Longrightarrow> Efreee a e \<Longrightarrow>
(\<And>u. GVrs2 u \<inter> A = {} \<Longrightarrow> Enoclash u \<Longrightarrow> a \<in> GVrs1 u \<Longrightarrow> \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow> P (Ector u)) \<Longrightarrow>
(\<And>e u. GVrs2 u \<inter> A = {} \<Longrightarrow> Enoclash u \<Longrightarrow> e \<in> GSupp1 u \<Longrightarrow> Efreee a e \<Longrightarrow> P e \<Longrightarrow> a \<notin> GVrs2 u \<Longrightarrow> P (Ector u)) \<Longrightarrow>
(\<And>e u. GVrs2 u \<inter> A = {} \<Longrightarrow> Enoclash u \<Longrightarrow> e \<in> GSupp2 u \<Longrightarrow> Efreee a e \<Longrightarrow> P e \<Longrightarrow> P (Ector u)) \<Longrightarrow> P e"
  sorry

inductive Efree\<eta> for a where 
  "Efree\<eta> a (Ector (\<eta> a))"
| "e \<in> GSupp1 u \<Longrightarrow> Efree\<eta> a e \<Longrightarrow> a \<notin> GVrs2 u \<Longrightarrow> Efree\<eta> a (Ector u)"
| "e \<in> GSupp2 u \<Longrightarrow> Efree\<eta> a e \<Longrightarrow> Efree\<eta> a (Ector u)"

lemma Efree\<eta>_strong_induct: "|A::'a set| <o |UNIV :: 'a ::var set| \<Longrightarrow> Efree\<eta> a x \<Longrightarrow>
P (Ector (\<eta> a)) \<Longrightarrow>
(\<And>e u. GVrs2 u \<inter> A = {} \<Longrightarrow> Enoclash u \<Longrightarrow> e \<in> GSupp1 u \<Longrightarrow> Efree\<eta> a e \<Longrightarrow> P e \<Longrightarrow> a \<notin> GVrs2 u \<Longrightarrow> P (Ector u)) \<Longrightarrow>
(\<And>e u. GVrs2 u \<inter> A = {} \<Longrightarrow> Enoclash u \<Longrightarrow> e \<in> GSupp2 u \<Longrightarrow> Efree\<eta> a e \<Longrightarrow> P e \<Longrightarrow> P (Ector u)) \<Longrightarrow> P x"
  sorry

inductive Efree\<eta>' for a where 
  "Efree\<eta>' a (Ector (\<eta>' a))"
| "e \<in> GSupp1 u \<Longrightarrow> Efree\<eta>' a e \<Longrightarrow> a \<notin> GVrs2 u \<Longrightarrow> Efree\<eta>' a (Ector u)"
| "e \<in> GSupp2 u \<Longrightarrow> Efree\<eta>' a e \<Longrightarrow> Efree\<eta>' a (Ector u)"

lemma Efree\<eta>'_strong_induct: "|A::'a set| <o |UNIV :: 'a ::var set| \<Longrightarrow> Efree\<eta>' a x \<Longrightarrow>
P (Ector (\<eta>' a)) \<Longrightarrow>
(\<And>e u. GVrs2 u \<inter> A = {} \<Longrightarrow> Enoclash u \<Longrightarrow> e \<in> GSupp1 u \<Longrightarrow> Efree\<eta>' a e \<Longrightarrow> P e \<Longrightarrow> a \<notin> GVrs2 u \<Longrightarrow> P (Ector u)) \<Longrightarrow>
(\<And>e u. GVrs2 u \<inter> A = {} \<Longrightarrow> Enoclash u \<Longrightarrow> e \<in> GSupp2 u \<Longrightarrow> Efree\<eta>' a e \<Longrightarrow> P e \<Longrightarrow> P (Ector u)) \<Longrightarrow> P x"
  sorry

definition "EFVrs e = {a. Efreee a e}"
definition "EFVrs\<eta> e = {a. Efree\<eta> a e}"
definition "EFVrs\<eta>' e = {a. Efree\<eta>' a e}"

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
  GVrs2 u \<inter> IImsupp' (Ector o \<eta>) EFVars \<rho> = {} \<Longrightarrow>
  GVrs2 u \<inter> IImsupp' (Ector o \<eta>') EFVars \<rho>' = {} \<Longrightarrow>
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
  GVrs2 u \<inter> IImsupp' (Ector o \<eta>) EFVars \<rho> = {} \<Longrightarrow>
  GVrs2 u \<inter> IImsupp' (Ector o \<eta>') EFVars \<rho>' = {} \<Longrightarrow>
  \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow>
  h (Ector u) = Ector (Gsub \<delta> id (Gmap h h u))"
  shows
    "h = Esub \<delta> \<rho> \<rho>'"
  apply (rule ext)
  apply (rule Esub_unique_fresh_relativized[where B=UNIV and B\<eta>=UNIV and B\<eta>'=UNIV and A=A])
              apply (auto intro!: assms)
  done

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
  apply (auto simp: Un_bound)
  done

lemma SSupp_comp_bound'[simp]:
  "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set| \<Longrightarrow>
  |SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set| \<Longrightarrow>
  |SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set| \<Longrightarrow>
  |SSupp (Ector \<circ> \<eta>') \<rho>''| <o |UNIV :: 'a set| \<Longrightarrow>
  |SSupp (Ector \<circ> \<eta>') (Esub \<delta> \<rho> \<rho>' \<circ> \<rho>'')| <o |UNIV :: 'a set|"
  apply (rule ordLeq_ordLess_trans)
   apply (erule (2) card_of_mono1[OF SSupp_comp_Esub_le(2)])
  apply (auto simp: Un_bound)
  done

lemma IImsupp_bound[simp]:
  "|SSupp Inj (\<rho> :: 'a::var \<Rightarrow> _)| <o |UNIV :: 'a set| \<Longrightarrow> (\<And>x. |Vr (\<rho> x)| <o |UNIV :: 'a set| ) \<Longrightarrow>
  |IImsupp' Inj (Vr :: _ \<Rightarrow> 'a set) \<rho>| <o |UNIV :: 'a set|"
  unfolding IImsupp_def
  by (auto simp: Un_bound UN_bound)

lemma Ector_eta_inj: "Ector u = Ector (\<eta> a) \<longleftrightarrow> u = \<eta> a"
  by (metis Ector_inject eta_natural supp_id_bound)

lemma Ector_eta'_inj: "Ector u = Ector (\<eta>' a) \<longleftrightarrow> u = \<eta>' a"
  unfolding Ector_inject
  apply safe
  subgoal for \<sigma>
    apply (drule arg_cong[where f = "Gsub id (inv \<sigma>) o Gmap (Eperm (inv \<sigma>)) id"])
    apply (auto simp: eta'_natural G.Map_comp[THEN fun_cong, simplified]
        G.Map_Sb[THEN fun_cong, simplified] G.Sb_comp[THEN fun_cong, simplified]
        G.Map_id G.Sb_Inj Eperm_comp Eperm_id)
    done
  subgoal
    apply (auto simp: eta'_natural)
    done
  done

lemma Ector_eta_inj': "Ector (\<eta> a) = Ector x \<longleftrightarrow> x = \<eta> a"
  using Ector_eta_inj by metis

lemma Ector_eta'_inj': "Ector (\<eta>' a) = Ector x \<longleftrightarrow> x = \<eta>' a"
  using Ector_eta'_inj by metis

lemma GVrs_eta[simp]:
  "GVrs1 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = {a}"
  "GVrs2 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = {}"
proof safe
  fix b assume b: "b \<in> GVrs1 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)"
  { assume "a \<noteq> b"
    then have *: "\<eta> a = Gsub (b \<leftrightarrow> c) id (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)" if "c \<notin> {a, b}" for c
      using eta_natural[of "b \<leftrightarrow> c" id id id a, symmetric, simplified] that
      by (auto simp: G.Map_id)
    have "c \<in> GVrs1 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)" if "c \<notin> {a, b}" for c
      using that b
      apply (subst (asm) *)
       apply (simp_all add: G.Vrs_Sb)
      apply (auto simp: swap_def)
      done
    with b have False
      apply simp
      by (smt (verit) G.Vrs_bd(1) UNIV_cinfinite UNIV_eq_I
          cinfinite_imp_infinite eta_mem finite_iff_ordLess_natLeq)
  }
  then show "b = a"
    by blast
next
  fix b :: 'a2 assume "b \<in> GVrs2 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)"
  then have "c \<in> GVrs2 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)" for c :: 'a2
    by (subst eta_natural[of id "b \<leftrightarrow> c" id id a, symmetric, simplified])
      (auto simp: G.Vrs_Sb  G.Map_id image_iff intro!: bexI[of _ b])
  then have "GVrs2 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = UNIV"
    by blast
  then show "b \<in> {}"
    by (metis G.Vrs_bd(2) finite_iff_ordLess_natLeq infinite_UNIV)
qed (rule eta_mem)

lemma GVrs_eta'[simp]:
  "GVrs1 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = {a}"
  "GVrs2 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = {}"
proof safe
  fix b assume b: "b \<in> GVrs1 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)"
  { assume "a \<noteq> b"
    then have *: "\<eta>' a = Gsub (b \<leftrightarrow> c) id (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)" if "c \<notin> {a, b}" for c
      using eta'_natural[of "b \<leftrightarrow> c" id id id a, symmetric, simplified] that
      by (auto simp: G.Map_id)
    have "c \<in> GVrs1 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)" if "c \<notin> {a, b}" for c
      using that b
      apply (subst (asm) *)
       apply (simp_all add: G.Vrs_Sb)
      apply (auto simp: swap_def)
      done
    with b have False
      apply simp
      by (smt (verit) G.Vrs_bd(1) UNIV_cinfinite UNIV_eq_I
          cinfinite_imp_infinite eta'_mem finite_iff_ordLess_natLeq)
  }
  then show "b = a"
    by blast
next
  fix b :: 'a2 assume "b \<in> GVrs2 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)"
  then have "c \<in> GVrs2 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)" for c :: 'a2
    by (subst eta'_natural[of id "b \<leftrightarrow> c" id id a, symmetric, simplified])
      (auto simp: G.Vrs_Sb  G.Map_id image_iff intro!: bexI[of _ b])
  then have "GVrs2 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = UNIV"
    by blast
  then show "b \<in> {}"
    by (metis G.Vrs_bd(2) finite_iff_ordLess_natLeq infinite_UNIV)
qed (rule eta'_mem)

lemma GSupp_eta[simp]:
  "GSupp1 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = {}"
  "GSupp2 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = {}"
proof safe
  fix b :: 'x1 assume "b \<in> GSupp1 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)"
  then have "c \<in> GSupp1 (\<eta> a :: ('a1 ::var, 'a2 :: var, nat, 'x2) G)" for c :: nat
    by (subst eta_natural[of id id "\<lambda>x. if x = b then c else 0" id a, symmetric, simplified])
      (auto simp: G.Supp_Sb  G.Supp_Map image_iff intro!: bexI[of _ b])
  then have "GSupp1 (\<eta> a :: ('a1 ::var, 'a2 :: var, nat, 'x2) G) = UNIV"
    by blast
  then show "b \<in> {}"
    by (metis G.Supp_bd(1) finite_iff_ordLess_natLeq infinite_UNIV)
next
  fix b :: 'x2 assume "b \<in> GSupp2 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)"
  then have "c \<in> GSupp2 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, nat) G)" for c :: nat
    by (subst eta_natural[of id id id "\<lambda>x. if x = b then c else 0" a, symmetric, simplified])
      (auto simp: G.Supp_Sb  G.Supp_Map image_iff intro!: bexI[of _ b])
  then have "GSupp2 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, nat) G) = UNIV"
    by blast
  then show "b \<in> {}"
    by (metis G.Supp_bd(2) finite_iff_ordLess_natLeq infinite_UNIV)
qed

lemma GSupp_eta'[simp]:
  "GSupp1 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = {}"
  "GSupp2 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = {}"
proof safe
  fix b :: 'x1 assume "b \<in> GSupp1 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)"
  then have "c \<in> GSupp1 (\<eta>' a :: ('a1 ::var, 'a2 :: var, nat, 'x2) G)" for c :: nat
    by (subst eta'_natural[of id id "\<lambda>x. if x = b then c else 0" id a, symmetric, simplified])
      (auto simp: G.Supp_Sb  G.Supp_Map image_iff intro!: bexI[of _ b])
  then have "GSupp1 (\<eta>' a :: ('a1 ::var, 'a2 :: var, nat, 'x2) G) = UNIV"
    by blast
  then show "b \<in> {}"
    by (metis G.Supp_bd(1) finite_iff_ordLess_natLeq infinite_UNIV)
next
  fix b :: 'x2 assume "b \<in> GSupp2 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)"
  then have "c \<in> GSupp2 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, nat) G)" for c :: nat
    by (subst eta'_natural[of id id id "\<lambda>x. if x = b then c else 0" a, symmetric, simplified])
      (auto simp: G.Supp_Sb  G.Supp_Map image_iff intro!: bexI[of _ b])
  then have "GSupp2 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, nat) G) = UNIV"
    by blast
  then show "b \<in> {}"
    by (metis G.Supp_bd(2) finite_iff_ordLess_natLeq infinite_UNIV)
qed

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

lemma Efreee_Efree: "Efreee a e \<Longrightarrow> a \<in> EFVars e"
  by (induct e pred: Efreee) (auto simp: EFVars_Ector)
lemma Efree\<eta>_Efree: "Efree\<eta> a e \<Longrightarrow> a \<in> EFVars e"
  by (induct e pred: Efree\<eta>) (auto simp: EFVars_Ector)
lemma Efree\<eta>'_Efree: "Efree\<eta>' a e \<Longrightarrow> a \<in> EFVars e"
  by (induct e pred: Efree\<eta>') (auto simp: EFVars_Ector)

lemma EFVrs_bd:
  "|EFVrs (x :: 'a :: var E)| <o natLeq"
  "|EFVrs\<eta> (x :: 'a :: var E)| <o natLeq"
  "|EFVrs\<eta>' (x :: 'a :: var E)| <o natLeq"
  apply (meson EFVars_bd Efree_alt(1) Efreee_Efree card_of_subset_bound subset_eq)
  apply (meson EFVars_bd Efree_alt(2) Efree\<eta>_Efree card_of_subset_bound subset_eq)
  apply (meson EFVars_bd Efree_alt(3) Efree\<eta>'_Efree card_of_subset_bound subset_eq)
  done

lemma EFVrs_bound[simp]:
  "|EFVars (x :: 'a :: var E)| <o |UNIV :: 'a set|"
  "|EFVrs (x :: 'a :: var E)| <o |UNIV :: 'a set|"
  "|EFVrs\<eta> (x :: 'a :: var E)| <o |UNIV :: 'a set|"
  "|EFVrs\<eta>' (x :: 'a :: var E)| <o |UNIV :: 'a set|"
  by (meson EFVars_bd EFVrs_bd FType_pre.var_large ordLess_ordLeq_trans)+

lemma EFVrs_EsubI1:
  assumes
    "z \<in> EFVrs e"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
  shows "\<delta> z \<in> EFVrs (Esub \<delta> \<rho> \<rho>' e)"
  using assms(1) unfolding EFVrs_def mem_Collect_eq
  apply (induct e rule: Efreee_strong_induct[rotated, consumes 1, where A = "imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EFVars \<rho> \<union> IImsupp' (Ector o \<eta>') EFVars \<rho>'"])
     apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(2-4))?)
     apply (rule Efreee.intros)
       apply (simp add: G.Vrs_Sb G.Vrs_Map assms(2-4))
  subgoal by (meson eta_inversion assms(2))
  subgoal by (meson eta'_inversion assms(2))
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(2-4))?)
      apply fastforce
     apply fastforce
    apply (rule Efreee.intros(2))
      apply (simp add: G.Supp_Sb G.Supp_Map assms(2-4))
      apply (erule imageI)
     apply assumption
    apply (simp add: G.Vrs_Sb G.Vrs_Map assms(2-4))
    apply (metis imsupp_empty_IntD1)
   apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(2-4))?)
     apply fastforce
    apply fastforce
   apply (rule Efreee.intros(3))
    apply (simp add: G.Supp_Sb G.Supp_Map assms(2-4))
    apply (erule imageI)
   apply assumption
  apply (auto intro!: imsupp_supp_bound[THEN iffD2] assms IImsupp_bound Un_bound EFVrs_bound)
  done

lemma EFVrs_EsubI2:
  assumes
    "a \<in> EFVrs\<eta> e" "z \<in> EFVrs (\<rho> a)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
  shows "z \<in> EFVrs (Esub \<delta> \<rho> \<rho>' e)"
  using assms(1,2) unfolding EFVrs_def EFVrs\<eta>_def mem_Collect_eq
  apply (induct e rule: Efree\<eta>_strong_induct[rotated, consumes 1, where A = "imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EFVars \<rho> \<union> IImsupp' (Ector o \<eta>') EFVars \<rho>'"])
     apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
      apply force
     apply force
    apply (rule Efreee.intros(2); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    apply (cases "\<rho> a = Ector (\<eta> a)")
     apply (metis Ector_eta_inj Efreee.cases GSupp_eta(1,2) empty_iff)
    apply (subgoal_tac "z \<in> IImsupp (Ector \<circ> \<eta>) EFVars \<rho>")
     apply blast
    apply (auto simp: IImsupp_def SSupp_def EFVrs\<eta>_def Efreee_Efree intro!: exI[of _ a]) []
   apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
     apply force
    apply force
   apply (rule Efreee.intros(3); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
  apply (auto intro!: imsupp_supp_bound[THEN iffD2] assms IImsupp_bound Un_bound EFVrs_bound)
  done

lemma EFVrs_EsubI3:
  assumes
    "a \<in> EFVrs\<eta>' e" "z \<in> EFVrs (\<rho>' a)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
  shows "z \<in> EFVrs (Esub \<delta> \<rho> \<rho>' e)"
  using assms(1,2) unfolding EFVrs_def EFVrs\<eta>'_def mem_Collect_eq
  apply (induct e rule: Efree\<eta>'_strong_induct[rotated, consumes 1, where A = "imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EFVars \<rho> \<union> IImsupp' (Ector o \<eta>') EFVars \<rho>'"])
     apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
      apply force
     apply force
    apply (rule Efreee.intros(2); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    apply (cases "\<rho>' a = Ector (\<eta>' a)")
     apply (metis Ector_eta'_inj Efreee.cases GSupp_eta'(1,2) empty_iff)
    apply (subgoal_tac "z \<in> IImsupp (Ector \<circ> \<eta>') EFVars \<rho>'")
     apply blast
    apply (auto simp: IImsupp_def SSupp_def EFVrs\<eta>_def Efreee_Efree intro!: exI[of _ a]) []
   apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
     apply force
    apply force
   apply (rule Efreee.intros(3); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
  apply (auto intro!: imsupp_supp_bound[THEN iffD2] assms IImsupp_bound Un_bound EFVrs_bound)
  done

lemma EFVrs_EsubD:
  assumes
    "z \<in> EFVrs (Esub \<delta> \<rho> \<rho>' e)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
  shows "
  z \<in> \<delta> ` EFVrs e \<union>
  ((\<Union>x\<in>EFVrs\<eta> e. EFVrs (\<rho> x)) \<union>
   (\<Union>x\<in>EFVrs\<eta>' e. EFVrs (\<rho>' x)))"
  using assms(1)
  unfolding EFVrs_def EFVrs\<eta>_def EFVrs\<eta>'_def mem_Collect_eq Un_iff UN_iff bex_simps
  apply (induct "Esub \<delta> \<rho> \<rho>' e" arbitrary: e rule:
      Efreee_strong_induct[rotated, consumes 1, where A = "imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EFVars \<rho> \<union> IImsupp' (Ector o \<eta>') EFVars \<rho>'"])
  subgoal for u e
    apply (cases "\<exists>a. e = Ector (\<eta> a)")
     apply (auto simp: Esub_Ector assms(2-4)) []
     apply (metis Efree\<eta>.intros(1) Efreee.intros(1))
    apply (cases "\<exists>a. e = Ector (\<eta>' a)")
     apply (auto simp: Esub_Ector assms(2-4)) []
     apply (metis Efree\<eta>'.intros(1) Efreee.intros(1))
    using assms(2-4)
    apply -
    apply (drule (5) Esub_inversion[rotated -1])
    apply simp
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (simp add: G.Vrs_Sb)
    unfolding G.Vrs_Map
    using Efreee.intros(1) by fastforce
  subgoal for e' u e
    using assms(2-4)
    apply -
    apply (drule (5) Esub_inversion[rotated -1])
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (simp add: Enoclash_def G.Supp_Sb G.Supp_Map G.Vrs_Sb Int_Un_distrib)
    unfolding G.Vrs_Map
    apply (erule imageE)
    apply hypsubst_thin
    apply (drule meta_spec, drule meta_mp, rule refl)
    subgoal for u' e'
      apply (elim disj_forward ex_forward; assumption?)
        apply (smt (verit, del_insts) Efreee.intros(2)
          Un_empty image_iff imsupp_empty_IntD1 mem_Collect_eq)
      subgoal for a
        apply (erule conjE)+
        apply (rule conjI[rotated])
         apply assumption
        apply (cases "\<rho> a = Ector (\<eta> a)")
         apply (metis Ector_eta_inj Efreee.cases GSupp_eta(1,2) empty_iff)
        apply (metis (mono_tags, lifting) Efree\<eta>.intros(2)
            IntI SSupp_def comp_apply empty_iff
            mem_Collect_eq)
        done
      subgoal for a
        apply (erule conjE)+
        apply (rule conjI[rotated])
         apply assumption
        apply (cases "\<rho>' a = Ector (\<eta>' a)")
         apply (metis Ector_eta'_inj Efreee.cases GSupp_eta'(1,2) empty_iff)
        apply (metis (mono_tags, lifting) Efree\<eta>'.intros(2)
            IntI SSupp_def comp_apply empty_iff
            mem_Collect_eq)
        done
      done
    done
  using assms(2-4)
   apply -
   apply (drule (5) Esub_inversion[rotated -1])
   apply (erule exE conjE)+
   apply hypsubst_thin
   apply (simp add: Enoclash_def G.Supp_Sb G.Supp_Map G.Vrs_Sb Int_Un_distrib)
  unfolding G.Vrs_Map
   apply (erule imageE)
   apply hypsubst_thin
   apply (drule meta_spec, drule meta_mp, rule refl)
   apply (elim disj_forward ex_forward; assumption?)
     apply (smt (verit, del_insts) Efreee.intros(3)
      Un_empty image_iff imsupp_empty_IntD1 mem_Collect_eq)
    apply (metis Efree\<eta>.intros(3))
   apply (metis Efree\<eta>'.intros(3))
  apply (auto intro!: Un_bound IImsupp_bound simp: imsupp_supp_bound)
  done

lemma EFVrs\<eta>_EsubI2:
  assumes
    "a \<in> EFVrs\<eta> e" "z \<in> EFVrs\<eta> (\<rho> a)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
  shows "z \<in> EFVrs\<eta> (Esub \<delta> \<rho> \<rho>' e)"
  using assms(1,2) unfolding EFVrs_def EFVrs\<eta>_def mem_Collect_eq
  apply (induct e rule: Efree\<eta>_strong_induct[rotated, consumes 1, where A = "imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EFVars \<rho> \<union> IImsupp' (Ector o \<eta>') EFVars \<rho>'"])
     apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
      apply force
     apply force
    apply (rule Efree\<eta>.intros(2); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    apply (cases "\<rho> a = Ector (\<eta> a)")
     apply (metis EFVrs\<eta>_Ector_eta assms(2) singletonD)
    apply (subgoal_tac "z \<in> IImsupp (Ector \<circ> \<eta>) EFVars \<rho>")
     apply blast
    apply (auto simp: IImsupp_def SSupp_def EFVrs\<eta>_def Efree\<eta>_Efree intro!: exI[of _ a]) []
   apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
     apply force
    apply force
   apply (rule Efree\<eta>.intros(3); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
  apply (auto intro!: imsupp_supp_bound[THEN iffD2] assms IImsupp_bound Un_bound EFVrs_bound)
  done

lemma EFVrs\<eta>_EsubI3:
  assumes
    "a \<in> EFVrs\<eta>' e" "z \<in> EFVrs\<eta> (\<rho>' a)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
  shows "z \<in> EFVrs\<eta> (Esub \<delta> \<rho> \<rho>' e)"
  using assms(1,2) unfolding EFVrs\<eta>_def EFVrs\<eta>'_def mem_Collect_eq
  apply (induct e rule: Efree\<eta>'_strong_induct[rotated, consumes 1, where A = "imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EFVars \<rho> \<union> IImsupp' (Ector o \<eta>') EFVars \<rho>'"])
     apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
      apply force
     apply force
    apply (rule Efree\<eta>.intros(2); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    apply (cases "\<rho>' a = Ector (\<eta>' a)")
     apply (metis Ector_eta'_inj Efree\<eta>.cases GSupp_eta'(1,2) empty_iff eta_distinct)
    apply (subgoal_tac "z \<in> IImsupp (Ector \<circ> \<eta>') EFVars \<rho>'")
     apply blast
    apply (auto simp: IImsupp_def SSupp_def EFVrs\<eta>_def Efree\<eta>_Efree intro!: exI[of _ a]) []
   apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
     apply force
    apply force
   apply (rule Efree\<eta>.intros(3); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
  apply (auto intro!: imsupp_supp_bound[THEN iffD2] assms IImsupp_bound Un_bound EFVrs_bound)
  done

lemma EFVrs\<eta>_EsubD:
  assumes
    "z \<in> EFVrs\<eta> (Esub \<delta> \<rho> \<rho>' e)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
  shows "
  z \<in> ((\<Union>x\<in>EFVrs\<eta> e. EFVrs\<eta> (\<rho> x)) \<union> (\<Union>x\<in>EFVrs\<eta>' e. EFVrs\<eta> (\<rho>' x)))"
  using assms(1)
  unfolding EFVrs_def EFVrs\<eta>_def EFVrs\<eta>'_def mem_Collect_eq Un_iff UN_iff bex_simps
  apply (induct "Esub \<delta> \<rho> \<rho>' e" arbitrary: e rule:
      Efree\<eta>_strong_induct[rotated, consumes 1, where A = "imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EFVars \<rho> \<union> IImsupp' (Ector o \<eta>') EFVars \<rho>'"])
  subgoal for e
    apply (cases "\<exists>a. e = Ector (\<eta> a)")
     apply (auto simp: Esub_Ector assms(2-4)) []
     apply (metis Efree\<eta>.intros(1))
    apply (cases "\<exists>a. e = Ector (\<eta>' a)")
     apply (auto simp: Esub_Ector assms(2-4)) []
     apply (metis Efree\<eta>'.intros(1) Efree\<eta>.intros(1))
    using assms(2-4)
    apply -
    apply (drule (3) Esub_inversion[rotated -1])
      apply simp
     apply (simp add: Enoclash_def)
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (simp add: G.Vrs_Sb)
    unfolding G.Vrs_Map
    apply (metis eta_inversion)
    done
  subgoal for e' u e
    using assms(2-4)
    apply -
    apply (drule (5) Esub_inversion[rotated -1])
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (simp add: Enoclash_def G.Supp_Sb G.Supp_Map G.Vrs_Sb Int_Un_distrib)
    unfolding G.Vrs_Map
    apply (erule imageE)
    apply hypsubst_thin
    apply (drule meta_spec, drule meta_mp, rule refl)
    subgoal for u' e'
      apply (elim disj_forward ex_forward; assumption?)
      apply (metis (mono_tags, lifting) EFVrs\<eta>_Ector_eta Efree\<eta>.intros(2)
            Efree_alt(2) Int_emptyD SSupp_def comp_apply empty_iff insert_iff mem_Collect_eq)
      subgoal for a
        apply (erule conjE)+
        apply (rule conjI[rotated])
         apply assumption
        apply (cases "\<rho>' a = Ector (\<eta>' a)")
         apply (metis Ector_eta'_inj Efree\<eta>.cases GSupp_eta'(1,2) empty_iff eta_distinct)
        apply (metis (mono_tags, lifting) Efree\<eta>'.intros(2)
            IntI SSupp_def comp_apply empty_iff mem_Collect_eq)
        done
      done
    done
  using assms(2-4)
   apply -
   apply (drule (5) Esub_inversion[rotated -1])
   apply (erule exE conjE)+
   apply hypsubst_thin
   apply (simp add: Enoclash_def G.Supp_Sb G.Supp_Map G.Vrs_Sb Int_Un_distrib)
  unfolding G.Vrs_Map
   apply (erule imageE)
   apply hypsubst_thin
   apply (drule meta_spec, drule meta_mp, rule refl)
   apply (elim disj_forward ex_forward; assumption?)
    apply (metis Efree\<eta>.intros(3))
   apply (metis Efree\<eta>'.intros(3))
  apply (auto intro!: Un_bound IImsupp_bound simp: imsupp_supp_bound)
  done

lemma EFVrs\<eta>'_EsubI2:
  assumes
    "a \<in> EFVrs\<eta> e" "z \<in> EFVrs\<eta>' (\<rho> a)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
  shows "z \<in> EFVrs\<eta>' (Esub \<delta> \<rho> \<rho>' e)"
  using assms(1,2) unfolding EFVrs\<eta>_def EFVrs\<eta>'_def mem_Collect_eq
  apply (induct e rule: Efree\<eta>_strong_induct[rotated, consumes 1, where A = "imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EFVars \<rho> \<union> IImsupp' (Ector o \<eta>') EFVars \<rho>'"])
     apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
      apply force
     apply force
    apply (rule Efree\<eta>'.intros(2); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    apply (cases "\<rho> a = Ector (\<eta> a)")
     apply (metis Ector_eta_inj Efree\<eta>'.cases GSupp_eta(1,2) empty_iff eta_distinct)
    apply (subgoal_tac "z \<in> IImsupp (Ector \<circ> \<eta>) EFVars \<rho>")
     apply blast
    apply (auto simp: IImsupp_def SSupp_def EFVrs\<eta>_def Efree\<eta>'_Efree intro!: exI[of _ a]) []
   apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
     apply force
    apply force
   apply (rule Efree\<eta>'.intros(3); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
  apply (auto intro!: imsupp_supp_bound[THEN iffD2] assms IImsupp_bound Un_bound EFVrs_bound)
  done

lemma EFVrs\<eta>'_EsubI3:
  assumes
    "a \<in> EFVrs\<eta>' e" "z \<in> EFVrs\<eta>' (\<rho>' a)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
  shows "z \<in> EFVrs\<eta>' (Esub \<delta> \<rho> \<rho>' e)"
  using assms(1,2) unfolding EFVrs\<eta>_def EFVrs\<eta>'_def mem_Collect_eq
  apply (induct e rule: Efree\<eta>'_strong_induct[rotated, consumes 1, where A = "imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EFVars \<rho> \<union> IImsupp' (Ector o \<eta>') EFVars \<rho>'"])
     apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
    apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
      apply force
     apply force
    apply (rule Efree\<eta>'.intros(2); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
    apply (cases "\<rho>' a = Ector (\<eta>' a)")
     apply (metis EFVrs\<eta>'_Ector_eta' assms(2) singletonD)
    apply (subgoal_tac "z \<in> IImsupp (Ector \<circ> \<eta>') EFVars \<rho>'")
     apply blast
    apply (auto simp: IImsupp_def SSupp_def EFVrs\<eta>_def Efree\<eta>'_Efree intro!: exI[of _ a]) []
   apply (subst Esub_Ector; (simp add: Int_Un_distrib assms(3-5))?)
     apply force
    apply force
   apply (rule Efree\<eta>'.intros(3); (simp add: G.Supp_Sb G.Supp_Map G.Vrs_Sb G.Vrs_Map assms(3-5))?)
  apply (auto intro!: imsupp_supp_bound[THEN iffD2] assms IImsupp_bound Un_bound EFVrs_bound)
  done

lemma EFVrs\<eta>'_EsubD:
  assumes
    "z \<in> EFVrs\<eta>' (Esub \<delta> \<rho> \<rho>' e)"
    "|supp (\<delta> :: 'a \<Rightarrow> 'a::var)| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set|"
    "|SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set|"
  shows "
  z \<in> ((\<Union>x\<in>EFVrs\<eta> e. EFVrs\<eta>' (\<rho> x)) \<union> (\<Union>x\<in>EFVrs\<eta>' e. EFVrs\<eta>' (\<rho>' x)))"
  using assms(1)
  unfolding EFVrs_def EFVrs\<eta>_def EFVrs\<eta>'_def mem_Collect_eq Un_iff UN_iff bex_simps
  apply (induct "Esub \<delta> \<rho> \<rho>' e" arbitrary: e rule:
      Efree\<eta>'_strong_induct[rotated, consumes 1, where A = "imsupp \<delta> \<union> IImsupp' (Ector o \<eta>) EFVars \<rho> \<union> IImsupp' (Ector o \<eta>') EFVars \<rho>'"])
  subgoal for e
    apply (cases "\<exists>a. e = Ector (\<eta> a)")
     apply (auto simp: Esub_Ector assms(2-4)) []
     apply (metis Efree\<eta>'.intros(1) Efree\<eta>.intros(1))
    apply (cases "\<exists>a. e = Ector (\<eta>' a)")
     apply (auto simp: Esub_Ector assms(2-4)) []
     apply (metis Efree\<eta>'.intros(1))
    using assms(2-4)
    apply -
    apply (drule (3) Esub_inversion[rotated -1])
      apply simp
     apply (simp add: Enoclash_def)
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (simp add: G.Vrs_Sb)
    unfolding G.Vrs_Map
    apply (metis eta'_inversion)
    done
  subgoal for e' u e
    using assms(2-4)
    apply -
    apply (drule (5) Esub_inversion[rotated -1])
    apply (erule exE conjE)+
    apply hypsubst_thin
    apply (simp add: Enoclash_def G.Supp_Sb G.Supp_Map G.Vrs_Sb Int_Un_distrib)
    unfolding G.Vrs_Map
    apply (erule imageE)
    apply hypsubst_thin
    apply (drule meta_spec, drule meta_mp, rule refl)
    subgoal for u' e'
      apply (elim disj_forward ex_forward; assumption?)
      subgoal for a
        apply (erule conjE)+
        apply (rule conjI[rotated])
         apply assumption
        apply (cases "\<rho> a = Ector (\<eta> a)")
         apply (metis Ector_eta_inj Efree\<eta>'.cases GSupp_eta(1,2) empty_iff eta_distinct)
        apply (metis (mono_tags, lifting) Efree\<eta>.intros(2)
            IntI SSupp_def comp_apply empty_iff mem_Collect_eq)
        done
      apply (metis (mono_tags, lifting) EFVrs\<eta>'_Ector_eta' Efree\<eta>'.intros(2)
            Efree_alt(3) Int_emptyD SSupp_def comp_apply empty_iff insert_iff
            mem_Collect_eq)
      done
    done
  using assms(2-4)
   apply -
   apply (drule (5) Esub_inversion[rotated -1])
   apply (erule exE conjE)+
   apply hypsubst_thin
   apply (simp add: Enoclash_def G.Supp_Sb G.Supp_Map G.Vrs_Sb Int_Un_distrib)
  unfolding G.Vrs_Map
   apply (erule imageE)
   apply hypsubst_thin
   apply (drule meta_spec, drule meta_mp, rule refl)
   apply (elim disj_forward ex_forward; assumption?)
    apply (metis Efree\<eta>.intros(3))
   apply (metis Efree\<eta>'.intros(3))
  apply (auto intro!: Un_bound IImsupp_bound simp: imsupp_supp_bound)
  done

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
          apply (simp_all add: G.Sb_Inj G.Map_id)
    done
  subgoal for \<delta> \<rho> \<rho>'
    by (simp add: fun_eq_iff Esub_Ector)
  subgoal
    by (simp add: fun_eq_iff Esub_Ector)
  subgoal for \<delta>1 \<rho>1 \<rho>1' \<delta>2 \<rho>2 \<rho>2'
    apply (rule Esub_unique_fresh[where A = "imsupp \<delta>1 \<union> imsupp \<delta>2 \<union>
   IImsupp' (Ector o \<eta>) EFVars \<rho>1 \<union> IImsupp' (Ector o \<eta>) EFVars \<rho>2 \<union>
   IImsupp' (Ector o \<eta>') EFVars \<rho>1' \<union> IImsupp' (Ector o \<eta>') EFVars \<rho>2'"])
          apply (simp_all add: supp_comp_bound Esub_Ector Un_bound
        imsupp_supp_bound Int_Un_distrib)
    apply (subst Esub_Ector;
        (simp add: G.Vrs_Sb G.Vrs_Map G.Map_comp[THEN fun_cong, simplified]
          G.Map_Sb[THEN fun_cong, simplified] G.Sb_comp[THEN fun_cong, simplified])?)
    subgoal by fast
    subgoal by fast
    subgoal by (meson eta_inversion)
    subgoal by (meson eta'_inversion)
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
  subgoal for \<delta> \<rho> \<rho>' x
    by (auto intro: EFVrs_EsubI1 EFVrs_EsubI2 EFVrs_EsubI3 dest: EFVrs_EsubD)
  subgoal for \<delta> \<rho> \<rho>' x
    by (auto intro: EFVrs\<eta>_EsubI2 EFVrs\<eta>_EsubI3 dest: EFVrs\<eta>_EsubD)
  subgoal for \<delta> \<rho> \<rho>' x 
    by (auto intro: EFVrs\<eta>'_EsubI2 EFVrs\<eta>'_EsubI3 dest: EFVrs\<eta>'_EsubD)
  subgoal for \<delta>1 \<rho>1 \<rho>1' \<delta>2 \<rho>2 \<rho>2' x
    apply (rule Esub_unique_fresh_relativized[where B = "{a. \<delta>1 a = \<delta>2 a}" and B\<eta> = "{a. \<rho>1 a = \<rho>2 a}" and B\<eta>' = "{a. \<rho>1' a = \<rho>2' a}" and
          A = "imsupp \<delta>2 \<union> IImsupp' (Ector \<circ> \<eta>) EFVars \<rho>2 \<union> IImsupp' (Ector \<circ> \<eta>') EFVars \<rho>2'", symmetric
          ])
    subgoal
      apply (rule ordLeq_ordLess_trans[OF card_of_mono1[where B = "supp \<delta>1 \<union> supp \<delta>2"]])
       apply (auto simp: supp_def) []
      apply (auto intro!: Un_bound)
      done
    subgoal
      apply (rule ordLeq_ordLess_trans[OF card_of_mono1[where B = "SSupp (Ector \<circ> \<eta>) \<rho>1 \<union> SSupp (Ector \<circ> \<eta>) \<rho>2"]])
       apply (auto simp: SSupp_def) []
      apply (auto intro!: Un_bound)
      done
    subgoal
      apply (rule ordLeq_ordLess_trans[OF card_of_mono1[where B = "SSupp (Ector \<circ> \<eta>') \<rho>1' \<union> SSupp (Ector \<circ> \<eta>') \<rho>2'"]])
       apply (auto simp: SSupp_def) []
      apply (auto intro!: Un_bound)
      done
    subgoal
      apply (auto intro!: Un_bound IImsupp_bound simp: imsupp_supp_bound)
      done
    subgoal by assumption
    subgoal by assumption
    subgoal by assumption
    subgoal for a
      apply (subst Esub_Ector; simp)
      done
    subgoal for a
      apply (subst Esub_Ector; simp)
      done
    subgoal for u
      apply (subst Esub_Ector; (simp add: Int_Un_distrib)?)
      apply (rule arg_cong[where f = Ector])
      apply (rule G.Sb_cong; simp?)
      apply (auto simp: G.Vrs_Map)
      apply (simp add: Collect_mono_iff EFVrs_def Efreee.intros(1))
      done
      apply auto
    done
  done

end