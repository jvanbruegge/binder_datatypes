theory Corecursor
  imports Greatest_Fixpoint
begin


(* Norrish's notation: *)
(*definition swapping :: "(('a::var \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> 'a set) \<Rightarrow> bool" where
  "swapping swp fvars \<equiv>
  swp id = id \<and>
  (\<forall> u v. bij u \<and> |supp u| <o |UNIV::'a set| \<and> bij v \<and> |supp v| <o |UNIV::'a set|
      \<longrightarrow> swp (u o v) = swp u o swp v) \<and>
  (\<forall> u c. bij u \<and> |supp u| <o |UNIV::'a set| \<and>
      (\<forall> a. a \<in> fvars c \<longrightarrow> u a = a) \<longrightarrow> swp u c = c) \<and>
  (\<forall> u c a. bij u \<and> |supp u| <o |UNIV::'a set|
     \<longrightarrow> (u a \<in> fvars (swp u c) \<longleftrightarrow> a \<in> fvars c))"*)

(* Need to factor in terms in the "swapping" condition for 'a D -- a heavily restricted
"swapping" condition, only assuming functoriality and nothing else;
in particular nothing about freshness.  *)
(*abbreviation swappingD :: "(('a::vvar_TT \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> bool" where
  "swappingD swp  \<equiv>
  (\<forall> c. swp id c = c) \<and>
  (\<forall> u v c. bij u \<and> |supp u| <o bound (any::'a) \<and> bij v \<and> |supp v| <o bound (any::'a)
    \<longrightarrow>  swp (u o v) c = swp u (swp v c))"*)

(* The following will not be used in the development, but motivates the
chosen axioms for DDTOR by showing that the terms satisfy them for their natural destructor.  *)
definition ddtor :: "'a::var term \<Rightarrow> ('a, 'a, 'a term, 'a term) term_pre set" where
  "ddtor t \<equiv> {x . t = term_ctor x}"

(*lemma ddtor_ne:
  "ddtor t \<noteq> {}"
  unfolding ddtor_def by (auto simp add: TT_nchotomy)
*)

(*lemma ddtor_map_TT:
  assumes "{x,x'} \<subseteq> ddtor t"
  shows "\<exists>u. bij (u::'a\<Rightarrow>'a) \<and> |supp u| <o bound(any::'a::vvar_TT) \<and> id_on (FFVarsB x) u \<and> map_F id u id (map_TT u) x = x'"
  using assms TT_inject0 by (auto simp: ddtor_def)

lemma FFVars_ddtor:
  assumes "x \<in> ddtor t"
  shows "FFVars t = set1_F x \<union> (\<Union>z \<in> set3_F x. FFVars z) \<union> FFVarsB x"
  using assms by (auto simp: ddtor_def FFVars_simps)
    (****)*)

(* The domain type: *)
typedecl 'a U

consts Udtor :: "'a::var U \<Rightarrow> ('a, 'a, 'a term + 'a U, 'a term + 'a U) term_pre set"
consts Umap :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a::var U \<Rightarrow> 'a U"
consts UFVars :: "'a::var U \<Rightarrow> 'a set"

axiomatization where
  (* The destructor is non-empty and deterministic modulo a renaming: *)
  DDTOR_ne: "\<And>d. Udtor d \<noteq> {}"
  and
  alpha_Udtor: "\<And>X X' d. {X,X'} \<subseteq> Udtor d \<Longrightarrow>
\<exists>u. bij (u::'a::var \<Rightarrow> 'a) \<and> |supp u| <o |UNIV::'a set| \<and> id_on ((\<Union>z \<in> set3_term_pre X. case_sum FVars_term UFVars z) - set2_term_pre X) u \<and>
     map_term_pre id u (map_sum (permute_term u) (Umap u)) id X = X'"
  and
  (* The dual of the first block of assumptions from Norrish's paper:   *)
  UFVars_Udtor:
  "\<And> d X. X \<in> Udtor d \<Longrightarrow>
  set1_term_pre X \<union> (\<Union>z \<in> set4_term_pre X. case_sum FVars_term UFVars z) \<union>
   ((\<Union>z \<in> set3_term_pre X. case_sum FVars_term UFVars z) - set2_term_pre X) \<subseteq>
  UFVars d"
  and
  (* The dual of the third block: *)
  Umap_Udtor: "\<And>u d.
  bij (u::'a\<Rightarrow>'a) \<Longrightarrow> |supp u| <o |UNIV::'a::var set| \<Longrightarrow>
  Udtor (Umap u d) \<subseteq>
  image
    (map_term_pre u u (map_sum (permute_term u) (Umap u)) (map_sum (permute_term u) (Umap u)))
    (Udtor d)"
  and
  Umap_id0: "Umap id = id"
and Umap_comp0: "bij f \<Longrightarrow> |supp (f::'a::var \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> bij g \<Longrightarrow> |supp (g::'a::var \<Rightarrow> 'a)| <o |UNIV::'a set|
  \<Longrightarrow> Umap f \<circ> Umap g = Umap (f \<circ> g)"
and Umap_cong0: "bij f \<Longrightarrow> |supp (f::'a::var \<Rightarrow> 'a)| <o |UNIV::'a set|
  \<Longrightarrow> (\<And>a. a \<in> UFVars d \<Longrightarrow> f a = a) \<Longrightarrow> Umap f d = d"
(*and Umap_UFVars: "bij f \<Longrightarrow> |supp (f::'a::var \<Rightarrow> 'a)| <o |UNIV::'a set|
  \<Longrightarrow> UFVars (Umap f d) = f ` UFVars d"*)

(*
D \<Rightarrow> U
TT \<Rightarrow> term
F \<Rightarrow> term_pre
vvar_TT \<Rightarrow> var

FFVars \<Rightarrow> FVars_term
FFVarsD \<Rightarrow> UFVars
DDTOR \<Rightarrow> Udtor
mmapD \<Rightarrow> Umap

set2_F \<Rightarrow> set2_term_pre
if set has minus \<Rightarrow> set3_term_pre
if not \<Rightarrow> set4_term_pre
*)

(* Defined analogously to the FVarsB: *)
definition FFVarsBD :: "('a::var, 'a, 'a term + 'a U, 'a term + 'a U) term_pre \<Rightarrow> 'a set" where
  "FFVarsBD X \<equiv> (\<Union>z \<in> set4_F X. case_sum FFVars FFVarsD z) - set2_F X"

lemmas DDTOR_mmapD = DDTOR_mmapD0[folded FFVarsBD_def]
lemmas FFVarsD_DDTOR = FFVarsD_DDTOR0[folded FFVarsBD_def]

(*  *)
lemma mmapD_id[simp,intro!]: "mmapD id d = d"
  using swapping_mmapD_FFVarsD by auto

lemma mmapD_comp:
  "bij (u::'a\<Rightarrow>'a) \<Longrightarrow> |supp u| <o bound (any::'a::vvar_TT) \<Longrightarrow> bij v \<Longrightarrow> |supp v| <o bound (any::'a) \<Longrightarrow>
 mmapD (u o v) d = mmapD u (mmapD v d)"
  using swapping_mmapD_FFVarsD by auto

(*  *)

lemma mmapD_DDTOR_strong:
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o bound(any::'a::vvar_TT)"
  shows
    "DDTOR (mmapD u d) =
 image
   (map_F u u (map_sum (map_TT u) (mmapD u)) (map_sum (map_TT u) (mmapD u)))
   (DDTOR d)" (is "?L = ?R")
proof
  show "?L \<subseteq> ?R" using mmapD_DDTOR[OF assms] .
next
  have iu: "bij (inv u)" "|supp (inv u)| <o bound(any::'a)" using u by(simp_all add: supp_inv_bound)
  define dd where "dd \<equiv> mmapD u d"
  have d: "d = mmapD (inv u) dd"
    using u unfolding dd_def by(simp add: mmapD_comp[symmetric] supp_inv_bound)
  have [simp]: "mmapD u \<circ> (mmapD (inv u)) = id" unfolding fun_eq_iff
    by (simp add: u iu mmapD_comp[symmetric])
  show "?R \<subseteq> ?L" unfolding dd_def[symmetric] d using mmapD_DDTOR[OF iu, of dd]
    by(auto simp: u iu F_map_comp[symmetric]
        map_sum.comp TT_map_o[symmetric] map_TT_id mmapD_comp[symmetric] map_sum.id F_map_id)
qed


(*************************************)
(* The raw-term-based model infrastructure *)

definition DTOR :: "'a::vvar_TT D \<Rightarrow> ('a, 'a, 'a T + 'a D, 'a T + 'a D) F set" where
  "DTOR d \<equiv>  map_F id id (map_sum rep_TT id) (map_sum rep_TT id) ` (DDTOR d)"

abbreviation mapD :: "('a::vvar_TT \<Rightarrow> 'a) \<Rightarrow> 'a D \<Rightarrow> 'a D" where
  "mapD \<equiv> mmapD"

abbreviation FVarsD :: "'a::vvar_TT D \<Rightarrow> 'a set" where
  "FVarsD \<equiv> FFVarsD"

definition FVarsBD :: "('a::vvar_TT, 'a, 'a T + 'a D, 'a T + 'a D) F \<Rightarrow> 'a set" where
  "FVarsBD X \<equiv> (\<Union>z \<in> set4_F X. case_sum FVars FVarsD z) - set2_F X"

lemmas FVars_def2 = FFVars.abs_eq[symmetric]


(* Preterm-based version of the assumptions: *)

(*  *)
lemmas mapD_id = mmapD_id

lemmas mapD_comp = mmapD_comp

lemma FVarsBD_FFVarsBD:
  "FVarsBD X = FFVarsBD (map_F id id (map_sum abs_TT id) (map_sum abs_TT id) X)"
  unfolding FVarsBD_def FFVarsBD_def FVars_def2
  apply(simp add: F_set_map FVars_def2 case_sum_map_sum supp_id_bound)
  unfolding o_def id_def ..

lemma DTOR_mapD:
  assumes "{X,X'} \<subseteq> DTOR d"
  shows "\<exists>u. bij (u::'a\<Rightarrow>'a) \<and> |supp u| <o bound(any::'a::vvar_TT) \<and> id_on (FVarsBD X) u \<and>
     rel_F id u
       (rel_sum alpha (=))
       (rel_sum (\<lambda> t t'. alpha (map_T u t) t') (\<lambda> d d'. mapD u d = d'))
     X X'"
proof-
  define XX XX' where
    "XX \<equiv> map_F id id (map_sum abs_TT id) (map_sum abs_TT id) X" and
    "XX' \<equiv> map_F id id (map_sum abs_TT id) (map_sum abs_TT id) X'"
  have 0: "{XX,XX'} \<subseteq> DDTOR d" using assms unfolding XX_def XX'_def DTOR_def
    by (auto simp: F_map_comp[symmetric] map_sum.comp abs_rep_TT map_sum.id F_map_id supp_id_bound)
  then obtain u where u: "bij u" "|supp u| <o bound(any::'a)" "id_on (FFVarsBD XX) u"
    and m: "map_F id u id (map_sum (map_TT u) (mmapD u)) XX = XX'"
    using DDTOR_mmapD[OF 0] by auto
  have [simp]: "asSS (asBij u) = u"  "asSS u = u" using u unfolding asSS_def by auto
  show ?thesis
  proof(rule exI[of _ u], safe )
    show "id_on (FVarsBD X) u"
      using u(3) unfolding id_on_def XX_def FVarsBD_FFVarsBD by auto
    show "rel_F id u (rel_sum alpha (=)) (rel_sum (\<lambda>t. alpha (map_T u t)) (\<lambda>d d'. mapD u d = d')) X X'"
      using m unfolding XX_def XX'_def
      apply(simp add: u F_map_comp[symmetric] F_map_id map_sum.comp map_TT_def F.rel_eq[symmetric]
          F_rel_map supp_id_bound)
      apply(rule F_rel_mono_strong1) apply (auto simp: u supp_id_bound)
      unfolding Grp_def apply auto
      subgoal for d1 d2
        using TT.abs_eq_iff apply(cases d1) by (cases d2,fastforce, fastforce)+
      subgoal for d1 d2
        using TT.abs_eq_iff abs_TT_alpha_aux[OF u(1,2)]
        apply(cases d1) apply(cases d2) apply auto
        apply(cases d2) by auto .
  qed(insert u, auto)
qed

lemma DTOR_ne:
  "DTOR d \<noteq> {}"
  unfolding DTOR_def using DDTOR_ne by auto

lemma FVarsD_DTOR:
  assumes "X \<in> DTOR d"
  shows "set1_F X \<union> (\<Union>z \<in> set3_F X. case_sum FVars FVarsD z) \<union> FVarsBD X \<subseteq> FVarsD d"
proof-
  define XX where "XX \<equiv> map_F id id (map_sum abs_TT id) (map_sum abs_TT id) X"
  have 0: "XX \<in> DDTOR d" using assms unfolding XX_def DTOR_def
    by (auto simp: F_map_comp[symmetric] map_sum.comp abs_rep_TT map_sum.id F_map_id supp_id_bound)
  show ?thesis using FFVarsD_DDTOR[OF 0] unfolding FVarsBD_FFVarsBD XX_def
    apply (simp add: F_set_map FVars_def2 case_sum_map_sum supp_id_bound) unfolding FVars_def2 o_def
      map_sum.simps id_def by simp
qed

lemma rel_set_reflI:
  assumes "\<And>a. a \<in> A \<Longrightarrow> r a a"
  shows "rel_set r A A"
  using assms unfolding rel_set_def by auto

lemma mapD_DTOR:
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o bound(any::'a::vvar_TT)"
  shows
    "rel_set
  (rel_F u u
     (rel_sum (\<lambda> t t'. alpha (map_T u t) t') (\<lambda> d d'. mapD u d = d'))
     (rel_sum (\<lambda> t t'. alpha (map_T u t) t') (\<lambda> d d'. mapD u d = d')))
 (DTOR d)
 (DTOR (mapD u d))"
  unfolding DTOR_def
  by (auto intro!: rel_set_reflI F.rel_refl_strong sum.rel_refl_strong
      simp: mmapD_DDTOR_strong[OF u, of d] rel_set_image u F_rel_map OO_def Grp_def sum.rel_map
      map_TT_def asSS_def alpha_rep_abs_TT alpha_sym
      image_comp F_map_comp1[symmetric] map_sum.comp supp_id_bound)

(*    *)

definition suitable ::  "('a::vvar_TT D \<Rightarrow> ('a,'a,'a T + 'a D,'a T + 'a D)F) \<Rightarrow> bool" where
  "suitable pick \<equiv> \<forall> d. pick d \<in> DTOR d"

definition f :: "('a::vvar_TT D \<Rightarrow> ('a,'a,'a T + 'a D,'a T + 'a D)F) \<Rightarrow> 'a D => 'a T" where
  "f pick \<equiv> corec_T pick"
thm T.corec[of "pick o DTOR", unfolded f_def[symmetric]]

lemma f_simps:
  "f pick d = ctor (map_F id id (case_sum id (f pick)) (case_sum id (f pick)) (pick d))"
  apply(subst T.corec[of pick, unfolded f_def[symmetric]]) unfolding id_def ..

lemma f_ctor:
  "ctor x = f pick d \<Longrightarrow>
 x = map_F id id (case_sum id (f pick)) (case_sum id (f pick)) (pick d)"
  using f_simps[of pick d] by simp

lemma suitable_FVarsD:
  assumes "suitable pick"
  shows "set1_F (pick d) \<union> (\<Union>z \<in> set3_F (pick d). case_sum FVars FVarsD z) \<union> FVarsBD (pick d)
       \<subseteq> FVarsD d"
  using FVarsD_DTOR[of "pick d"] using assms[unfolded suitable_def] by auto

(*  *)

lemma f_FVarsD:
  assumes p: "suitable pick"
  shows "FVars (f pick d) \<subseteq> FVarsD d"
proof safe
  fix a assume aa: "a \<in> FVars (f pick d)"
  define t where "t = f pick d"
  show "a \<in> FVarsD d" using aa[unfolded t_def[symmetric]] using t_def
  proof(induction arbitrary: d)
    case (set1 a x)
    note x = f_ctor[OF `ctor x = f pick d`]
    note fvd = suitable_FVarsD[OF assms, of d]
    show ?case using set1.hyps fvd unfolding x by (auto simp add: F_set_map supp_id_bound)
  next
    case (set2_free t x a)
    note x = f_ctor[OF `ctor x = f pick d`]
    note fvd = suitable_FVarsD[OF assms, of d]
    from `t \<in> set3_F x` obtain td where t: "t = case_sum id (f pick) td"
      and td: "td \<in> set3_F (pick d)" unfolding x by (auto simp add: F_set_map supp_id_bound)
    have a: "a \<in> case_sum FVars FVarsD td"
      using set2_free.IH set2_free.hyps unfolding t by(cases td) auto
    show ?case using a td by (intro rev_subsetD[OF _ fvd]) auto
  next
    case (set2_rec t x a d)
    note x = f_ctor[OF `ctor x = f pick d`]
    note fvd = suitable_FVarsD[OF assms, of d]
    from `t \<in> set4_F x` obtain td where t: "t = case_sum id (f pick) td"
      and td: "td \<in> set4_F (pick d)" unfolding x by (auto simp add: F_set_map supp_id_bound)
    have a: "a \<in> case_sum FVars FVarsD td"
      using set2_rec.IH set2_rec.hyps unfolding t by(cases td) auto
    have "a \<notin> set2_F (pick d)" using `a \<notin> set2_F x` unfolding x by(auto simp: F_set_map supp_id_bound)
    thus ?case using a td apply (intro rev_subsetD[OF _ fvd]) unfolding FVarsBD_def by auto
  qed
qed


lemma rel_F_suitable_mapD:
  assumes pp': "suitable pick" "suitable pick'"
    and u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o bound(any::'a::vvar_TT)"
  shows "\<exists> v. bij v \<and> |supp v| <o bound(any::'a) \<and> id_on (FVarsBD (pick d)) v \<and>
 rel_F u (u o v)
   (rel_sum (\<lambda>t t'. alpha (map_T u t) t')
            (\<lambda>d d'. d' = mapD u d))
   (rel_sum (\<lambda>t t'. alpha (map_T (u o v) t) t')
            (\<lambda>d d'. mapD (u o v) d = d'))
 (pick d)
 (pick' (mapD u d))"
proof-
  have p: "pick d \<in> DTOR d" and p': "pick' (mapD u d) \<in> DTOR (mapD u d)"
    using pp' unfolding suitable_def by auto
  obtain X where X: "X \<in> DTOR d" and 0:
    "rel_F u u
       (rel_sum (\<lambda>t. alpha (map_T u t)) (\<lambda>d. (=) (mapD u d)))
       (rel_sum (\<lambda>t. alpha (map_T u t)) (\<lambda>d. (=) (mapD u d)))
     X (pick' (mapD u d))"
    using mapD_DTOR[OF u, of d] p' unfolding rel_set_def by auto
  obtain v where v: "bij v" "|supp v| <o bound(any::'a)" "id_on (FVarsBD (pick d)) v"
    and 2:
    "rel_F id v
      (rel_sum alpha (=))
      (rel_sum (\<lambda>t. alpha (map_T v t)) (\<lambda>d. (=) (mapD v d)))
   (pick d) X" using DTOR_mapD[of "pick d" X d] using pp' X unfolding suitable_def by auto
  show ?thesis apply(rule exI[of _ v], simp add: v)
    apply(rule F_rel_mono_strong1[OF _ _ _ F_rel_comp_imp[OF _ _ _ _ _ _ 2 0], simplified])
           apply(auto simp: u v supp_comp_bound supp_inv_bound supp_id_bound)
    subgoal for td1 td3 td2 using alpha_refl
      apply(cases td1) apply auto
       apply(cases td2) apply auto  apply(cases td3) apply auto
       apply (smt alpha_bij_eq alpha_trans rel_sum_simps(1) u(1) u(2))
      apply(cases td2) apply auto  apply(cases td3) by auto
    subgoal for td1 td3 td2 using alpha_refl
      apply(cases td1) apply auto
       apply(cases td2) apply auto  apply(cases td3) apply (auto  simp: u v T_map_comp supp_inv_bound
          ) using alpha_bij_eq alpha_trans  using u(1) u(2) apply blast
      apply(cases td2) apply auto  apply(cases td3)
      by (auto simp: u v T_map_comp mapD_comp[symmetric]) .
qed

(* The "monster lemma": swapping and "pick"-irrelevance covered in one shot: *)

lemma f_swap_alpha:
  assumes p: "suitable pick" and p': "suitable pick'"
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o bound(any::'a::vvar_TT)"
  shows "alpha (map_T u (f pick d)) (f pick' (mapD u d))"
proof-
  let ?\<phi> = "\<lambda> tL tR. \<exists> u d. bij u \<and> |supp u| <o bound(any::'a) \<and>
   tL = map_T u (f pick d) \<and> tR = f pick' (mapD u d)"
  {fix tL tR assume "?\<phi> tL tR"
    hence "alpha tL tR"
    proof(induction rule: alpha_coinduct2)
      case (C xL xR)
      then obtain u d
        where u: "bij u" "|supp u| <o bound(any::'a)"
          and "ctor xL = map_T u (f pick d)" "ctor xR = f pick' (mapD u d)" by auto
      hence xL: "xL = map_F u u (map_T u \<circ> case_sum id (f pick)) (map_T u\<circ> case_sum id (f pick)) (pick d)"
        and xR: "xR = map_F id id (case_sum id (f pick')) (case_sum id (f pick')) (pick' (mapD u d))"
        using f_simps[of "pick"] f_simps[of "pick'"]
        by (auto simp: u map_T_simps F_map_comp[symmetric] supp_id_bound)
          (*  *)
      obtain v where v: "bij v" "|supp v| <o bound(any::'a)" and iv: "id_on (FVarsBD (pick d)) v"
        and rv:
        "rel_F u (u \<circ> v)
       (rel_sum (\<lambda>t. alpha (map_T u t)) (\<lambda>d d'. d' = mapD u d))
       (rel_sum (\<lambda>t. alpha (map_T (u \<circ> v) t)) (\<lambda>d. (=) (mapD (u \<circ> v) d)))
     (pick d) (pick' (mapD u d)) "
        using rel_F_suitable_mapD[OF p p' u(1,2)] by blast
      define w where "w \<equiv> u o v o inv u"
      have w: "bij w" "|supp w| <o bound(any::'a)" by (simp_all add: w_def u v supp_comp_bound supp_inv_bound)
      have fv_xL: "FVarsB xL \<subseteq> u ` (FVarsBD (pick d))"
        using f_FVarsD[OF p] unfolding xL apply (auto simp: u F_set_map FVars_map_T FVarsBD_def)
        subgoal for td a apply (cases td) by fastforce+ .
      have fv_p'd: "FVarsBD (pick d) \<subseteq> FVarsD d"
        using FVarsD_DTOR[of "pick d"] p unfolding suitable_def by auto
      have "id_on (u ` (FVarsBD (pick d))) w"
        using iv fv_p'd unfolding id_on_def xL w_def eq_on_def id_on_def by (auto simp: F_set_map u)
      hence iw: "id_on (FVarsB xL) w" using fv_xL unfolding id_on_def by auto
      show ?case proof(rule exI[of _ w], safe)
        show "rel_F id w
      (\<lambda>t t'. (\<exists>u d. bij u \<and> |supp u| <o bound(any::'a) \<and>
                     t = map_T u (f pick d) \<and> t' = f pick' (mapD u d))
              \<or> alpha t t')
      (\<lambda>t t'. (\<exists>u d. bij u \<and> |supp u| <o bound(any::'a) \<and>
                     map_T w t = map_T u (f pick d)  \<and> t' = f pick' (mapD u d))
              \<or> alpha (map_T w t) t')
      xL xR" unfolding xL xR
          apply(simp add: w u F_rel_map Grp_def OO_def supp_comp_bound supp_inv_bound T_map_comp[symmetric] supp_id_bound)
        proof(rule F_rel_mono_strong0[OF _ _ _ _ _ _ rv], auto)
          fix a assume "a \<in> set2_F (pick d)"
          thus "u (v a) = w (u a)"
            unfolding w_def by (simp add: u v)
        next
          fix ttdL ttdR assume ttdLin: "ttdL \<in> set3_F (pick d)"
            and ttdRin: "ttdR \<in> set3_F (pick' (mapD u d))"
            and r: "rel_sum (\<lambda>t. alpha (map_T u t)) (\<lambda>d d'. d' = mapD u d) ttdL ttdR"
            and na: "\<not> alpha (map_T u (case_sum id (f pick) ttdL)) (case_sum id (f pick') ttdR)"
          {fix tL assume 000: "ttdL = Inl tL"
            then obtain tR where "ttdR = Inl tR"
              and  "alpha (map_T u tL) tR" "\<not> alpha (map_T u tL) tR" using r na by (cases ttdR, auto)
            moreover have "alpha (map_T u tL) (map_T u tL)"
              apply(rule alpha_cong) by (auto simp: u)
            ultimately have False using alpha_trans alpha_sym by blast
          }
          then obtain dd where ttdL: "ttdL = Inr dd" by (cases ttdL, auto)
          hence ttdR: "ttdR = Inr (mapD u dd)" using r by(cases ttdR, auto)
          have fv_dd: "FVarsD dd \<subseteq> FVarsD d" using ttdLin unfolding ttdL
            using FVarsD_DTOR p unfolding suitable_def by force
          show "\<exists>uu. bij uu \<and> |supp uu| <o bound(any::'a) \<and>
             (\<exists> dd. map_T u (case_sum id (f pick) ttdL) = map_T uu (f pick dd) \<and>
                    case_sum id (f pick') ttdR = f pick' (mapD uu dd))"
            by (auto simp: u ttdL ttdR intro: exI[of _ u] exI[of _ dd])
        next
          fix ttdL ttdR assume ttdLin: "ttdL \<in> set4_F (pick d)"
            and ttdRin: "ttdR \<in> set4_F (pick' (mapD u d))"
            and r: "rel_sum (\<lambda>t. alpha (map_T (u \<circ> v) t)) (\<lambda>d. (=) (mapD (u \<circ> v) d)) ttdL ttdR"
            and na: "\<not> alpha (map_T (w \<circ> u) (case_sum id (f pick) ttdL)) (case_sum id (f pick') ttdR)"
          have uvw: "u \<circ> v = w \<circ> u" unfolding w_def by (auto simp: u)
          {fix tL assume 000: "ttdL = Inl tL"
            then obtain tR where "ttdR = Inl tR"
              and  "alpha (map_T (u \<circ> v) tL) tR" "\<not> alpha (map_T (w \<circ> u) tL) tR"
              using r na by (cases ttdR, auto)
            moreover have "alpha (map_T (u \<circ> v) tL) (map_T (w \<circ> u) tL)"
              unfolding uvw using alpha_refl .
            ultimately have False using alpha_trans alpha_sym by blast
          }
          then obtain dd where ttdL: "ttdL = Inr dd" by (cases ttdL, auto)
          hence ttdR: "ttdR = Inr (mapD (u \<circ> v) dd)" using r by (cases ttdR, auto)
          show "\<exists>uu. bij uu \<and> |supp uu| <o bound(any::'a) \<and>
              (\<exists> dd. map_T (w \<circ> u) (case_sum id (f pick) ttdL) = map_T uu (f pick dd) \<and>
                     case_sum id (f pick') ttdR = f pick' (mapD uu dd))"
            by (auto simp: u w supp_comp_bound ttdL ttdR uvw intro: exI[of _ "w o u"] exI[of _ dd])
        qed(simp_all add: w u v supp_comp_bound)
      qed(simp_all add: w iw)
    qed
  }
  thus ?thesis using assms by blast
qed

lemma f_alpha:
  assumes p: "suitable pick" and p': "suitable pick'"
  shows "alpha (f pick d) (f pick' d)"
  using f_swap_alpha[OF assms bij_id supp_id_bound, of d] by (simp add: T_map_id)

(*******************************)
(* Committing to a particular pick function: *)

definition pick0 :: "'a::vvar_TT D \<Rightarrow> ('a, 'a, 'a T + 'a D, 'a T + 'a D) F" where
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

definition "f0 \<equiv> f pick0"

lemmas f0_low_level_simps = f_simps[of pick0, unfolded f0_def[symmetric]]

lemma f0_DTOR:
  assumes "X \<in> DTOR d"
  shows "alpha (f0 d) (ctor (map_F id id (case_sum id f0) (case_sum id f0) X))"
proof-
  define pick1 where "pick1 \<equiv> \<lambda> d'. if d' = d then X else pick0 d'"
  have 1: "suitable pick1" using suitable_pick0 assms unfolding suitable_def pick1_def by auto
  have 2: "pick1 d = X" unfolding pick1_def by auto
  have 3: "\<And> dd. alpha (f0 dd) (f pick1 dd)" using f_alpha[OF suitable_pick0 1, of ]
    unfolding f0_def[symmetric] .
  have 4: "f pick1 d = ctor (map_F id id (case_sum id (f pick1)) (case_sum id (f pick1)) X)"
    apply(subst f_simps) unfolding 2 ..
  have 5: "alpha (ctor (map_F id id (case_sum id (f pick1)) (case_sum id (f pick1)) X))
                       (ctor (map_F id id (case_sum id f0) (case_sum id f0) X))"
    apply(rule alpha.intros[of id]) apply (auto simp: F_rel_map simp: Grp_def OO_def supp_id_bound)
    apply(rule F.rel_refl_strong)
    subgoal for td by (cases td, auto simp: alpha_refl alpha_sym[OF 3])
    subgoal for td by (cases td, auto simp: T_map_id alpha_refl alpha_sym[OF 3]) .
  show ?thesis using 3[of d] 5 unfolding 4[symmetric] using alpha_trans by blast
qed

lemma f0_mapD:
  assumes "bij (u::'a\<Rightarrow>'a)" and "|supp u| <o bound(any::'a::vvar_TT)"
  shows "alpha (f0 (mapD u d)) (map_T u (f0 d))"
  using alpha_sym[OF f_swap_alpha[OF suitable_pick0 suitable_pick0 assms, unfolded f0_def[symmetric]]] .

lemmas f0_FVarsD = f_FVarsD[OF suitable_pick0, unfolded f0_def[symmetric]]


(* The following theorems for raw theorems will now be lifted to quotiented terms: *)
thm f0_DTOR f0_mapD f0_FVarsD

(*******************)
(* End product: *)
definition ff0 :: "'a::vvar_TT D \<Rightarrow> 'a TT" where "ff0 d = abs_TT (f0 d)"

theorem ff0_DDTOR:
  assumes "X \<in> DDTOR d"
  shows "ff0 d = cctor (map_F id id (case_sum id ff0) (case_sum id ff0) X)"
  using assms using DTOR_def
proof-
  define XX where "XX \<equiv> map_F id id (map_sum rep_TT id) (map_sum rep_TT id) X"
  have XX: "XX \<in> DTOR d" using assms unfolding XX_def DTOR_def by auto
  have 0: "alpha
    (ctor (map_F id id (case_sum rep_TT f0) (case_sum rep_TT f0) X))
    (ctor (map_F id id (case_sum rep_TT (rep_TT \<circ> (abs_TT \<circ> f0)))
                       (case_sum rep_TT (rep_TT \<circ> (abs_TT \<circ> f0))) X))"
    apply(rule alpha.intros[of id]) apply (auto simp: F_rel_map Grp_def OO_def supp_id_bound)
    apply(rule F.rel_refl_strong)
    subgoal for td by (cases td) (auto simp add: alpha_refl alpha_rep_abs_TT alpha_sym)
    subgoal for td by (cases td) (auto simp add: alpha_refl alpha_rep_abs_TT alpha_sym T_map_id) .
  show ?thesis using f0_DTOR[OF XX] unfolding ff0_def cctor_def
    apply(auto simp: F_map_comp[symmetric] supp_id_bound id_def[symmetric] XX_def
        TT.abs_eq_iff o_case_sum case_sum_o_map_sum)
    unfolding o_def[symmetric] using alpha_trans[OF _ 0] by auto
qed

lemma ff0_mmapD:
  assumes "bij (u::'a\<Rightarrow>'a)" and "|supp u| <o bound(any::'a::vvar_TT)"
  shows "ff0 (mmapD u d) = map_TT u (ff0 d)"
proof-
  {assume "alpha (f0 (mmapD u d)) (map_T u (f0 d))"
    moreover have "alpha (map_T u (f0 d)) (map_T u (rep_TT (abs_TT (f0 d))))"
      unfolding alpha_bij_eq[OF assms] by (simp add: alpha_rep_abs_TT alpha_sym)
    ultimately have "alpha (f0 (mmapD u d)) (map_T u (rep_TT (abs_TT (f0 d))))"
      using alpha_trans by blast
  }
  thus ?thesis using f0_mapD[OF assms, of d]
    unfolding ff0_def map_TT_def by(auto simp: TT.abs_eq_iff asSS_def asBij_def assms)
qed

theorem ff0_FFVarsD:
  "FFVars (ff0 d) \<subseteq> FFVarsD d"
  using f0_FVarsD[of d] alpha_FVars alpha_rep_abs_TT
  unfolding ff0_def FFVars_def by fastforce

end

end