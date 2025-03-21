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
definition udtor :: "'a::var term \<Rightarrow> ('a, 'a, 'a term, 'a term) term_pre set" where
  "udtor t \<equiv> {x . t = term_ctor x}"

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
  Udtor_ne: "\<And>d. Udtor d \<noteq> {}"
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
(* TODO(ozkutuk): rename this? FFVarsBD \<rightarrow> UFVarsB? *)
definition FFVarsBD :: "('a::var, 'a, 'a term + 'a U, 'a term + 'a U) term_pre \<Rightarrow> 'a set" where
  "FFVarsBD X \<equiv> (\<Union>z \<in> set3_term_pre X. case_sum FVars_term UFVars z) - set2_term_pre X"

thm alpha_Udtor
lemmas Udtor_Umap = alpha_Udtor[folded FFVarsBD_def]
lemmas FVars_term_Udtor = UFVars_Udtor[folded FFVarsBD_def]

lemma Umap_id[simp,intro!]: "Umap id d = d"
  by (simp add: Umap_id0)

lemma Umap_comp:
  "bij (u::'a\<Rightarrow>'a) \<Longrightarrow> |supp u| <o |UNIV::('a::var) set| \<Longrightarrow> bij v \<Longrightarrow> |supp v| <o |UNIV::'a set| \<Longrightarrow>
 Umap (u o v) d = Umap u (Umap v d)"
  by (metis Umap_comp0 comp_apply)

lemma Umap_Udtor_strong:
  assumes u: "bij (u::'a::var\<Rightarrow>'a)" "|supp u| <o |UNIV::'a set|"
  shows
    "Udtor (Umap u d) =
 image
   (map_term_pre u u (map_sum (permute_term u) (Umap u)) (map_sum (permute_term u) (Umap u)))
   (Udtor d)" (is "?L = ?R")
proof
  show "?L \<subseteq> ?R" using Umap_Udtor[OF assms] .
next
  have iu: "bij (inv u)" "|supp (inv u)| <o |UNIV::'a set|" using u by(simp_all add: supp_inv_bound)
  define dd where "dd \<equiv> Umap u d"
  have d: "d = Umap (inv u) dd"
    using u unfolding dd_def by(simp add: Umap_comp[symmetric] supp_inv_bound)
  have [simp]: "Umap u \<circ> (Umap (inv u)) = id" unfolding fun_eq_iff
    by (simp add: u iu Umap_comp[symmetric])
  show "?R \<subseteq> ?L" unfolding dd_def[symmetric] d using Umap_Udtor[OF iu, of dd]
    apply (auto simp: u iu term_pre.map_comp map_sum.comp
        permute_comp0s permute_id0s Umap_comp[symmetric] map_sum.id term_pre.map_id0)
    apply (drule subsetD)
     apply assumption
    apply (erule imageE)
    apply hypsubst
apply (auto simp: u iu term_pre.map_comp map_sum.comp
        permute_comp0s permute_id0s Umap_comp[symmetric] map_sum.id term_pre.map_id0 sum.map_ident permute_ids[unfolded id_def])
    apply (unfold sum.map_ident id_def term_pre.map_ident)
    apply assumption
    done

qed


(*************************************)
(* The raw-term-based model infrastructure *)

definition Utor :: "'a::var U \<Rightarrow> ('a, 'a, 'a raw_term + 'a U, 'a raw_term + 'a U) term_pre set" where
  "Utor d \<equiv>  map_term_pre id id (map_sum TT_rep id) (map_sum TT_rep id) ` (Udtor d)"

abbreviation raw_Umap :: "('a::var \<Rightarrow> 'a) \<Rightarrow> 'a U \<Rightarrow> 'a U" where
  "raw_Umap \<equiv> Umap"

abbreviation raw_UFVars :: "'a::var U \<Rightarrow> 'a set" where
  "raw_UFVars \<equiv> UFVars"

definition raw_UFVarsBD :: "('a::var, 'a, 'a raw_term + 'a U, 'a raw_term + 'a U) term_pre \<Rightarrow> 'a set" where
  "raw_UFVarsBD X \<equiv> \<Union>(case_sum FVars_raw_term raw_UFVars ` set3_term_pre X) - set2_term_pre X"

lemmas raw_UFVars_def2 = trans[OF meta_eq_to_obj_eq[OF FVars_term_def[of "TT_abs _"]] alpha_FVars[OF TT_rep_abs], symmetric]

(* Preterm-based version of the assumptions: *)

(*  *)
lemmas raw_Umap_id = Umap_id

lemmas raw_Umap_comp = Umap_comp

lemma FVarsBD_FFVarsBD:
  "raw_UFVarsBD X = FFVarsBD (map_term_pre id id (map_sum TT_abs id) (map_sum TT_abs id) X)"
  unfolding raw_UFVarsBD_def FFVarsBD_def raw_UFVars_def2
  apply(simp add: raw_UFVars_def2 case_sum_map_sum supp_id_bound term_pre.set_map)
  unfolding o_def id_def ..

term rel_term_pre
term mr_rel_term_pre

lemmas supp_comp_bound = supp_comp_bound[OF _ _ infinite_UNIV]

lemma abs_rep_id[simp]: "TT_abs o TT_rep = id"
  using TT_abs_rep by fastforce

definition asSS :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "asSS f \<equiv> if |supp f| <o |UNIV::'a set| then f else id"

lemma DTOR_mapD:
  assumes "{X,X'} \<subseteq> Utor d"
  shows "\<exists>u. bij (u::'a::var\<Rightarrow>'a) \<and> |supp u| <o |UNIV::'a set| \<and> id_on (raw_UFVarsBD X) u \<and>
     mr_rel_term_pre id u
       (rel_sum (\<lambda> t t'. alpha_term (permute_raw_term u t) t') (\<lambda> d d'. raw_Umap u d = d'))
(rel_sum alpha_term (=))
     X X'"
proof-
  define XX XX' where
    "XX \<equiv> map_term_pre id id (map_sum TT_abs id) (map_sum TT_abs id) X" and
    "XX' \<equiv> map_term_pre id id (map_sum TT_abs id) (map_sum TT_abs id) X'"
  have 0: "{XX,XX'} \<subseteq> Udtor d" using assms unfolding XX_def XX'_def Utor_def
    by (auto simp: Umap_comp[symmetric] map_sum.comp TT_abs_rep map_sum.id
        supp_id_bound term_pre.map_comp term_pre.map_id)
  then obtain u where u: "bij u" "|supp u| <o |UNIV::'a set|" "id_on (FFVarsBD XX) u"
    and m: "map_term_pre id u (map_sum (permute_term u) (Umap u)) id XX = XX'"
    using Udtor_Umap[OF 0] by auto
  have [simp]: "asSS (asBij u) = u"  "asSS u = u" using u unfolding asSS_def by auto
  show ?thesis
  proof(rule exI[of _ u], safe )
    show "id_on (raw_UFVarsBD X) u"
      using u(3) unfolding id_on_def XX_def FVarsBD_FFVarsBD by auto
    show "mr_rel_term_pre id u  (rel_sum (\<lambda>t. alpha_term (permute_raw_term u t)) (\<lambda>d d'. raw_Umap u d = d')) (rel_sum alpha_term (=)) X X'"
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

lemma Utor_ne:
  "Utor d \<noteq> {}"
  unfolding Utor_def using Udtor_ne by auto

lemma raw_UFVars_Utor:
  assumes "X \<in> Utor d"
  shows "set1_term_pre X \<union> \<Union>(case_sum FVars_raw_term raw_UFVars ` set4_term_pre X) \<union> raw_UFVarsBD X \<subseteq> raw_UFVars d"
proof-
  define XX where "XX \<equiv> map_term_pre id id (map_sum TT_abs id) (map_sum TT_abs id) X"
  have 0: "XX \<in> Udtor d" using assms unfolding XX_def Utor_def
    by (auto simp: term_pre.map_comp map_sum.comp TT_abs_rep map_sum.id term_pre.map_id supp_id_bound)
  show ?thesis using FVars_term_Udtor[OF 0] unfolding FVarsBD_FFVarsBD XX_def
    apply (simp add: term_pre.set_map raw_UFVars_def2 case_sum_map_sum supp_id_bound) unfolding raw_UFVars_def2 o_def
      map_sum.simps id_def by simp
qed

lemma rel_set_reflI:
  assumes "\<And>a. a \<in> A \<Longrightarrow> r a a"
  shows "rel_set r A A"
  using assms unfolding rel_set_def by auto

lemma raw_Umap_Utor:
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a::var set|"
  shows
    "rel_set
  (mr_rel_term_pre u u
     (rel_sum (\<lambda> t t'. alpha_term (permute_raw_term u t) t') (\<lambda> d d'. raw_Umap u d = d'))
     (rel_sum (\<lambda> t t'. alpha_term (permute_raw_term u t) t') (\<lambda> d d'. raw_Umap u d = d')))
 (Utor d)
 (Utor (raw_Umap u d))"
  unfolding Utor_def
  by (auto intro!: rel_set_reflI term_pre.rel_refl_strong sum.rel_refl_strong 
      simp: Umap_Udtor_strong[OF u, of d] rel_set_image u term_pre.mr_rel_map OO_def Grp_def sum.rel_map 
      permute_term_def asSS_def alpha_syms term_pre.mr_rel_id[symmetric] TT_rep_abs
      image_comp map_sum.comp supp_id_bound) 

(*    *)

definition suitable ::  "('a::var U \<Rightarrow> ('a,'a,'a raw_term + 'a U,'a raw_term + 'a U) term_pre) \<Rightarrow> bool" where
  "suitable pick \<equiv> \<forall> d. pick d \<in> Utor d"

definition f :: "('a::var U \<Rightarrow> ('a,'a,'a raw_term + 'a U,'a raw_term + 'a U) term_pre) \<Rightarrow> 'a U => 'a raw_term" where
  "f pick \<equiv> corec_raw_term pick"

thm raw_term.corec[of "pick o Utor", unfolded f_def[symmetric]]

lemma f_simps:
  "f pick d = raw_term_ctor (map_term_pre id id (case_sum id (f pick)) (case_sum id (f pick)) (pick d))"
  apply(subst raw_term.corec[of pick, unfolded f_def[symmetric]]) unfolding id_def ..

lemma f_ctor:
  "raw_term_ctor x = f pick d \<Longrightarrow>
 x = map_term_pre id id (case_sum id (f pick)) (case_sum id (f pick)) (pick d)"
  using f_simps[of pick d] by simp

lemma suitable_FVarsD:
  assumes "suitable pick"
  shows "set1_term_pre (pick d) \<union> \<Union>(case_sum FVars_raw_term raw_UFVars ` set4_term_pre (pick d)) \<union> raw_UFVarsBD (pick d)
       \<subseteq> raw_UFVars d"
  using raw_UFVars_Utor[of "pick d"] using assms[unfolded suitable_def] by auto

(*  *)

lemma f_FVarsD:
  assumes p: "suitable pick"
  shows "FVars_raw_term (f pick d) \<subseteq> raw_UFVars d"
proof safe
  fix a assume aa: "a \<in> FVars_raw_term (f pick d)"
  define t where "t = f pick d"
  show "a \<in> raw_UFVars d" using aa[unfolded t_def[symmetric]] using t_def unfolding FVars_raw_term_def mem_Collect_eq
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
    have a: "a \<in> case_sum FVars_raw_term raw_UFVars td"
      using 2 unfolding t by(cases td) (auto simp: FVars_raw_term_def)
    have "a \<notin> set2_term_pre (pick d)" using `a \<notin> set2_term_pre x` unfolding x by(auto simp: term_pre.set_map supp_id_bound)
    thus ?case using a td apply (intro rev_subsetD[OF _ fvd]) unfolding raw_UFVarsBD_def by auto 
  next
    case (3 t x a)
    note x = f_ctor[OF `raw_term_ctor x = f pick d`]  
    note fvd = suitable_FVarsD[OF assms, of d]
    from `t \<in> set4_term_pre x` obtain td where t: "t = case_sum id (f pick) td" 
      and td: "td \<in> set4_term_pre (pick d)" unfolding x by (auto simp add: term_pre.set_map supp_id_bound)
    have a: "a \<in> case_sum FVars_raw_term raw_UFVars td"
      using 3 unfolding t apply (cases td) by (auto simp: FVars_raw_term_def)
    show ?case using a td by (intro rev_subsetD[OF _ fvd]) auto
  qed
qed

lemma rel_F_suitable_mapD:
  assumes pp': "suitable pick" "suitable pick'"
    and u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a::var set|"
  shows "\<exists> v. bij v \<and> |supp v| <o |UNIV::'a set| \<and> id_on (raw_UFVarsBD (pick d)) v \<and>
 mr_rel_term_pre u (u o v)
   (rel_sum (\<lambda>t t'. alpha_term (permute_raw_term (u o v) t) t')
            (\<lambda>d d'. raw_Umap (u o v) d = d'))
   (rel_sum (\<lambda>t t'. alpha_term (permute_raw_term u t) t')
            (\<lambda>d d'. d' = raw_Umap u d))
 (pick d)
 (pick' (raw_Umap u d))"
proof- 
  have p: "pick d \<in> Utor d" and p': "pick' (raw_Umap u d) \<in> Utor (raw_Umap u d)" 
    using pp' unfolding suitable_def by auto
  obtain X where X: "X \<in> Utor d" and 0: 
    "mr_rel_term_pre u u 
       (rel_sum (\<lambda>t. alpha_term (permute_raw_term u t)) (\<lambda>d. (=) (raw_Umap u d)))
       (rel_sum (\<lambda>t. alpha_term (permute_raw_term u t)) (\<lambda>d. (=) (raw_Umap u d)))
     X (pick' (raw_Umap u d))"
    using raw_Umap_Utor[OF u, of d] p' unfolding rel_set_def by auto
  obtain v where v: "bij v" "|supp v| <o |UNIV::'a set|" "id_on (raw_UFVarsBD (pick d)) v" 
    and 2: 
    "mr_rel_term_pre id v
      (rel_sum (\<lambda>t. alpha_term (permute_raw_term v t)) (\<lambda>d. (=) (raw_Umap v d)))
      (rel_sum alpha_term (=)) 
   (pick d) X" using DTOR_mapD[of "pick d" X d] using pp' X unfolding suitable_def by auto
  show ?thesis apply(rule exI[of _ v], simp add: v)
    apply(rule term_pre.mr_rel_mono_strong0[rotated -5])
              apply (rule term_pre.mr_rel_OO[THEN fun_cong, THEN fun_cong, THEN iffD2, rotated -1, OF relcomppI, OF 2 0])
              apply(auto simp: u v supp_comp_bound supp_inv_bound supp_id_bound)
    subgoal for td1 td3 td2 using alpha_refls
      apply(cases td1) apply auto 
       apply(cases td2) apply auto  apply(cases td3) apply (auto  simp: u v permute_raw_comps supp_inv_bound 
          ) using alpha_bij_eqs alpha_trans  using u(1) u(2)
      apply (smt (verit, best) permute_raw_comps v(1,2))
      apply(cases td2) apply auto  apply(cases td3) 
      by (auto simp: u v permute_raw_comps raw_Umap_comp[symmetric])
    subgoal for td1 td3 td2 using alpha_refls
      apply(cases td1) apply auto 
       apply(cases td2) apply auto  apply(cases td3) apply auto
       apply (smt alpha_bij_eqs alpha_trans rel_sum_simps(1) u(1) u(2))
      apply(cases td2) apply auto  apply(cases td3) by auto . 
qed

lemma map_comp_ids:
  assumes "|supp f1| <o |UNIV|"
    "bij f2"
    "|supp f2| <o |UNIV|"
  shows "map_term_pre f1 f2 (g3 \<circ> f3) (g4 \<circ> f4) v = map_term_pre id id g3 g4 (map_term_pre f1 f2 f3 f4 v)"
proof -
  have id_laws: "bij id" "|supp id| <o |UNIV|"
    by (simp add: supp_id)+
  have "map_term_pre (id \<circ> f1) (id \<circ> f2) (g3 \<circ> f3) (g4 \<circ> f4) v = map_term_pre id id g3 g4 (map_term_pre f1 f2 f3 f4 v)"
    apply (subst term_pre.map_comp[symmetric, OF _ _ _ id_laws(2) id_laws])
       apply assumption (* huh? *)
    oops

(* The "monster lemma": swapping and "pick"-irrelevance covered in one shot: *)

lemma f_swap_alpha:
  assumes p: "suitable pick" and p': "suitable pick'"
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a::var set|"
  shows "alpha_term (permute_raw_term u (f pick d)) (f pick' (raw_Umap u d))"
proof-
  let ?\<phi> = "\<lambda> tL tR. \<exists> u d. bij u \<and> |supp u| <o |UNIV::'a set| \<and>
   tL = permute_raw_term u (f pick d) \<and> tR = f pick' (raw_Umap u d)"
  {fix tL tR assume "?\<phi> tL tR"
    hence "alpha_term tL tR"
    proof(induction rule: alpha_term.coinduct)
      case (alpha_term xL xR)
      term xL
      term un_raw_term_ctor
      then obtain u d
        where u: "bij u" "|supp u| <o |UNIV::'a set|"
          and "xL = permute_raw_term u (f pick d)" "xR = f pick' (raw_Umap u d)" by auto
      hence xL: "xL = raw_term_ctor (map_term_pre u u (permute_raw_term u \<circ> case_sum id (f pick)) (permute_raw_term u \<circ> case_sum id (f pick)) (pick d))"
        and xR: "xR = raw_term_ctor (map_term_pre id id (case_sum id (f pick')) (case_sum id (f pick')) (pick' (raw_Umap u d)))"
        using f_simps[of "pick"] f_simps[of "pick'"]
        by (auto simp: u permute_raw_simps term_pre.map_comp supp_id_bound)
          (*  *)
      obtain v where v: "bij v" "|supp v| <o |UNIV::'a set|" and iv: "id_on (raw_UFVarsBD (pick d)) v"
        and rv:
        "mr_rel_term_pre u (u \<circ> v)
       (rel_sum (\<lambda>t. alpha_term (permute_raw_term (u \<circ> v) t)) (\<lambda>d. (=) (raw_Umap (u \<circ> v) d)))
       (rel_sum (\<lambda>t. alpha_term (permute_raw_term u t)) (\<lambda>d d'. d' = raw_Umap u d))
     (pick d) (pick' (raw_Umap u d)) "
        using rel_F_suitable_mapD[OF p p' u(1,2)] by blast
      define w where "w \<equiv> u o v o inv u"
      have w: "bij w" "|supp w| <o |UNIV::'a set|" by (simp_all add: w_def u v supp_comp_bound supp_inv_bound)
      
      have fv_xL: "FVars_raw_term xL \<subseteq> u ` (raw_UFVarsBD (pick d))"
        thm term_pre.map_comp[symmetric]
         f_FVarsD[OF p] u term_pre.set_map FVars_raw_permutes[OF u] raw_UFVarsBD_def permute_raw_simps[OF u] permute_raw_sels[OF u]
        unfolding xL apply (auto simp: u term_pre.set_map FVars_raw_permutes raw_UFVarsBD_def)
        (* subgoal for td a apply (cases td) by fastforce+ . *)
      have fv_p'd: "raw_UFVarsBD (pick d) \<subseteq> raw_UFVars d"
        using raw_UFVars_Utor[of "pick d"] p unfolding suitable_def by auto
      have "id_on (u ` (raw_UFVarsBD (pick d))) w"
        using iv fv_p'd unfolding id_on_def xL w_def eq_on_def id_on_def by (auto simp: term_pre.set_map u)
      hence iw: "id_on (FVars_raw_term xL) w" using fv_xL unfolding id_on_def by auto
      thm exI[of _ w]
      show ?case proof
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