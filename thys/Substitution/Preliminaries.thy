theory Preliminaries 
  imports "Binders.MRBNF_Recursor"
begin

(**************************)
(* Preliminaries *)

declare supp_id_bound[simp] supp_inv_bound[simp] infinite_UNIV[simp]

definition "IImsupp' Inj Vr \<rho> = SSupp Inj \<rho> \<union> IImsupp Inj Vr \<rho>"

term curry
definition "uncurry f \<equiv> \<lambda>(a,b). f a b" 
lemma uncorry_apply[simp]: "uncurry f (a,b) = f a b"
  unfolding uncurry_def by auto

lemma fst_comp_id[simp]: "fst \<circ> (\<lambda>e. (e, p)) = id" by auto

lemma tri_Un1: "A \<subseteq> B \<union> C \<Longrightarrow> A \<union> B \<subseteq> B \<union> C" by auto
lemma tri_Un3: "A \<union> A' \<union> A'' \<subseteq> B \<union> C \<Longrightarrow> B \<union> A \<union> A' \<union> A'' \<subseteq> B \<union> C" by auto

lemma A_Int_Un_emp: "A \<inter> (B \<union> C) = {} \<longleftrightarrow> A \<inter> B = {} \<and> A \<inter> C = {}" by auto

lemma bij_inv_Un_triv: "bij \<sigma> \<Longrightarrow> \<sigma> ` A \<inter> B = {} \<longleftrightarrow> A \<inter> inv \<sigma> ` B = {}"
  by (metis bij_def empty_is_image image_Int image_inv_f_f surj_imp_inj_inv)

lemma bij_in_inv_Un_triv: "bij \<sigma> \<Longrightarrow> inv \<sigma> a \<in> B \<longleftrightarrow> a \<in> \<sigma> ` B"
  by (metis bij_inv_eq_iff imageE image_eqI)

lemma incl_Un_triv3: "A1 \<union> A2 \<union> A3 \<subseteq> A \<Longrightarrow> A1 \<subseteq> A \<and> A2 \<subseteq> A \<and> A3 \<subseteq> A" by auto

lemma incl_Un3_triv3: "A1 \<subseteq> B1 \<Longrightarrow> A2 \<subseteq> B2 \<union> P \<Longrightarrow> A3 \<subseteq> B3 \<union> P \<Longrightarrow> A1 \<union> A2 \<union> A3 \<subseteq> B1 \<union> B2 \<union> B3 \<union> P" 
by auto

lemma triv_Un4_remove: "A1 \<union> A2 \<union> A3 \<subseteq> B1 \<union> B2 \<union> B3 \<union> P \<Longrightarrow> A1 \<union> A2 \<union> A3 \<union> P \<subseteq> B1 \<union> B2 \<union> B3 \<union> P"
by auto

definition small :: "('a::var \<Rightarrow> 'a) \<Rightarrow> bool" where 
"small \<sigma> \<equiv> countable (supp \<sigma>)" 

declare supp_id[simp,intro] (*: "supp id = {}" unfolding supp_def by auto *)
lemma small_id[simp,intro]: "small id" unfolding small_def by auto
lemma supp_id'[simp,intro]: "supp (\<lambda>a. a) = {}" unfolding supp_def by auto
lemma small_id'[simp,intro]: "small (\<lambda>a. a)" unfolding small_def by auto

thm supp_o
(* lemma supp_o: "supp (\<sigma> o \<tau>) \<subseteq> supp \<sigma> \<union> supp \<tau>" unfolding supp_def by auto *)
lemma small_o[simp]: "small \<sigma> \<Longrightarrow> small \<tau> \<Longrightarrow> small (\<sigma> o \<tau>)" 
unfolding small_def using supp_o by (metis countable_Un_iff countable_subset)

lemma supp_inv[simp]: "bij \<sigma> \<Longrightarrow> small \<sigma> \<Longrightarrow> supp (inv \<sigma>) = supp \<sigma>" 
unfolding supp_def by (metis bij_inv_eq_iff)
lemma small_inv[simp]: "bij \<sigma> \<Longrightarrow> small (inv \<sigma>) \<longleftrightarrow> small \<sigma>" 
unfolding small_def by (metis bij_betw_inv_into inv_inv_eq small_def supp_inv)

(* declare bij_id[intro] *)
lemmas bij_id'[simp,intro]=bij_id[unfolded id_def]
(* declare bij_comp[simp] *)
(* declare bij_imp_bij_inv[simp] *)

lemmas bij_inv_id1 = inv_o_simp2 (* [simp] *) (* : "bij f \<Longrightarrow> f o inv f = id" unfolding fun_eq_iff *)
 (*  by (simp add: bij_def surj_iff) *)
lemmas bij_inv_id2 = inv_o_simp1 
(*[simp]: "bij f \<Longrightarrow> inv f o f = id" unfolding fun_eq_iff 
by (simp add: bij_def surj_iff) *)

end 