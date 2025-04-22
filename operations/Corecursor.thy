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
  shows "FFVars t = set1_F x \<union> (\<Union>z \<in> set4_term_pre x. FFVars z) \<union> FFVarsB x"
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
and Umap_comp0: "bij f \<Longrightarrow> |supp (f::'a::var \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> bij g \<Longrightarrow> |supp (g::'a::var \<Rightarrow> 'a)| <o |UNIV::'a set|
  \<Longrightarrow> Umap f \<circ> Umap g = Umap (f \<circ> g)"
and Umap_cong0: "bij f \<Longrightarrow> |supp (f::'a::var \<Rightarrow> 'a)| <o |UNIV::'a set|
  \<Longrightarrow> (\<And>a. a \<in> UFVars d \<Longrightarrow> f a = a) \<Longrightarrow> Umap f d = d"
(*and Umap_UFVars: "bij f \<Longrightarrow> |supp (f::'a::var \<Rightarrow> 'a)| <o |UNIV::'a set|
  \<Longrightarrow> UFVars (Umap f d) = f ` UFVars d"*)

lemma Umap_id0: "Umap id = id"
  apply (rule ext)
  apply (rule trans[OF _ id_apply[symmetric]])
  apply (rule Umap_cong0)
    apply (rule bij_id supp_id_bound)+
  apply (rule id_apply)
  done

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
  apply (rule trans[OF Umap_id0[THEN fun_cong]])
  apply (rule id_apply)
  done

lemma Umap_comp:
  "bij (u::'a\<Rightarrow>'a) \<Longrightarrow> |supp u| <o |UNIV::('a::var) set| \<Longrightarrow> bij v \<Longrightarrow> |supp v| <o |UNIV::'a set| \<Longrightarrow>
 Umap (u o v) d = Umap u (Umap v d)"
  apply (subst Umap_comp0[symmetric])
      apply assumption+
  apply (rule comp_apply)
  done

lemma Umap_Udtor_strong:
  assumes u: "bij (u::'a::var\<Rightarrow>'a)" "|supp u| <o |UNIV::'a set|"
  shows
    "Udtor (Umap u d) =
 image
   (map_term_pre u u (map_sum (permute_term u) (Umap u)) (map_sum (permute_term u) (Umap u)))
   (Udtor d)"
proof -
  have x: "d = Umap (inv u) (Umap u d)"
    apply (rule sym)
    apply (rule trans[OF Umap_comp[symmetric]])
        apply (rule bij_imp_bij_inv supp_inv_bound assms)+
    apply (subst inv_o_simp1, rule assms)+
    apply (rule trans[OF Umap_id0[THEN fun_cong]])
    apply (rule id_apply)
    done
    show ?thesis
  apply (rule subset_antisym)
       apply (rule Umap_Udtor[OF assms])
      apply (subst x)
      apply (rule image_subsetI)
      apply (drule Umap_Udtor[THEN subsetD, rotated -1])
        apply (rule bij_imp_bij_inv supp_inv_bound assms)+
      apply (erule imageE)
      apply hypsubst
      apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<in>)"]])
       apply (rule term_pre.map_comp)
             apply (rule bij_imp_bij_inv supp_inv_bound assms)+
      apply (unfold map_sum.comp)
      apply (subst inv_o_simp2 permute_comp0s Umap_comp0, (rule bij_imp_bij_inv supp_inv_bound assms)+)+
      apply (unfold Umap_id0 permute_id0s map_sum.id term_pre.map_id)
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
  apply (unfold raw_UFVarsBD_def FFVarsBD_def raw_UFVars_def2)
  apply (subst term_pre.set_map[OF supp_id_bound bij_id supp_id_bound])+
  apply (subst image_id)
  apply (subst image_image)
  apply (subst case_sum_map_sum)
  apply (subst comp_id)
  apply (subst comp_def)
  apply (rule refl)
  done

lemmas supp_comp_bound = supp_comp_bound[OF _ _ infinite_UNIV]

lemma abs_rep_id: "TT_abs o TT_rep = id"
  apply (unfold comp_def)
  apply (subst TT_abs_rep)
  apply (fold id_def)
  apply (rule refl)
  done

definition asSS :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "asSS f \<equiv> if |supp f| <o |UNIV::'a set| then f else id"

lemma DTOR_mapD:
  shows "{X,X'} \<subseteq> Utor d \<Longrightarrow> \<exists>u. bij (u::'a::var\<Rightarrow>'a) \<and> |supp u| <o |UNIV::'a set| \<and> id_on (raw_UFVarsBD X) u \<and>
     mr_rel_term_pre id u
       (rel_sum (\<lambda> t t'. alpha_term (permute_raw_term u t) t') (\<lambda> d d'. raw_Umap u d = d'))
(rel_sum alpha_term (=))
     X X'"
  apply (drule image_mono[of _ _ "map_term_pre id id (map_sum TT_abs id) (map_sum TT_abs id)"])
  apply (unfold image_insert image_empty Utor_def image_comp)
  apply (subst (asm) term_pre.map_comp0[symmetric], (rule supp_id_bound bij_id)+)
  apply (unfold id_o map_sum.comp abs_rep_id map_sum.id term_pre.map_id0 image_id)
  apply (drule alpha_Udtor)
  apply (erule exE conjE)+
  apply (subst (asm) term_pre.set_map term_pre.map_comp, (rule supp_id_bound bij_id | assumption)+)+
  apply (unfold image_id id_o o_id map_sum.comp)
  apply (drule term_pre.mr_rel_eq[THEN fun_cong, THEN fun_cong, THEN iffD2])
  apply (subst (asm) term_pre.mr_rel_map, (rule supp_id_bound bij_id | assumption)+)
  apply (unfold id_o o_id)
  apply (subst (asm) term_pre.mr_rel_map, (rule supp_id_bound bij_id | assumption)+)
  apply (unfold inv_id id_o o_id relcompp_conversep_Grp)
  apply (unfold Grp_OO)
  apply (rule exI)+
  apply (rule conjI[rotated])+
     apply (erule term_pre.mr_rel_mono_strong0[rotated -5])
              apply (rule ballI, rule refl)+
          (* REPEAT_DETERM *)
            apply (rule ballI impI)+
            apply (drule sum.rel_eq[THEN fun_cong, THEN fun_cong, THEN iffD2])
            apply (unfold sum.rel_map comp_def id_apply)[1]
            apply (erule sum.rel_mono_strong)
             apply (subst (asm) permute_abs, assumption+)?
             apply (drule TT_total_abs_eq_iffs[THEN iffD1])
             apply assumption
            apply assumption
    (* repeated *)
            apply (rule ballI impI)+
            apply (drule sum.rel_eq[THEN fun_cong, THEN fun_cong, THEN iffD2])
            apply (unfold sum.rel_map comp_def id_apply)[1]
            apply (erule sum.rel_mono_strong)
             apply (subst (asm) permute_abs, assumption+)?
             apply (drule TT_total_abs_eq_iffs[THEN iffD1])
             apply assumption
           apply assumption
      (* END REPEAT_DETERM *)
          apply (rule supp_id_bound bij_id | assumption)+
    apply (unfold raw_UFVarsBD_def raw_UFVars_def2 image_comp[unfolded comp_def] case_sum_map_sum o_id)
    apply (unfold comp_def)
    apply assumption+
  done

lemma Utor_ne:
  "Utor d \<noteq> {}"
  by (unfold Utor_def arg_cong[OF image_is_empty, of Not])
     (rule Udtor_ne)

lemma Utor_abs_Udtor: "X \<in> Utor d \<Longrightarrow> map_term_pre id id (map_sum TT_abs id) (map_sum TT_abs id) X \<in> Udtor d"
  apply (unfold Utor_def)
  apply (erule imageE)
  apply hypsubst_thin
  apply (subst term_pre.map_comp)
    apply (rule supp_id_bound bij_id)+
  apply (subst map_sum.comp)+
  apply (subst id_o)+
  apply (subst abs_rep_id)+
  apply (subst map_sum.id)+
  apply (subst term_pre.map_id)
  apply assumption
  done

lemma raw_UFVars_def2_comp: "FVars_raw_term = FVars_term \<circ> TT_abs"
  apply (unfold raw_UFVars_def2)
  apply (unfold comp_apply)
  apply (rule refl)
  done

lemma aux_raw_UFVars_Utor: "case_sum FVars_term raw_UFVars ` set4_term_pre (map_term_pre id id (map_sum TT_abs id) (map_sum TT_abs id) X) =
       case_sum FVars_raw_term raw_UFVars ` set4_term_pre X"
  apply (unfold raw_UFVars_def2_comp)
  (* what could be a good way to do this without specifying the
     exact subst position? *)
  apply (subst (50) o_id[symmetric])
  apply (subst case_sum_o_map_sum[symmetric])
  apply (subst image_comp[symmetric])
  apply (rule image_cong[OF _ refl])
  apply (rule term_pre.set_map)
  apply (rule supp_id_bound | rule bij_id)+
  done

lemma raw_UFVars_Utor:
  "X \<in> Utor d \<Longrightarrow> set1_term_pre X \<union> \<Union>(case_sum FVars_raw_term raw_UFVars ` set4_term_pre X) \<union> raw_UFVarsBD X \<subseteq> raw_UFVars d"
  apply (drule FVars_term_Udtor[OF Utor_abs_Udtor])
  apply (unfold FVarsBD_FFVarsBD)
  apply (subst (asm) term_pre.set_map, (rule supp_id_bound bij_id)+)
  apply (subst(asm) aux_raw_UFVars_Utor)
  apply (subst (asm) image_id)
  apply assumption
  done

lemma rel_set_reflI:
  "(\<And>a. a \<in> A \<Longrightarrow> r a a) \<Longrightarrow> rel_set r A A"
  by (unfold rel_set_def Bex_def)
     (rule ballI exI conjI | assumption)+

lemma raw_Umap_Utor:
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a::var set|"
  shows
    "rel_set
  (mr_rel_term_pre u u
     (rel_sum (\<lambda> t t'. alpha_term (permute_raw_term u t) t') (\<lambda> d d'. raw_Umap u d = d'))
     (rel_sum (\<lambda> t t'. alpha_term (permute_raw_term u t) t') (\<lambda> d d'. raw_Umap u d = d')))
 (Utor d)
 (Utor (raw_Umap u d))"
  apply (unfold Utor_def)
  apply (subst Umap_Udtor_strong[OF u, of d])
  apply (subst image_comp)
  apply (subst term_pre.map_comp0[symmetric])
      apply (rule assms supp_id_bound bij_id)+
  apply (subst map_sum.comp)+
  apply (subst id_o)+
  apply (subst rel_set_image)+
  apply (rule rel_set_reflI)
  apply (subst term_pre.mr_rel_map)
      apply (rule supp_id_bound bij_id u)+
  apply (subst o_id)+
  apply (subst term_pre.mr_rel_map | rule u)+
  apply (subst inv_o_simp1 | rule u)+
  apply (unfold relcompp_conversep_Grp Grp_OO term_pre.mr_rel_id[symmetric])
  apply (subst sum.rel_map)+
  apply (unfold permute_term_def)
  apply (rule term_pre.rel_refl)
(* REPEAT *)
   apply (rule sum.rel_refl)
  apply (subst comp_apply)
    apply (rule TT_rep_abs_syms)
   apply (subst id_apply)
   apply (rule refl)
(* REPEAT *)
   apply (rule sum.rel_refl)
  apply (subst comp_apply)
    apply (rule TT_rep_abs_syms)
   apply (subst id_apply)
  apply (rule refl)
  done

(*    *)

definition suitable ::  "('a::var U \<Rightarrow> ('a,'a,'a raw_term + 'a U,'a raw_term + 'a U) term_pre) \<Rightarrow> bool" where
  "suitable pick \<equiv> \<forall> d. pick d \<in> Utor d"

definition f :: "('a::var U \<Rightarrow> ('a,'a,'a raw_term + 'a U,'a raw_term + 'a U) term_pre) \<Rightarrow> 'a U => 'a raw_term" where
  "f pick \<equiv> corec_raw_term pick"

thm raw_term.corec[of "pick o Utor", unfolded f_def[symmetric]]

lemma f_simps:
  "f pick d = raw_term_ctor (map_term_pre id id (case_sum id (f pick)) (case_sum id (f pick)) (pick d))"
  apply(subst raw_term.corec[of pick, unfolded f_def[symmetric]])
  apply (unfold id_def)
  apply (rule refl)
  done

lemma f_ctor:
  assumes "raw_term_ctor x = f pick d"
  shows "x = map_term_pre id id (case_sum id (f pick)) (case_sum id (f pick)) (pick d)"
  by (rule trans[OF assms f_simps, unfolded raw_term.inject])

lemma suitable_FVarsD:
  assumes "suitable pick"
  shows "set1_term_pre (pick d) \<union> \<Union>(case_sum FVars_raw_term raw_UFVars ` set4_term_pre (pick d)) \<union> raw_UFVarsBD (pick d)
       \<subseteq> raw_UFVars d"
  by (rule allE[OF assms[unfolded suitable_def]])
     (erule raw_UFVars_Utor)

(*  *)

lemma f_FVarsD_td:
  assumes "raw_term_ctor x = f pick d"
  shows "t \<in> set3_term_pre x \<Longrightarrow> (\<exists>td. t = case_sum id (f pick) td \<and> td \<in> set3_term_pre (pick d))"
        "t \<in> set4_term_pre x \<Longrightarrow> (\<exists>td. t = case_sum id (f pick) td \<and> td \<in> set4_term_pre (pick d))"
   apply (unfold f_ctor[OF assms])
(* REPEAT *)
  apply (subst (asm) term_pre.set_map, (rule bij_id supp_id_bound)+)
  apply (erule imageE)
  apply (rule exI)
  apply (rule conjI)
    apply assumption+
(* REPEAT *)
  apply (subst (asm) term_pre.set_map, (rule bij_id supp_id_bound)+)
  apply (erule imageE)
  apply (rule exI)
  apply (rule conjI)
   apply assumption+
  done

lemma f_FVarsD_aux:
  assumes "free_raw_term a t"
          "(\<And>d. t = f pick d \<Longrightarrow> a \<in> raw_UFVars d)"
shows "t = case_sum id (f pick) td \<Longrightarrow> a \<in> case_sum FVars_raw_term raw_UFVars td"
      apply (rule sumE[of td])
       apply hypsubst
       apply (subst sum.case)
      apply (unfold FVars_raw_term_def mem_Collect_eq)
       apply (insert assms(1))[1]
       apply (hypsubst_thin)
       apply (subst (asm) sum.case)
       apply (subst (asm) id_apply)
       apply assumption
       apply hypsubst
  apply (subst sum.case)
      apply (rule assms(2))
      apply (hypsubst_thin)
      apply (subst sum.case)
      apply (rule refl)
  done

lemma f_FVarsD:
  assumes p: "suitable pick"
  shows "FVars_raw_term (f pick d) \<subseteq> raw_UFVars d"
  apply (rule subsetI)
  apply (unfold FVars_raw_term_def mem_Collect_eq)
  subgoal
(* TODO: this seems to work, but requires additional work to be done in each subgoal
since the implications and universal quantifiers are now object-level instead of meta-level *)
    (* apply (erule free_raw_term.induct[where P = "\<lambda>x y. \<forall>d. y = f pick d \<longrightarrow> x \<in> raw_UFVars d", THEN allE]) *)
     apply (induction _ "(f pick d)" arbitrary: d rule: free_raw_term.induct)
    subgoal premises prems
 apply (rule le_supE[OF suitable_FVarsD[OF assms, unfolded Un_assoc]])
      apply (erule subsetD)
      apply (insert prems(1)[unfolded f_ctor[OF prems(2)]])
      apply (subst (asm) term_pre.set_map(1)[OF supp_id_bound bij_id supp_id_bound, unfolded image_id])
      apply assumption
      done
    subgoal premises prems
apply (rule rev_subsetD[OF _ suitable_FVarsD[OF assms]])
      apply (unfold raw_UFVarsBD_def)
      apply (rule UnI2)
      apply (rule f_FVarsD_td(1)[OF prems(5,1), THEN exE])
      apply (rule DiffI)
       apply (erule conjE)
       apply (drule f_FVarsD_aux[OF prems(2), rotated])
      apply (erule prems(3))
      apply (erule UN_I)
       apply assumption
      apply (insert prems(4)[unfolded f_ctor[OF prems(5)]])
      apply (subst (asm) term_pre.set_map, (rule supp_id_bound bij_id)+)
      apply (subst (asm) image_id)
      apply assumption
      done
    subgoal premises prems
      apply (rule rev_subsetD[OF _ suitable_FVarsD[OF assms]])
      apply (rule UnI1)
      apply (rule UnI2)
      apply (rule f_FVarsD_td(2)[OF prems(4,1), THEN exE])
      apply (erule conjE)
      apply (drule f_FVarsD_aux[OF prems(2), rotated])
      apply (erule prems(3))
      apply (erule UN_I)
      apply assumption
      done
    done
  done

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

abbreviation (input) "FVarsB x \<equiv> \<Union>(FVars_raw_term ` set3_term_pre x) - set2_term_pre x"

lemma alpha_coinduct2[consumes 1, case_names C]: 
  fixes t t' :: "'a::var raw_term"
  assumes 0: "\<phi> t t'" and 1:
    "\<And>x x' :: ('a,'a,'a raw_term,'a raw_term) term_pre. \<phi> (raw_term_ctor x) (raw_term_ctor x') \<Longrightarrow>
    \<exists>f. bij f \<and> |supp f| <o |UNIV::'a set| \<and>
    id_on (FVarsB x) f \<and> 
    mr_rel_term_pre id f 
 (\<lambda>t t'.  \<phi> (permute_raw_term f t) t' \<or> alpha_term (permute_raw_term f t) t')
 (\<lambda>t t'. \<phi> t t' \<or> alpha_term t t')
       x x'"
  shows "alpha_term t t'"
  apply(rule alpha_term.coinduct[of \<phi>, OF 0]) (*
  apply (drule arg_cong2[of _  _ _ _ "\<phi>", THEN iffD1, THEN 1, rotated -1])
      prefer 3
      apply (erule exE)
      apply (rule exI)+
      apply (rule conjI[rotated])
       apply (rule conjI[rotated])
      apply assumption
  using raw_term.nchotomy
     apply (rule exE)
  thm allI
      apply (rule allE[OF raw_term.nchotomy])
      apply simp
  apply assumption
  prefer 2
    using allE[OF raw_term.nchotomy]
    thm exE
  apply (rule raw_term.nchotomy)
  thm exE[OF 1, rotated]
     apply (rule exE[OF 1, rotated])
      prefer 2
  thm exE[OF 1]



        apply (rule prems)
       apply (insert prems)
       apply (insert 1)
      apply (rule prems)
    apply (rule exI)
    apply (rule exI)
    thm arg_cong2[of _  _ _ _ "\<phi>", THEN iffD1, THEN 1, rotated -1, THEN exE]
    apply (drule arg_cong2[of _  _ _ _ "\<phi>", THEN iffD1, THEN 1, rotated -1])
      prefer 3
      apply safe
    thm exE
    subgoal premises prems
      apply (rule exI)+
      apply (rule conjI[rotated])+
      prefer 4
      using prems(2) 
    apply (drule arg_cong2[of _  _ _ _ "\<phi>", THEN iffD1, THEN 1, rotated -1])
      prefer 3
      apply (rule exI)+
      apply (erule exE)

*)
  (*apply (rule exI)+
  apply (rule conjI[rotated])
   apply (rule conjI[rotated])
  using assms(2) arg_cong2[of _  _ _ _ "\<phi>", THEN iffD1, OF _ _ assms(1), THEN 1, THEN exE]*)
  (* subgoal premises prems for x1 x2
    apply (rule exI)+
    apply (rule conjI[rotated])
     apply (rule conjI[rotated])
      apply (rule exE)
       apply (rule arg_cong2[of _  _ _ _ "\<phi>", THEN iffD1, OF _ _ prems, THEN 1])
        prefer 3
        apply (rule conjI)
         apply (erule conjE)+
         apply blast (* TODO fix *)

         apply (rotate_tac 1)
    apply (erule TrueE)
    apply assumption
    using arg_cong2[of _  _ _ _ "\<phi>", THEN iffD1, OF _ _ prems, THEN 1]
    thm 1 prems arg_cong2[of _  _ _ _ "\<phi>", THEN iffD1, OF _ _ prems, THEN 1]
    thm prems trans fun_cong arg_cong2[of _  _ _ _ "\<phi>", THEN iffD1] iffD1
    apply (rule exI)+
    apply (rule conjI)
     prefer 2
     apply (rule conjI)
      prefer 2
      apply (rule exE[OF 1])
    apply
    apply (erule exE)
    apply (rule 1)
    using 1 prems *)
  using 1 apply auto subgoal for t1 t2
    apply (cases t1)
    apply (cases t2)
    apply auto
    done
  done

lemma alpha_cong:
  fixes u v :: "'a::var \<Rightarrow> 'a"
  assumes u: "bij u" "|supp u| <o |UNIV::'a set|" and v: "bij v" "|supp v| <o |UNIV::'a set|" 
  assumes uv: "\<And> a. a \<in> FVars_raw_term t \<Longrightarrow> u a = v a"
  shows "alpha_term (permute_raw_term u t) (permute_raw_term v t)" 
  apply (rule alpha_bijs | rule assms)+
   apply (rule eq_onI)
   apply (erule uv)
  apply (rule alpha_refls)
  done

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
    proof(induction rule: alpha_coinduct2)
      case (C xL xR)
      term xL
      term un_raw_term_ctor
      then obtain u d
        where u: "bij u" "|supp u| <o |UNIV::'a set|"
          and "raw_term_ctor xL = permute_raw_term u (f pick d)" "raw_term_ctor xR = f pick' (raw_Umap u d)" by auto
      hence xL: "xL = map_term_pre u u (permute_raw_term u \<circ> case_sum id (f pick)) (permute_raw_term u \<circ> case_sum id (f pick)) (pick d)"
        and xR: "xR = map_term_pre id id (case_sum id (f pick')) (case_sum id (f pick')) (pick' (raw_Umap u d))"
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
      
      have fv_xL: "FVarsB xL \<subseteq> u ` (raw_UFVarsBD (pick d))"
        using f_FVarsD[OF p] unfolding xL apply (auto simp: u term_pre.set_map FVars_raw_permutes raw_UFVarsBD_def)
        subgoal for td a apply (cases td) by fastforce+ .
      have fv_p'd: "raw_UFVarsBD (pick d) \<subseteq> raw_UFVars d"
        using raw_UFVars_Utor[of "pick d"] p unfolding suitable_def by auto
      have "id_on (u ` (raw_UFVarsBD (pick d))) w"
        using iv fv_p'd unfolding id_on_def xL w_def eq_on_def id_on_def by (auto simp: term_pre.set_map u)
      hence iw: "id_on (FVarsB xL) w" using fv_xL unfolding id_on_def by auto
      show ?case proof(rule exI[of _ w], safe)
        show "mr_rel_term_pre id w
     (\<lambda>t t'.
         (\<exists>u d. bij u \<and> |supp u| <o |UNIV::'a set| \<and> permute_raw_term w t = permute_raw_term u (f pick d) \<and> t' = f pick' (raw_Umap u d)) \<or>
         alpha_term (permute_raw_term w t) t')
     (\<lambda>t t'. (\<exists>u d. bij u \<and> |supp u| <o |UNIV::'a set| \<and> t = permute_raw_term u (f pick d) \<and> t' = f pick' (raw_Umap u d)) \<or> alpha_term t t') xL xR" unfolding xL xR
          apply(simp add: w u term_pre.mr_rel_map Grp_def OO_def supp_comp_bound supp_inv_bound permute_raw_comps supp_id_bound)
        proof(rule term_pre.mr_rel_mono_strong0[OF _ _ _ _ _ _ rv], auto)
          fix a assume "a \<in> set2_term_pre (pick d)"
          thus "u (v a) = w (u a)"
            unfolding w_def by (simp add: u v)
        next
          fix ttdL ttdR assume ttdLin: "ttdL \<in> set4_term_pre (pick d)"
            and ttdRin: "ttdR \<in> set4_term_pre (pick' (raw_Umap u d))"
            and r: "rel_sum (\<lambda>t. alpha_term (permute_raw_term u t)) (\<lambda>d d'. d' = raw_Umap u d) ttdL ttdR"
            and na: "\<not> alpha_term (permute_raw_term u (case_sum id (f pick) ttdL)) (case_sum id (f pick') ttdR)"
          {fix tL assume 000: "ttdL = Inl tL"
            then obtain tR where "ttdR = Inl tR"
              and  "alpha_term (permute_raw_term u tL) tR" "\<not> alpha_term (permute_raw_term u tL) tR" using r na by (cases ttdR, auto)
            moreover have "alpha_term (permute_raw_term u tL) (permute_raw_term u tL)"
              apply(rule alpha_cong) by (auto simp: u)
            ultimately have False using alpha_trans alpha_syms by blast
          }
          then obtain dd where ttdL: "ttdL = Inr dd" by (cases ttdL, auto)
          hence ttdR: "ttdR = Inr (raw_Umap u dd)" using r by(cases ttdR, auto)
          have fv_dd: "raw_UFVars dd \<subseteq> raw_UFVars d" using ttdLin unfolding ttdL
            using raw_UFVars_Utor p unfolding suitable_def by force
          show "\<exists>uu. bij uu \<and> |supp uu| <o |UNIV::'a set| \<and>
             (\<exists> dd. permute_raw_term u (case_sum id (f pick) ttdL) = permute_raw_term uu (f pick dd) \<and>
                    case_sum id (f pick') ttdR = f pick' (raw_Umap uu dd))"
            by (auto simp: u ttdL ttdR intro: exI[of _ u] exI[of _ dd])
        next
          fix ttdL ttdR assume ttdLin: "ttdL \<in> set3_term_pre (pick d)"
            and ttdRin: "ttdR \<in> set3_term_pre (pick' (raw_Umap u d))"
            and r: "rel_sum (\<lambda>t. alpha_term (permute_raw_term (u \<circ> v) t)) (\<lambda>d. (=) (raw_Umap (u \<circ> v) d)) ttdL ttdR"
            and na: "\<not> alpha_term (permute_raw_term (w \<circ> u) (case_sum id (f pick) ttdL)) (case_sum id (f pick') ttdR)"
          have uvw: "u \<circ> v = w \<circ> u" unfolding w_def by (auto simp: u)
          {fix tL assume 000: "ttdL = Inl tL"
            then obtain tR where "ttdR = Inl tR"
              and  "alpha_term (permute_raw_term (u \<circ> v) tL) tR" "\<not> alpha_term (permute_raw_term (w \<circ> u) tL) tR"
              using r na by (cases ttdR, auto)
            moreover have "alpha_term (permute_raw_term (u \<circ> v) tL) (permute_raw_term (w \<circ> u) tL)"
              unfolding uvw using alpha_refls .
            ultimately have False using alpha_trans alpha_syms by blast
          }
          then obtain dd where ttdL: "ttdL = Inr dd" by (cases ttdL, auto)
          hence ttdR: "ttdR = Inr (raw_Umap (u \<circ> v) dd)" using r by (cases ttdR, auto)
          show "\<exists>uu. bij uu \<and> |supp uu| <o |UNIV::'a set| \<and>
              (\<exists> dd. permute_raw_term (w \<circ> u) (case_sum id (f pick) ttdL) = permute_raw_term uu (f pick dd) \<and>
                     case_sum id (f pick') ttdR = f pick' (raw_Umap uu dd))"
            by (auto simp: u w supp_comp_bound ttdL ttdR uvw intro: exI[of _ "w o u"] exI[of _ dd])
        qed(simp_all add: w u v supp_comp_bound)
      qed(simp_all add: w iw)
    qed
  }
  thus ?thesis using assms by blast
qed

lemma f_alpha:
  assumes p: "suitable pick" and p': "suitable pick'"
  shows "alpha_term (f pick d) (f pick' d)"
  using f_swap_alpha[OF assms bij_id supp_id_bound, of d] by (simp add: permute_raw_ids)

(*******************************)
(* Committing to a particular pick function: *)

definition pick0 :: "'a::var U \<Rightarrow> ('a, 'a, 'a raw_term + 'a U, 'a raw_term + 'a U) term_pre" where
  "pick0 \<equiv> SOME pick. suitable pick"

lemma exists_suitable:
  "\<exists> pick. suitable pick"
proof-
  have "\<forall>d. \<exists> X. X \<in> Utor d" using Utor_ne by auto
  thus ?thesis unfolding suitable_def by metis
qed

lemma suitable_pick0:
  "suitable pick0"
  using someI_ex[OF exists_suitable] unfolding pick0_def[symmetric] .

definition "f0 \<equiv> f pick0"

lemmas f0_low_level_simps = f_simps[of pick0, unfolded f0_def[symmetric]]

(*
lemma map_comp_ids:
  fixes f1::"'a::var \<Rightarrow> 'a" and f2::"'b::var \<Rightarrow> 'b"
  assumes "|supp f1| <o |UNIV::'a set|"
    "bij f2"
    "|supp f2| <o |UNIV::'b set|"
  shows "map_term_pre f1 f2 (g3 \<circ> f3) (g4 \<circ> f4) v = map_term_pre id id g3 g4 (map_term_pre f1 f2 f3 f4 v)"
*)

lemma mr_rel_id_refl_strong:
  shows "(\<And>z. z \<in> set3_term_pre x \<Longrightarrow> R1 z z) \<Longrightarrow>
         (\<And>z. z \<in> set4_term_pre x \<Longrightarrow> R2 z z) \<Longrightarrow>
         mr_rel_term_pre id id R1 R2 x x"
  by (metis term_pre.mr_rel_id term_pre.rel_refl_strong)

term permute_term
term map_term_pre

lemma f0_Utor:
  assumes "X \<in> Utor d"
  shows "alpha_term (f0 d) (raw_term_ctor (map_term_pre id id (case_sum id f0) (case_sum id f0) X))"
proof-
  define pick1 where "pick1 \<equiv> \<lambda> d'. if d' = d then X else pick0 d'"
  have 1: "suitable pick1" using suitable_pick0 assms unfolding suitable_def pick1_def by auto
  have 2: "pick1 d = X" unfolding pick1_def by auto
  have 3: "\<And> dd. alpha_term (f0 dd) (f pick1 dd)" using f_alpha[OF suitable_pick0 1, of ]
    unfolding f0_def[symmetric] .
  have 4: "f pick1 d = raw_term_ctor (map_term_pre id id (case_sum id (f pick1)) (case_sum id (f pick1)) X)"
    apply(subst f_simps) unfolding 2 ..
  have 5: "alpha_term (raw_term_ctor (map_term_pre id id (case_sum id (f pick1)) (case_sum id (f pick1)) X))
                       (raw_term_ctor (map_term_pre id id (case_sum id f0) (case_sum id f0) X))"
    thm term_pre.rel_map mr_rel_term_pre_def
    apply(rule alpha_term.intros[of id]) apply (auto simp: term_pre.rel_map Grp_def OO_def supp_id_bound term_pre.mr_rel_id[symmetric])
    apply(rule term_pre.rel_refl_strong)
    subgoal for td by (cases td, auto simp: alpha_refls alpha_syms[OF 3] permute_raw_ids)
    subgoal for td by (cases td, auto simp: alpha_refls alpha_syms[OF 3]) .
  show ?thesis using 3[of d] 5 unfolding 4[symmetric] using alpha_trans by blast
qed

lemma f0_mapD:
  assumes "bij (u::'a\<Rightarrow>'a)" and "|supp u| <o |UNIV::'a::var set|"
  shows "alpha_term (f0 (raw_Umap u d)) (permute_raw_term u (f0 d))"
  using alpha_syms[OF f_swap_alpha[OF suitable_pick0 suitable_pick0 assms, unfolded f0_def[symmetric]]] .

lemmas f0_FVarsD = f_FVarsD[OF suitable_pick0, unfolded f0_def[symmetric]]


(* The following theorems for raw theorems will now be lifted to quotiented terms: *)
thm f0_Utor f0_mapD f0_FVarsD



(*******************)
(* End product: *)
definition ff0 :: "'a::var U \<Rightarrow> 'a term" where "ff0 d = TT_abs (f0 d)"

theorem ff0_DDTOR:
  assumes "X \<in> Udtor d"
  shows "ff0 d = term_ctor (map_term_pre id id (case_sum id ff0) (case_sum id ff0) X)"
  using assms using Utor_def
proof-
  define XX where "XX \<equiv> map_term_pre id id (map_sum TT_rep id) (map_sum TT_rep id) X"
  have XX: "XX \<in> Utor d" using assms unfolding XX_def Utor_def by auto
  have 0: "alpha_term
    (raw_term_ctor (map_term_pre id id (case_sum TT_rep f0) (case_sum TT_rep f0) X))
    (raw_term_ctor (map_term_pre id id (case_sum TT_rep (TT_rep \<circ> (TT_abs \<circ> f0)))
                       (case_sum TT_rep (TT_rep \<circ> (TT_abs \<circ> f0))) X))"
    apply(rule alpha_term.intros[of id]) apply (auto simp: term_pre.rel_map Grp_def OO_def supp_id_bound term_pre.mr_rel_id[symmetric])
    apply(rule term_pre.rel_refl_strong)
    subgoal for td by (cases td) (auto simp add: alpha_refls TT_rep_abs alpha_syms permute_raw_ids)
    subgoal for td by (cases td) (auto simp add: alpha_refls TT_rep_abs alpha_syms) .
  show ?thesis using f0_Utor[OF XX] unfolding ff0_def term_ctor_def
    apply(auto simp: term_pre.map_comp supp_id_bound id_def[symmetric] XX_def
        TT_total_abs_eq_iffs o_case_sum case_sum_o_map_sum)
    unfolding o_def[symmetric] using alpha_trans[OF _ 0] by auto
qed

lemma ff0_mmapD:
  assumes "bij (u::'a\<Rightarrow>'a)" and "|supp u| <o |UNIV::'a::var set|"
  shows "ff0 (Umap u d) = permute_term u (ff0 d)"
proof-
  {assume "alpha_term (f0 (Umap u d)) (permute_raw_term u (f0 d))"
    moreover have "alpha_term (permute_raw_term u (f0 d)) (permute_raw_term u (TT_rep (TT_abs (f0 d))))"
      unfolding alpha_bij_eqs[OF assms] by (simp add: TT_rep_abs alpha_syms)
    ultimately have "alpha_term (f0 (Umap u d)) (permute_raw_term u (TT_rep (TT_abs (f0 d))))"
      using alpha_trans by blast
  }
  thus ?thesis using f0_mapD[OF assms, of d]
    unfolding ff0_def permute_term_def by(auto simp: TT_total_abs_eq_iffs asSS_def asBij_def assms)
qed

theorem ff0_FFVarsD:
  "FVars_term (ff0 d) \<subseteq> UFVars d"
  using f0_FVarsD[of d] alpha_FVars TT_rep_abs
  unfolding ff0_def FVars_term_def by fastforce

end