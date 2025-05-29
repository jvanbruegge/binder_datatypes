theory Corecursor
  imports Greatest_Fixpoint
begin

(* helper lemmas *)

lemma rel_set_reflI: "(\<And>a. a \<in> A \<Longrightarrow> r a a) \<Longrightarrow> rel_set r A A"
  by (auto simp: rel_set_def)

definition asSS :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "asSS f \<equiv> if |supp f| <o |UNIV::'a set| then f else id"

lemma flip_lambda_equality: "(\<lambda>d. (=) (g x d)) = (\<lambda>d d'. d' = g x d)"
  by (subst (2) eq_commute) (rule refl)

(* Definitions *)

locale COREC =
  fixes Udtor :: "'u \<Rightarrow> ('a::var, 'a, 'a term + 'u, 'a term + 'u) term_pre set"
  and Umap :: "('a::var \<Rightarrow> 'a) \<Rightarrow> 'u \<Rightarrow> 'u"
  and UFVars :: "'u \<Rightarrow> 'a::var set"
  and valid_U :: "'u \<Rightarrow> bool"
  assumes Udtor_ne: "\<And>d. valid_U d \<Longrightarrow> Udtor d \<noteq> {}"
    and alpha_Udtor: "\<And>X X' d. valid_U d \<Longrightarrow> {X,X'} \<subseteq> Udtor d \<Longrightarrow>
\<exists>u. bij (u::'a::var \<Rightarrow> 'a) \<and> |supp u| <o |UNIV::'a set| \<and> id_on ((\<Union>z \<in> set3_term_pre X. case_sum FVars_term UFVars z) - set2_term_pre X) u \<and>
     map_term_pre id u (map_sum (permute_term u) (Umap u)) id X = X'"
    and
    (* The dual of the first block of assumptions from Norrish's paper:   *)
    UFVars_Udtor:
    "\<And> d X. valid_U d \<Longrightarrow> X \<in> Udtor d \<Longrightarrow>
  set1_term_pre X \<union> (\<Union>z \<in> set4_term_pre X. case_sum FVars_term UFVars z) \<union>
   ((\<Union>z \<in> set3_term_pre X. case_sum FVars_term UFVars z) - set2_term_pre X) \<subseteq>
  UFVars d"
    and
    (* The dual of the third block: *)
    Umap_Udtor: "\<And>u d. valid_U d \<Longrightarrow>
  bij (u::'a\<Rightarrow>'a) \<Longrightarrow> |supp u| <o |UNIV::'a::var set| \<Longrightarrow>
  Udtor (Umap u d) \<subseteq>
  image
    (map_term_pre u u (map_sum (permute_term u) (Umap u)) (map_sum (permute_term u) (Umap u)))
    (Udtor d)"
    and Umap_comp: "valid_U d \<Longrightarrow> bij f \<Longrightarrow> |supp (f::'a::var \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> bij g \<Longrightarrow> |supp (g::'a::var \<Rightarrow> 'a)| <o |UNIV::'a set|
  \<Longrightarrow> Umap f (Umap g d) = Umap (f \<circ> g) d"
    and Umap_cong0: "valid_U d \<Longrightarrow> bij f \<Longrightarrow> |supp (f::'a::var \<Rightarrow> 'a)| <o |UNIV::'a set|
  \<Longrightarrow> (\<And>a. a \<in> UFVars d \<Longrightarrow> f a = a) \<Longrightarrow> Umap f d = d"
    and valid_Umap: "bij f \<Longrightarrow> |supp (f::'a::var \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> valid_U d \<Longrightarrow> valid_U (Umap f d)"
    and valid_Udtor: "\<And>x. valid_U d \<Longrightarrow> x \<in> Udtor d \<Longrightarrow> pred_term_pre (pred_sum (\<lambda>_. True) valid_U)  (pred_sum (\<lambda>_. True) valid_U) x"
begin

lemma Umap_id: "valid_U d \<Longrightarrow> Umap id d = d"
  apply (rule Umap_cong0)
  apply assumption
    apply (rule bij_id supp_id_bound)+
  apply (rule id_apply)
  done

lemma valid_Udtor': "\<And>x z r. valid_U d \<Longrightarrow> x \<in> Udtor d \<Longrightarrow> z \<in> set3_term_pre x \<union> set4_term_pre x \<Longrightarrow> r \<in> Basic_BNFs.setr z \<Longrightarrow> valid_U r"
  apply (drule valid_Udtor)
   apply assumption
  apply (erule UnE)
  (* REPEAT_DETERM *)
   apply (unfold term_pre.pred_set)
   apply (erule conjE)
  apply (rotate_tac 2)
   apply (drule bspec[rotated])
    apply assumption
   apply (unfold sum.pred_set)
   apply (erule conjE)
   apply (erule bspec)
   apply assumption
  (* repeated *)
   apply (erule conjE)
  apply (rotate_tac 2)
   apply (drule bspec[rotated])
    apply assumption
   apply (erule conjE)
   apply (erule bspec)
  apply assumption
  done

lemma Umap_Udtor_strong:
  assumes u: "bij (u::'a::var\<Rightarrow>'a)" "|supp u| <o |UNIV::'a set|"
    and "valid_U d"
  shows
    "Udtor (Umap u d) =
 image
   (map_term_pre u u (map_sum (permute_term u) (Umap u)) (map_sum (permute_term u) (Umap u)))
   (Udtor d)"
proof -
  have x: "d = Umap (inv u) (Umap u d)"
    apply (rule sym)
    apply (rule trans[OF Umap_comp])
         apply (rule bij_imp_bij_inv supp_inv_bound assms)+
    apply (subst inv_o_simp1, rule assms)+
    apply (rule trans[OF Umap_id])
     apply (rule assms)
    apply (rule refl)
    done
  show ?thesis
    apply (rule subset_antisym)
     apply (rule Umap_Udtor[OF assms(3,1,2)])
    apply (subst x)
    apply (rule image_subsetI)
    apply (drule Umap_Udtor[THEN subsetD, rotated -1])
       apply (rule bij_imp_bij_inv supp_inv_bound assms valid_Umap)+
    apply (erule imageE)
    apply hypsubst
    apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<in>)"]])
     apply (rule term_pre.map_comp)
          apply (rule bij_imp_bij_inv supp_inv_bound assms)+
    apply (unfold map_sum.comp)
    apply (subst inv_o_simp2 permute_comp0s Umap_comp, (rule bij_imp_bij_inv supp_inv_bound assms)+)+
    apply (unfold comp_def)
    apply (unfold Umap_id permute_id0s map_sum.id term_pre.map_id)
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
     apply (rule term_pre.map_cong[rotated -5])
               apply (rule refl)
              apply (rule refl)
             apply (rule refl)
      (* REPEAT_DETERM *)
            apply (rule sum.map_cong0[OF refl])
            apply (drule valid_Udtor'[rotated])
               apply (erule UnI2 UnI1)
              apply assumption
             apply (rule valid_Umap)
               apply (rule assms bij_imp_bij_inv supp_inv_bound | assumption)+
            apply (rule trans)
             apply (rule Umap_comp)
                 apply (rule assms bij_imp_bij_inv supp_inv_bound | assumption)+
            apply (rule trans)
             apply (rule arg_cong2[OF _ refl, of _ _ Umap])
             apply (rule inv_o_simp2)
             apply (rule assms)
            apply (rule Umap_id)
            apply assumption
      (* repeated *)
           apply (rule sum.map_cong0[OF refl])
           apply (drule valid_Udtor'[rotated])
              apply (erule UnI2 UnI1)
             apply assumption
            apply (rule valid_Umap)
              apply (rule assms bij_imp_bij_inv supp_inv_bound | assumption)+
           apply (rule trans)
            apply (rule Umap_comp)
                apply (rule assms bij_imp_bij_inv supp_inv_bound | assumption)+
           apply (rule trans)
            apply (rule arg_cong2[OF _ refl, of _ _ Umap])
            apply (rule inv_o_simp2)
            apply (rule assms)
           apply (rule Umap_id)
           apply assumption
      (* END REPEAT_DETERM *)
          apply (rule supp_id_bound bij_id)+
    apply (unfold Umap_id permute_id0s map_sum.id term_pre.map_id id_def[symmetric])
    apply assumption
    done
qed

definition FFVarsBD :: "('a::var, 'a, 'a term + 'u, 'a term + 'u) term_pre \<Rightarrow> 'a set" where
  "FFVarsBD X \<equiv> (\<Union>z \<in> set3_term_pre X. case_sum FVars_term UFVars z) - set2_term_pre X"

lemmas Udtor_Umap = alpha_Udtor[folded FFVarsBD_def]
lemmas FVars_term_Udtor = UFVars_Udtor[folded FFVarsBD_def]

(*************************************)
(* The raw-term-based model infrastructure *)

definition Utor :: "'u \<Rightarrow> ('a::var, 'a, 'a raw_term + 'u, 'a raw_term + 'u) term_pre set" where
  "Utor d \<equiv>  map_term_pre id id (map_sum TT_rep id) (map_sum TT_rep id) ` (Udtor d)"

abbreviation raw_Umap :: "('a::var \<Rightarrow> 'a) \<Rightarrow> 'u \<Rightarrow> 'u" where
  "raw_Umap \<equiv> Umap"

abbreviation raw_UFVars :: "'u \<Rightarrow> 'a::var set" where
  "raw_UFVars \<equiv> UFVars"

definition raw_UFVarsBD :: "('a::var, 'a, 'a raw_term + 'u, 'a raw_term + 'u) term_pre \<Rightarrow> 'a set" where
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

lemma DTOR_mapD:
  assumes "valid_U d"
  shows "{X,X'} \<subseteq> Utor d \<Longrightarrow> \<exists>u. bij (u::'a::var\<Rightarrow>'a) \<and> |supp u| <o |UNIV::'a set| \<and> id_on (raw_UFVarsBD X) u \<and>
     mr_rel_term_pre id u
       (rel_sum (\<lambda> t t'. alpha_term (permute_raw_term u t) t') (\<lambda> d d'. raw_Umap u d = d'))
(rel_sum alpha_term (=))
     X X'"
  apply (drule image_mono[of _ _ "map_term_pre id id (map_sum TT_abs id) (map_sum TT_abs id)"])
  apply (unfold image_insert image_empty Utor_def image_comp)
  apply (subst (asm) term_pre.map_comp0[symmetric], (rule supp_id_bound bij_id)+)
  apply (unfold id_o map_sum.comp abs_rep_id map_sum.id term_pre.map_id0 image_id)
  apply (drule alpha_Udtor[OF assms])
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
  "valid_U d \<Longrightarrow> Utor d \<noteq> {}"
  by (unfold Utor_def arg_cong[OF image_is_empty, of Not])
    (erule Udtor_ne)

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

lemma aux_raw_UFVars_Utor: "case_sum FVars_term raw_UFVars ` set4_term_pre (map_term_pre id id (map_sum TT_abs id) (map_sum TT_abs id) X) =
       case_sum FVars_raw_term raw_UFVars ` set4_term_pre X"
  apply (unfold raw_UFVars_def2)
  apply (subst term_pre.set_map)
     apply (rule supp_id_bound bij_id)+
  apply (unfold image_comp case_sum_o_map_sum o_id)
  apply (unfold comp_def)
  apply (rule refl)
  done

lemma raw_UFVars_Utor:
  assumes "valid_U d"
  shows "X \<in> Utor d \<Longrightarrow> set1_term_pre X \<union> \<Union>(case_sum FVars_raw_term raw_UFVars ` set4_term_pre X) \<union> raw_UFVarsBD X \<subseteq> raw_UFVars d"
  apply (drule FVars_term_Udtor[OF assms Utor_abs_Udtor])
  apply (unfold FVarsBD_FFVarsBD)
  apply (subst (asm) term_pre.set_map, (rule supp_id_bound bij_id)+)
  apply (subst(asm) aux_raw_UFVars_Utor)
  apply (subst (asm) image_id)
  apply assumption
  done

lemma raw_Umap_Utor:
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a::var set|"
    and valid_d: "valid_U d"
  shows
    "rel_set
  (mr_rel_term_pre u u
     (rel_sum (\<lambda> t t'. alpha_term (permute_raw_term u t) t') (\<lambda> d d'. raw_Umap u d = d'))
     (rel_sum (\<lambda> t t'. alpha_term (permute_raw_term u t) t') (\<lambda> d d'. raw_Umap u d = d')))
 (Utor d)
 (Utor (raw_Umap u d))"
  apply (unfold Utor_def)
  apply (subst Umap_Udtor_strong[OF u, of d])
  apply (rule valid_d)
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

definition suitable ::  "('u \<Rightarrow> ('a, 'a, 'a raw_term + 'u,'a raw_term + 'u) term_pre) \<Rightarrow> bool" where
  "suitable pick \<equiv> \<forall> d. valid_U d \<longrightarrow> pick d \<in> Utor d"
definition f :: "('u \<Rightarrow> ('a::var,'a,'a raw_term + 'u,'a raw_term + 'u) term_pre) \<Rightarrow> 'u => 'a raw_term" where
  "f pick \<equiv> corec_raw_term pick"
definition pick0 :: "'u \<Rightarrow> ('a, 'a, 'a raw_term + 'u, 'a raw_term + 'u) term_pre" where
  "pick0 \<equiv> SOME pick. suitable pick"
definition f0 :: "'u \<Rightarrow> 'a raw_term" where
  "f0 \<equiv> f pick0"
definition COREC :: "'u \<Rightarrow> 'a term" where
  "COREC d = TT_abs (f0 d)"

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
  assumes "suitable pick" "valid_U d"
  shows "set1_term_pre (pick d) \<union> \<Union>(case_sum FVars_raw_term raw_UFVars ` set4_term_pre (pick d)) \<union> raw_UFVarsBD (pick d)
       \<subseteq> raw_UFVars d"
  by (rule raw_UFVars_Utor[OF assms(2) assms(1)[unfolded suitable_def, THEN spec, THEN mp, OF assms(2)]])

lemma f_FVarsD_aux:
  assumes "free_raw_term a t"
    "(\<And>d. valid_U d \<Longrightarrow> t = f pick d \<Longrightarrow> a \<in> raw_UFVars d)"
    "pred_sum (\<lambda>_. True) valid_U td"
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
   apply (unfold sum.simps)
   apply (insert assms(3))[1]
   apply hypsubst_thin
   apply (subst (asm) pred_sum_inject)
  apply assumption
  apply assumption
  done

lemma valid_pick_set3: "suitable pick \<Longrightarrow> xc \<in> set3_term_pre (pick xb) \<Longrightarrow> valid_U xb \<Longrightarrow> pred_sum (\<lambda>_. True) valid_U xc"
  apply (unfold suitable_def Utor_def)
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply (erule imageE[of _ _ "Udtor xb"])
  apply (simp only:)
  apply (subst (asm) term_pre.set_map, (rule supp_id_bound bij_id)+)
  apply (cases xc)
  apply hypsubst_thin
   apply (subst pred_sum.simps)
   apply simp
  apply hypsubst_thin
  apply (subst pred_sum.simps)
  apply (rule disjI2)
  apply (rule exI)
  apply (rule conjI)
   apply (rule refl)
  apply (rule imageE)
  prefer 2
  apply (erule valid_Udtor')
     apply assumption
    prefer 3
  apply assumption
   apply (rule UnI1)
   apply assumption
  apply (subst sum.set_map[of _ id, unfolded image_id, symmetric])
  apply (rule setr.intros)
  apply (rule sym)
  apply assumption
  done

lemma valid_pick_set4: "suitable pick \<Longrightarrow> xc \<in> set4_term_pre (pick xb) \<Longrightarrow> valid_U xb \<Longrightarrow> pred_sum (\<lambda>_. True) valid_U xc"
  apply (unfold suitable_def Utor_def)
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply (erule imageE[of _ _ "Udtor xb"])
  apply (simp only:)
  apply (subst (asm) term_pre.set_map, (rule supp_id_bound bij_id)+)
  apply (cases xc)
  apply hypsubst_thin
   apply (subst pred_sum.simps)
   apply simp
  apply hypsubst_thin
  apply (subst pred_sum.simps)
  apply (rule disjI2)
  apply (rule exI)
  apply (rule conjI)
   apply (rule refl)
  apply (rule imageE)
  prefer 2
  apply (erule valid_Udtor')
     apply assumption
    prefer 3
  apply assumption
   apply (rule UnI2)
   apply assumption
  apply (subst sum.set_map[of _ id, unfolded image_id, symmetric])
  apply (rule setr.intros)
  apply (rule sym)
  apply assumption
  done

lemma f_FVarsD:
  assumes p: "suitable pick"
and valid_d: "valid_U d"
  shows "FVars_raw_term (f pick d) \<subseteq> raw_UFVars d"
  apply (rule subsetI)
  apply (unfold FVars_raw_term_def mem_Collect_eq)
  apply (erule free_raw_term.induct[of _ _ "\<lambda>x y. \<forall>d. valid_U d \<longrightarrow> y = f pick d \<longrightarrow> x \<in> raw_UFVars d", THEN spec, THEN mp, THEN mp[OF _ refl]])
     prefer 4
     apply (rule valid_d)


     apply (rule allI)
    apply (rule impI)+
    apply (rule le_supE[OF suitable_FVarsD[OF assms(1), unfolded Un_assoc]])
  prefer 2
     apply (erule subsetD)
    apply (drule f_ctor)
    apply hypsubst
    apply (subst (asm) term_pre.set_map)
      apply (rule supp_id_bound bij_id)+
    apply (unfold image_id)
     apply assumption

  prefer 2

(* REPEAT_DETERM *)
   apply (rule allI)
   apply (rule impI)+
   apply (frule f_ctor)
   apply hypsubst
   apply (subst (asm) term_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id)?
   apply (erule imageE)
   apply hypsubst
  thm f_FVarsD_aux
   apply (drule f_FVarsD_aux)
     apply (erule allE)
      apply (erule impE)
       prefer 2
  apply (erule impE)
      apply assumption
        apply assumption
  apply assumption
     prefer 2
  apply (rule refl)
     prefer 2
   apply (rule suitable_FVarsD[THEN subsetD, unfolded raw_UFVarsBD_def, rotated]) (* TODO: put union members in correct order *)
  apply assumption
       apply (unfold Un_assoc)
    apply (rule UnI2)
    apply (unfold Un_assoc[symmetric])?
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 2 2] 1\<close>) (* normally: Use goal number here *)
    apply (rule DiffI[rotated], assumption)?
    apply (rule UN_I)
     apply assumption
    apply assumption
     apply (rule assms)
  prefer 2
    apply assumption
   apply (drule valid_pick_set3[OF p])
    apply assumption
  apply assumption
    (* repeated *)
(* TODO: this not actually a repeat anymore, reorganize the proof
to recover that property *)
   apply (rule allI)
   apply (rule impI)+
   apply (frule f_ctor)
   apply hypsubst
   apply (subst (asm) term_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id)?
   apply (erule imageE)
   apply hypsubst
  thm f_FVarsD_aux
   apply (drule f_FVarsD_aux)
     apply (erule allE)
      apply (erule impE)
       prefer 2
  apply (erule impE)
      apply assumption
        apply assumption
  apply assumption
     prefer 2
  apply (rule refl)
     prefer 2
   apply (rule suitable_FVarsD[THEN subsetD, unfolded raw_UFVarsBD_def, rotated]) (* TODO: put union members in correct order *)
  apply assumption
       apply (unfold Un_assoc)
    apply (rule UnI2)
    apply (unfold Un_assoc[symmetric])?
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 2 1] 1\<close>) (* normally: Use goal number here *)
    apply (rule DiffI[rotated], assumption)?
    apply (rule UN_I)
     apply assumption
    apply assumption
   apply (rule assms)
  apply (rule valid_pick_set4[OF p])
  prefer 2
   apply assumption
  apply assumption
  done
    (* END REPEAT_DETERM *)

lemma OO_permute:
  assumes "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a::var set|"
          "bij (v::'a\<Rightarrow>'a)" "|supp v| <o |UNIV::'a::var set|"
  shows "((\<lambda>t. alpha_term (permute_raw_term v t)) OO (\<lambda>t. alpha_term (permute_raw_term u t))) = (\<lambda>t. alpha_term (permute_raw_term (u \<circ> v) t))"
  apply (unfold permute_raw_comp0s[OF assms, symmetric])
  apply (rule ext)
  apply (rule ext)
  apply (rule iffI)
  apply (subst (asm) relcompp.simps)
   apply (erule exE)+
   apply (erule conjE)+
   apply hypsubst
   apply (erule alpha_trans[rotated])
  apply (subst comp_apply)
   apply (subst alpha_bij_eqs, (rule assms)+)
   apply assumption
  apply (subst (asm) comp_apply)
  apply (subst relcompp.simps)
  apply (rule exI)+
  apply (rule conjI[rotated])+
  prefer 2
     apply (rule alpha_refls)
    apply assumption
   apply (rule refl)+
  done


lemma OO_comp:
  assumes "\<And>d. valid_U d \<Longrightarrow> (g u \<circ> g v) d = g (u \<circ> v) d"
  shows "valid_U x \<Longrightarrow> ((\<lambda>d. (=) (g v d)) OO (\<lambda>d. (=) (g u d))) x = (\<lambda>d. (=) (g (u \<circ> v) d)) x"
  apply (subst (2) Grp_UNIV_def[symmetric])
  apply (subst (2) Grp_UNIV_def[symmetric])
  apply (subst Grp_o[symmetric])
  apply (unfold Grp_UNIV_def)
  apply (subst assms)
  apply assumption
  apply (rule refl)
  done

lemma OO_raw_Umap:
  assumes "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a::var set|"
          "bij (v::'a\<Rightarrow>'a)" "|supp v| <o |UNIV::'a::var set|"
        shows "valid_U x \<Longrightarrow> ((\<lambda>d. (=) (raw_Umap v d)) OO (\<lambda>d. (=) (raw_Umap u d))) x  = (\<lambda>d. (=) (raw_Umap (u \<circ> v) d)) x"
  apply (rule OO_comp)
  apply (subst comp_apply)
   apply (rule Umap_comp[OF _ assms])
   apply assumption+
  done

lemma rel_F_suitable_mapD_aux:
  assumes "valid_U d" "suitable pick"
  shows "X \<in> Utor d \<Longrightarrow> \<exists>v. bij v \<and> |supp v| <o |UNIV::'a::var set| \<and> id_on (raw_UFVarsBD (pick d)) v \<and>
      (mr_rel_term_pre id v
        (rel_sum (\<lambda>t. alpha_term (permute_raw_term v t)) (\<lambda>d. (=) (raw_Umap v d)))
        (rel_sum alpha_term (=)) 
        (pick d) X)"
    apply (rule DTOR_mapD[OF assms(1)])
    apply (unfold insert_subset)
    apply (rule conjI)
     apply (rule assms(2)[unfolded suitable_def, THEN spec, THEN mp, OF assms(1)])
    apply (rule conjI)
    apply assumption
    apply (rule empty_subsetI)
  done

lemma OO_alpha_permute:
  assumes  "bij (g::'a \<Rightarrow> 'a)" "|supp g| <o |UNIV::'a::var set|"
  shows "alpha_term OO (\<lambda>t. alpha_term (permute_raw_term g t)) = (\<lambda>t. alpha_term (permute_raw_term g t))"
  apply (rule ext)
  apply (rule ext)
  apply (rule iffI)
  prefer 2
   apply (rule relcomppI)
    prefer 2
    apply assumption
   apply (rule alpha_refls)
  apply (erule relcomppE)
  apply (subst (asm) alpha_bij_eqs[OF assms, symmetric])
  apply (erule alpha_trans)
  apply assumption
  done

lemma set3_setr_valid:
  assumes "suitable pick"
and "valid_U d"
and "z \<in> set3_term_pre (pick d)"
shows "x \<in> Basic_BNFs.setr z \<Longrightarrow> valid_U x"
  by (rule valid_pick_set3[OF assms(1,3,2), THEN sum.pred_set[THEN fun_cong, THEN iffD1, THEN conjunct2], THEN bspec])

lemma rel_F_suitable_mapD:
  assumes valid_d: "valid_U d"
    and pp': "suitable pick" "suitable pick'"
    and u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a::var set|"
  shows "\<exists> v. bij v \<and> |supp v| <o |UNIV::'a set| \<and> id_on (raw_UFVarsBD (pick d)) v \<and>
 mr_rel_term_pre u (u o v)
   (rel_sum (\<lambda>t t'. alpha_term (permute_raw_term (u o v) t) t')
            (\<lambda>d d'. raw_Umap (u o v) d = d'))
   (rel_sum (\<lambda>t t'. alpha_term (permute_raw_term u t) t')
            (\<lambda>d d'. d' = raw_Umap u d))
 (pick d)
 (pick' (raw_Umap u d))"
  apply (rule raw_Umap_Utor[OF u valid_d, unfolded rel_set_def, THEN conjunct2, THEN bspec, THEN bexE])
   apply (rule allE)
    apply (rule pp'(2)[unfolded suitable_def])
   apply (erule impE)
    prefer 2
    apply assumption
   apply (rule valid_Umap, (rule u valid_d)+)
 
  apply (drule rel_F_suitable_mapD_aux[OF valid_d pp'(1)])
  apply (erule exE)
   apply (erule conjE)+

  apply(rule exI)
  apply (rule conjI[rotated])+
     apply(rule term_pre.mr_rel_mono_strong0[rotated -5])
               apply (rule term_pre.mr_rel_OO[THEN fun_cong, THEN fun_cong, THEN iffD2, rotated -1, OF relcomppI])
                      apply assumption+
                    apply (rule supp_id_bound)
                   apply assumption+
                 apply (rule u)+
              apply (subst o_id)
              apply (rule ballI)
              apply (rule refl)
             apply (rule ballI)
             apply (rule refl)
            apply (rule ballI)+
            apply (rule impI)
            apply (unfold sum.rel_compp[symmetric])
            apply (subst OO_permute[OF u, symmetric])
              apply assumption+
            apply (erule sum.rel_cong[OF refl refl, THEN iffD1, rotated -1])
             apply (rule refl)
            apply (subst OO_raw_Umap[OF u])
               apply assumption+
             apply (erule set3_setr_valid[OF pp'(1) valid_d])
             apply assumption
            apply (rule refl)
            apply (rule ballI)+
           apply (rule impI)
           apply (erule sum.rel_cong[OF refl refl, THEN iffD1, rotated -1])
            apply (subst OO_alpha_permute[OF u])
  apply (rule refl)
           apply (subst eq_OO)
           apply (rule iffI)
            apply (rule sym)
            apply assumption
           apply (rule sym)
           apply assumption
          apply (subst o_id)
          apply (rule u)
         apply (rule bij_comp[OF _ u(1)])
         apply assumption
        apply (rule supp_comp_bound[OF _ u(2)])
        apply assumption
       apply (rule u)
      apply (rule bij_comp[OF _ u(1)])
      apply assumption
     apply (rule supp_comp_bound[OF _ u(2)])
     apply assumption+
  done

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
  apply(rule alpha_term.coinduct[of \<phi>, OF 0])  
  subgoal for x1 x2
    apply (rule raw_term.exhaust[of x1])
    apply (rule raw_term.exhaust[of x2])
    apply hypsubst_thin
    apply (drule 1)
    apply (erule exE)
    apply (rule exI)+
    apply (rule conjI, rule refl)+
    apply assumption
    done
  done

(* The "monster lemma": swapping and "pick"-irrelevance covered in one shot: *)

lemma f_swap_alpha_aux1:
  assumes p: "suitable pick"
    and u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a::var set|"
    and "FVarsB x \<subseteq> u ` raw_UFVarsBD (pick d)"
    and id_on_pick: "id_on (raw_UFVarsBD (pick d)) y"
  shows "id_on (FVarsB x) (u \<circ> y \<circ> inv u)"
  apply (rule id_on_antimono)
   apply (unfold id_on_def)[1]
   apply (rule allI)
   apply (rule impI)
   apply (drule imageI[of _ "u ` raw_UFVarsBD (pick d)" "inv u"])
   apply (unfold image_inv_f_f[OF bij_is_inj[OF u(1)]])
   apply (subst comp_assoc)
   apply (subst comp_apply)
   apply (subst comp_apply)
   apply (rule allE[OF id_on_pick[unfolded id_on_def]])
   apply (erule impE)
    apply assumption
   apply (drule arg_cong[of _ _ "u"])
   apply (subst (asm) surj_f_inv_f[OF bij_is_surj[OF u(1)]])
   apply assumption
  apply (rule assms)
  done

lemma FVars_raw_permutes':
  "bij (g::'a \<Rightarrow> 'a) \<Longrightarrow> |supp g| <o |UNIV::'a set| \<Longrightarrow> FVars_raw_term \<circ> permute_raw_term g = image g \<circ> FVars_raw_term"
  apply (subst comp_def)+
  apply (subst FVars_raw_permutes)
    apply assumption+
  apply (rule refl)
  done

lemma f_swap_alpha_xL:
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a::var set|"
    and x: "raw_term_ctor x = permute_raw_term u (f pick d)"
  shows "x = map_term_pre u u (permute_raw_term u \<circ> case_sum id (f pick)) (permute_raw_term u \<circ> case_sum id (f pick)) (pick d)"
  apply (insert x)
  apply (subst (asm) f_simps[of "pick"])
  apply (subst (asm) permute_raw_simps[OF u])
  apply (subst (asm) raw_term.inject)
  apply hypsubst_thin
  apply (subst term_pre.map_comp, (rule supp_id_bound bij_id u)+)
  apply (unfold o_id)
  apply (rule refl)
  done

lemma l_is_inr:
  assumes
    r: "rel_sum (\<lambda>t. alpha_term (permute_raw_term u t)) (\<lambda>d d'. d' = raw_Umap u d) ttdL ttdR"
    and na: "\<not> alpha_term (permute_raw_term u (case_sum id (f pick) ttdL)) (case_sum id (f pick') ttdR)"
  shows "\<exists>tL. ttdL = Inr tL"
  apply (rule sumE[of ttdR])
   apply (insert r na)
   apply hypsubst_thin
   apply (subst (asm) sum.case)+
   apply (unfold id_apply)
   apply (rule sumE[of ttdL])
    apply hypsubst_thin
    apply (subst (asm) rel_sum_simps)
  apply (subst (asm) sum.case)
   apply (drule cnf.clause2raw_notE)
     apply assumption
  apply (erule FalseE)
   apply hypsubst_thin
   apply (rule exI)
   apply (rule refl)
  apply (rule sumE[of ttdL])
   apply hypsubst_thin
   apply (subst (asm) rel_sum_simps)
   apply (erule FalseE)
  apply hypsubst_thin
  apply (rule exI)
  apply (rule refl)
  done

lemma r_is_Umap:
  assumes
    r: "rel_sum (\<lambda>t. alpha_term (permute_raw_term u t)) (\<lambda>d d'. d' = raw_Umap u d) ttdL ttdR"
    and ttdL: "ttdL = Inr x"
  shows "ttdR = Inr (raw_Umap u x)"
  apply (insert r ttdL)
  apply hypsubst_thin
  apply (unfold rel_sum.simps)
  apply (erule disjE)
   apply (erule exE)+
   apply (erule conjE)
   apply (subst (asm) Inr_Inl_False)
   apply (erule FalseE)
  apply (erule exE)+
  apply (erule conjE)+
  apply (subst (asm) sum.inject)
  apply hypsubst_thin
  apply (rule refl)
  done

lemma f_swap_alpha_aux:
  assumes p: "suitable pick" and p': "suitable pick'"
    and valid_d: "valid_U d"
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a::var set|"
  shows "\<exists> u d. valid_U d \<and> bij u \<and> |supp u| <o |UNIV::'a set| \<and>
   tL = permute_raw_term u (f pick d) \<and> tR = f pick' (raw_Umap u d) \<Longrightarrow> alpha_term tL tR"
  apply (erule alpha_coinduct2[of "\<lambda> tL tR. \<exists> u d. valid_U d \<and> bij u \<and> |supp u| <o |UNIV::'a set| \<and>
   tL = permute_raw_term u (f pick d) \<and> tR = f pick' (raw_Umap u d)"])
  apply (erule exE conjE)+
  apply (frule rel_F_suitable_mapD[OF _ p p'])
    apply assumption+
  apply (erule exE)
  apply (rule exI)+
  apply (rule conjI[rotated])+
     prefer 4
     apply (rule bij_comp)
      apply (rule bij_imp_bij_inv)
      apply assumption
     apply (rule bij_comp)
      prefer 2
      apply assumption
     apply (erule conjE)
     apply (rotate_tac -2)
     apply assumption
    prefer 3
    apply (rule supp_comp_bound)
     apply (rule supp_inv_bound)
      apply assumption
     apply assumption
    apply (rule supp_comp_bound)
     apply (erule conjE)+
     apply assumption
    apply assumption
   prefer 2

   apply (rule id_on_antimono)
    apply (unfold id_on_def)
    apply (rule allI)
    apply (rule impI)
    apply (subst comp_assoc)
    apply (subst comp_apply)
    apply (subst comp_apply)
    apply (frule bij_inv_rev[THEN iffD1, THEN sym])
     prefer 2
     apply assumption
    apply (erule conjE)+
    apply (erule allE)
    apply (erule impE)
     prefer 2
     apply assumption
    apply (rule image_inv_f_f[OF bij_is_inj, THEN arg_cong2[OF refl, of _ _ "(\<in>)"], THEN iffD1])
     prefer 2
     apply (erule imageI)
    apply assumption
   apply (subst f_swap_alpha_xL[of _ _ "pick"])
      apply assumption+
   apply (subst term_pre.set_map, (rule supp_id_bound bij_id | assumption)+)+
   apply (subst Diff_subset_conv)
   apply (subst image_comp)
   apply (subst comp_assoc[symmetric])
   apply (subst FVars_raw_permutes', assumption+)
   apply (subst comp_assoc)
   apply (subst image_comp[symmetric])
   apply (subst f_swap_alpha_xL[of _ _ "pick"])
      apply assumption+
   apply (subst term_pre.set_map, (rule supp_id_bound bij_id | assumption)+)+
   apply (subst image_Un[symmetric])
   apply (subst image_Union[symmetric])
   apply (rule image_mono)
   apply (unfold raw_UFVarsBD_def)
   apply (subst Un_Diff_cancel)
   apply (rule le_supI2)
   apply (subst o_case_sum)
   apply (unfold o_id)
   apply (rule UN_mono)
    apply (rule subset_refl)
  subgoal for _ _ _ _ _ x
    apply (rule sumE[of x])
     apply hypsubst_thin
     apply (unfold sum.simps)
     apply (rule subset_refl)
    apply hypsubst_thin
    apply (unfold sum.simps)
    apply (subst comp_apply)
    apply (rule f_FVarsD[OF p])
    apply (drule valid_pick_set3[OF p])
     apply assumption
    apply (unfold pred_sum_inject)
    apply assumption
    done
  apply (erule conjE)+
  apply (rotate_tac -6)
  apply (drule f_swap_alpha_xL[of _ _ "pick", rotated -1], assumption+)
  apply (drule f_ctor)
  apply hypsubst
  apply (subst term_pre.mr_rel_map, (assumption | rule supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound)+)
  apply (subst term_pre.mr_rel_map, (assumption | rule supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound bij_id)+)
  apply (subst relcompp_conversep_Grp)+
  apply (subst Grp_OO)+
  apply (unfold id_o inv_id)
  apply (subst (2) comp_assoc)
  apply (subst inv_o_simp1, assumption)
  apply (unfold o_id)
  apply (subst comp_apply)+
  apply (subst permute_raw_comps, (assumption | rule supp_id_bound bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound)+)
  apply (erule term_pre.mr_rel_mono_strong0[rotated -5])
           apply (rule ballI)
           apply (rule refl)
          apply (rule ballI)
          apply (rule refl)
         apply (rule ballI)+
         apply (rule impI)
         apply (subst permute_raw_comps)
             prefer 6

              apply (rule ballI)+
              apply (rule impI)
              apply (rotate_tac -1)
              apply (subst disj_commute)
             apply (rule verit_and_neg)
              apply (frule l_is_inr[of _ _ _ pick "pick'"])
               apply assumption
              apply (erule exE)
              apply hypsubst
              apply (subst sum.case)+
              apply (rule exI)+
              apply (drule r_is_Umap)
               apply (rule refl)
              apply hypsubst
              apply (unfold sum.case)
              apply (rule conjI[rotated])+
                  apply (rule refl)+
                apply assumption+
              apply (drule valid_pick_set4[rotated])
                apply assumption
               apply (rule p)
              apply (unfold pred_sum_inject)
              apply assumption

             prefer 5

             apply (subst (2) comp_assoc)
             apply (subst (3) comp_assoc)
             apply (unfold inv_o_simp1)
              apply (unfold o_id)
              apply (rotate_tac -1)
              apply (subst disj_commute)
              apply (rule verit_and_neg)
              apply (subst (asm) flip_lambda_equality)
              apply (frule l_is_inr[of _ _ _ pick "pick'"])
               apply assumption
              apply (erule exE)
              apply hypsubst
              apply (subst sum.case)+
              apply (rule exI)+
              apply (drule r_is_Umap)
               apply (rule refl)
              apply hypsubst
              apply (unfold sum.case)
              apply (rule conjI[rotated])+
                  apply (rule refl)+
                prefer 3
                apply (drule valid_pick_set3[rotated])
                  apply assumption
                 apply (rule p)
                apply (unfold pred_sum_inject)
                apply assumption
               apply (rule supp_comp_bound bij_comp bij_imp_bij_inv supp_inv_bound | assumption)+
  done

lemma f_swap_alpha:
  assumes p: "suitable pick" and p': "suitable pick'"
   and valid_d: "valid_U d"
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a::var set|"
  shows "alpha_term (permute_raw_term u (f pick d)) (f pick' (raw_Umap u d))"
  apply (rule f_swap_alpha_aux[OF assms])
  apply (rule exI)+
  apply (rule conjI[rotated])+
      apply (rule refl)+
    apply (rule assms)+
  done

lemma f_alpha:
  assumes p: "suitable pick" and p': "suitable pick'" and valid_d: "valid_U d"
  shows "alpha_term (f pick d) (f pick' d)"
  by (rule f_swap_alpha[OF assms bij_id supp_id_bound, unfolded permute_raw_ids raw_Umap_id[OF valid_d]])

lemma exists_suitable:
  "\<exists> pick. suitable pick"
  apply (unfold suitable_def)
  apply (rule choice)
  apply (rule allI)
  apply (subst ex_simps)
  apply (rule impI)
  apply (erule ex_in_conv[THEN iffD2, OF Utor_ne])
  done

lemma suitable_pick0:
  "suitable pick0"
  apply (unfold pick0_def)
  apply (rule someI_ex[OF exists_suitable])
  done
lemmas f0_low_level_simps = f_simps[of pick0, unfolded f0_def[symmetric]]

lemma f0_Utor_aux:
  assumes "X \<in> Utor d" and valid_d: "valid_U d"
  shows "alpha_term (f (\<lambda> d'. if d' = d then X else pick0 d') d)
                       (raw_term_ctor (map_term_pre id id (case_sum id f0) (case_sum id f0) X))"
    apply(subst f_simps)
    apply (subst if_P[OF refl])
    apply(rule alpha_term.intros[of id], (rule bij_id supp_id_bound id_on_id)+)
    apply (unfold term_pre.mr_rel_id[symmetric] term_pre.rel_map)
    apply(rule term_pre.rel_refl_strong)
(* REPEAT *)
     apply (rule sumE)
      apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
       apply assumption
      apply hypsubst
      apply (unfold sum.simps)
      apply (unfold permute_raw_ids id_apply)?
      apply (rule alpha_refls)
      apply hypsubst
     apply (unfold sum.simps)
     apply (unfold f0_def)?
     apply (rule f_alpha[OF _ suitable_pick0])

(* BLOCK: SUITABLE *)
     apply (unfold suitable_def)
    apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
    apply (rule impI)
    apply (insert suitable_pick0[unfolded suitable_def, THEN spec, THEN mp])
    apply assumption
   apply (rule assms(1)[unfolded Utor_def, THEN imageE])
   apply (rotate_tac -1)
   apply (erule valid_Udtor'[rotated])
     prefer 2
     apply (rule Basic_BNFs.setr.intros)
     apply (rule refl)
     apply hypsubst_thin
    apply (subst (asm) term_pre.set_map, (rule bij_id supp_id_bound)+)
    apply (rule UnI1)
    apply (erule imageE)
    apply (drule setr.intros[OF sym])
    apply (unfold sum.set_map image_id setr.simps)
    apply (erule exE)
    apply (erule conjE)
    apply (hypsubst_thin)
  apply assumption
  apply (rule assms)
  
(* END BLOCK *)

(* REPEATED, except UnI2 instead of UnI1 *)
  apply (rule sumE)
      apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
       apply assumption
      apply hypsubst
      apply (unfold sum.simps)
      apply (unfold permute_raw_ids id_apply)?
      apply (rule alpha_refls)
      apply hypsubst
     apply (unfold sum.simps)
     apply (unfold f0_def)?
     apply (rule f_alpha[OF _ suitable_pick0])

     apply (unfold suitable_def)
    apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
    apply (rule impI)
    apply (insert suitable_pick0[unfolded suitable_def, THEN spec, THEN mp])
    apply assumption
   apply (rule assms(1)[unfolded Utor_def, THEN imageE])
   apply (rotate_tac -1)
   apply (erule valid_Udtor'[rotated])
     prefer 2
     apply (rule Basic_BNFs.setr.intros)
     apply (rule refl)
     apply hypsubst_thin
    apply (subst (asm) term_pre.set_map, (rule bij_id supp_id_bound)+)
    apply (rule UnI2)
    apply (erule imageE)
    apply (drule setr.intros[OF sym])
    apply (unfold sum.set_map image_id setr.simps)
    apply (erule exE)
    apply (erule conjE)
    apply (hypsubst_thin)
  apply assumption
  apply (rule assms)

(* END REPEAT *)
    done

lemma f0_Utor:
  assumes "X \<in> Utor d" "valid_U d"
  shows "alpha_term (f0 d) (raw_term_ctor (map_term_pre id id (case_sum id f0) (case_sum id f0) X))"
    apply (rule alpha_trans[rotated])
    apply (rule f0_Utor_aux[OF assms])
    apply (rule f_alpha[OF suitable_pick0 _ assms(2), unfolded f0_def[symmetric]])

(* BLOCK: SUITABLE *)
     apply (unfold suitable_def)
  apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
    apply (rule impI)
    apply (insert suitable_pick0[unfolded suitable_def, THEN spec, THEN mp])
     apply assumption
(* END BLOCK *)
  done

lemma f0_mapD:
  assumes "bij (u::'a\<Rightarrow>'a)" and "|supp u| <o |UNIV::'a::var set|" "valid_U d"
  shows "alpha_term (f0 (raw_Umap u d)) (permute_raw_term u (f0 d))"
  by (rule alpha_syms[OF f_swap_alpha[OF suitable_pick0 suitable_pick0 assms(3,1,2), unfolded f0_def[symmetric]]])

lemmas f0_FVarsD = f_FVarsD[OF suitable_pick0, unfolded f0_def[symmetric]]


(* The following theorems for raw theorems will now be lifted to quotiented terms: *)
thm f0_Utor f0_mapD f0_FVarsD


(*******************)
(* End product: *)

theorem COREC_DDTOR:
  assumes "X \<in> Udtor d" "valid_U d"
  shows "COREC d = term_ctor (map_term_pre id id (case_sum id COREC) (case_sum id COREC) X)"
  apply (unfold COREC_def term_ctor_def)
  apply (unfold o_def[symmetric])
  apply (subst term_pre.map_comp, (rule supp_id_bound bij_id)+)
  apply (unfold TT_total_abs_eq_iffs)
  apply (unfold o_case_sum)
  apply (unfold id_comp comp_id)
  apply (rule alpha_trans)
   apply (rule arg_cong[of _ _ "alpha_term (f0 d)", THEN iffD1])
    prefer 2
    apply (rule f0_Utor)
    apply (unfold Utor_def)
    apply (rule imageI)
     apply (rule assms)+
   apply (subst term_pre.map_comp, (rule supp_id_bound bij_id)+)
   apply (unfold case_sum_o_map_sum)
   apply (unfold id_comp comp_id)
   apply (rule refl)
  apply(rule alpha_term.intros[of id], (rule bij_id supp_id_bound)+)
   apply (rule id_on_id)
  apply (unfold term_pre.mr_rel_id[symmetric] term_pre.rel_map)
  apply(rule term_pre.rel_refl_strong)
   prefer 2
   apply (rule sumE)
    apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
     apply assumption
    apply hypsubst
    apply (unfold sum.simps)
    apply (rule alpha_refls)
   apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
    apply assumption
   apply hypsubst
   apply (unfold sum.simps)
   apply (unfold comp_apply)
   apply (rule TT_rep_abs_syms)

  apply (rule sumE)
   apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
    apply assumption
   apply hypsubst
   apply (unfold sum.simps)
   apply (unfold permute_raw_ids)
   apply (rule alpha_refls)
  apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
   apply assumption
  apply hypsubst
  apply (unfold sum.simps)
  apply (rule TT_rep_abs_syms)
  done

lemma COREC_mmapD:
  assumes "bij (u::'a\<Rightarrow>'a)" and "|supp u| <o |UNIV::'a::var set|" and "valid_U d"
  shows "COREC (Umap u d) = permute_term u (COREC d)"
  apply (unfold COREC_def permute_term_def)
  apply (unfold TT_total_abs_eq_iffs)
  apply (rule alpha_trans)
   apply (rule f0_mapD[OF assms])
  apply (unfold alpha_bij_eqs[OF assms(1,2)])
  apply (rule alpha_syms)
  apply (rule TT_rep_abs)
  done

theorem COREC_FFVarsD:
  "valid_U d \<Longrightarrow> FVars_term (COREC d) \<subseteq> UFVars d"
  apply (unfold COREC_def FVars_term_def alpha_FVars[OF TT_rep_abs])
  apply (erule f0_FVarsD)
  done

end

end