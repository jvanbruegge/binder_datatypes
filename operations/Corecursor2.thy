theory Corecursor2
  imports "Binders.MRBNF_FP" "./Composition"
begin

(* helper lemmas *)

lemma rel_set_reflI: "(\<And>a. a \<in> A \<Longrightarrow> r a a) \<Longrightarrow> rel_set r A A"
  by (auto simp: rel_set_def)

definition asSS :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "asSS f \<equiv> if |supp f| <o |UNIV::'a set| then f else id"

declare [[mrbnf_internals]]
local_setup \<open>fn lthy =>
let
  val (fp_res, lthy) = MRBNF_FP.construct_binder_fp BNF_Util.Greatest_FP
    [{
      FVars = replicate 2 NONE,
      T_name = "T1",
      nrecs = 2,
      permute = NONE,
      pre_mrbnf = the (MRBNF_Def.mrbnf_of lthy @{type_name T1_pre})
    }, {
      FVars = replicate 2 NONE,
      T_name = "T2",
      nrecs = 2,
      permute = NONE,
      pre_mrbnf = the (MRBNF_Def.mrbnf_of lthy @{type_name T2_pre})
    }]
    [[([0], [1, 3])], [([], [1])]]
    lthy
in lthy end
\<close>
print_theorems
(*
'var \<rightarrow> 'bfree, T1 and T2
'tyvar \<rightarrow> T1

('a::covar, 'b::covar, 'c::covar,    'd,            'a,      'b,     'a,   ('a, 'b, 'c, 'd) T1 + 'u1, ('a, 'b, 'c, 'd) T1 + 'u1, ('a, 'b, 'c, 'd) T2 + 'u2, ('a, 'b, 'c, 'd) T2 + 'u2) T1_pre

free var1, free var2, passive free, passive live, bound 1, bound 2, bfree1, rec1,                         brec1,                     rec2,                         brec2

*)

typ "('var, 'tyvar, 'a, 'b) T1"
typ "('var, 'tyvar, 'a, 'b) T2"

term "T1_ctor"

(* Definitions *)

thm alpha_T1_alpha_T2.intros

locale COREC =
  fixes Udtor1 :: "'u1 \<Rightarrow> ('a::covar, 'b::covar, 'c::covar, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) T1 + 'u1, ('a, 'b, 'c, 'd) T1 + 'u1, ('a, 'b, 'c, 'd) T2 + 'u2, ('a, 'b, 'c, 'd) T2 + 'u2) T1_pre set"
  and Udtor2 :: "'u2 \<Rightarrow> ('a::covar, 'b::covar, 'c::covar, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) T1 + 'u1, ('a, 'b, 'c, 'd) T1 + 'u1, ('a, 'b, 'c, 'd) T2 + 'u2, ('a, 'b, 'c, 'd) T2 + 'u2) T2_pre set"
  and Umap1 :: "('a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> 'u1 \<Rightarrow> 'u1"
  and Umap2 :: "('a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> 'u2 \<Rightarrow> 'u2"
  and UFVars11 :: "'u1 \<Rightarrow> 'a set"
  and UFVars12 :: "'u1 \<Rightarrow> 'b set"
  and UFVars21 :: "'u2 \<Rightarrow> 'a set"
  and UFVars22 :: "'u2 \<Rightarrow> 'b set"
  and valid_U1 :: "'u1 \<Rightarrow> bool"
  and valid_U2 :: "'u2 \<Rightarrow> bool"
  assumes Udtor_ne: "\<And>d. valid_U1 d \<Longrightarrow> Udtor1 d \<noteq> {}" "\<And>d. valid_U2 d \<Longrightarrow> Udtor2 d \<noteq> {}"
    and alpha_Udtor1: "\<And>X X' d. valid_U1 d \<Longrightarrow> {X,X'} \<subseteq> Udtor1 d \<Longrightarrow>
  \<exists>u v. bij (u::'a \<Rightarrow> 'a) \<and> |supp u| <o |UNIV::'a set| \<and> bij (v::'b \<Rightarrow> 'b) \<and> |supp v| <o |UNIV::'b set|
  \<and> id_on ((set7_T1_pre X \<union> \<Union>(case_sum FVars_T1_1 UFVars11 ` set9_T1_pre X) \<union> \<Union>(case_sum FVars_T2_1 UFVars21 ` set11_T1_pre X)) - set5_T1_pre X) u
  \<and> id_on ((\<Union>(case_sum FVars_T1_2 UFVars12 ` set9_T1_pre X) \<union> \<Union>(case_sum FVars_T2_2 UFVars22 ` set11_T1_pre X)) - set6_T1_pre X) v
  \<and> map_T1_pre id id id id u v u id (map_sum (permute_T1 u v) (Umap1 u v)) id (map_sum (permute_T2 u id) (Umap2 u id)) X = X'"
and alpha_Udtor2: "\<And>X X' d. valid_U2 d \<Longrightarrow> {X,X'} \<subseteq> Udtor2 d \<Longrightarrow>
  \<exists>u v. bij (u::'a \<Rightarrow> 'a) \<and> |supp u| <o |UNIV::'a set| \<and> bij (v::'b \<Rightarrow> 'b) \<and> |supp v| <o |UNIV::'b set|
  \<and> id_on ((set7_T2_pre X \<union> \<Union>(case_sum FVars_T1_1 UFVars11 ` set9_T2_pre X) \<union> \<Union>(case_sum FVars_T2_1 UFVars21 ` set11_T2_pre X)) - set5_T2_pre X) u
  \<and> id_on ((\<Union>(case_sum FVars_T1_2 UFVars12 ` set9_T2_pre X) \<union> \<Union>(case_sum FVars_T2_2 UFVars22 ` set11_T2_pre X)) - set6_T2_pre X) v
  \<and> map_T2_pre id id id id u v u id (map_sum (permute_T1 u v) (Umap1 u v)) id (map_sum (permute_T2 u id) (Umap2 u id)) X = X'"
    and
    (* The dual of the first block of assumptions from Norrish's paper:   *)
    UFVars11_Udtor:
    "\<And> d X. valid_U1 d \<Longrightarrow> X \<in> Udtor1 d \<Longrightarrow>
  set1_T1_pre X \<union> (set7_T1_pre X - set5_T1_pre X)
  \<union> \<Union>(case_sum FVars_T1_1 UFVars11 ` set8_T1_pre X) \<union> (\<Union>(case_sum FVars_T1_1 UFVars11 ` set9_T1_pre X) - set5_T1_pre X)
  \<union> \<Union>(case_sum FVars_T2_1 UFVars21 ` set10_T1_pre X) \<union> (\<Union>(case_sum FVars_T2_1 UFVars21 ` set11_T1_pre X) - set5_T1_pre X)
   \<subseteq> UFVars11 d"
  and UFVars12_Udtor:
    "\<And> d X. valid_U1 d \<Longrightarrow> X \<in> Udtor1 d \<Longrightarrow>
  set2_T1_pre X
  \<union> \<Union>(case_sum FVars_T1_2 UFVars12 ` set8_T1_pre X) \<union> (\<Union>(case_sum FVars_T1_2 UFVars12 ` set9_T1_pre X) - set6_T1_pre X)
  \<union> \<Union>(case_sum FVars_T2_2 UFVars22 ` set10_T1_pre X) \<union> (\<Union>(case_sum FVars_T2_2 UFVars22 ` set11_T1_pre X))
   \<subseteq> UFVars12 d"
  and UFVars21_Udtor:
    "\<And> d X. valid_U2 d \<Longrightarrow> X \<in> Udtor2 d \<Longrightarrow>
  set1_T2_pre X \<union> (set7_T2_pre X - set5_T2_pre X)
  \<union> \<Union>(case_sum FVars_T1_1 UFVars11 ` set8_T2_pre X) \<union> (\<Union>(case_sum FVars_T1_1 UFVars11 ` set9_T2_pre X) - set5_T2_pre X)
  \<union> \<Union>(case_sum FVars_T2_1 UFVars21 ` set10_T2_pre X) \<union> (\<Union>(case_sum FVars_T2_1 UFVars21 ` set11_T2_pre X) - set5_T2_pre X)
   \<subseteq> UFVars21 d"
  and UFVars22_Udtor:
    "\<And> d X. valid_U2 d \<Longrightarrow> X \<in> Udtor2 d \<Longrightarrow>
  set2_T2_pre X
  \<union> \<Union>(case_sum FVars_T1_2 UFVars12 ` set8_T2_pre X) \<union> (\<Union>(case_sum FVars_T1_2 UFVars12 ` set9_T2_pre X) - set6_T2_pre X)
  \<union> \<Union>(case_sum FVars_T2_2 UFVars22 ` set10_T2_pre X) \<union> (\<Union>(case_sum FVars_T2_2 UFVars22 ` set11_T2_pre X))
   \<subseteq> UFVars22 d"
    and
    (* The dual of the third block: *)
    Umap_Udtor1: "\<And>u v d. valid_U1 d \<Longrightarrow>
  bij (u::'a\<Rightarrow>'a) \<Longrightarrow> |supp u| <o |UNIV::'a set| \<Longrightarrow> bij (v::'b\<Rightarrow>'b) \<Longrightarrow> |supp v| <o |UNIV::'b set| \<Longrightarrow>
  Udtor1 (Umap1 u v d) \<subseteq>
  image
    (map_T1_pre u v id id u v u (map_sum (permute_T1 u v) (Umap1 u v)) (map_sum (permute_T1 u v) (Umap1 u v))
      (map_sum (permute_T2 u v) (Umap2 u v)) (map_sum (permute_T2 u v) (Umap2 u v)))
    (Udtor1 d)"
  and Umap_Udtor2: "\<And>u v d. valid_U2 d \<Longrightarrow>
  bij (u::'a\<Rightarrow>'a) \<Longrightarrow> |supp u| <o |UNIV::'a set| \<Longrightarrow> bij (v::'b\<Rightarrow>'b) \<Longrightarrow> |supp v| <o |UNIV::'b set| \<Longrightarrow>
  Udtor2 (Umap2 u v d) \<subseteq>
  image
    (map_T2_pre u v id id u v u (map_sum (permute_T1 u v) (Umap1 u v)) (map_sum (permute_T1 u v) (Umap1 u v))
      (map_sum (permute_T2 u v) (Umap2 u v)) (map_sum (permute_T2 u v) (Umap2 u v)))
    (Udtor2 d)"
    and Umap_comp1: "\<And>f1 f2 g1 g2 d. valid_U1 d \<Longrightarrow> bij f1 \<Longrightarrow> |supp (f1::'a \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (f2::'b \<Rightarrow> 'b)| <o |UNIV::'b set|
  \<Longrightarrow> bij g1 \<Longrightarrow> |supp (g1::'a \<Rightarrow> 'a)| <o |UNIV::'a set|\<Longrightarrow> bij g2 \<Longrightarrow> |supp (g2::'b \<Rightarrow> 'b)| <o |UNIV::'b set|
  \<Longrightarrow> Umap1 f1 f2 (Umap1 g1 g2 d) = Umap1 (f1 \<circ> g1) (f2 \<circ> g2) d"
    and Umap_comp2: "\<And>f1 f2 g1 g2 d. valid_U2 d \<Longrightarrow> bij f1 \<Longrightarrow> |supp (f1::'a \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (f2::'b \<Rightarrow> 'b)| <o |UNIV::'b set|
  \<Longrightarrow> bij g1 \<Longrightarrow> |supp (g1::'a \<Rightarrow> 'a)| <o |UNIV::'a set|\<Longrightarrow> bij g2 \<Longrightarrow> |supp (g2::'b \<Rightarrow> 'b)| <o |UNIV::'b set|
  \<Longrightarrow> Umap2 f1 f2 (Umap2 g1 g2 d) = Umap2 (f1 \<circ> g1) (f2 \<circ> g2) d"
    and Umap1_cong0: "\<And>f1 f2 d. valid_U1 d \<Longrightarrow> bij f1 \<Longrightarrow> |supp (f1::'a \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (f2::'b \<Rightarrow> 'b)| <o |UNIV::'b set|
  \<Longrightarrow> (\<And>a. a \<in> UFVars11 d \<Longrightarrow> f1 a = a) \<Longrightarrow> (\<And>a. a \<in> UFVars12 d \<Longrightarrow> f2 a = a) \<Longrightarrow> Umap1 f1 f2 d = d"
    and Umap2_cong0: "\<And>f1 f2 d. valid_U2 d \<Longrightarrow> bij f1 \<Longrightarrow> |supp (f1::'a \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (f2::'b \<Rightarrow> 'b)| <o |UNIV::'b set|
  \<Longrightarrow> (\<And>a. a \<in> UFVars21 d \<Longrightarrow> f1 a = a) \<Longrightarrow> (\<And>a. a \<in> UFVars22 d \<Longrightarrow> f2 a = a) \<Longrightarrow> Umap2 f1 f2 d = d"

    and valid_Umap1: "\<And>f1 f2 d. bij f1 \<Longrightarrow> |supp (f1::'a \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (f2::'b \<Rightarrow> 'b)| <o |UNIV::'b set| \<Longrightarrow>
     valid_U1 d \<Longrightarrow> valid_U1 (Umap1 f1 f2 d)"
    and valid_Umap2: "\<And>f1 f2 d. bij f1 \<Longrightarrow> |supp (f1::'a \<Rightarrow> 'a)| <o |UNIV::'a set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp (f2::'b \<Rightarrow> 'b)| <o |UNIV::'b set| \<Longrightarrow>
     valid_U2 d \<Longrightarrow> valid_U2 (Umap2 f1 f2 d)"
    and valid_Udtor1: "\<And>x d. valid_U1 d \<Longrightarrow> x \<in> Udtor1 d \<Longrightarrow>
      pred_T1_pre (\<lambda>_. True) (pred_sum (\<lambda>_. True) valid_U1)  (pred_sum (\<lambda>_. True) valid_U1) (pred_sum (\<lambda>_. True) valid_U2)  (pred_sum (\<lambda>_. True) valid_U2) x"
    and valid_Udtor2: "\<And>x d. valid_U2 d \<Longrightarrow> x \<in> Udtor2 d \<Longrightarrow>
      pred_T2_pre (\<lambda>_. True) (pred_sum (\<lambda>_. True) valid_U1)  (pred_sum (\<lambda>_. True) valid_U1) (pred_sum (\<lambda>_. True) valid_U2)  (pred_sum (\<lambda>_. True) valid_U2) x"
begin

lemmas Umap_cong0 = Umap1_cong0 Umap2_cong0
lemmas valid_Udtor = valid_Udtor1 valid_Udtor2

lemmas T1_T2_pred_set = T1_pre.pred_set T2_pre.pred_set

lemma Umap_id:
  "valid_U1 d1 \<Longrightarrow> Umap1 id id d1 = d1"
  "valid_U2 d2 \<Longrightarrow> Umap2 id id d2 = d2"
   apply -
  apply (rule Umap_cong0)
  apply assumption
        apply (rule bij_id supp_id_bound id_apply)+
  (* repeated *)
  apply (rule Umap_cong0)
  apply assumption
        apply (rule bij_id supp_id_bound id_apply)+
  done

lemma valid_Udtor':
  "\<And>x z r. valid_U1 d1 \<Longrightarrow> x \<in> Udtor1 d1 \<Longrightarrow> z \<in> set8_T1_pre x \<union> set9_T1_pre x \<Longrightarrow> r \<in> Basic_BNFs.setr z \<Longrightarrow> valid_U1 r"
  "\<And>x z r. valid_U1 d1 \<Longrightarrow> x \<in> Udtor1 d1 \<Longrightarrow> z \<in> set10_T1_pre x \<union> set11_T1_pre x \<Longrightarrow> r \<in> Basic_BNFs.setr z \<Longrightarrow> valid_U2 r"
  "\<And>x z r. valid_U2 d2 \<Longrightarrow> x \<in> Udtor2 d2 \<Longrightarrow> z \<in> set8_T2_pre x \<union> set9_T2_pre x \<Longrightarrow> r \<in> Basic_BNFs.setr z \<Longrightarrow> valid_U1 r"
  "\<And>x z r. valid_U2 d2 \<Longrightarrow> x \<in> Udtor2 d2 \<Longrightarrow> z \<in> set10_T2_pre x \<union> set11_T2_pre x \<Longrightarrow> r \<in> Basic_BNFs.setr z \<Longrightarrow> valid_U2 r"
  apply -
  apply (drule valid_Udtor)
   apply assumption
  apply (erule UnE)
   apply (unfold T1_T2_pred_set sum.pred_set)
  (* REPEAT_DETERM *)
   apply (erule conjE)+
  apply (rotate_tac 2)
   apply (drule bspec[rotated])
    apply assumption
   apply (erule conjE)
   apply (erule bspec)
   apply assumption
  (* repeated *)
   apply (erule conjE)+
  apply (rotate_tac 2)
   apply (drule bspec[rotated])
    apply assumption
   apply (erule conjE)
   apply (erule bspec)
   apply assumption
  (* END REPEAT_DETERM *)


  apply (drule valid_Udtor)
   apply assumption
  apply (erule UnE)
   apply (unfold T1_T2_pred_set sum.pred_set)
  (* REPEAT_DETERM *)
   apply (erule conjE)+
  apply (rotate_tac 2)
   apply (drule bspec[rotated])
    apply assumption
   apply (erule conjE)
   apply (erule bspec)
   apply assumption
  (* repeated *)
   apply (erule conjE)+
  apply (rotate_tac 2)
   apply (drule bspec[rotated])
    apply assumption
   apply (erule conjE)
   apply (erule bspec)
   apply assumption
  (* END REPEAT_DETERM *) 


   apply (drule valid_Udtor)
   apply assumption
  apply (erule UnE)
   apply (unfold T1_T2_pred_set sum.pred_set)
  (* REPEAT_DETERM *)
   apply (erule conjE)+
  apply (rotate_tac 2)
   apply (drule bspec[rotated])
    apply assumption
   apply (erule conjE)
   apply (erule bspec)
   apply assumption
  (* repeated *)
   apply (erule conjE)+
  apply (rotate_tac 2)
   apply (drule bspec[rotated])
    apply assumption
   apply (erule conjE)
   apply (erule bspec)
   apply assumption
  (* END REPEAT_DETERM *) 


  apply (drule valid_Udtor)
   apply assumption
  apply (erule UnE)
   apply (unfold T1_T2_pred_set sum.pred_set)
  (* REPEAT_DETERM *)
   apply (erule conjE)+
  apply (rotate_tac 2)
   apply (drule bspec[rotated])
    apply assumption
   apply (erule conjE)
   apply (erule bspec)
   apply assumption
  (* repeated *)
   apply (erule conjE)+
  apply (rotate_tac 2)
   apply (drule bspec[rotated])
    apply assumption
   apply (erule conjE)
   apply (erule bspec)
   apply assumption
  (* END REPEAT_DETERM *)
  done

lemma Umap_Udtor1_strong:
  assumes u: "bij u" "|supp u| <o |UNIV::'a set|"
    and v: "bij v" "|supp v| <o |UNIV::'b set|"
    and valid1: "valid_U1 d"
  shows
    "Udtor1 (Umap1 u v d) =
 image
(map_T1_pre u v id id u v u (map_sum (permute_T1 u v) (Umap1 u v)) (map_sum (permute_T1 u v) (Umap1 u v))
      (map_sum (permute_T2 u v) (Umap2 u v)) (map_sum (permute_T2 u v) (Umap2 u v)))
   (Udtor1 d)"
proof -
  have x: "d = Umap1 (inv u) (inv v) (Umap1 u v d)"
    apply (rule sym)
    apply (rule trans[OF Umap_comp1])
         apply (rule bij_imp_bij_inv supp_inv_bound assms)+
    apply (subst inv_o_simp1, rule assms)+
    apply (rule trans[OF Umap_id(1)])
     apply (rule assms)
    apply (rule refl)
    done
  show ?thesis
    apply (rule subset_antisym)
     apply (rule Umap_Udtor1[OF valid1 u v])
    apply (subst x)
    apply (rule image_subsetI)
    apply (drule Umap_Udtor1[THEN subsetD, rotated -1])
       apply (rule bij_imp_bij_inv supp_inv_bound assms valid_Umap1)+
    apply (erule imageE)
    apply hypsubst
    apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<in>)"]])
     apply (rule T1_pre.map_comp)
          apply (rule bij_imp_bij_inv supp_inv_bound supp_id_bound assms)+
                  apply (unfold map_sum.comp)
    apply (subst inv_o_simp2 T1.permute_comp0 T2.permute_comp0, (rule bij_imp_bij_inv supp_inv_bound assms)+)+
    apply (unfold comp_id)?
    apply (unfold comp_def)
    apply (unfold Umap_id T1.permute_id0 T2.permute_id0 map_sum.id)
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
     apply (rule T1_pre.map_cong[rotated -12])
                        apply (rule refl)
                        apply (rule refl)
                        apply (rule refl)
                        apply (rule refl)
                        apply (rule refl)
                        apply (rule refl)
                        apply (rule refl)
                        apply (rule refl)
      (* REPEAT_DETERM *)
            apply (rule sum.map_cong0[OF refl])
            apply (drule valid_Udtor'[rotated])
               apply (erule UnI2 UnI1)
              apply assumption
             apply (rule valid_Umap1)
               apply (rule assms bij_imp_bij_inv supp_inv_bound | assumption)+
            apply (rule trans)
             apply (rule Umap_comp1 Umap_comp2)
                 apply (rule assms bij_imp_bij_inv supp_inv_bound | assumption)+
                        apply (rule trans)
(* TODO: this "arg_cong3" (vars + 1) should be generalized to the number of args Umap* takes
         in the ML code *)
             apply (rule arg_cong3[OF _ _ refl, of _ _ _ _ Umap1])
             apply (rule inv_o_simp2, rule assms)+
            apply (rule Umap_id)
            apply assumption
      (* repeated *)
            apply (rule sum.map_cong0[OF refl])
            apply (drule valid_Udtor'[rotated])
               apply (erule UnI2 UnI1)
              apply assumption
             apply (rule valid_Umap1)
               apply (rule assms bij_imp_bij_inv supp_inv_bound | assumption)+
            apply (rule trans)
             apply (rule Umap_comp1 Umap_comp2)
                 apply (rule assms bij_imp_bij_inv supp_inv_bound | assumption)+
                       apply (rule trans)
             apply (rule arg_cong3[OF _ _ refl, of _ _ _ _ Umap1])
             apply (rule inv_o_simp2, rule assms)+
            apply (rule Umap_id)
                       apply assumption
      (* repeated *)
                      apply (rule sum.map_cong0[OF refl])
(* TODO: we need to explicitly pick the 2nd lemma here in valid_Udtor',
         because the first one also matches but leads to a dead end.
         Can we somehow make it so that it wouldn't be necessary to explicitly
         pick here? *)
            apply (drule valid_Udtor'(2)[rotated])
               apply (erule UnI2 UnI1)
              apply assumption
             apply (rule valid_Umap1)
               apply (rule assms bij_imp_bij_inv supp_inv_bound | assumption)+
            apply (rule trans)
             apply (rule Umap_comp1 Umap_comp2)
                 apply (rule assms bij_imp_bij_inv supp_inv_bound | assumption)+
                      apply (rule trans)
(* TODO: we need to alternate between Umap1 and Umap2 here between repeats,
can we rewrite this so that it wouldn't be necessary? *)
             apply (rule arg_cong3[OF _ _ refl, of _ _ _ _ Umap2])
             apply (rule inv_o_simp2, rule assms)+
            apply (rule Umap_id)
                      apply assumption
      (* repeated *)
                      apply (rule sum.map_cong0[OF refl])
            apply (drule valid_Udtor'(2)[rotated])
               apply (erule UnI2 UnI1)
              apply assumption
             apply (rule valid_Umap1)
               apply (rule assms bij_imp_bij_inv supp_inv_bound | assumption)+
            apply (rule trans)
             apply (rule Umap_comp1 Umap_comp2)
                 apply (rule assms bij_imp_bij_inv supp_inv_bound | assumption)+
                     apply (rule trans)
             apply (rule arg_cong3[OF _ _ refl, of _ _ _ _ Umap2])
             apply (rule inv_o_simp2, rule assms)+
            apply (rule Umap_id)
            apply assumption
      (* END REPEAT_DETERM *)
                      apply (rule supp_id_bound bij_id)+
      apply (unfold Umap_id T1.permute_id0 map_sum.id T1_pre.map_id id_def[symmetric])
    apply assumption
    done
qed

lemma Umap_Udtor2_strong:
  assumes u: "bij u" "|supp u| <o |UNIV::'a set|"
    and v: "bij v" "|supp v| <o |UNIV::'b set|"
    and valid2: "valid_U2 d"
  shows
    "Udtor2 (Umap2 u v d) =
 image
(map_T2_pre u v id id u v u (map_sum (permute_T1 u v) (Umap1 u v)) (map_sum (permute_T1 u v) (Umap1 u v))
      (map_sum (permute_T2 u v) (Umap2 u v)) (map_sum (permute_T2 u v) (Umap2 u v)))
   (Udtor2 d)"
proof -
  have x: "d = Umap2 (inv u) (inv v) (Umap2 u v d)"
    apply (rule sym)
    apply (rule trans[OF Umap_comp2])
         apply (rule bij_imp_bij_inv supp_inv_bound assms)+
    apply (subst inv_o_simp1, rule assms)+
    apply (rule trans[OF Umap_id(2)])
     apply (rule assms)
    apply (rule refl)
    done
  show ?thesis
    apply (rule subset_antisym)
     apply (rule Umap_Udtor2[OF valid2 u v])
    apply (subst x)
    apply (rule image_subsetI)
    apply (drule Umap_Udtor2[THEN subsetD, rotated -1])
       apply (rule bij_imp_bij_inv supp_inv_bound assms valid_Umap2)+
    apply (erule imageE)
    apply hypsubst
    apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<in>)"]])
     apply (rule T2_pre.map_comp)
          apply (rule bij_imp_bij_inv supp_inv_bound supp_id_bound assms)+
                  apply (unfold map_sum.comp)
    apply (subst inv_o_simp2 T1.permute_comp0 T2.permute_comp0, (rule bij_imp_bij_inv supp_inv_bound assms)+)+
    apply (unfold comp_id)?
    apply (unfold comp_def)
    apply (unfold Umap_id T1.permute_id0 T2.permute_id0 map_sum.id)
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD2])
     apply (rule T2_pre.map_cong[rotated -12])
                        apply (rule refl)
                        apply (rule refl)
                        apply (rule refl)
                        apply (rule refl)
                        apply (rule refl)
                        apply (rule refl)
                        apply (rule refl)
                        apply (rule refl)
      (* REPEAT_DETERM *)
            apply (rule sum.map_cong0[OF refl])
            apply (drule valid_Udtor'[rotated])
               apply (erule UnI2 UnI1)
              apply assumption
             apply (rule valid_Umap2)
               apply (rule assms bij_imp_bij_inv supp_inv_bound | assumption)+
            apply (rule trans)
             apply (rule Umap_comp1 Umap_comp2)
                 apply (rule assms bij_imp_bij_inv supp_inv_bound | assumption)+
                        apply (rule trans)
(* TODO: this "arg_cong3" should be generalized to the number of args Umap* takes
         in the ML code *)
             apply (rule arg_cong3[OF _ _ refl, of _ _ _ _ Umap1])
             apply (rule inv_o_simp2, rule assms)+
            apply (rule Umap_id)
            apply assumption
      (* repeated *)
            apply (rule sum.map_cong0[OF refl])
            apply (drule valid_Udtor'[rotated])
               apply (erule UnI2 UnI1)
              apply assumption
             apply (rule valid_Umap2)
               apply (rule assms bij_imp_bij_inv supp_inv_bound | assumption)+
            apply (rule trans)
             apply (rule Umap_comp1 Umap_comp2)
                 apply (rule assms bij_imp_bij_inv supp_inv_bound | assumption)+
                       apply (rule trans)
             apply (rule arg_cong3[OF _ _ refl, of _ _ _ _ Umap1])
             apply (rule inv_o_simp2, rule assms)+
            apply (rule Umap_id)
                       apply assumption
      (* repeated *)
                      apply (rule sum.map_cong0[OF refl])
(* TODO: we need to explicitly pick the 4th lemma here in valid_Udtor',
         because the 3rd one also matches but leads to a dead end.
         Can we somehow make it so that it wouldn't be necessary to explicitly
         pick here? *)
            apply (drule valid_Udtor'(4)[rotated])
               apply (erule UnI2 UnI1)
              apply assumption
             apply (rule valid_Umap2)
               apply (rule assms bij_imp_bij_inv supp_inv_bound | assumption)+
            apply (rule trans)
             apply (rule Umap_comp1 Umap_comp2)
                 apply (rule assms bij_imp_bij_inv supp_inv_bound | assumption)+
                      apply (rule trans)
(* TODO: we need to alternate between Umap1 and Umap2 here between repeats,
can we rewrite this so that it wouldn't be necessary? *)
             apply (rule arg_cong3[OF _ _ refl, of _ _ _ _ Umap2])
             apply (rule inv_o_simp2, rule assms)+
            apply (rule Umap_id)
                      apply assumption
      (* repeated *)
                      apply (rule sum.map_cong0[OF refl])
            apply (drule valid_Udtor'(4)[rotated])
               apply (erule UnI2 UnI1)
              apply assumption
             apply (rule valid_Umap2)
               apply (rule assms bij_imp_bij_inv supp_inv_bound | assumption)+
            apply (rule trans)
             apply (rule Umap_comp1 Umap_comp2)
                 apply (rule assms bij_imp_bij_inv supp_inv_bound | assumption)+
                     apply (rule trans)
             apply (rule arg_cong3[OF _ _ refl, of _ _ _ _ Umap2])
             apply (rule inv_o_simp2, rule assms)+
            apply (rule Umap_id)
            apply assumption
      (* END REPEAT_DETERM *)
                      apply (rule supp_id_bound bij_id)+
      apply (unfold Umap_id T1.permute_id0 map_sum.id T2_pre.map_id id_def[symmetric])
    apply assumption
    done
qed

lemmas Umap_Udtor_strong = Umap_Udtor1_strong Umap_Udtor2_strong

abbreviation "FFVarsBD11 X \<equiv> (set7_T1_pre X \<union> \<Union>(case_sum FVars_T1_1 UFVars11 ` set9_T1_pre X) \<union> \<Union>(case_sum FVars_T2_1 UFVars21 ` set11_T1_pre X)) - set5_T1_pre X"

abbreviation "FFVarsBD12 X \<equiv> (\<Union> (case_sum FVars_T1_2 UFVars12 ` set9_T1_pre X) \<union> \<Union> (case_sum FVars_T2_2 UFVars22 ` set11_T1_pre X) - set6_T1_pre X)"

abbreviation "FFVarsBD21 X \<equiv> (set7_T2_pre X \<union> \<Union>(case_sum FVars_T1_1 UFVars11 ` set9_T2_pre X) \<union> \<Union>(case_sum FVars_T2_1 UFVars21 ` set11_T2_pre X)) - set5_T2_pre X"

abbreviation "FFVarsBD22 X \<equiv> (\<Union> (case_sum FVars_T1_2 UFVars12 ` set9_T2_pre X) \<union> \<Union> (case_sum FVars_T2_2 UFVars22 ` set11_T2_pre X) - set6_T2_pre X)"


lemmas Udtor_Umap = alpha_Udtor1 alpha_Udtor2

lemmas FVars_T1_Udtor = UFVars11_Udtor UFVars12_Udtor
lemmas FVars_T2_Udtor = UFVars21_Udtor UFVars22_Udtor

(*************************************)
(* The raw-term-based model infrastructure *)

abbreviation "T1_abs \<equiv> quot_type.abs alpha_T1 Abs_T1"
abbreviation "T1_rep \<equiv> quot_type.rep Rep_T1"
abbreviation "T2_abs \<equiv> quot_type.abs alpha_T2 Abs_T2"
abbreviation "T2_rep \<equiv> quot_type.rep Rep_T2"

definition Utor1 :: "'u1 \<Rightarrow> ('a, 'b, 'c, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T2 + 'u2, ('a, 'b, 'c, 'd) raw_T2 + 'u2) T1_pre set" where
  "Utor1 d \<equiv>  map_T1_pre id id id id id id id (map_sum T1_rep id) (map_sum T1_rep id) (map_sum T2_rep id) (map_sum T2_rep id) ` (Udtor1 d)"

definition Utor2 :: "'u2 \<Rightarrow> ('a, 'b, 'c, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T2 + 'u2, ('a, 'b, 'c, 'd) raw_T2 + 'u2) T2_pre set" where
  "Utor2 d \<equiv>  map_T2_pre id id id id id id id (map_sum T1_rep id) (map_sum T1_rep id) (map_sum T2_rep id) (map_sum T2_rep id) ` (Udtor2 d)"

abbreviation raw_Umap1 :: "('a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> 'u1 \<Rightarrow> 'u1" where
  "raw_Umap1 \<equiv> Umap1"

abbreviation raw_Umap2 :: "('a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> 'u2 \<Rightarrow> 'u2" where
  "raw_Umap2 \<equiv> Umap2"

abbreviation raw_UFVars11 :: "'u1 \<Rightarrow> 'a set" where
  "raw_UFVars11 \<equiv> UFVars11"
abbreviation raw_UFVars12 :: "'u1 \<Rightarrow> 'b set" where
  "raw_UFVars12 \<equiv> UFVars12"
abbreviation raw_UFVars21 :: "'u2 \<Rightarrow> 'a set" where
  "raw_UFVars21 \<equiv> UFVars21"
abbreviation raw_UFVars22 :: "'u2 \<Rightarrow> 'b set" where
  "raw_UFVars22 \<equiv> UFVars22"

(* definition raw_UFVarsBD11 :: "('a, 'b, 'c, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T2 + 'u2, ('a, 'b, 'c, 'd) raw_T2 + 'u2) T1_pre \<Rightarrow> 'a set" where *)
abbreviation raw_UFVarsBD11 :: "('a, 'b, 'c, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T2 + 'u2, ('a, 'b, 'c, 'd) raw_T2 + 'u2) T1_pre \<Rightarrow> 'a set" where
  "raw_UFVarsBD11 X \<equiv> (set7_T1_pre X \<union> \<Union>(case_sum FVars_T1_1_raw UFVars11 ` set9_T1_pre X) \<union> \<Union>(case_sum FVars_T2_1_raw UFVars21 ` set11_T1_pre X)) - set5_T1_pre X"

(* definition raw_UFVarsBD12 :: "('a, 'b, 'c, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T2 + 'u2, ('a, 'b, 'c, 'd) raw_T2 + 'u2) T1_pre \<Rightarrow>'b set" where *)
abbreviation "raw_UFVarsBD12 X \<equiv> (\<Union> (case_sum FVars_T1_2_raw UFVars12 ` set9_T1_pre X) \<union> \<Union> (case_sum FVars_T2_2_raw UFVars22 ` set11_T1_pre X) - set6_T1_pre X)"

(* definition raw_UFVarsBD21 :: "('a, 'b, 'c, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T2 + 'u2, ('a, 'b, 'c, 'd) raw_T2 + 'u2) T2_pre \<Rightarrow> 'a set" where *)
abbreviation "raw_UFVarsBD21 X \<equiv> (set7_T2_pre X \<union> \<Union>(case_sum FVars_T1_1_raw UFVars11 ` set9_T2_pre X) \<union> \<Union>(case_sum FVars_T2_1_raw UFVars21 ` set11_T2_pre X)) - set5_T2_pre X"

(* definition raw_UFVarsBD22 :: "('a, 'b, 'c, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T2 + 'u2, ('a, 'b, 'c, 'd) raw_T2 + 'u2) T2_pre \<Rightarrow> 'b set" where *)
abbreviation "raw_UFVarsBD22 X \<equiv> (\<Union> (case_sum FVars_T1_2_raw UFVars12 ` set9_T2_pre X) \<union> \<Union> (case_sum FVars_T2_2_raw UFVars22 ` set11_T2_pre X) - set6_T2_pre X)"


lemmas raw_UFVars_def2_11 = trans[OF meta_eq_to_obj_eq[OF FVars_T1_1_def[of "T1_abs _"]] T1.alpha_FVars(1)[OF T1.rep_abs], symmetric]
lemmas raw_UFVars_def2_12 = trans[OF meta_eq_to_obj_eq[OF FVars_T1_2_def[of "T1_abs _"]] T1.alpha_FVars(2)[OF T1.rep_abs], symmetric]
lemmas raw_UFVars_def2_21 = trans[OF meta_eq_to_obj_eq[OF FVars_T2_1_def[of "T2_abs _"]] T2.alpha_FVars(1)[OF T2.rep_abs], symmetric]
lemmas raw_UFVars_def2_22 = trans[OF meta_eq_to_obj_eq[OF FVars_T2_2_def[of "T2_abs _"]] T2.alpha_FVars(2)[OF T2.rep_abs], symmetric]

lemmas raw_UFVars_def2 = raw_UFVars_def2_11 raw_UFVars_def2_12 raw_UFVars_def2_21 raw_UFVars_def2_22

(* Preterm-based version of the assumptions: *)

(*  *)
lemmas raw_Umap_id = Umap_id

lemmas raw_Umap_comp = Umap_comp1 Umap_comp2

term map_T2_pre

thm T1_pre.set_map


lemma FVarsBD_FFVarsBD1:
  "raw_UFVarsBD11 X = FFVarsBD11 (map_T1_pre id id id id id id id (map_sum T1_abs id) (map_sum T1_abs id) (map_sum T2_abs id) (map_sum T2_abs id) X)"
  "raw_UFVarsBD12 X = FFVarsBD12 (map_T1_pre id id id id id id id (map_sum T1_abs id) (map_sum T1_abs id) (map_sum T2_abs id) (map_sum T2_abs id) X)"
   apply -
 (* REPEAT_DETERM *)
  apply (unfold raw_UFVars_def2)[1]
  apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (subst image_id)+
  apply (subst image_image)+
  apply (subst case_sum_map_sum)+
  apply (subst comp_id)+
  apply (subst comp_def)+
   apply (rule refl)
(* repeated *)
  apply (unfold raw_UFVars_def2)[1]
  apply (subst T1_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (subst image_id)+
  apply (subst image_image)+
  apply (subst case_sum_map_sum)+
  apply (subst comp_id)+
  apply (subst comp_def)+
  apply (rule refl)
 (* END REPEAT_DETERM *)
  done

lemma FVarsBD_FFVarsBD2:
  "raw_UFVarsBD21 X = FFVarsBD21 (map_T2_pre id id id id id id id (map_sum T1_abs id) (map_sum T1_abs id) (map_sum T2_abs id) (map_sum T2_abs id) X)"
  "raw_UFVarsBD22 X = FFVarsBD22 (map_T2_pre id id id id id id id (map_sum T1_abs id) (map_sum T1_abs id) (map_sum T2_abs id) (map_sum T2_abs id) X)"
   apply -
 (* REPEAT_DETERM *)
  apply (unfold raw_UFVars_def2)[1]
  apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (subst image_id)+
  apply (subst image_image)+
  apply (subst case_sum_map_sum)+
  apply (subst comp_id)+
  apply (subst comp_def)+
   apply (rule refl)
(* repeated *)
  apply (unfold raw_UFVars_def2)[1]
  apply (subst T2_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (subst image_id)+
  apply (subst image_image)+
  apply (subst case_sum_map_sum)+
  apply (subst comp_id)+
  apply (subst comp_def)+
  apply (rule refl)
 (* END REPEAT_DETERM *)
  done

lemmas FVarsBD_FFVarsBD = FVarsBD_FFVarsBD1 FVarsBD_FFVarsBD2

lemmas supp_comp_bound = supp_comp_bound[OF _ _ infinite_UNIV]

lemma abs_rep_id:
  "T1_abs o T1_rep = id"
  "T2_abs o T2_rep = id"
  apply (unfold comp_def)
  apply (unfold T1.abs_rep T2.abs_rep)
  apply (fold id_def)
  apply (rule refl)+
  done

(*

REPEAT_DETERM o FIRST' [
  rtac ctxt @{thm ballI} THEN' rtac ctxt refl,
  rtac ctxt @{thm ballI} THEN' rtac ctxt @{thm ballI} THEN' rtac ctxt @{thm imp_refl},
  EVERY' [
    REPEAT_DETERM o resolve_tac ctxt @{thms ballI impI},
    dtac ctxt @{thm sum.rel_eq[THEN fun_cong, THEN fun_cong, THEN iffD2]},
    SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms sum.rel_map comp_def id_apply}),
    etac ctxt @{thm sum.rel_mono_strong},
    TRY o EVERY' [
      EqSubst.eqsubst_asm_tac ctxt [0] (map (#permute_abs o #inner) quots),
      REPEAT_DETERM o (resolve_tac ctxt @{thms bij_id supp_id_bound} ORELSE' assume_tac ctxt)
    ],
    eresolve_tac ctxt (map (#total_abs_eq_iff o #inner) quots),
    assume_tac ctxt
  ]
]

*)

lemma DTOR_mapD1:
  assumes "valid_U1 d"
  shows "{X,X'} \<subseteq> Utor1 d \<Longrightarrow> \<exists>u v. bij (u::'a\<Rightarrow>'a) \<and> |supp u| <o |UNIV::'a set| \<and> id_on (raw_UFVarsBD11 X) u \<and>
   bij (v::'b\<Rightarrow>'b) \<and> |supp v| <o |UNIV::'b set| \<and> id_on (raw_UFVarsBD12 X) v \<and>
     mr_rel_T1_pre id id id (=) u v u
       (rel_sum alpha_T1 (=))
       (rel_sum (\<lambda> t t'. alpha_T1 (permute_T1_raw u v t) t') (\<lambda> d d'. raw_Umap1 u v d = d'))
       (rel_sum alpha_T2 (=))
       (rel_sum (\<lambda> t t'. alpha_T2 (permute_T2_raw u id t) t') (\<lambda> d d'. raw_Umap2 u id d = d'))
     X X'"
  apply (drule image_mono[of _ _ "map_T1_pre id id id id id id id (map_sum T1_abs id) (map_sum T1_abs id) (map_sum T2_abs id) (map_sum T2_abs id)"])
  apply (unfold image_insert image_empty Utor1_def image_comp)
  apply (subst (asm) T1_pre.map_comp0[symmetric], (rule supp_id_bound bij_id)+)
  apply (unfold id_o map_sum.comp abs_rep_id map_sum.id T1_pre.map_id0 image_id)
  apply (drule alpha_Udtor1[OF assms])
  apply (erule exE conjE)+
  apply (subst (asm) T1_pre.set_map T1_pre.map_comp, (rule supp_id_bound bij_id | assumption)+)+
  apply (unfold image_id id_o o_id map_sum.comp)
  apply (drule T1_pre.mr_rel_eq[THEN fun_cong, THEN fun_cong, THEN iffD2])
  apply (subst (asm) T1_pre.mr_rel_map, (rule supp_id_bound bij_id | assumption)+)
  apply (unfold id_o o_id)
  apply (subst (asm) T1_pre.mr_rel_map, (rule supp_id_bound bij_id | assumption)+)
  apply (unfold inv_id id_o o_id relcompp_conversep_Grp)
  apply (unfold Grp_OO)
  apply (rule exI)+
  apply (rule conjI[rotated])+
        apply (erule T1_pre.mr_rel_mono_strong0[rotated -12]) (* nargs + 1 *)
                      apply (unfold0 id_apply)?
    (* REPEAT_DETERM *)
                      apply (rule ballI, rule refl)+
                      apply (rule ballI, rule ballI, rule imp_refl)+
                      apply (rule ballI, rule refl)+
    (* repeated *)
                      apply (rule ballI impI)+
                      apply (drule sum.rel_eq[THEN fun_cong, THEN fun_cong, THEN iffD2])
                      apply (unfold sum.rel_map comp_def id_apply)[1]
                      apply (erule sum.rel_mono_strong)
                      apply (subst (asm) T1.permute_abs, (rule bij_id supp_id_bound | assumption)+)?
                      apply (erule T1.total_abs_eq_iff[THEN iffD1])
                      apply assumption
    (* repeated *)
                      apply (rule ballI impI)+
                      apply (drule sum.rel_eq[THEN fun_cong, THEN fun_cong, THEN iffD2])
                      apply (unfold0 sum.rel_map comp_def id_apply)[1]
                      apply (erule sum.rel_mono_strong)
                      apply (subst (asm) T1.permute_abs, (rule bij_id supp_id_bound | assumption)+)?
                      apply (erule T1.total_abs_eq_iff[THEN iffD1])
                      apply assumption
    (* repeated *)
                      apply (rule ballI impI)+
                      apply (drule sum.rel_eq[THEN fun_cong, THEN fun_cong, THEN iffD2])
                      apply (unfold0 sum.rel_map comp_def id_apply)[1]
                      apply (erule sum.rel_mono_strong)
                      apply (subst (asm) T1.permute_abs, (rule bij_id supp_id_bound | assumption)+)?
                      apply (erule T2.total_abs_eq_iff[THEN iffD1])
                      apply assumption
    (* repeated *)
                      apply (rule ballI impI)+
                      apply (drule sum.rel_eq[THEN fun_cong, THEN fun_cong, THEN iffD2])
                      apply (unfold0 sum.rel_map comp_def id_apply)[1]
                      apply (erule sum.rel_mono_strong)
                      apply (subst (asm) T2.permute_abs, (rule bij_id supp_id_bound | assumption)+)?
                      apply (erule T2.total_abs_eq_iff[THEN iffD1])
                      apply assumption
    (* END REPEAT_DETERM *)
                      apply (rule supp_id_bound bij_id | assumption)+
       apply (unfold raw_UFVars_def2 image_comp[unfolded comp_def] case_sum_map_sum o_id)
       apply (unfold comp_def)
       apply assumption+
  done

lemma DTOR_mapD2:
  assumes "valid_U2 d"
  shows "{X,X'} \<subseteq> Utor2 d \<Longrightarrow> \<exists>u v. bij (u::'a\<Rightarrow>'a) \<and> |supp u| <o |UNIV::'a set| \<and> id_on (raw_UFVarsBD21 X) u \<and>
   bij (v::'b\<Rightarrow>'b) \<and> |supp v| <o |UNIV::'b set| \<and> id_on (raw_UFVarsBD22 X) v \<and>
     mr_rel_T2_pre id id id (=) u v u
       (rel_sum alpha_T1 (=))
       (rel_sum (\<lambda> t t'. alpha_T1 (permute_T1_raw u v t) t') (\<lambda> d d'. raw_Umap1 u v d = d'))
       (rel_sum alpha_T2 (=))
       (rel_sum (\<lambda> t t'. alpha_T2 (permute_T2_raw u id t) t') (\<lambda> d d'. raw_Umap2 u id d = d'))
     X X'"
  apply (drule image_mono[of _ _ "map_T2_pre id id id id id id id (map_sum T1_abs id) (map_sum T1_abs id) (map_sum T2_abs id) (map_sum T2_abs id)"])
  apply (unfold image_insert image_empty Utor2_def image_comp)
  apply (subst (asm) T2_pre.map_comp0[symmetric], (rule supp_id_bound bij_id)+)
  apply (unfold id_o map_sum.comp abs_rep_id map_sum.id T2_pre.map_id0 image_id)
  apply (drule alpha_Udtor2[OF assms])
  apply (erule exE conjE)+
  apply (subst (asm) T2_pre.set_map T2_pre.map_comp, (rule supp_id_bound bij_id | assumption)+)+
  apply (unfold image_id id_o o_id map_sum.comp)
  apply (drule T2_pre.mr_rel_eq[THEN fun_cong, THEN fun_cong, THEN iffD2])
  apply (subst (asm) T2_pre.mr_rel_map, (rule supp_id_bound bij_id | assumption)+)
  apply (unfold id_o o_id)
  apply (subst (asm) T2_pre.mr_rel_map, (rule supp_id_bound bij_id | assumption)+)
  apply (unfold inv_id id_o o_id relcompp_conversep_Grp)
  apply (unfold Grp_OO)
  apply (rule exI)+
  apply (rule conjI[rotated])+
        apply (erule T2_pre.mr_rel_mono_strong0[rotated -12]) (* nargs + 1 *)
                      apply (unfold0 id_apply)?
    (* REPEAT_DETERM *)
                      apply (rule ballI, rule refl)+
                      apply (rule ballI, rule ballI, rule imp_refl)+
                      apply (rule ballI, rule refl)+
    (* repeated *)
                      apply (rule ballI impI)+
                      apply (drule sum.rel_eq[THEN fun_cong, THEN fun_cong, THEN iffD2])
                      apply (unfold sum.rel_map comp_def id_apply)[1]
                      apply (erule sum.rel_mono_strong)
                      apply (subst (asm) T1.permute_abs, (rule bij_id supp_id_bound | assumption)+)?
                      apply (erule T1.total_abs_eq_iff[THEN iffD1])
                      apply assumption
    (* repeated *)
                      apply (rule ballI impI)+
                      apply (drule sum.rel_eq[THEN fun_cong, THEN fun_cong, THEN iffD2])
                      apply (unfold0 sum.rel_map comp_def id_apply)[1]
                      apply (erule sum.rel_mono_strong)
                      apply (subst (asm) T1.permute_abs, (rule bij_id supp_id_bound | assumption)+)?
                      apply (erule T1.total_abs_eq_iff[THEN iffD1])
                      apply assumption
    (* repeated *)
                      apply (rule ballI impI)+
                      apply (drule sum.rel_eq[THEN fun_cong, THEN fun_cong, THEN iffD2])
                      apply (unfold0 sum.rel_map comp_def id_apply)[1]
                      apply (erule sum.rel_mono_strong)
                      apply (subst (asm) T1.permute_abs, (rule bij_id supp_id_bound | assumption)+)?
                      apply (erule T2.total_abs_eq_iff[THEN iffD1])
                      apply assumption
    (* repeated *)
                      apply (rule ballI impI)+
                      apply (drule sum.rel_eq[THEN fun_cong, THEN fun_cong, THEN iffD2])
                      apply (unfold0 sum.rel_map comp_def id_apply)[1]
                      apply (erule sum.rel_mono_strong)
                      apply (subst (asm) T2.permute_abs, (rule bij_id supp_id_bound | assumption)+)?
                      apply (erule T2.total_abs_eq_iff[THEN iffD1])
                      apply assumption
    (* END REPEAT_DETERM *)
                      apply (rule supp_id_bound bij_id | assumption)+
       apply (unfold raw_UFVars_def2 image_comp[unfolded comp_def] case_sum_map_sum o_id)
       apply (unfold comp_def)
       apply assumption+
  done
lemmas DTOR_mapD = DTOR_mapD1 DTOR_mapD2

lemma Utor_ne:
  "valid_U1 d \<Longrightarrow> Utor1 d \<noteq> {}"
  "valid_U2 d2 \<Longrightarrow> Utor2 d2 \<noteq> {}"
   apply (unfold Utor1_def arg_cong[OF image_is_empty, of Not])
   apply (erule Udtor_ne)
  (* repeated *)
  apply (unfold Utor2_def arg_cong[OF image_is_empty, of Not])
  apply (erule Udtor_ne)
  done

lemma Utor_abs_Udtor1: "X \<in> Utor1 d \<Longrightarrow> map_T1_pre id id id id id id id (map_sum T1_abs id) (map_sum T1_abs id) (map_sum T2_abs id) (map_sum T2_abs id) X \<in> Udtor1 d"
  apply (unfold Utor1_def)
  apply (erule imageE)
  apply hypsubst_thin
  apply (subst T1_pre.map_comp)
    apply (rule supp_id_bound bij_id)+
  apply (subst map_sum.comp)+
  apply (subst id_o)+
  apply (subst abs_rep_id)+
  apply (subst map_sum.id)+
  apply (subst T1_pre.map_id)
  apply assumption
  done

lemma Utor_abs_Udtor2: "X \<in> Utor2 d \<Longrightarrow> map_T2_pre id id id id id id id (map_sum T1_abs id) (map_sum T1_abs id) (map_sum T2_abs id) (map_sum T2_abs id) X \<in> Udtor2 d"
  apply (unfold Utor2_def)
  apply (erule imageE)
  apply hypsubst_thin
  apply (subst T2_pre.map_comp)
    apply (rule supp_id_bound bij_id)+
  apply (subst map_sum.comp)+
  apply (subst id_o)+
  apply (subst abs_rep_id)+
  apply (subst map_sum.id)+
  apply (subst T2_pre.map_id)
  apply assumption
  done

lemmas Utor_abs_Udtor = Utor_abs_Udtor1 Utor_abs_Udtor2

thm FVars_T1_Udtor[OF _ Utor_abs_Udtor(1)]

lemma raw_UFVars_Utor1:
  assumes "valid_U1 d"
  shows "X \<in> Utor1 d \<Longrightarrow> set1_T1_pre X \<union> (set7_T1_pre X - set5_T1_pre X) \<union> \<Union>(case_sum FVars_T1_1_raw raw_UFVars11 ` set8_T1_pre X)
     \<union> (\<Union>(case_sum FVars_T1_1_raw raw_UFVars11 ` set9_T1_pre X) - set5_T1_pre X)
 \<union> \<Union>(case_sum FVars_T2_1_raw raw_UFVars21 ` set10_T1_pre X) \<union> (\<Union>(case_sum FVars_T2_1_raw raw_UFVars21 ` set11_T1_pre X) - set5_T1_pre X) \<subseteq> raw_UFVars11 d"
"X \<in> Utor1 d \<Longrightarrow> set2_T1_pre X \<union> \<Union>(case_sum FVars_T1_2_raw raw_UFVars12 ` set8_T1_pre X)
     \<union> (\<Union>(case_sum FVars_T1_2_raw raw_UFVars12 ` set9_T1_pre X) - set6_T1_pre X)
 \<union> \<Union>(case_sum FVars_T2_2_raw raw_UFVars22 ` set10_T1_pre X) \<union> (\<Union>(case_sum FVars_T2_2_raw raw_UFVars22 ` set11_T1_pre X)) \<subseteq> raw_UFVars12 d"
  apply (drule FVars_T1_Udtor(1)[OF assms Utor_abs_Udtor(1)])
  apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_comp case_sum_o_map_sum o_id image_id raw_UFVars_def2)
  apply (unfold FVarsBD_FFVarsBD comp_def)
   apply assumption
  (* repeated *)
  apply (drule FVars_T1_Udtor(2)[OF assms Utor_abs_Udtor(1)])
  apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_comp case_sum_o_map_sum o_id image_id raw_UFVars_def2)
  apply (unfold FVarsBD_FFVarsBD comp_def)
  apply assumption
  done

lemma raw_UFVars_Utor2:
  assumes "valid_U2 d"
  shows "X \<in> Utor2 d \<Longrightarrow> set1_T2_pre X \<union> (set7_T2_pre X - set5_T2_pre X) \<union> \<Union>(case_sum FVars_T1_1_raw raw_UFVars11 ` set8_T2_pre X)
     \<union> (\<Union>(case_sum FVars_T1_1_raw raw_UFVars11 ` set9_T2_pre X) - set5_T2_pre X)
 \<union> \<Union>(case_sum FVars_T2_1_raw raw_UFVars21 ` set10_T2_pre X) \<union> (\<Union>(case_sum FVars_T2_1_raw raw_UFVars21 ` set11_T2_pre X) - set5_T2_pre X) \<subseteq> raw_UFVars21 d"
"X \<in> Utor2 d \<Longrightarrow> set2_T2_pre X \<union> \<Union>(case_sum FVars_T1_2_raw raw_UFVars12 ` set8_T2_pre X)
     \<union> (\<Union>(case_sum FVars_T1_2_raw raw_UFVars12 ` set9_T2_pre X) - set6_T2_pre X)
 \<union> \<Union>(case_sum FVars_T2_2_raw raw_UFVars22 ` set10_T2_pre X) \<union> (\<Union>(case_sum FVars_T2_2_raw raw_UFVars22 ` set11_T2_pre X)) \<subseteq> raw_UFVars22 d"
  apply (drule FVars_T2_Udtor(1)[OF assms Utor_abs_Udtor(2)])
  apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_comp case_sum_o_map_sum o_id image_id raw_UFVars_def2)
  apply (unfold FVarsBD_FFVarsBD comp_def)
   apply assumption
  (* repeated *)
  apply (drule FVars_T2_Udtor(2)[OF assms Utor_abs_Udtor(2)])
  apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_comp case_sum_o_map_sum o_id image_id raw_UFVars_def2)
  apply (unfold FVarsBD_FFVarsBD comp_def)
  apply assumption
  done
                                     
lemmas raw_UFVars_Utor = raw_UFVars_Utor1 raw_UFVars_Utor2
                                      
term mr_rel_T1_pre

lemma raw_Umap_Utor1:
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a set|"
    and v: "bij (v::'b\<Rightarrow>'b)" "|supp v| <o |UNIV::'b set|"
    and valid_d: "valid_U1 d"
  shows
    "rel_set
  (mr_rel_T1_pre u v id (=) u v u
     (rel_sum (\<lambda> t t'. alpha_T1 (permute_T1_raw u v t) t') (\<lambda> d d'. raw_Umap1 u v d = d'))
     (rel_sum (\<lambda> t t'. alpha_T1 (permute_T1_raw u v t) t') (\<lambda> d d'. raw_Umap1 u v d = d'))
     (rel_sum (\<lambda> t t'. alpha_T2 (permute_T2_raw u v t) t') (\<lambda> d d'. raw_Umap2 u v d = d'))
     (rel_sum (\<lambda> t t'. alpha_T2 (permute_T2_raw u v t) t') (\<lambda> d d'. raw_Umap2 u v d = d')))
 (Utor1 d)
 (Utor1 (raw_Umap1 u v d))"
  apply (unfold Utor1_def)
  apply (subst Umap_Udtor_strong(1)[OF u v, of d])
  apply (rule valid_d)
  apply (subst image_comp)
  apply (subst T1_pre.map_comp0[symmetric])
      apply (rule assms supp_id_bound bij_id)+
  apply (subst map_sum.comp)+
  apply (subst id_o)+
  apply (subst rel_set_image)+
  apply (rule rel_set_reflI)
  apply (subst T1_pre.mr_rel_map)
      apply (rule supp_id_bound bij_id u v)+
  apply (subst o_id)+
  apply (subst T1_pre.mr_rel_map | rule u v supp_id_bound bij_id)+
  apply (subst inv_o_simp1 | rule u v bij_id)+
  apply (unfold relcompp_conversep_Grp Grp_OO T1_pre.mr_rel_id[symmetric])
  apply (subst sum.rel_map)+
  apply (unfold permute_T1_def permute_T2_def)
  apply (rule T1_pre.rel_refl)
  apply (rule refl)
    (* REPEAT *)
   apply (rule sum.rel_refl)
      apply (subst comp_apply)
    apply (rule T1.rep_abs_sym)
   apply (subst id_apply)
   apply (rule refl)
    (* repeated *)
   apply (rule sum.rel_refl)
     apply (subst comp_apply)
    apply (rule T1.rep_abs_sym)
   apply (subst id_apply)
    apply (rule refl)
    (* repeated *)
   apply (rule sum.rel_refl)
    apply (subst comp_apply)
    apply (rule T2.rep_abs_sym)
   apply (subst id_apply)
   apply (rule refl)
    (* repeated *)
   apply (rule sum.rel_refl)
    apply (subst comp_apply)
    apply (rule T2.rep_abs_sym)
   apply (subst id_apply)
  apply (rule refl)
(* END REPEAT *)
  done

lemma raw_Umap_Utor2:
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a set|"
    and v: "bij (v::'b\<Rightarrow>'b)" "|supp v| <o |UNIV::'b set|"
    and valid_d: "valid_U2 d"
  shows
    "rel_set
  (mr_rel_T2_pre u v id (=) u v u
     (rel_sum (\<lambda> t t'. alpha_T1 (permute_T1_raw u v t) t') (\<lambda> d d'. raw_Umap1 u v d = d'))
     (rel_sum (\<lambda> t t'. alpha_T1 (permute_T1_raw u v t) t') (\<lambda> d d'. raw_Umap1 u v d = d'))
     (rel_sum (\<lambda> t t'. alpha_T2 (permute_T2_raw u v t) t') (\<lambda> d d'. raw_Umap2 u v d = d'))
     (rel_sum (\<lambda> t t'. alpha_T2 (permute_T2_raw u v t) t') (\<lambda> d d'. raw_Umap2 u v d = d')))
 (Utor2 d)
 (Utor2 (raw_Umap2 u v d))"
  apply (unfold Utor2_def)
  apply (subst Umap_Udtor_strong(2)[OF u v, of d])
  apply (rule valid_d)
  apply (subst image_comp)
  apply (subst T2_pre.map_comp0[symmetric])
      apply (rule assms supp_id_bound bij_id)+
  apply (subst map_sum.comp)+
  apply (subst id_o)+
  apply (subst rel_set_image)+
  apply (rule rel_set_reflI)
  apply (subst T2_pre.mr_rel_map)
      apply (rule supp_id_bound bij_id u v)+
  apply (subst o_id)+
  apply (subst T2_pre.mr_rel_map | rule u v supp_id_bound bij_id)+
  apply (subst inv_o_simp1 | rule u v bij_id)+
  apply (unfold relcompp_conversep_Grp Grp_OO T2_pre.mr_rel_id[symmetric])
  apply (subst sum.rel_map)+
  apply (unfold permute_T1_def permute_T2_def)
  apply (rule T2_pre.rel_refl)
  apply (rule refl)
    (* REPEAT *)
   apply (rule sum.rel_refl)
      apply (subst comp_apply)
    apply (rule T1.rep_abs_sym)
   apply (subst id_apply)
   apply (rule refl)
    (* repeated *)
   apply (rule sum.rel_refl)
     apply (subst comp_apply)
    apply (rule T1.rep_abs_sym)
   apply (subst id_apply)
    apply (rule refl)
    (* repeated *)
   apply (rule sum.rel_refl)
    apply (subst comp_apply)
    apply (rule T2.rep_abs_sym)
   apply (subst id_apply)
   apply (rule refl)
    (* repeated *)
   apply (rule sum.rel_refl)
    apply (subst comp_apply)
    apply (rule T2.rep_abs_sym)
   apply (subst id_apply)
  apply (rule refl)
(* END REPEAT *)
  done

lemmas raw_Umap_Utor = raw_Umap_Utor1 raw_Umap_Utor2

definition suitable1 :: "('u1 \<Rightarrow> ('a, 'b, 'c, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T2 + 'u2, ('a, 'b, 'c, 'd) raw_T2 + 'u2) T1_pre) \<Rightarrow> bool" where
  "suitable1 pick \<equiv> \<forall> d. valid_U1 d \<longrightarrow> pick d \<in> Utor1 d"
definition suitable2 :: "('u2 \<Rightarrow> ('a, 'b, 'c, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T2 + 'u2, ('a, 'b, 'c, 'd) raw_T2 + 'u2) T2_pre) \<Rightarrow> bool" where
  "suitable2 pick \<equiv> \<forall> d. valid_U2 d \<longrightarrow> pick d \<in> Utor2 d"

term corec_raw_T1
term corec_raw_T2

definition f1 :: "('u1 \<Rightarrow> ('a, 'b, 'c, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T2 + 'u2, ('a, 'b, 'c, 'd) raw_T2 + 'u2) T1_pre) \<Rightarrow> ('u2 \<Rightarrow> ('a, 'b, 'c, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T2 + 'u2, ('a, 'b, 'c, 'd) raw_T2 + 'u2) T2_pre) \<Rightarrow> 'u1 => ('a, 'b, 'c, 'd) raw_T1" where
"f1 pick1 pick2 \<equiv> corec_raw_T1 pick1 pick2"
definition f2 :: "('u1 \<Rightarrow> ('a, 'b, 'c, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T2 + 'u2, ('a, 'b, 'c, 'd) raw_T2 + 'u2) T1_pre) \<Rightarrow> ('u2 \<Rightarrow> ('a, 'b, 'c, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T2 + 'u2, ('a, 'b, 'c, 'd) raw_T2 + 'u2) T2_pre) \<Rightarrow> 'u2 => ('a, 'b, 'c, 'd) raw_T2" where
"f2 pick1 pick2 \<equiv> corec_raw_T2 pick1 pick2"

definition pick0_1 :: "'u1 \<Rightarrow> ('a, 'b, 'c, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T2 + 'u2, ('a, 'b, 'c, 'd) raw_T2 + 'u2) T1_pre" where
  "pick0_1 \<equiv> SOME pick. suitable1 pick"
definition pick0_2 :: "'u2 \<Rightarrow> ('a, 'b, 'c, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T1 + 'u1, ('a, 'b, 'c, 'd) raw_T2 + 'u2, ('a, 'b, 'c, 'd) raw_T2 + 'u2) T2_pre" where
  "pick0_2 \<equiv> SOME pick. suitable2 pick"

definition f0_1 :: "'u1 \<Rightarrow> ('a, 'b, 'c, 'd) raw_T1" where
  "f0_1 \<equiv> f1 pick0_1 pick0_2"
definition f0_2 :: "'u2 \<Rightarrow> ('a, 'b, 'c, 'd) raw_T2" where
  "f0_2 \<equiv> f2 pick0_1 pick0_2"

definition COREC1 :: "'u1 \<Rightarrow> ('a, 'b, 'c, 'd) T1" where
  "COREC1 d = T1_abs (f0_1 d)"
definition COREC2 :: "'u2 \<Rightarrow> ('a, 'b, 'c, 'd) T2" where
  "COREC2 d = T2_abs (f0_2 d)"

thm raw_T1.corec

lemma f1_simps:
  "f1 pick1 pick2 d = raw_T1_ctor (map_T1_pre id id id id id id id (case_sum id (f1 pick1 pick2)) (case_sum id (f1 pick1 pick2)) (case_sum id (f2 pick1 pick2)) (case_sum id (f2 pick1 pick2)) (pick1 d))"
  apply(subst raw_T1.corec[of pick1 pick2, unfolded f1_def[symmetric] f2_def[symmetric]])
  apply (unfold id_def)
  apply (rule refl)
  done

lemma f2_simps:
  "f2 pick1 pick2 d = raw_T2_ctor (map_T2_pre id id id id id id id (case_sum id (f1 pick1 pick2)) (case_sum id (f1 pick1 pick2)) (case_sum id (f2 pick1 pick2)) (case_sum id (f2 pick1 pick2)) (pick2 d))"
  apply(subst raw_T2.corec[of pick1 pick2, unfolded f1_def[symmetric] f2_def[symmetric]])
  apply (unfold id_def)
  apply (rule refl)
  done

lemmas f_simps = f1_simps f2_simps

lemma f1_ctor:
  assumes "raw_T1_ctor x = f1 pick1 pick2 d"
  shows "x = map_T1_pre id id id id id id id(case_sum id (f1 pick1 pick2)) (case_sum id (f1 pick1 pick2)) (case_sum id (f2 pick1 pick2)) (case_sum id (f2 pick1 pick2)) (pick1 d)"
  by (rule trans[OF assms f_simps(1), unfolded raw_T1.inject])

lemma f2_ctor:
  assumes "raw_T2_ctor x = f2 pick1 pick2 d"
  shows "x = map_T2_pre id id id id id id id(case_sum id (f1 pick1 pick2)) (case_sum id (f1 pick1 pick2)) (case_sum id (f2 pick1 pick2)) (case_sum id (f2 pick1 pick2)) (pick2 d)"
  by (rule trans[OF assms f_simps(2), unfolded raw_T2.inject])

lemmas f_ctor = f1_ctor f2_ctor

lemma suitable1_FVarsD:
  assumes "suitable1 pick" "valid_U1 d"
  shows "set1_T1_pre (pick d) \<union> (set7_T1_pre (pick d) - set5_T1_pre (pick d)) \<union> \<Union> (case_sum FVars_T1_1_raw raw_UFVars11 ` set8_T1_pre (pick d)) \<union>
  (\<Union> (case_sum FVars_T1_1_raw raw_UFVars11 ` set9_T1_pre (pick d)) - set5_T1_pre (pick d)) \<union>
  \<Union> (case_sum FVars_T2_1_raw raw_UFVars21 ` set10_T1_pre (pick d)) \<union>
  (\<Union> (case_sum FVars_T2_1_raw raw_UFVars21 ` set11_T1_pre (pick d)) - set5_T1_pre (pick d))
  \<subseteq> raw_UFVars11 d"
  "set2_T1_pre (pick d) \<union> \<Union> (case_sum FVars_T1_2_raw raw_UFVars12 ` set8_T1_pre (pick d)) \<union>
  (\<Union> (case_sum FVars_T1_2_raw raw_UFVars12 ` set9_T1_pre (pick d)) - set6_T1_pre (pick d)) \<union>
  \<Union> (case_sum FVars_T2_2_raw raw_UFVars22 ` set10_T1_pre (pick d)) \<union>
  (\<Union> (case_sum FVars_T2_2_raw raw_UFVars22 ` set11_T1_pre (pick d)))
  \<subseteq> raw_UFVars12 d"
  by (rule raw_UFVars_Utor(1-2)[OF assms(2) assms(1)[unfolded suitable1_def, THEN spec, THEN mp, OF assms(2)]])+

lemma suitable2_FVarsD:
  assumes "suitable2 pick" "valid_U2 d"
  shows "set1_T2_pre (pick d) \<union> (set7_T2_pre (pick d) - set5_T2_pre (pick d)) \<union> \<Union> (case_sum FVars_T1_1_raw raw_UFVars11 ` set8_T2_pre (pick d)) \<union>
  (\<Union> (case_sum FVars_T1_1_raw raw_UFVars11 ` set9_T2_pre (pick d)) - set5_T2_pre (pick d)) \<union>
  \<Union> (case_sum FVars_T2_1_raw raw_UFVars21 ` set10_T2_pre (pick d)) \<union>
  (\<Union> (case_sum FVars_T2_1_raw raw_UFVars21 ` set11_T2_pre (pick d)) - set5_T2_pre (pick d))
  \<subseteq> raw_UFVars21 d"
    "set2_T2_pre (pick d) \<union> \<Union> (case_sum FVars_T1_2_raw raw_UFVars12 ` set8_T2_pre (pick d)) \<union>
  (\<Union> (case_sum FVars_T1_2_raw raw_UFVars12 ` set9_T2_pre (pick d)) - set6_T2_pre (pick d)) \<union>
  \<Union> (case_sum FVars_T2_2_raw raw_UFVars22 ` set10_T2_pre (pick d)) \<union>
  \<Union> (case_sum FVars_T2_2_raw raw_UFVars22 ` set11_T2_pre (pick d))
  \<subseteq> raw_UFVars22 d"
  by (rule raw_UFVars_Utor(3-4)[OF assms(2) assms(1)[unfolded suitable2_def, THEN spec, THEN mp, OF assms(2)]])+

lemmas suitable_FVarsD = suitable1_FVarsD suitable2_FVarsD

lemma f_FVarsD_aux11:
  assumes "is_free_raw_T11 a t"
    "(\<And>d. valid_U1 d \<Longrightarrow> t = f1 pick1 pick2 d \<Longrightarrow> a \<in> raw_UFVars11 d)"
    "pred_sum (\<lambda>_. True) valid_U1 td"
  shows "t = case_sum id (f1 pick1 pick2) td \<Longrightarrow> a \<in> case_sum FVars_T1_1_raw raw_UFVars11 td"
  apply (rule sumE[of td])
   apply hypsubst
   apply (subst sum.case)
   apply (unfold FVars_T1_1_raw_def mem_Collect_eq)
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
lemma f_FVarsD_aux21:
  assumes "is_free_raw_T21 a t"
    "(\<And>d. valid_U2 d \<Longrightarrow> t = f2 pick1 pick2 d \<Longrightarrow> a \<in> raw_UFVars21 d)"
    "pred_sum (\<lambda>_. True) valid_U2 td"
  shows "t = case_sum id (f2 pick1 pick2) td \<Longrightarrow> a \<in> case_sum FVars_T2_1_raw raw_UFVars21 td"
  apply (rule sumE[of td])
   apply hypsubst
   apply (subst sum.case)
   apply (unfold FVars_T2_1_raw_def mem_Collect_eq)
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
lemma f_FVarsD_aux12:
  assumes "is_free_raw_T12 a t"
    "(\<And>d. valid_U1 d \<Longrightarrow> t = f1 pick1 pick2 d \<Longrightarrow> a \<in> raw_UFVars12 d)"
    "pred_sum (\<lambda>_. True) valid_U1 td"
  shows "t = case_sum id (f1 pick1 pick2) td \<Longrightarrow> a \<in> case_sum FVars_T1_2_raw raw_UFVars12 td"
  apply (rule sumE[of td])
   apply hypsubst
   apply (subst sum.case)
   apply (unfold FVars_T1_2_raw_def mem_Collect_eq)
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
lemma f_FVarsD_aux22:
  assumes "is_free_raw_T22 a t"
    "(\<And>d. valid_U2 d \<Longrightarrow> t = f2 pick1 pick2 d \<Longrightarrow> a \<in> raw_UFVars22 d)"
    "pred_sum (\<lambda>_. True) valid_U2 td"
  shows "t = case_sum id (f2 pick1 pick2) td \<Longrightarrow> a \<in> case_sum FVars_T2_2_raw raw_UFVars22 td"
  apply (rule sumE[of td])
   apply hypsubst
   apply (subst sum.case)
   apply (unfold FVars_T2_2_raw_def mem_Collect_eq)
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

lemmas f_FVarsD_aux1 = f_FVarsD_aux11 f_FVarsD_aux21
lemmas f_FVarsD_aux2 = f_FVarsD_aux12 f_FVarsD_aux22
lemmas f_FVarsD_aux = f_FVarsD_aux1 f_FVarsD_aux2

(* TODO: just realized there exists some simp tactics in this proof :') *)
(* TODO: we probably also need variants of these for T2 *)
lemma valid_pick_set8:
  "suitable1 pick \<Longrightarrow> xc \<in> set8_T1_pre (pick xb) \<Longrightarrow> valid_U1 xb \<Longrightarrow> pred_sum (\<lambda>_. True) valid_U1 xc"
  "suitable2 pick2 \<Longrightarrow> xc2 \<in> set8_T2_pre (pick2 xb2) \<Longrightarrow> valid_U2 xb2 \<Longrightarrow> pred_sum (\<lambda>_. True) valid_U1 xc2"
(* REPEAT_DETERM *)
  apply (unfold suitable1_def Utor1_def)
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply (erule imageE[of _ _ "Udtor1 xb"])
  apply (simp only:)
  apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id)+)
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
(* repeated *)
  apply (unfold suitable2_def Utor2_def)
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply (erule imageE[of _ _ "Udtor2 xb2"])
  apply (simp only:)
  apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id)+)
  apply (cases xc2)
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
(* END REPEAT_DETERM *)
  done

lemma valid_pick_set9:
  "suitable1 pick \<Longrightarrow> xc \<in> set9_T1_pre (pick xb) \<Longrightarrow> valid_U1 xb \<Longrightarrow> pred_sum (\<lambda>_. True) valid_U1 xc"
  "suitable2 pick2 \<Longrightarrow> xc2 \<in> set9_T2_pre (pick2 xb2) \<Longrightarrow> valid_U2 xb2 \<Longrightarrow> pred_sum (\<lambda>_. True) valid_U1 xc2"
(* REPEAT_DETERM *)
  apply (unfold suitable1_def Utor1_def)
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply (erule imageE[of _ _ "Udtor1 xb"])
  apply (simp only:)
  apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id)+)
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
(* repeated *)
  apply (unfold suitable2_def Utor2_def)
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply (erule imageE[of _ _ "Udtor2 xb2"])
  apply (simp only:)
  apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id)+)
  apply (cases xc2)
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
(* END REPEAT_DETERM *)
  done

lemma valid_pick_set10:
  "suitable1 pick \<Longrightarrow> xc \<in> set10_T1_pre (pick xb) \<Longrightarrow> valid_U1 xb \<Longrightarrow> pred_sum (\<lambda>_. True) valid_U2 xc"
  "suitable2 pick2 \<Longrightarrow> xc2 \<in> set10_T2_pre (pick2 xb2) \<Longrightarrow> valid_U2 xb2 \<Longrightarrow> pred_sum (\<lambda>_. True) valid_U2 xc2"
(* REPEAT_DETERM *)
  apply (unfold suitable1_def Utor1_def)
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply (erule imageE[of _ _ "Udtor1 xb"])
  apply (simp only:)
  apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id)+)
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
(* repeated *)
  apply (unfold suitable2_def Utor2_def)
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply (erule imageE[of _ _ "Udtor2 xb2"])
  apply (simp only:)
  apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id)+)
  apply (cases xc2)
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
(* END REPEAT_DETERM *)
  done

lemma valid_pick_set11:
  "suitable1 pick \<Longrightarrow> xc \<in> set11_T1_pre (pick xb) \<Longrightarrow> valid_U1 xb \<Longrightarrow> pred_sum (\<lambda>_. True) valid_U2 xc"
  "suitable2 pick2 \<Longrightarrow> xc2 \<in> set11_T2_pre (pick2 xb2) \<Longrightarrow> valid_U2 xb2 \<Longrightarrow> pred_sum (\<lambda>_. True) valid_U2 xc2"
(* REPEAT_DETERM *)
  apply (unfold suitable1_def Utor1_def)
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply (erule imageE[of _ _ "Udtor1 xb"])
  apply (simp only:)
  apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id)+)
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
(* repeated *)
  apply (unfold suitable2_def Utor2_def)
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply (erule imageE[of _ _ "Udtor2 xb2"])
  apply (simp only:)
  apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id)+)
  apply (cases xc2)
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
(* END REPEAT_DETERM *)
  done

lemma f_FVarsD1:
  assumes p: "suitable1 pick1" "suitable2 pick2"
  shows "valid_U1 d \<Longrightarrow> FVars_T1_1_raw (f1 pick1 pick2 d) \<subseteq> raw_UFVars11 d"
    "valid_U2 d2 \<Longrightarrow> FVars_T2_1_raw (f2 pick1 pick2 d2) \<subseteq> raw_UFVars21 d2"
proof -
  have x: "\<And>a y y2. (is_free_raw_T11 a y \<longrightarrow> (\<forall>d. valid_U1 d \<longrightarrow> y = f1 pick1 pick2 d \<longrightarrow> a \<in> raw_UFVars11 d))
    \<and> (is_free_raw_T21 a y2 \<longrightarrow> (\<forall>d2. valid_U2 d2 \<longrightarrow> y2 = f2 pick1 pick2 d2 \<longrightarrow> a \<in> raw_UFVars21 d2))"
    apply (rule is_free_raw_T11_is_free_raw_T21.induct)
          (* REPEAT_DETERM *)
              apply (rule allI)
              apply (rule impI)+
               apply (drule DiffI, assumption)?
               apply (erule suitable_FVarsD(1)[OF assms(1), unfolded Un_assoc, THEN set_mp])
               apply (drule f_ctor)
              apply hypsubst
              apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id)+)+
               apply (unfold image_id Un_assoc[symmetric])[1]
               apply (erule UnI1 UnI2 | rule UnI1)+
            (* repeated *)
            apply (rule allI)
              apply (rule impI)+
               apply (drule DiffI, assumption)?
               apply (erule suitable_FVarsD(1)[OF assms(1), unfolded Un_assoc, THEN set_mp])
               apply (drule f_ctor)
              apply hypsubst
              apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id)+)+
               apply (unfold image_id Un_assoc[symmetric])[1]
              apply (erule UnI1 UnI2 | rule UnI1)+
          (* END REPEAT_DETERM *)

(* REPEAT_DETERM *)
   apply (rule allI)
   apply (rule impI)+
   apply (frule f_ctor)
   apply hypsubst
   apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id)?
   apply (erule imageE)
   apply hypsubst
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
   apply (rule suitable_FVarsD[THEN subsetD, rotated])
  apply assumption
       apply (unfold Un_assoc)
    apply (rule UnI2)
    apply (unfold Un_assoc[symmetric])?
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 2] 1\<close>) (* normally: Use goal number here *)
    apply (rule DiffI[rotated], assumption)?
    apply (rule UN_I)
     apply assumption
    apply assumption
     apply (rule assms)
   apply (drule valid_pick_set8(1)[OF p(1)])
    apply assumption
            apply assumption
(* repeated *)
   apply (rule allI)
   apply (rule impI)+
   apply (frule f_ctor)
   apply hypsubst
   apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id)?
   apply (erule imageE)
   apply hypsubst
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
   apply (rule suitable_FVarsD[THEN subsetD, rotated])
  apply assumption
       apply (unfold Un_assoc)
    apply (rule UnI2)
    apply (unfold Un_assoc[symmetric])?
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 3] 1\<close>) (* normally: Use goal number here *)
    apply (rule DiffI[rotated], assumption)?
    apply (rule UN_I)
     apply assumption
    apply assumption
     apply (rule assms)
   apply (drule valid_pick_set9(1)[OF p(1)])
    apply assumption
  apply assumption
(* repeated *)
   apply (rule allI)
          apply (rule impI)+
   apply (frule f_ctor)
   apply hypsubst
   apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id)?
   apply (erule imageE)
   apply hypsubst
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
   apply (rule suitable_FVarsD[THEN subsetD, rotated])
  apply assumption
       apply (unfold Un_assoc)
    apply (rule UnI2)
    apply (unfold Un_assoc[symmetric])?
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 4] 1\<close>) (* normally: Use goal number here *)
    apply (rule DiffI[rotated], assumption)?
    apply (rule UN_I)
     apply assumption
    apply assumption
            apply (rule assms)
   apply (drule valid_pick_set10(1)[OF p(1)])
    apply assumption
           apply assumption
(* repeated *)
   apply (rule allI)
          apply (rule impI)+
   apply (frule f_ctor)
   apply hypsubst
   apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id)?
   apply (erule imageE)
   apply hypsubst
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
   apply (rule suitable_FVarsD[THEN subsetD, rotated])
  apply assumption
       apply (unfold Un_assoc)
    apply (rule UnI2)
    apply (unfold Un_assoc[symmetric])?
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 5] 1\<close>) (* normally: Use goal number here *)
    apply (rule DiffI[rotated], assumption)?
    apply (rule UN_I)
     apply assumption
    apply assumption
            apply (rule assms)
   apply (drule valid_pick_set11(1)[OF p(1)])
    apply assumption
          apply assumption
    (* END REPEAT_DETERM *)

          (* REPEAT_DETERM *)
              apply (rule allI)
              apply (rule impI)+
         apply (drule DiffI, assumption)?
               apply (erule suitable_FVarsD(3)[OF assms(2), unfolded Un_assoc, THEN set_mp])
               apply (drule f_ctor)
              apply hypsubst
              apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id)+)+
               apply (unfold image_id Un_assoc[symmetric])[1]
               apply (erule UnI1 UnI2 | rule UnI1)+
            (* repeated *)
            apply (rule allI)
              apply (rule impI)+
               apply (drule DiffI, assumption)?
               apply (erule suitable_FVarsD(3)[OF assms(2), unfolded Un_assoc, THEN set_mp])
               apply (drule f_ctor)
              apply hypsubst
              apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id)+)+
               apply (unfold image_id Un_assoc[symmetric])[1]
              apply (erule UnI1 UnI2 | rule UnI1)+
          (* END REPEAT_DETERM *)

(* REPEAT_DETERM *)
   apply (rule allI)
   apply (rule impI)+
   apply (frule f_ctor)
   apply hypsubst
   apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id)?
   apply (erule imageE)
   apply hypsubst
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
   apply (rule suitable_FVarsD[THEN subsetD, rotated])
  apply assumption
       apply (unfold Un_assoc)
    apply (rule UnI2)
    apply (unfold Un_assoc[symmetric])?
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 2] 1\<close>) (* normally: Use goal number here *)
    apply (rule DiffI[rotated], assumption)?
    apply (rule UN_I)
     apply assumption
    apply assumption
     apply (rule assms)
   apply (drule valid_pick_set8(2)[OF p(2)])
    apply assumption
            apply assumption
(* repeated *)
   apply (rule allI)
   apply (rule impI)+
   apply (frule f_ctor)
   apply hypsubst
   apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id)?
   apply (erule imageE)
   apply hypsubst
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
   apply (rule suitable_FVarsD[THEN subsetD, rotated])
  apply assumption
       apply (unfold Un_assoc)
    apply (rule UnI2)
    apply (unfold Un_assoc[symmetric])?
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 3] 1\<close>) (* normally: Use goal number here *)
    apply (rule DiffI[rotated], assumption)?
    apply (rule UN_I)
     apply assumption
    apply assumption
     apply (rule assms)
   apply (drule valid_pick_set9(2)[OF p(2)])
    apply assumption
  apply assumption
(* repeated *)
   apply (rule allI)
          apply (rule impI)+
   apply (frule f_ctor)
   apply hypsubst
   apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id)?
   apply (erule imageE)
   apply hypsubst
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
   apply (rule suitable_FVarsD[THEN subsetD, rotated])
  apply assumption
       apply (unfold Un_assoc)
    apply (rule UnI2)
    apply (unfold Un_assoc[symmetric])?
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 4] 1\<close>) (* normally: Use goal number here *)
    apply (rule DiffI[rotated], assumption)?
    apply (rule UN_I)
     apply assumption
    apply assumption
            apply (rule assms)
   apply (drule valid_pick_set10(2)[OF p(2)])
    apply assumption
           apply assumption
(* repeated *)
   apply (rule allI)
          apply (rule impI)+
   apply (frule f_ctor)
   apply hypsubst
   apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id)?
   apply (erule imageE)
   apply hypsubst
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
   apply (rule suitable_FVarsD[THEN subsetD, rotated])
  apply assumption
       apply (unfold Un_assoc)
    apply (rule UnI2)
    apply (unfold Un_assoc[symmetric])?
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 5 5] 1\<close>) (* normally: Use goal number here *)
    apply (rule DiffI[rotated], assumption)?
    apply (rule UN_I)
     apply assumption
    apply assumption
            apply (rule assms)
   apply (drule valid_pick_set11(2)[OF p(2)])
    apply assumption
          apply assumption
    (* END REPEAT_DETERM *)
    done
    
  show "valid_U1 d \<Longrightarrow> FVars_T1_1_raw (f1 pick1 pick2 d) \<subseteq> raw_UFVars11 d"
    "valid_U2 d2 \<Longrightarrow> FVars_T2_1_raw (f2 pick1 pick2 d2) \<subseteq> raw_UFVars21 d2"
     apply -
     apply (rule subsetI)
     apply (erule x[THEN conjunct1, THEN mp, THEN spec, THEN mp, THEN mp, rotated 1] x[THEN conjunct2, THEN mp, THEN spec, THEN mp, THEN mp, rotated 1])
      apply (rule refl)
     apply (unfold FVars_T1_1_raw_def mem_Collect_eq)
     apply assumption
  (* repeated *)
     apply (rule subsetI)
     apply (erule x[THEN conjunct1, THEN mp, THEN spec, THEN mp, THEN mp, rotated 1] x[THEN conjunct2, THEN mp, THEN spec, THEN mp, THEN mp, rotated 1])
      apply (rule refl)
     apply (unfold FVars_T2_1_raw_def mem_Collect_eq)
    apply assumption
    done
qed

thm is_free_raw_T11_is_free_raw_T21.induct is_free_raw_T12_is_free_raw_T22.induct

lemma f_FVarsD2:
  assumes p: "suitable1 pick1" "suitable2 pick2"
  shows "valid_U1 d \<Longrightarrow> FVars_T1_2_raw (f1 pick1 pick2 d) \<subseteq> raw_UFVars12 d"
    "valid_U2 d2 \<Longrightarrow> FVars_T2_2_raw (f2 pick1 pick2 d2) \<subseteq> raw_UFVars22 d2"
proof -
  have x: "\<And>a y y2. (is_free_raw_T12 a y \<longrightarrow> (\<forall>d. valid_U1 d \<longrightarrow> y = f1 pick1 pick2 d \<longrightarrow> a \<in> raw_UFVars12 d))
    \<and> (is_free_raw_T22 a y2 \<longrightarrow> (\<forall>d2. valid_U2 d2 \<longrightarrow> y2 = f2 pick1 pick2 d2 \<longrightarrow> a \<in> raw_UFVars22 d2))"
    apply (rule is_free_raw_T12_is_free_raw_T22.induct)
              apply (rule allI)
              apply (rule impI)+
             apply (drule DiffI, assumption)?
               apply (erule suitable_FVarsD(2)[OF assms(1), unfolded Un_assoc, THEN set_mp])
               apply (drule f_ctor)
              apply hypsubst
              apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id)+)+
               apply (unfold image_id Un_assoc[symmetric])[1]
               apply (erule UnI1 UnI2 | rule UnI1)+

(* REPEAT_DETERM *)
   apply (rule allI)
   apply (rule impI)+
   apply (frule f_ctor)
   apply hypsubst
   apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id)?
   apply (erule imageE)
            apply hypsubst
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
   apply (rule suitable_FVarsD[THEN subsetD, rotated])
  apply assumption
       apply (unfold Un_assoc)
    apply (rule UnI2)
    apply (unfold Un_assoc[symmetric])?
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 4 1] 1\<close>) (* normally: Use goal number here *)
    apply (rule DiffI[rotated], assumption)?
    apply (rule UN_I)
     apply assumption
    apply assumption
     apply (rule assms)
   apply (drule valid_pick_set8(1)[OF p(1)])
    apply assumption
            apply assumption
(* repeated *)
   apply (rule allI)
   apply (rule impI)+
   apply (frule f_ctor)
   apply hypsubst
   apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id)?
   apply (erule imageE)
   apply hypsubst
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
   apply (rule suitable_FVarsD[THEN subsetD, rotated])
  apply assumption
       apply (unfold Un_assoc)
    apply (rule UnI2)
    apply (unfold Un_assoc[symmetric])?
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 4 2] 1\<close>) (* normally: Use goal number here *)
    apply (rule DiffI[rotated], assumption)?
    apply (rule UN_I)
     apply assumption
    apply assumption
     apply (rule assms)
   apply (drule valid_pick_set9(1)[OF p(1)])
    apply assumption
  apply assumption
(* repeated *)
   apply (rule allI)
          apply (rule impI)+
   apply (frule f_ctor)
   apply hypsubst
   apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id)?
   apply (erule imageE)
   apply hypsubst
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
   apply (rule suitable_FVarsD[THEN subsetD, rotated])
  apply assumption
       apply (unfold Un_assoc)
    apply (rule UnI2)
    apply (unfold Un_assoc[symmetric])?
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 4 3] 1\<close>) (* normally: Use goal number here *)
    apply (rule DiffI[rotated], assumption)?
    apply (rule UN_I)
     apply assumption
    apply assumption
            apply (rule assms)
   apply (drule valid_pick_set10(1)[OF p(1)])
    apply assumption
           apply assumption
(* repeated *)
   apply (rule allI)
          apply (rule impI)+
   apply (frule f_ctor)
   apply hypsubst
   apply (subst (asm) T1_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id)?
   apply (erule imageE)
   apply hypsubst
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
    thm suitable_FVarsD[THEN subsetD, rotated]
          apply (rule suitable_FVarsD[THEN subsetD, rotated])
    thm suitable_FVarsD
  apply assumption
           apply (unfold Un_assoc)
    apply (rule UnI2)
    apply (unfold Un_assoc[symmetric])?
           apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 4 4] 1\<close>) (* normally: Use goal number here *)
           apply (rule DiffI[rotated], assumption)?
    apply (rule UN_I)
     apply assumption
    apply assumption
            apply (rule assms)
   apply (drule valid_pick_set11(1)[OF p(1)])
    apply assumption
          apply assumption
    (* END REPEAT_DETERM *)

          (* REPEAT_DETERM *)
              apply (rule allI)
              apply (rule impI)+
         apply (drule DiffI, assumption)?
               apply (erule suitable_FVarsD(4)[OF assms(2), unfolded Un_assoc, THEN set_mp])
               apply (drule f_ctor)
              apply hypsubst
              apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id)+)+
               apply (unfold image_id Un_assoc[symmetric])[1]
               apply (erule UnI1 UnI2 | rule UnI1)+
            (* END REPEAT_DETERM *)

(* REPEAT_DETERM *)
   apply (rule allI)
   apply (rule impI)+
   apply (frule f_ctor)
   apply hypsubst
   apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id)?
   apply (erule imageE)
   apply hypsubst
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
   apply (rule suitable_FVarsD[THEN subsetD, rotated])
  apply assumption
       apply (unfold Un_assoc)
    apply (rule UnI2)
    apply (unfold Un_assoc[symmetric])?
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 4 1] 1\<close>) (* normally: Use goal number here *)
    apply (rule DiffI[rotated], assumption)?
    apply (rule UN_I)
     apply assumption
    apply assumption
     apply (rule assms)
   apply (drule valid_pick_set8(2)[OF p(2)])
    apply assumption
            apply assumption
(* repeated *)
   apply (rule allI)
   apply (rule impI)+
   apply (frule f_ctor)
   apply hypsubst
   apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id)?
   apply (erule imageE)
   apply hypsubst
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
   apply (rule suitable_FVarsD[THEN subsetD, rotated])
  apply assumption
       apply (unfold Un_assoc)
    apply (rule UnI2)
    apply (unfold Un_assoc[symmetric])?
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 4 2] 1\<close>) (* normally: Use goal number here *)
    apply (rule DiffI[rotated], assumption)?
    apply (rule UN_I)
     apply assumption
    apply assumption
     apply (rule assms)
   apply (drule valid_pick_set9(2)[OF p(2)])
    apply assumption
  apply assumption
(* repeated *)
   apply (rule allI)
          apply (rule impI)+
   apply (frule f_ctor)
   apply hypsubst
   apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id)?
   apply (erule imageE)
   apply hypsubst
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
   apply (rule suitable_FVarsD[THEN subsetD, rotated])
  apply assumption
       apply (unfold Un_assoc)
    apply (rule UnI2)
    apply (unfold Un_assoc[symmetric])?
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 4 3] 1\<close>) (* normally: Use goal number here *)
    apply (rule DiffI[rotated], assumption)?
    apply (rule UN_I)
     apply assumption
    apply assumption
            apply (rule assms)
   apply (drule valid_pick_set10(2)[OF p(2)])
    apply assumption
           apply assumption
(* repeated *)
   apply (rule allI)
          apply (rule impI)+
   apply (frule f_ctor)
   apply hypsubst
   apply (subst (asm) T2_pre.set_map, (rule supp_id_bound bij_id)+)+
   apply (unfold image_id)?
   apply (erule imageE)
   apply hypsubst
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
   apply (rule suitable_FVarsD[THEN subsetD, rotated])
  apply assumption
       apply (unfold Un_assoc)
    apply (rule UnI2)
    apply (unfold Un_assoc[symmetric])?
    apply (tactic \<open>resolve_tac @{context} [BNF_Util.mk_UnIN 4 4] 1\<close>) (* normally: Use goal number here *)
    apply (rule DiffI[rotated], assumption)?
    apply (rule UN_I)
     apply assumption
    apply assumption
            apply (rule assms)
   apply (drule valid_pick_set11(2)[OF p(2)])
    apply assumption
          apply assumption
    (* END REPEAT_DETERM *)
    done
    
  show "valid_U1 d \<Longrightarrow> FVars_T1_2_raw (f1 pick1 pick2 d) \<subseteq> raw_UFVars12 d"
    "valid_U2 d2 \<Longrightarrow> FVars_T2_2_raw (f2 pick1 pick2 d2) \<subseteq> raw_UFVars22 d2"
     apply -
     apply (rule subsetI)
     apply (erule x[THEN conjunct1, THEN mp, THEN spec, THEN mp, THEN mp, rotated 1] x[THEN conjunct2, THEN mp, THEN spec, THEN mp, THEN mp, rotated 1])
      apply (rule refl)
     apply (unfold FVars_T1_2_raw_def mem_Collect_eq)
     apply assumption
  (* repeated *)
     apply (rule subsetI)
     apply (erule x[THEN conjunct1, THEN mp, THEN spec, THEN mp, THEN mp, rotated 1] x[THEN conjunct2, THEN mp, THEN spec, THEN mp, THEN mp, rotated 1])
      apply (rule refl)
     apply (unfold FVars_T2_2_raw_def mem_Collect_eq)
    apply assumption
    done
qed

lemmas f_FVarsD = f_FVarsD1 f_FVarsD2

thm T1.permute_raw_comp0s

lemma OO_permute:
  assumes "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a set|"
          "bij (v::'b\<Rightarrow>'b)" "|supp v| <o |UNIV::'b set|"
          "bij (u'::'a\<Rightarrow>'a)" "|supp u'| <o |UNIV::'a set|"
          "bij (v'::'b\<Rightarrow>'b)" "|supp v'| <o |UNIV::'b set|"
  shows
    "((\<lambda>t. alpha_T1 (permute_T1_raw u v t)) OO (\<lambda>t. alpha_T1 (permute_T1_raw u' v' t))) = (\<lambda>t. alpha_T1 (permute_T1_raw (u' \<circ> u) (v' \<circ> v) t))"
    "((\<lambda>t. alpha_T2 (permute_T2_raw u v t)) OO (\<lambda>t. alpha_T2 (permute_T2_raw u' v' t))) = (\<lambda>t. alpha_T2 (permute_T2_raw (u' \<circ> u) (v' \<circ> v) t))"
  (* REPEAT_DETERM *)
  apply (unfold T1.permute_raw_comp0s[OF assms, symmetric])
  apply (rule ext)
  apply (rule ext)
  apply (rule iffI)
  apply (subst (asm) relcompp.simps)
   apply (erule exE)+
   apply (erule conjE)+
   apply hypsubst
   apply (erule T1.alpha_trans[rotated])
   apply (subst comp_apply)
   apply (subst T1.alpha_bij_eq, (rule assms)+)
   apply assumption
  apply (subst (asm) comp_apply)
  apply (subst relcompp.simps)
  apply (rule exI)+
  apply (rule conjI[rotated])+
     prefer 2
     apply (rule T1.alpha_refl)
    apply assumption
    apply (rule refl)+
(* repeated *)
  apply (unfold T2.permute_raw_comp0s[OF assms, symmetric])
  apply (rule ext)
  apply (rule ext)
  apply (rule iffI)
  apply (subst (asm) relcompp.simps)
   apply (erule exE)+
   apply (erule conjE)+
   apply hypsubst
   apply (erule T2.alpha_trans[rotated])
   apply (subst comp_apply)
   apply (subst T2.alpha_bij_eq, (rule assms)+)
   apply assumption
  apply (subst (asm) comp_apply)
  apply (subst relcompp.simps)
  apply (rule exI)+
  apply (rule conjI[rotated])+
     prefer 2
     apply (rule T2.alpha_refl)
    apply assumption
   apply (rule refl)+
  done

lemma OO_comp1:
  assumes "\<And>d. valid_U1 d \<Longrightarrow> (g u' v' \<circ> g u v) d = g (u' \<circ> u) (v' \<circ> v) d"
  shows "valid_U1 x \<Longrightarrow> ((\<lambda>d. (=) (g u v d)) OO (\<lambda>d. (=) (g u' v' d))) x = (\<lambda>d. (=) (g (u' \<circ> u) (v' \<circ> v) d)) x"
  apply (subst (2) Grp_UNIV_def[symmetric])
  apply (subst (2) Grp_UNIV_def[symmetric])
  apply (subst Grp_o[symmetric])
  apply (unfold Grp_UNIV_def)
  apply (subst assms)
  apply assumption
  apply (rule refl)
  done

lemma OO_comp2:
  assumes "\<And>d. valid_U2 d \<Longrightarrow> (g u' v' \<circ> g u v) d = g (u' \<circ> u) (v' \<circ> v) d"
  shows "valid_U2 x \<Longrightarrow> ((\<lambda>d. (=) (g u v d)) OO (\<lambda>d. (=) (g u' v' d))) x = (\<lambda>d. (=) (g (u' \<circ> u) (v' \<circ> v) d)) x"
  apply (subst (2) Grp_UNIV_def[symmetric])
  apply (subst (2) Grp_UNIV_def[symmetric])
  apply (subst Grp_o[symmetric])
  apply (unfold Grp_UNIV_def)
  apply (subst assms)
  apply assumption
  apply (rule refl)
  done

lemmas OO_comp = OO_comp1 OO_comp2

lemma OO_raw_Umap:
  assumes "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a set|"
          "bij (v::'b\<Rightarrow>'b)" "|supp v| <o |UNIV::'b set|"
          "bij (u'::'a\<Rightarrow>'a)" "|supp u'| <o |UNIV::'a set|"
          "bij (v'::'b\<Rightarrow>'b)" "|supp v'| <o |UNIV::'b set|"
        shows
          "valid_U1 x \<Longrightarrow> ((\<lambda>d. (=) (raw_Umap1 u v d)) OO (\<lambda>d. (=) (raw_Umap1 u' v' d))) x  = (\<lambda>d. (=) (raw_Umap1 (u' \<circ> u) (v' \<circ> v) d)) x"
          "valid_U2 x' \<Longrightarrow> ((\<lambda>d. (=) (raw_Umap2 u v d)) OO (\<lambda>d. (=) (raw_Umap2 u' v' d))) x'  = (\<lambda>d. (=) (raw_Umap2 (u' \<circ> u) (v' \<circ> v) d)) x'"
 (* REPEAT_DETERM *)
   apply (rule OO_comp)
   apply (subst comp_apply)
    apply (rule Umap_comp1, (assumption | rule assms)+)
(* repeated *)
  apply (rule OO_comp)
   apply (subst comp_apply)
   apply (rule Umap_comp2, (assumption | rule assms)+)
(* END REPEAT_DETERM *)
  done

lemma OO_alpha_permute:
  assumes  "bij (g::'a \<Rightarrow> 'a)" "|supp g| <o |UNIV::'a set|"
           "bij (h::'b \<Rightarrow> 'b)" "|supp h| <o |UNIV::'b set|"
  shows
    "alpha_T1 OO (\<lambda>t. alpha_T1 (permute_T1_raw g h t)) = (\<lambda>t. alpha_T1 (permute_T1_raw g h t))"
    "alpha_T2 OO (\<lambda>t. alpha_T2 (permute_T2_raw g h t)) = (\<lambda>t. alpha_T2 (permute_T2_raw g h t))"
  (* REPEAT_DETERM *)
  apply (rule ext)
  apply (rule ext)
  apply (rule iffI)
  prefer 2
   apply (rule relcomppI)
    prefer 2
    apply assumption
   apply (rule T1.alpha_refl)
  apply (erule relcomppE)
  apply (subst (asm) T1.alpha_bij_eq[OF assms, symmetric])
  apply (erule T1.alpha_trans)
   apply assumption
(* repeated *)
  apply (rule ext)
  apply (rule ext)
  apply (rule iffI)
  prefer 2
   apply (rule relcomppI)
    prefer 2
    apply assumption
   apply (rule T2.alpha_refl)
  apply (erule relcomppE)
  apply (subst (asm) T2.alpha_bij_eq[OF assms, symmetric])
  apply (erule T2.alpha_trans)
  apply assumption
(* END REPEAT_DETERM *)
  done


lemma set9_setr_valid1:
  assumes "suitable1 pick"
and "valid_U1 d"
and "z \<in> set9_T1_pre (pick d)"
shows "x \<in> Basic_BNFs.setr z \<Longrightarrow> valid_U1 x"
  by (rule valid_pick_set9(1)[OF assms(1,3,2), THEN sum.pred_set[THEN fun_cong, THEN iffD1, THEN conjunct2], THEN bspec])

lemma set9_setr_valid2:
  assumes "suitable2 pick"
and "valid_U2 d"
and "z \<in> set9_T2_pre (pick d)"
shows "x \<in> Basic_BNFs.setr z \<Longrightarrow> valid_U1 x"
  by (rule valid_pick_set9(2)[OF assms(1,3,2), THEN sum.pred_set[THEN fun_cong, THEN iffD1, THEN conjunct2], THEN bspec])

lemmas set9_setr_valid = set9_setr_valid1 set9_setr_valid2

lemma set11_setr_valid1:
  assumes "suitable1 pick"
and "valid_U1 d"
and "z \<in> set11_T1_pre (pick d)"
shows "x \<in> Basic_BNFs.setr z \<Longrightarrow> valid_U2 x"
  by (rule valid_pick_set11(1)[OF assms(1,3,2), THEN sum.pred_set[THEN fun_cong, THEN iffD1, THEN conjunct2], THEN bspec])

lemma set11_setr_valid2:
  assumes "suitable2 pick"
and "valid_U2 d"
and "z \<in> set11_T2_pre (pick d)"
shows "x \<in> Basic_BNFs.setr z \<Longrightarrow> valid_U2 x"
  by (rule valid_pick_set11(2)[OF assms(1,3,2), THEN sum.pred_set[THEN fun_cong, THEN iffD1, THEN conjunct2], THEN bspec])

lemmas set11_setr_valid = set11_setr_valid1 set11_setr_valid2

lemma rel_F_suitable_mapD1:
  assumes valid_d: "valid_U1 d"
    and pp': "suitable1 pick1" "suitable1 pick1'"
    and u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a set|"
    and v: "bij (v::'b\<Rightarrow>'b)" "|supp v| <o |UNIV::'b set|"
  shows "\<exists> u' v'. bij u' \<and> |supp u'| <o |UNIV::'a set| \<and> id_on (raw_UFVarsBD11 (pick1 d)) u' \<and>
                  bij v' \<and> |supp v'| <o |UNIV::'b set| \<and> id_on (raw_UFVarsBD12 (pick1 d)) v' \<and>
 mr_rel_T1_pre u v id (=) (u o u') (v o v') (u o u')
   (rel_sum (\<lambda>t t'. alpha_T1 (permute_T1_raw u v t) t')
            (\<lambda>t t'. raw_Umap1 u v t = t'))
   (rel_sum (\<lambda>t t'. alpha_T1 (permute_T1_raw (u o u') (v o v') t) t')
            (\<lambda>d d'. raw_Umap1 (u o u') (v o v') d = d'))
   (rel_sum (\<lambda>t t'. alpha_T2 (permute_T2_raw u v t) t')
            (\<lambda>t t'. raw_Umap2 u v t = t'))
   (rel_sum (\<lambda>t t'. alpha_T2 (permute_T2_raw (u o u') v t) t')
            (\<lambda>d d'. raw_Umap2 (u o u') v d = d'))
 (pick1 d)
 (pick1' (raw_Umap1 u v d))"
  apply (rule raw_Umap_Utor(1)[OF u v valid_d, unfolded rel_set_def, THEN conjunct2, THEN bspec, THEN bexE])
   apply (rule allE)
    apply (rule pp'(2)[unfolded suitable1_def])
   apply (erule impE)
    prefer 2
    apply assumption
   apply (rule valid_Umap1, (rule u v valid_d)+)
  apply (rule exE)
   apply (rule DTOR_mapD(1)[OF assms(1)])
   apply (unfold insert_subset)
   apply (rule conjI)
    apply (rule assms(2)[unfolded suitable1_def, THEN spec, THEN mp, OF assms(1)])
   apply (rule conjI)
    apply assumption
   apply (rule empty_subsetI)

  apply (erule exE)

  apply (erule conjE)+
  apply(rule exI)+
  apply (rule conjI[rotated])+
  apply (rotate_tac -1)
        apply (drule T1_pre.mr_rel_OO[THEN fun_cong, THEN fun_cong, THEN iffD2, rotated -1, OF relcomppI])
                      apply assumption
                      apply (rule supp_id_bound bij_id assms | assumption)+
  apply (unfold id_o o_id eq_OO sum.rel_compp[symmetric])

        apply(erule T1_pre.mr_rel_mono_strong0[rotated -12])
                      apply ((rule ballI)+, rule refl imp_refl)+

                    (* REPEAT_DETERM *)
                      apply (rule ballI)+
                      apply (rule impI)
                      apply (erule sum.rel_cong[OF refl refl, THEN iffD1, rotated -1])
                      apply (subst OO_alpha_permute[OF u v])
                      apply (rule refl)
                      apply (rule iffI)
                      apply assumption+

                      apply (rule ballI)+
                      apply (rule impI)
                      apply (erule sum.rel_mono_strong)
                      apply (drule OO_permute[THEN fun_cong, THEN fun_cong, THEN iffD1, rotated -1])
                      apply (unfold o_id)?
                      apply (assumption | rule assms supp_id_bound bij_id)+
                      apply (drule OO_raw_Umap[THEN fun_cong, THEN iffD1, rotated -1])
                      apply (assumption | rule assms supp_id_bound bij_id)+
                      apply (erule set9_setr_valid(1)[OF pp'(1) valid_d])
                      apply assumption
                      apply (unfold o_id)?
                      apply assumption

                      apply (rule ballI)+
                      apply (rule impI)
                      apply (erule sum.rel_cong[OF refl refl, THEN iffD1, rotated -1])
                      apply (subst OO_alpha_permute[OF u v])
                      apply (rule refl)
                      apply (rule iffI)
                      apply assumption+

                      apply (rule ballI)+
                      apply (rule impI)
                      apply (erule sum.rel_mono_strong)
                      apply (drule OO_permute[THEN fun_cong, THEN fun_cong, THEN iffD1, rotated -1])
                      apply (unfold o_id)?
                      apply (assumption | rule assms supp_id_bound bij_id)+
                      apply (drule OO_raw_Umap[THEN fun_cong, THEN iffD1, rotated -1])
                      apply (assumption | rule assms supp_id_bound bij_id)+
                      apply (erule set11_setr_valid(1)[OF pp'(1) valid_d])
                      apply assumption
                      apply (unfold o_id)?
                      apply assumption
                    (* END REPEAT_DETERM *)
                      apply (rule u v supp_id_bound)+
                    apply (rule bij_comp supp_comp_bound u v supp_id_bound | assumption)+
  done

lemma rel_F_suitable_mapD2:
  assumes valid_d: "valid_U2 d"
    and pp': "suitable2 pick1" "suitable2 pick1'"
    and u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a set|"
    and v: "bij (v::'b\<Rightarrow>'b)" "|supp v| <o |UNIV::'b set|"
  shows "\<exists> u' v'. bij u' \<and> |supp u'| <o |UNIV::'a set| \<and> id_on (raw_UFVarsBD21 (pick1 d)) u' \<and>
                  bij v' \<and> |supp v'| <o |UNIV::'b set| \<and> id_on (raw_UFVarsBD22 (pick1 d)) v' \<and>
 mr_rel_T2_pre u v id (=) (u o u') (v o v') (u o u')
   (rel_sum (\<lambda>t t'. alpha_T1 (permute_T1_raw u v t) t')
            (\<lambda>t t'. raw_Umap1 u v t = t'))
   (rel_sum (\<lambda>t t'. alpha_T1 (permute_T1_raw (u o u') (v o v') t) t')
            (\<lambda>d d'. raw_Umap1 (u o u') (v o v') d = d'))
   (rel_sum (\<lambda>t t'. alpha_T2 (permute_T2_raw u v t) t')
            (\<lambda>t t'. raw_Umap2 u v t = t'))
   (rel_sum (\<lambda>t t'. alpha_T2 (permute_T2_raw (u o u') v t) t')
            (\<lambda>d d'. raw_Umap2 (u o u') v d = d'))
 (pick1 d)
 (pick1' (raw_Umap2 u v d))"
  apply (rule raw_Umap_Utor(2)[OF u v valid_d, unfolded rel_set_def, THEN conjunct2, THEN bspec, THEN bexE])
   apply (rule allE)
    apply (rule pp'(2)[unfolded suitable2_def])
   apply (erule impE)
    prefer 2
    apply assumption
   apply (rule valid_Umap2, (rule u v valid_d)+)
  apply (rule exE)
   apply (rule DTOR_mapD(2)[OF assms(1)])
   apply (unfold insert_subset)
   apply (rule conjI)
    apply (rule assms(2)[unfolded suitable2_def, THEN spec, THEN mp, OF assms(1)])
   apply (rule conjI)
    apply assumption
   apply (rule empty_subsetI)

  apply (erule exE)

  apply (erule conjE)+
  apply(rule exI)+
  apply (rule conjI[rotated])+
  apply (rotate_tac -1)
        apply (drule T2_pre.mr_rel_OO[THEN fun_cong, THEN fun_cong, THEN iffD2, rotated -1, OF relcomppI])
                      apply assumption
                      apply (rule supp_id_bound bij_id assms | assumption)+
  apply (unfold id_o o_id eq_OO sum.rel_compp[symmetric])

        apply(erule T2_pre.mr_rel_mono_strong0[rotated -12])
                      apply ((rule ballI)+, rule refl imp_refl)+

                    (* REPEAT_DETERM *)
                      apply (rule ballI)+
                      apply (rule impI)
                      apply (erule sum.rel_cong[OF refl refl, THEN iffD1, rotated -1])
                      apply (subst OO_alpha_permute[OF u v])
                      apply (rule refl)
                      apply (rule iffI)
                      apply assumption+

                      apply (rule ballI)+
                      apply (rule impI)
                      apply (erule sum.rel_mono_strong)
                      apply (drule OO_permute[THEN fun_cong, THEN fun_cong, THEN iffD1, rotated -1])
                      apply (unfold o_id)?
                      apply (assumption | rule assms supp_id_bound bij_id)+
                      apply (drule OO_raw_Umap[THEN fun_cong, THEN iffD1, rotated -1])
                      apply (assumption | rule assms supp_id_bound bij_id)+
                      apply (erule set9_setr_valid(2)[OF pp'(1) valid_d])
                      apply assumption
                      apply (unfold o_id)?
                      apply assumption

                      apply (rule ballI)+
                      apply (rule impI)
                      apply (erule sum.rel_cong[OF refl refl, THEN iffD1, rotated -1])
                      apply (subst OO_alpha_permute[OF u v])
                      apply (rule refl)
                      apply (rule iffI)
                      apply assumption+

                      apply (rule ballI)+
                      apply (rule impI)
                      apply (erule sum.rel_mono_strong)
                      apply (drule OO_permute[THEN fun_cong, THEN fun_cong, THEN iffD1, rotated -1])
                      apply (unfold o_id)?
                      apply (assumption | rule assms supp_id_bound bij_id)+
                      apply (drule OO_raw_Umap[THEN fun_cong, THEN iffD1, rotated -1])
                      apply (assumption | rule assms supp_id_bound bij_id)+
                      apply (erule set11_setr_valid(2)[OF pp'(1) valid_d])
                      apply assumption
                      apply (unfold o_id)?
                      apply assumption
                    (* END REPEAT_DETERM *)
                      apply (rule u v supp_id_bound)+
                    apply (rule bij_comp supp_comp_bound u v supp_id_bound | assumption)+
  done

lemmas rel_F_suitable_mapD = rel_F_suitable_mapD1 rel_F_suitable_mapD2

abbreviation (input) "FVarsB11 X \<equiv> set7_T1_pre X - set5_T1_pre X \<union> (\<Union> (FVars_T1_1_raw ` set9_T1_pre X) - set5_T1_pre X) \<union> (\<Union> (FVars_T2_1_raw ` set11_T1_pre X) - set5_T1_pre X)"
abbreviation (input) "FVarsB12 X \<equiv> \<Union> (FVars_T1_2_raw ` set9_T1_pre X) - set6_T1_pre X"
abbreviation (input) "FVarsB21 X \<equiv> set7_T2_pre X - set5_T2_pre X \<union> (\<Union> (FVars_T1_1_raw ` set9_T2_pre X) - set5_T2_pre X) \<union> (\<Union> (FVars_T2_1_raw ` set11_T2_pre X) - set5_T2_pre X)"
abbreviation (input) "FVarsB22 X \<equiv> \<Union> (FVars_T1_2_raw ` set9_T2_pre X) - set6_T2_pre X"


(*thm alpha_T1_alpha_T2.coinduct
lemma alpha_coinduct2[consumes 1, case_names C]:
  assumes 
    "\<And>x (x' :: ('a, 'b, 'c, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) raw_T1, ('a, 'b, 'c, 'd) raw_T1, ('a, 'b, 'c, 'd) raw_T2, ('a, 'b, 'c, 'd) raw_T2) T1_pre).
    \<phi> (raw_T1_ctor x) (raw_T1_ctor x') \<Longrightarrow>
    (\<exists>f g. bij f \<and> |supp f| <o |UNIV::'a set| \<and>
    bij g \<and> |supp g| <o |UNIV::'b set| \<and>
    id_on (FVarsB11 x) f \<and> id_on (FVarsB12 x) g \<and>
    mr_rel_T1_pre id id id (=) f g f
       (\<lambda> t t'. \<phi> t t' \<or> alpha_T1 t t')
       (\<lambda> t t'. \<phi> (permute_T1_raw f g t) t' \<or> alpha_T1 (permute_T1_raw f g t) t')
       (\<lambda> t t'. \<phi>' t t' \<or> alpha_T2 t t')
       (\<lambda> t t'. \<phi>' (permute_T2_raw f id t) t' \<or> alpha_T2 (permute_T2_raw f id t) t')
       x x')"
    "\<And>x (x' :: ('a, 'b, 'c, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) raw_T1, ('a, 'b, 'c, 'd) raw_T1, ('a, 'b, 'c, 'd) raw_T2, ('a, 'b, 'c, 'd) raw_T2) T2_pre).
    \<phi>' (raw_T2_ctor x) (raw_T2_ctor x') \<Longrightarrow>
    (\<exists>f g. bij f \<and> |supp f| <o |UNIV::'a set| \<and>
    bij g \<and> |supp g| <o |UNIV::'b set| \<and>
    id_on (FVarsB21 x) f \<and> id_on (FVarsB22 x) g \<and>
    mr_rel_T2_pre id id id (=) f g f
       (\<lambda> t t'. \<phi> t t' \<or> alpha_T1 t t')
       (\<lambda> t t'. \<phi> (permute_T1_raw f g t) t' \<or> alpha_T1 (permute_T1_raw f g t) t')
       (\<lambda> t t'. \<phi>' t t' \<or> alpha_T2 t t')
       (\<lambda> t t'. \<phi>' (permute_T2_raw f id t) t' \<or> alpha_T2 (permute_T2_raw f id t) t')
       x x')"
  shows "(\<forall>t1 t1'. \<phi> t1 t1' \<longrightarrow> alpha_T1 t1 t1') \<and> (\<forall>t2 t2'. \<phi>' t2 t2' \<longrightarrow> alpha_T2 t2 t2')"
  apply(rule alpha_T1_alpha_T2.coinduct)
(* REPEAT_DETERM *)
  subgoal for x1 x2
    apply (rule raw_T1.exhaust[of x1])
    apply (rule raw_T1.exhaust[of x2])
    apply hypsubst_thin
    apply (drule assms)
    apply (erule exE)+
    apply (rule exI)+
    apply (rule conjI, rule refl)+
    apply assumption
    done
(* repeated *)
  subgoal for x1 x2
    apply (rule raw_T2.exhaust[of x1])
    apply (rule raw_T2.exhaust[of x2])
    apply hypsubst_thin
    apply (drule assms)
    apply (erule exE)+
    apply (rule exI)+
    apply (rule conjI, rule refl)+
    apply assumption
    done
(* END REPEAT_DETERM *)
  done*)

(* The "monster lemma": swapping and "pick"-irrelevance covered in one shot: *)

(* TODO: can we obtain this from ML automation? *)
lemma permute_T1_raw_simps:
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a set|"
    and v: "bij (v::'b\<Rightarrow>'b)" "|supp v| <o |UNIV::'b set|"
  shows  "permute_T1_raw u v (raw_T1_ctor x) =
         raw_T1_ctor (map_T1_pre u v id id u v u (permute_T1_raw u v) (permute_T1_raw u v) (permute_T2_raw u v) (permute_T2_raw u v) x)"
  apply (rule raw_T1.expand)
  apply (rule trans)
   apply (rule permute_T1_raw.simps)
  apply (unfold raw_T1.sel)
  apply (subst T1_pre.map_comp, (rule assms supp_id_bound bij_id)+)
  apply (unfold o_id id_o)
  apply (rule refl)
  done

lemma f_swap_alpha_xL:
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a set|"
    and v: "bij (v::'b\<Rightarrow>'b)" "|supp v| <o |UNIV::'b set|"
    and x: "raw_T1_ctor x = permute_T1_raw u v (f1 pick1 pick2 d)"
  shows "x =  map_T1_pre u v id id u v u (permute_T1_raw u v \<circ> case_sum id (f1 pick1 pick2)) (permute_T1_raw u v \<circ> case_sum id (f1 pick1 pick2)) (permute_T2_raw u v \<circ> case_sum id (f2 pick1 pick2)) (permute_T2_raw u v \<circ> case_sum id (f2 pick1 pick2)) (pick1 d)"
  apply (insert x)
  apply (subst (asm) f_simps[of pick1 pick2])
  thm permute_T1_raw_simps[OF u v]
  apply (subst (asm) permute_T1_raw_simps[OF u v])
  apply (subst (asm) raw_T1.inject)
  apply hypsubst_thin
  apply (subst T1_pre.map_comp, (rule supp_id_bound bij_id u v)+)
  apply (unfold o_id)
  apply (rule refl)
  done

term alpha_T1

lemma l_is_inr1:
  assumes
    r: "rel_sum (\<lambda>t. alpha_T1 (permute_T1_raw u v t)) (\<lambda>d d'. raw_Umap1 u v d = d') ttdL ttdR"
    and na: "\<not> alpha_T1 (permute_T1_raw u v (case_sum id (f1 pick1 pick2) ttdL)) (case_sum id (f1 pick1' pick2') ttdR)"
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

lemma l_is_inr2:
  assumes
    r: "rel_sum (\<lambda>t. alpha_T2 (permute_T2_raw u v t)) (\<lambda>d d'. raw_Umap2 u v d = d') ttdL ttdR"
    and na: "\<not> alpha_T2 (permute_T2_raw u v (case_sum id (f2 pick1 pick2) ttdL)) (case_sum id (f2 pick1' pick2') ttdR)"
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

lemmas l_is_inr = l_is_inr1 l_is_inr2

lemma r_is_Umap1:
  assumes
    r: "rel_sum (\<lambda>t. alpha_T1 (permute_T1_raw u v t)) (\<lambda>d d'. raw_Umap1 u v d = d') ttdL ttdR"
    and ttdL: "ttdL = Inr x"
  shows "ttdR = Inr (raw_Umap1 u v x)"
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

lemma r_is_Umap2:
  assumes
    r: "rel_sum (\<lambda>t. alpha_T2 (permute_T2_raw u v t)) (\<lambda>d d'. raw_Umap2 u v d = d') ttdL ttdR"
    and ttdL: "ttdL = Inr x"
  shows "ttdR = Inr (raw_Umap2 u v x)"
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

lemmas r_is_Umap = r_is_Umap1 r_is_Umap2

lemma conj_spec: "(\<forall>x. P x) \<and> (\<forall>y. Q y) \<Longrightarrow> P x \<and> Q y"
  by simp
lemma conj_mp: "(P1 \<longrightarrow> Q1) \<and> (P2 \<longrightarrow> Q2) \<Longrightarrow> P1 \<Longrightarrow> P2 \<Longrightarrow> Q1 \<and> Q2"
  by simp
lemma comp_inv_aux: "bij u \<Longrightarrow> u \<circ> u' = u \<circ> u' \<circ> inv u \<circ> u"
  by auto

lemma id_on_f_inv_f: "bij f \<Longrightarrow> id_on (inv f ` A) g \<Longrightarrow> id_on A (f \<circ> g \<circ> inv f)"
  unfolding id_on_def by simp

thm T1.permute_raw_comp0s

lemma T1_permute_raw_comps:
  "bij (h1::'a\<Rightarrow>'a) \<Longrightarrow>|supp h1| <o |UNIV::'a set|\<Longrightarrow>
  bij (h2::'b\<Rightarrow>'b) \<Longrightarrow> |supp h2| <o |UNIV::'b set| \<Longrightarrow>
   bij (g1::'a\<Rightarrow>'a) \<Longrightarrow>|supp g1| <o |UNIV::'a set| \<Longrightarrow>
  bij (g2::'b\<Rightarrow>'b) \<Longrightarrow> |supp g2| <o |UNIV::'b set| \<Longrightarrow>
  permute_T1_raw g1 g2 (permute_T1_raw h1 h2 x) =
  permute_T1_raw (g1 \<circ> h1) (g2 \<circ> h2) x"
  oops

lemma f_swap_alpha:
  assumes p: "suitable1 pick1" "suitable2 pick2" and p': "suitable1 pick1'" "suitable2 pick2'"
    and valid_d: "valid_U1 d" "valid_U2 d2"
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a set|"
    and  v: "bij (v::'b\<Rightarrow>'b)" "|supp v| <o |UNIV::'b set|"
  shows "alpha_T1 (permute_T1_raw u v (f1 pick1 pick2 d)) (f1 pick1' pick2' (raw_Umap1 u v d))
    \<and> alpha_T2 (permute_T2_raw u v (f2 pick1 pick2 d2)) (f2 pick1' pick2' (raw_Umap2 u v d2))
  "
  
  thm alpha_T1_alpha_T2.coinduct[of
    "\<lambda> tL tR. \<exists> u v d. valid_U1 d \<and> bij u \<and> |supp u| <o |UNIV::'a set| \<and>
     bij v \<and> |supp v| <o |UNIV::'b set| \<and>
     tL = permute_T1_raw u v (f1 pick1 pick2 d) \<and>
     tR = f1 pick1' pick2' (raw_Umap1 u v d)"

    "\<lambda> tL tR. \<exists> u v d. valid_U2 d \<and> bij u \<and> |supp u| <o |UNIV::'a set| \<and>
     bij v \<and> |supp v| <o |UNIV::'b set| \<and>
     tL = permute_T2_raw u v (f2 pick1 pick2 d) \<and>
     tR = f2 pick1' pick2' (raw_Umap2 u v d)", THEN conj_spec, THEN conj_spec, THEN conj_mp
]
  apply (rule alpha_T1_alpha_T2.coinduct[of
    "\<lambda> tL tR. \<exists> u v d. valid_U1 d \<and> bij u \<and> |supp u| <o |UNIV::'a set| \<and>
     bij v \<and> |supp v| <o |UNIV::'b set| \<and>
     tL = permute_T1_raw u v (f1 pick1 pick2 d) \<and>
     tR = f1 pick1' pick2' (raw_Umap1 u v d)"

    "\<lambda> tL tR. \<exists> u v d. valid_U2 d \<and> bij u \<and> |supp u| <o |UNIV::'a set| \<and>
     bij v \<and> |supp v| <o |UNIV::'b set| \<and>
     tL = permute_T2_raw u v (f2 pick1 pick2 d) \<and>
     tR = f2 pick1' pick2' (raw_Umap2 u v d)", THEN conj_spec, THEN conj_spec, THEN conj_mp
])

  subgoal for x1 x2
    apply (erule exE conjE)+

    apply (rule raw_T1.exhaust[of x1])
    apply (drule trans[OF sym])
     apply assumption
    apply (rule raw_T1.exhaust[of x2])
    apply (drule trans[OF sym])
     apply assumption
    apply hypsubst_thin


  (* this is new *)
    apply (unfold0 f1_simps)
    apply (subst (asm) T1.permute_raw_ctor)
    apply assumption+
    apply (drule iffD1[OF raw_T1.inject])+
    apply (subst (asm) T1_pre.map_comp)
             apply (rule supp_id_bound bij_id | assumption)+
    apply (unfold id_o o_id)
    apply hypsubst

    thm rel_F_suitable_mapD(1)[OF _ p(1) p'(1)]
    apply (frule rel_F_suitable_mapD(1)[OF _ p(1) p'(1)])
      apply assumption+
    apply (erule exE conjE)+
    apply (rule exI)+
    apply (rule conjI, rule refl)+
    apply (rule conjI[rotated])+

  (* new, move map into relator args *)
          apply (rule T1_pre.mr_rel_map(1)[THEN iffD2, rotated -1])
                        apply (unfold id_o o_id Grp_UNIV_id eq_OO)
          apply (rule T1_pre.mr_rel_map(3)[THEN iffD2, rotated -1])
                        apply (unfold inv_id id_o o_id Grp_UNIV_id eq_OO conversep_eq)
                        apply (erule T1_pre.mr_rel_mono_strong0[rotated -12]) (* use monotonicity to fix all variables *)
                        apply ((rule ballI)+, rule refl imp_refl)+
                        apply (rule ballI, rule comp_inv_aux[THEN fun_cong], assumption)+
                      (* at this point there are no more schematic variables *)
                        defer defer defer defer (* nrec times *)
                        apply (assumption | rule supp_id_bound bij_id bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound)+ (* minimize proof state *)

             apply (rule id_on_f_inv_f)
              apply assumption
             apply (subst T1_pre.set_map, (assumption | rule supp_id_bound bij_id)+)+
             apply (erule id_on_antimono)
             apply (unfold0 image_comp[unfolded comp_def] comp_apply)[1]
    apply (subst T1.FVars_raw_permute, (assumption | rule supp_id_bound bij_id)+)
             apply (unfold image_set_diff[OF bij_is_inj[OF bij_imp_bij_inv]] image_comp inv_o_simp1 image_id image_UN[symmetric])[1]
    apply (rule Diff_mono[OF _ subset_refl])
             apply (rule subsetI)
             apply (((rule UnI2)?, erule UN_mono[THEN subsetD, OF subset_refl, rotated -1]) | rule UnI1)+
     subgoal for u v d _ xa u' v' xb x
      apply (rule sumE[of x])
       apply hypsubst_thin
       apply (unfold0 sum.simps id_apply)
       apply (rule subset_refl)
      apply hypsubst_thin
      apply (unfold sum.simps)
      apply (rule f_FVarsD[OF p]) thm valid_pick_set9
      apply (drule valid_pick_set9[rotated])
         apply assumption
       apply (rule p)
      apply (unfold pred_sum_inject)
      apply assumption
       done

             apply (rule id_on_f_inv_f)
              apply assumption
             apply (subst T1_pre.set_map, (assumption | rule supp_id_bound bij_id)+)+
             apply (erule id_on_antimono)
             apply (unfold0 image_comp[unfolded comp_def] comp_apply image_Un)[1]
    apply (subst T1.FVars_raw_permute T2.FVars_raw_permute, (assumption | rule supp_id_bound bij_id)+)+
             apply (unfold image_set_diff[OF bij_is_inj[OF bij_imp_bij_inv]] image_comp inv_o_simp1 image_id image_UN[symmetric] Un_Diff[symmetric])[1]
             apply (rule Diff_mono[OF _ subset_refl])
             apply (rule subsetI)
             apply (erule UnE)+
        (* REPEAT_DETERM *)
               apply (((rule UnI2)?, erule UN_mono[THEN subsetD, OF subset_refl, rotated -1]) | rule UnI1)+
     apply assumption
    (* orelse *)
               apply (((rule UnI2)?, erule UN_mono[THEN subsetD, OF subset_refl, rotated -1]) | rule UnI1)+
     subgoal for u v d _ xa u' v' xb x
      apply (rule sumE[of x])
       apply hypsubst_thin
       apply (unfold0 sum.simps id_apply)
       apply (rule subset_refl)
      apply hypsubst_thin
      apply (unfold sum.simps)
       apply (rule f_FVarsD[OF p])
      apply (drule valid_pick_set9[rotated])
         apply assumption
       apply (rule p)
      apply (unfold pred_sum_inject)
      apply assumption
       done
(* repeated *)
             apply (((rule UnI2)?, erule UN_mono[THEN subsetD, OF subset_refl, rotated -1]) | rule UnI1)+
     subgoal for u v d _ xa u' v' xb x
       apply (rule sumE[of x])
        apply hypsubst_thin
        apply (unfold0 sum.simps id_apply)
        apply (rule subset_refl)
       apply hypsubst_thin
       apply (unfold sum.simps)
       apply (rule f_FVarsD[OF p])
       apply (drule valid_pick_set11[rotated])
         apply assumption
        apply (rule p)
       apply (unfold pred_sum_inject)
       apply assumption
       done

            apply (rule supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv infinite_UNIV | assumption)+
(* REPEAT_DETERM *)
        apply (rule ballI impI)+
        apply (unfold relcompp_conversep_Grp)[1]
        apply (unfold Grp_OO)[1]
        apply (rule disjCI)
     thm l_is_inr[of _ _ _ _ pick1 pick2 pick1' pick2']
        apply (frule l_is_inr[of _ _ _ _ pick1 pick2 pick1' pick2'])
         apply (unfold comp_apply)[1]
         apply assumption
        apply (erule exE)
        apply hypsubst
        apply (rule exI)+
        apply (rule conjI)
         apply (drule valid_pick_set8[rotated])
           apply assumption
          apply (rule p)
         apply (unfold pred_sum_inject)
         apply (rotate_tac -1)
         apply assumption
        apply (rule conjI | assumption)+
         apply (rule trans[OF comp_apply])
         apply (rule arg_cong[of "case_sum _ _ _"])
         apply (unfold f_simps[symmetric])?
         apply (unfold sum.case)
         apply (rule refl)
        apply (drule r_is_Umap)
         apply (rule refl)
        apply hypsubst
        apply (unfold sum.case)
        apply (rule refl)
(* repeated *)
        apply (rule ballI impI)+
        apply (unfold relcompp_conversep_Grp)[1]
       apply (unfold Grp_OO)[1]
       apply (rule disjCI)
       apply (frule l_is_inr[of _ _ _ _ pick1 pick2 pick1' pick2'])
        apply (erule contrapos_nn)
        apply (erule arg_cong2[OF _ refl, of _ _ alpha_T1, THEN iffD1, rotated])
        apply (subst comp_apply)
        apply (subst T1.permute_raw_comps)
                apply (rule supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv bij_id supp_id_bound | assumption)+
        apply (unfold o_inv_o_cancel[OF bij_is_inj])[1]
        apply (unfold0 o_id id_o)?
        apply (rule refl)
apply (erule exE)
       apply hypsubst
     apply (subst comp_apply)
              apply (subst sum.case)+
              apply (rule exI)+
              apply (drule r_is_Umap)
               apply (rule refl)
              apply hypsubst
              apply (unfold sum.case)
              apply (rule conjI[rotated])+
             apply (rule refl)+
            apply (subst T1.permute_raw_comps)
                    apply (rule supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv bij_id supp_id_bound | assumption)+
            apply (unfold o_inv_o_cancel[OF bij_is_inj])[1]
            apply (unfold0 o_id id_o)?
            apply (rule refl)
           apply (rule supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv | assumption)+
         apply (drule valid_pick_set9[rotated])
           apply assumption
          apply (rule p)
         apply (unfold pred_sum_inject)
         apply (rotate_tac -1)
       apply assumption
(* repeated *)
        apply (rule ballI impI)+
        apply (unfold relcompp_conversep_Grp)[1]
        apply (unfold Grp_OO)[1]
        apply (rule disjCI)
     thm l_is_inr[of _ _ _ _ pick1 pick2 pick1' pick2']
        apply (frule l_is_inr[of _ _ _ _ pick1 pick2 pick1' pick2'])
         apply (unfold comp_apply)[1]
         apply assumption
        apply (erule exE)
        apply hypsubst
        apply (rule exI)+
        apply (rule conjI)
         apply (drule valid_pick_set10[rotated])
           apply assumption
          apply (rule p)
         apply (unfold pred_sum_inject)
         apply (rotate_tac -1)
         apply assumption
        apply (rule conjI | assumption)+
         apply (rule trans[OF comp_apply])
         apply (rule arg_cong[of "case_sum _ _ _"])
         apply (unfold f_simps[symmetric])?
         apply (unfold sum.case)
         apply (rule refl)
        apply (drule r_is_Umap)
         apply (rule refl)
        apply hypsubst
        apply (unfold sum.case)
        apply (rule refl)
(* repeated *)
        apply (rule ballI impI)+
        apply (unfold relcompp_conversep_Grp)[1]
       apply (unfold Grp_OO)[1]
      apply (rule disjCI)
       apply (frule l_is_inr[of _ _ _ _ pick1 pick2 pick1' pick2'])
        apply (erule contrapos_nn)
        apply (erule arg_cong2[OF _ refl, of _ _ alpha_T2, THEN iffD1, rotated])
        apply (subst comp_apply)
        apply (subst T2.permute_raw_comps)
                apply (rule supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv bij_id supp_id_bound | assumption)+
      apply (unfold o_inv_o_cancel[OF bij_is_inj])[1]
     apply (unfold0 o_id id_o)?
        apply (rule refl)
apply (erule exE)
       apply hypsubst
     apply (subst comp_apply)
              apply (subst sum.case)+
              apply (rule exI)+
              apply (drule r_is_Umap)
               apply (rule refl)
              apply hypsubst
              apply (unfold sum.case)
              apply (rule conjI[rotated])+
             apply (rule refl)+
            apply (subst T2.permute_raw_comps)
                    apply (rule supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv bij_id supp_id_bound | assumption)+
          apply (unfold o_inv_o_cancel[OF bij_is_inj])[1]
    apply (unfold0 o_id id_o)?
            apply (rule refl)
           apply (rule supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv | assumption)+
         apply (drule valid_pick_set11[rotated])
           apply assumption
          apply (rule p)
         apply (unfold pred_sum_inject)
         apply (rotate_tac -1)
     apply assumption
(* END REPEAT_DETERM *)
     done

  subgoal for x1 x2
    apply (erule exE conjE)+

    apply (rule raw_T2.exhaust[of x1])
    apply (drule trans[OF sym])
     apply assumption
    apply (rule raw_T2.exhaust[of x2])
    apply (drule trans[OF sym])
     apply assumption
    apply hypsubst_thin


  (* this is new *)
    apply (unfold0 f_simps)
    apply (subst (asm) T2.permute_raw_ctor)
    apply assumption+
    apply (drule iffD1[OF raw_T2.inject])+
    apply (subst (asm) T2_pre.map_comp)
             apply (rule supp_id_bound bij_id | assumption)+
    apply (unfold id_o o_id)
    apply hypsubst

    thm rel_F_suitable_mapD(2)[OF _ p(2) p'(2)]
    apply (frule rel_F_suitable_mapD(2)[OF _ p(2) p'(2)])
      apply assumption+
    apply (erule exE conjE)+
    apply (rule exI)+
    apply (rule conjI, rule refl)+
    apply (rule conjI[rotated])+

  (* new, move map into relator args *)
          apply (rule T2_pre.mr_rel_map(1)[THEN iffD2, rotated -1])
                        apply (unfold id_o o_id Grp_UNIV_id eq_OO)
          apply (rule T2_pre.mr_rel_map(3)[THEN iffD2, rotated -1])
                        apply (unfold inv_id id_o o_id Grp_UNIV_id eq_OO conversep_eq)
                        apply (erule T2_pre.mr_rel_mono_strong0[rotated -12]) (* use monotonicity to fix all variables *)
                        apply ((rule ballI)+, rule refl imp_refl)+
                        apply (rule ballI, rule comp_inv_aux[THEN fun_cong], assumption)+
                      (* at this point there are no more schematic variables *)
                        defer defer defer defer (* nrec times *)
                        apply (assumption | rule supp_id_bound bij_id bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound)+ (* minimize proof state *)

             apply (rule id_on_f_inv_f)
              apply assumption
             apply (subst T2_pre.set_map, (assumption | rule supp_id_bound bij_id)+)+
             apply (erule id_on_antimono)
             apply (unfold0 image_comp[unfolded comp_def] comp_apply)[1]
    apply (subst T1.FVars_raw_permute, (assumption | rule supp_id_bound bij_id)+)
             apply (unfold image_set_diff[OF bij_is_inj[OF bij_imp_bij_inv]] image_comp inv_o_simp1 image_id image_UN[symmetric])[1]
    apply (rule Diff_mono[OF _ subset_refl])
             apply (rule subsetI)
             apply (((rule UnI2)?, erule UN_mono[THEN subsetD, OF subset_refl, rotated -1]) | rule UnI1)+
     subgoal for u v d _ xa u' v' xb x
      apply (rule sumE[of x])
       apply hypsubst_thin
       apply (unfold0 sum.simps id_apply)
       apply (rule subset_refl)
      apply hypsubst_thin
      apply (unfold sum.simps)
      apply (rule f_FVarsD[OF p]) thm valid_pick_set9
      apply (drule valid_pick_set9[rotated])
         apply assumption
       apply (rule p)
      apply (unfold pred_sum_inject)
      apply assumption
       done

             apply (rule id_on_f_inv_f)
              apply assumption
             apply (subst T2_pre.set_map, (assumption | rule supp_id_bound bij_id)+)+
             apply (erule id_on_antimono)
             apply (unfold0 image_comp[unfolded comp_def] comp_apply image_Un)[1]
    apply (subst T1.FVars_raw_permute T2.FVars_raw_permute, (assumption | rule supp_id_bound bij_id)+)+
             apply (unfold image_set_diff[OF bij_is_inj[OF bij_imp_bij_inv]] image_comp inv_o_simp1 image_id image_UN[symmetric] Un_Diff[symmetric])[1]
             apply (rule Diff_mono[OF _ subset_refl])
             apply (rule subsetI)
             apply (erule UnE)+
        (* REPEAT_DETERM *)
               apply (((rule UnI2)?, erule UN_mono[THEN subsetD, OF subset_refl, rotated -1]) | rule UnI1)+
     apply assumption
    (* orelse *)
               apply (((rule UnI2)?, erule UN_mono[THEN subsetD, OF subset_refl, rotated -1]) | rule UnI1)+
     subgoal for u v d _ xa u' v' xb x
      apply (rule sumE[of x])
       apply hypsubst_thin
       apply (unfold0 sum.simps id_apply)
       apply (rule subset_refl)
      apply hypsubst_thin
      apply (unfold sum.simps)
       apply (rule f_FVarsD[OF p])
      apply (drule valid_pick_set9[rotated])
         apply assumption
       apply (rule p)
      apply (unfold pred_sum_inject)
      apply assumption
       done
(* repeated *)
             apply (((rule UnI2)?, erule UN_mono[THEN subsetD, OF subset_refl, rotated -1]) | rule UnI1)+
     subgoal for u v d _ xa u' v' xb x
       apply (rule sumE[of x])
        apply hypsubst_thin
        apply (unfold0 sum.simps id_apply)
        apply (rule subset_refl)
       apply hypsubst_thin
       apply (unfold sum.simps)
       apply (rule f_FVarsD[OF p])
       apply (drule valid_pick_set11[rotated])
         apply assumption
        apply (rule p)
       apply (unfold pred_sum_inject)
       apply assumption
       done

            apply (rule supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv infinite_UNIV | assumption)+
(* REPEAT_DETERM *)
        apply (rule ballI impI)+
        apply (unfold relcompp_conversep_Grp)[1]
        apply (unfold Grp_OO)[1]
        apply (rule disjCI)
     thm l_is_inr[of _ _ _ _ pick1 pick2 pick1' pick2']
        apply (frule l_is_inr[of _ _ _ _ pick1 pick2 pick1' pick2'])
         apply (unfold comp_apply)[1]
         apply assumption
        apply (erule exE)
        apply hypsubst
        apply (rule exI)+
        apply (rule conjI)
         apply (drule valid_pick_set8[rotated])
           apply assumption
          apply (rule p)
         apply (unfold pred_sum_inject)
         apply (rotate_tac -1)
         apply assumption
        apply (rule conjI | assumption)+
         apply (rule trans[OF comp_apply])
         apply (rule arg_cong[of "case_sum _ _ _"])
         apply (unfold f_simps[symmetric])?
         apply (unfold sum.case)
         apply (rule refl)
        apply (drule r_is_Umap)
         apply (rule refl)
        apply hypsubst
        apply (unfold sum.case)
        apply (rule refl)
(* repeated *)
        apply (rule ballI impI)+
        apply (unfold relcompp_conversep_Grp)[1]
       apply (unfold Grp_OO)[1]
       apply (rule disjCI)
       apply (frule l_is_inr[of _ _ _ _ pick1 pick2 pick1' pick2'])
        apply (erule contrapos_nn)
        apply (erule arg_cong2[OF _ refl, of _ _ alpha_T1, THEN iffD1, rotated])
        apply (subst comp_apply)
        apply (subst T1.permute_raw_comps)
                apply (rule supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv bij_id supp_id_bound | assumption)+
        apply (unfold o_inv_o_cancel[OF bij_is_inj])[1]
        apply (unfold0 o_id id_o)?
        apply (rule refl)
apply (erule exE)
       apply hypsubst
     apply (subst comp_apply)
              apply (subst sum.case)+
              apply (rule exI)+
              apply (drule r_is_Umap)
               apply (rule refl)
              apply hypsubst
              apply (unfold sum.case)
              apply (rule conjI[rotated])+
             apply (rule refl)+
            apply (subst T1.permute_raw_comps)
                    apply (rule supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv bij_id supp_id_bound | assumption)+
            apply (unfold o_inv_o_cancel[OF bij_is_inj])[1]
            apply (unfold0 o_id id_o)?
            apply (rule refl)
           apply (rule supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv | assumption)+
         apply (drule valid_pick_set9[rotated])
           apply assumption
          apply (rule p)
         apply (unfold pred_sum_inject)
         apply (rotate_tac -1)
       apply assumption
(* repeated *)
        apply (rule ballI impI)+
        apply (unfold relcompp_conversep_Grp)[1]
        apply (unfold Grp_OO)[1]
        apply (rule disjCI)
     thm l_is_inr[of _ _ _ _ pick1 pick2 pick1' pick2']
        apply (frule l_is_inr[of _ _ _ _ pick1 pick2 pick1' pick2'])
         apply (unfold comp_apply)[1]
         apply assumption
        apply (erule exE)
        apply hypsubst
        apply (rule exI)+
        apply (rule conjI)
         apply (drule valid_pick_set10[rotated])
           apply assumption
          apply (rule p)
         apply (unfold pred_sum_inject)
         apply (rotate_tac -1)
         apply assumption
        apply (rule conjI | assumption)+
         apply (rule trans[OF comp_apply])
         apply (rule arg_cong[of "case_sum _ _ _"])
         apply (unfold f_simps[symmetric])?
         apply (unfold sum.case)
         apply (rule refl)
        apply (drule r_is_Umap)
         apply (rule refl)
        apply hypsubst
        apply (unfold sum.case)
        apply (rule refl)
(* repeated *)
        apply (rule ballI impI)+
        apply (unfold relcompp_conversep_Grp)[1]
       apply (unfold Grp_OO)[1]
      apply (rule disjCI)
       apply (frule l_is_inr[of _ _ _ _ pick1 pick2 pick1' pick2'])
        apply (erule contrapos_nn)
        apply (erule arg_cong2[OF _ refl, of _ _ alpha_T2, THEN iffD1, rotated])
        apply (subst comp_apply)
        apply (subst T2.permute_raw_comps)
                apply (rule supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv bij_id supp_id_bound | assumption)+
      apply (unfold o_inv_o_cancel[OF bij_is_inj])[1]
     apply (unfold0 o_id id_o)?
        apply (rule refl)
apply (erule exE)
       apply hypsubst
     apply (subst comp_apply)
              apply (subst sum.case)+
              apply (rule exI)+
              apply (drule r_is_Umap)
               apply (rule refl)
              apply hypsubst
              apply (unfold sum.case)
              apply (rule conjI[rotated])+
             apply (rule refl)+
            apply (subst T2.permute_raw_comps)
                    apply (rule supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv bij_id supp_id_bound | assumption)+
          apply (unfold o_inv_o_cancel[OF bij_is_inj])[1]
    apply (unfold0 o_id id_o)?
            apply (rule refl)
           apply (rule supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv | assumption)+
         apply (drule valid_pick_set11[rotated])
           apply assumption
          apply (rule p)
         apply (unfold pred_sum_inject)
         apply (rotate_tac -1)
     apply assumption
(* END REPEAT_DETERM *)
     done

(* REPEAT_DETERM *)
  apply (rule exI)+
  apply (rule conjI[rotated])+
      apply (rule refl)+
        apply (rule assms)+
(* repeated *)
  apply (rule exI)+
  apply (rule conjI[rotated])+
      apply (rule refl)+
       apply (rule assms)+
(* END REPEAT_DETERM *)
   done

lemma f_alpha:
  assumes "suitable1 pick1" "suitable2 pick2" "suitable1 pick1'" "suitable2 pick2'"
    and valid_d: "valid_U1 d" "valid_U2 d2"
  shows "alpha_T1 (f1 pick1 pick2 d) (f1 pick1' pick2' d) \<and>
         alpha_T2 (f2 pick1 pick2 d2) (f2 pick1' pick2' d2)"
  by (rule f_swap_alpha[OF assms bij_id supp_id_bound bij_id supp_id_bound, unfolded T1.permute_raw_id T2.permute_raw_id raw_Umap_id(1)[OF valid_d(1)] raw_Umap_id(2)[OF valid_d(2)]])

lemma exists_suitable:
  "\<exists> pick. suitable1 pick" "\<exists> pick. suitable2 pick"
(* REPEAT_DETERM *)
  apply (unfold suitable1_def)
  apply (rule choice)
  apply (rule allI)
  apply (subst ex_simps)
  apply (rule impI)
   apply (erule ex_in_conv[THEN iffD2, OF Utor_ne(1)])
(* repeated *)
  apply (unfold suitable2_def)
  apply (rule choice)
  apply (rule allI)
  apply (subst ex_simps)
  apply (rule impI)
  apply (erule ex_in_conv[THEN iffD2, OF Utor_ne(2)])
  done

lemma suitable_pick0:
  "suitable1 pick0_1" "suitable2 pick0_2"
(* REPEAT_DETERM *)
  apply (unfold pick0_1_def)
   apply (rule someI_ex[OF exists_suitable(1)])
(* repeated *)
apply (unfold pick0_2_def)
  apply (rule someI_ex[OF exists_suitable(2)])
(* END REPEAT_DETERM *)
  done

lemmas f0_low_level_simps = f_simps[of pick0_1 pick0_2, unfolded f0_1_def[symmetric] f0_2_def[symmetric]]

lemma f0_Utor_aux1:
  assumes "X \<in> Utor1 d" "X' \<in> Utor2 d2" and valid_d: "valid_U1 d" "valid_U2 d2"
  shows "alpha_T1 (f1 (\<lambda> d'. if d' = d then X else pick0_1 d') (\<lambda> d'. if d' = d2 then X' else pick0_2 d') d)
                       (raw_T1_ctor (map_T1_pre id id id id id id id (case_sum id f0_1) (case_sum id f0_1) (case_sum id f0_2) (case_sum id f0_2) X))"
    apply(subst f_simps)
  apply (subst if_P[OF refl])
    apply(rule alpha_T1_alpha_T2.intros[of id id], (rule bij_id supp_id_bound id_on_id)+)
    apply (unfold T1_pre.mr_rel_id[symmetric] T1_pre.rel_map)
  apply(rule T1_pre.rel_refl_strong)
  apply (rule refl)
(* REPEAT *)
     apply (rule sumE)
      apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
       apply assumption
      apply hypsubst
      apply (unfold sum.simps)
      apply (unfold T1.permute_raw_id T2.permute_raw_id id_apply)[1]
      apply (rule T1.alpha_refl)
  apply hypsubst
     apply (unfold sum.simps)
     apply (unfold f0_1_def)?
     apply (rule f_alpha[OF _ _ suitable_pick0, THEN conjunct1])

(* BLOCK: SUITABLE *)

(* REPEAT_DETERM *)
     apply (unfold suitable1_def)
    apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
    apply (rule impI)
    apply (insert suitable_pick0[unfolded suitable1_def suitable2_def, THEN spec, THEN mp])[1]
        apply assumption
(* repeated *)
     apply (unfold suitable2_def)
    apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
    apply (rule impI)
    apply (insert suitable_pick0[unfolded suitable1_def suitable2_def, THEN spec, THEN mp])[1]
        apply assumption
(* END REPEAT_DETERM *)

   apply (rule assms(1)[unfolded Utor1_def, THEN imageE])
       apply (rotate_tac -1)
   apply (erule valid_Udtor'[rotated])
     prefer 2
     apply (rule Basic_BNFs.setr.intros)
     apply (rule refl)
     apply hypsubst_thin
    apply (subst (asm) T1_pre.set_map, (rule bij_id supp_id_bound)+)
    apply (rule UnI1)
    apply (erule imageE)
    apply (drule setr.intros[OF sym])
    apply (unfold sum.set_map image_id setr.simps)
    apply (erule exE)
    apply (erule conjE)
    apply (hypsubst_thin)
  apply assumption
      apply (rule assms)+

(* END BLOCK *)

     apply (rule sumE)
      apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
       apply assumption
      apply hypsubst
     apply (unfold sum.simps)
     apply (unfold T1.permute_raw_id T2.permute_raw_id id_apply)?
      apply (rule T1.alpha_refl)
  apply hypsubst
     apply (unfold sum.simps)
     apply (unfold f0_1_def)?
     apply (rule f_alpha[OF _ _ suitable_pick0, THEN conjunct1])

(* BLOCK: SUITABLE *)

(* REPEAT_DETERM *)
     apply (unfold suitable1_def)
    apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
    apply (rule impI)
    apply (insert suitable_pick0[unfolded suitable1_def suitable2_def, THEN spec, THEN mp])[1]
        apply assumption
(* repeated *)
     apply (unfold suitable2_def)
    apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
    apply (rule impI)
    apply (insert suitable_pick0[unfolded suitable1_def suitable2_def, THEN spec, THEN mp])[1]
        apply assumption
(* END REPEAT_DETERM *)

   apply (rule assms(1)[unfolded Utor1_def, THEN imageE])
       apply (rotate_tac -1)
   apply (erule valid_Udtor'[rotated])
     prefer 2
     apply (rule Basic_BNFs.setr.intros)
     apply (rule refl)
     apply hypsubst_thin
    apply (subst (asm) T1_pre.set_map, (rule bij_id supp_id_bound)+)
    apply (rule UnI2)
    apply (erule imageE)
    apply (drule setr.intros[OF sym])
    apply (unfold sum.set_map image_id setr.simps)
    apply (erule exE)
    apply (erule conjE)
    apply (hypsubst_thin)
  apply assumption
      apply (rule assms)+

(* END BLOCK *)
(* END REPEAT *)

(* REPEAT *)
     apply (rule sumE)
      apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
       apply assumption
      apply hypsubst
      apply (unfold sum.simps)
      apply (unfold T1.permute_raw_id T2.permute_raw_id id_apply)?
      apply (rule T2.alpha_refl)
  apply hypsubst
     apply (unfold sum.simps)
     apply (unfold f0_2_def)?
     apply (rule f_alpha[OF _ _ suitable_pick0, THEN conjunct2])

(* BLOCK: SUITABLE *)

(* REPEAT_DETERM *)
     apply (unfold suitable1_def)
    apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
    apply (rule impI)
    apply (insert suitable_pick0[unfolded suitable1_def suitable2_def, THEN spec, THEN mp])[1]
        apply assumption
(* repeated *)
     apply (unfold suitable2_def)
    apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
    apply (rule impI)
    apply (insert suitable_pick0[unfolded suitable1_def suitable2_def, THEN spec, THEN mp])[1]
        apply assumption
(* END REPEAT_DETERM *)

  apply (rule assms)
   apply (rule assms(1)[unfolded Utor1_def, THEN imageE])
    apply (rotate_tac -1)
   apply (erule valid_Udtor'[rotated])
     prefer 2
     apply (rule Basic_BNFs.setr.intros)
     apply (rule refl)
     apply hypsubst_thin
    apply (subst (asm) T1_pre.set_map, (rule bij_id supp_id_bound)+)
    apply (rule UnI1)
    apply (erule imageE)
    apply (drule setr.intros[OF sym])
    apply (unfold sum.set_map image_id setr.simps)
    apply (erule exE)
    apply (erule conjE)
    apply (hypsubst_thin)
  apply assumption
      apply (rule assms)+

(* END BLOCK *)

     apply (rule sumE)
      apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
       apply assumption
      apply hypsubst
     apply (unfold sum.simps)
     apply (unfold T1.permute_raw_id T2.permute_raw_id id_apply)?
      apply (rule T2.alpha_refl)
  apply hypsubst
     apply (unfold sum.simps)
     apply (unfold f0_2_def)?
     apply (rule f_alpha[OF _ _ suitable_pick0, THEN conjunct2])

(* BLOCK: SUITABLE *)

(* REPEAT_DETERM *)
     apply (unfold suitable1_def)
    apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
    apply (rule impI)
    apply (insert suitable_pick0[unfolded suitable1_def suitable2_def, THEN spec, THEN mp])[1]
        apply assumption
(* repeated *)
     apply (unfold suitable2_def)
    apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
    apply (rule impI)
    apply (insert suitable_pick0[unfolded suitable1_def suitable2_def, THEN spec, THEN mp])[1]
        apply assumption
(* END REPEAT_DETERM *)

  apply (rule assms)
   apply (rule assms(1)[unfolded Utor1_def, THEN imageE])
       apply (rotate_tac -1)
   apply (erule valid_Udtor'[rotated])
     prefer 2
     apply (rule Basic_BNFs.setr.intros)
     apply (rule refl)
     apply hypsubst_thin
    apply (subst (asm) T1_pre.set_map, (rule bij_id supp_id_bound)+)
    apply (rule UnI2)
    apply (erule imageE)
    apply (drule setr.intros[OF sym])
    apply (unfold sum.set_map image_id setr.simps)
    apply (erule exE)
    apply (erule conjE)
    apply (hypsubst_thin)
  apply assumption
      apply (rule assms)+

(* END BLOCK *)
(* END REPEAT *)
  done

lemma f0_Utor_aux2:
  assumes "X \<in> Utor1 d" "X' \<in> Utor2 d2" and valid_d: "valid_U1 d" "valid_U2 d2"
  shows "alpha_T2 (f2 (\<lambda> d'. if d' = d then X else pick0_1 d') (\<lambda> d'. if d' = d2 then X' else pick0_2 d') d2)
                       (raw_T2_ctor (map_T2_pre id id id id id id id (case_sum id f0_1) (case_sum id f0_1) (case_sum id f0_2) (case_sum id f0_2) X'))"
    apply(subst f_simps)
  apply (subst if_P[OF refl])
    apply(rule alpha_T1_alpha_T2.intros[of id id], (rule bij_id supp_id_bound id_on_id)+)
    apply (unfold T2_pre.mr_rel_id[symmetric] T2_pre.rel_map)
  apply(rule T2_pre.rel_refl_strong)
  apply (rule refl)
(* REPEAT *)
     apply (rule sumE)
      apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
       apply assumption
      apply hypsubst
      apply (unfold sum.simps)
      apply (unfold T1.permute_raw_id T2.permute_raw_id id_apply)[1]
      apply (rule T1.alpha_refl)
  apply hypsubst
     apply (unfold sum.simps)
     apply (unfold f0_1_def)?
     apply (rule f_alpha[OF _ _ suitable_pick0, THEN conjunct1])

(* BLOCK: SUITABLE *)

(* REPEAT_DETERM *)
     apply (unfold suitable1_def)
    apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
    apply (rule impI)
    apply (insert suitable_pick0[unfolded suitable1_def suitable2_def, THEN spec, THEN mp])[1]
        apply assumption
(* repeated *)
     apply (unfold suitable2_def)
    apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
    apply (rule impI)
    apply (insert suitable_pick0[unfolded suitable1_def suitable2_def, THEN spec, THEN mp])[1]
        apply assumption
(* END REPEAT_DETERM *)

   apply (rule assms(2)[unfolded Utor2_def, THEN imageE])
       apply (rotate_tac -1)
   apply (erule valid_Udtor'[rotated])
     prefer 2
     apply (rule Basic_BNFs.setr.intros)
     apply (rule refl)
     apply hypsubst_thin
    apply (subst (asm) T2_pre.set_map, (rule bij_id supp_id_bound)+)
    apply (rule UnI1)
    apply (erule imageE)
    apply (drule setr.intros[OF sym])
    apply (unfold sum.set_map image_id setr.simps)
    apply (erule exE)
    apply (erule conjE)
    apply (hypsubst_thin)
  apply assumption
      apply (rule assms)+

(* END BLOCK *)

     apply (rule sumE)
      apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
       apply assumption
      apply hypsubst
     apply (unfold sum.simps)
     apply (unfold T1.permute_raw_id T2.permute_raw_id id_apply)?
      apply (rule T1.alpha_refl)
  apply hypsubst
     apply (unfold sum.simps)
     apply (unfold f0_1_def)?
     apply (rule f_alpha[OF _ _ suitable_pick0, THEN conjunct1])

(* BLOCK: SUITABLE *)

(* REPEAT_DETERM *)
     apply (unfold suitable1_def)
    apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
    apply (rule impI)
    apply (insert suitable_pick0[unfolded suitable1_def suitable2_def, THEN spec, THEN mp])[1]
        apply assumption
(* repeated *)
     apply (unfold suitable2_def)
    apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
    apply (rule impI)
    apply (insert suitable_pick0[unfolded suitable1_def suitable2_def, THEN spec, THEN mp])[1]
        apply assumption
(* END REPEAT_DETERM *)

   apply (rule assms(2)[unfolded Utor2_def, THEN imageE])
       apply (rotate_tac -1)
   apply (erule valid_Udtor'[rotated])
     prefer 2
     apply (rule Basic_BNFs.setr.intros)
     apply (rule refl)
     apply hypsubst_thin
    apply (subst (asm) T2_pre.set_map, (rule bij_id supp_id_bound)+)
    apply (rule UnI2)
    apply (erule imageE)
    apply (drule setr.intros[OF sym])
    apply (unfold sum.set_map image_id setr.simps)
    apply (erule exE)
    apply (erule conjE)
    apply (hypsubst_thin)
  apply assumption
      apply (rule assms)+

(* END BLOCK *)
(* END REPEAT *)

(* REPEAT *)
     apply (rule sumE)
      apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
       apply assumption
      apply hypsubst
      apply (unfold sum.simps)
      apply (unfold T1.permute_raw_id T2.permute_raw_id id_apply)?
      apply (rule T2.alpha_refl)
  apply hypsubst
     apply (unfold sum.simps)
     apply (unfold f0_2_def)?
     apply (rule f_alpha[OF _ _ suitable_pick0, THEN conjunct2])

(* BLOCK: SUITABLE *)

(* REPEAT_DETERM *)
     apply (unfold suitable1_def)
    apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
    apply (rule impI)
    apply (insert suitable_pick0[unfolded suitable1_def suitable2_def, THEN spec, THEN mp])[1]
        apply assumption
(* repeated *)
     apply (unfold suitable2_def)
    apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
    apply (rule impI)
    apply (insert suitable_pick0[unfolded suitable1_def suitable2_def, THEN spec, THEN mp])[1]
        apply assumption
(* END REPEAT_DETERM *)

  apply (rule assms)
   apply (rule assms(2)[unfolded Utor2_def, THEN imageE])
    apply (rotate_tac -1)
   apply (erule valid_Udtor'[rotated])
     prefer 2
     apply (rule Basic_BNFs.setr.intros)
     apply (rule refl)
     apply hypsubst_thin
    apply (subst (asm) T2_pre.set_map, (rule bij_id supp_id_bound)+)
    apply (rule UnI1)
    apply (erule imageE)
    apply (drule setr.intros[OF sym])
    apply (unfold sum.set_map image_id setr.simps)
    apply (erule exE)
    apply (erule conjE)
    apply (hypsubst_thin)
  apply assumption
      apply (rule assms)+

(* END BLOCK *)

     apply (rule sumE)
      apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
       apply assumption
      apply hypsubst
     apply (unfold sum.simps)
     apply (unfold T1.permute_raw_id T2.permute_raw_id id_apply)?
      apply (rule T2.alpha_refl)
  apply hypsubst
     apply (unfold sum.simps)
     apply (unfold f0_2_def)?
     apply (rule f_alpha[OF _ _ suitable_pick0, THEN conjunct2])

(* BLOCK: SUITABLE *)

(* REPEAT_DETERM *)
     apply (unfold suitable1_def)
    apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
    apply (rule impI)
    apply (insert suitable_pick0[unfolded suitable1_def suitable2_def, THEN spec, THEN mp])[1]
        apply assumption
(* repeated *)
     apply (unfold suitable2_def)
    apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
    apply (rule impI)
    apply (insert suitable_pick0[unfolded suitable1_def suitable2_def, THEN spec, THEN mp])[1]
        apply assumption
(* END REPEAT_DETERM *)

  apply (rule assms)
   apply (rule assms(2)[unfolded Utor2_def, THEN imageE])
       apply (rotate_tac -1)
   apply (erule valid_Udtor'[rotated])
     prefer 2
     apply (rule Basic_BNFs.setr.intros)
     apply (rule refl)
     apply hypsubst_thin
    apply (subst (asm) T2_pre.set_map, (rule bij_id supp_id_bound)+)
    apply (rule UnI2)
    apply (erule imageE)
    apply (drule setr.intros[OF sym])
    apply (unfold sum.set_map image_id setr.simps)
    apply (erule exE)
    apply (erule conjE)
    apply (hypsubst_thin)
  apply assumption
      apply (rule assms)+

(* END BLOCK *)
(* END REPEAT *)
  done

lemmas f0_Utor_aux = f0_Utor_aux1 f0_Utor_aux2

lemma f0_Utor1:
  assumes "X \<in> Utor1 d" "X' \<in> Utor2 d2" and valid_d: "valid_U1 d" "valid_U2 d2"
  shows "alpha_T1 (f0_1 d) (raw_T1_ctor (map_T1_pre id id id id id id id (case_sum id f0_1) (case_sum id f0_1) (case_sum id f0_2) (case_sum id f0_2) X))"
  apply (rule T1.alpha_trans[rotated])
  thm f0_Utor_aux[OF assms]
   apply (rule f0_Utor_aux[OF assms])
  thm f_alpha[OF suitable_pick0 _ _ valid_d, unfolded f0_1_def[symmetric] f0_2_def[symmetric]]
    apply (rule f_alpha[OF suitable_pick0 _ _ valid_d, unfolded f0_1_def[symmetric] f0_2_def[symmetric], THEN conjunct1])

(* REPEAT_DETERM *)
     apply (unfold suitable1_def)
  apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
  apply (rule impI)
    apply (insert suitable_pick0(1)[unfolded suitable1_def, THEN spec, THEN mp])[1]
   apply assumption
(* repeated *)
     apply (unfold suitable2_def)
  apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
  apply (rule impI)
    apply (insert suitable_pick0(2)[unfolded suitable2_def, THEN spec, THEN mp])[1]
   apply assumption
(* END REPEAT_DETERM *)
  done

lemma f0_Utor2:
  assumes "X \<in> Utor1 d" "X' \<in> Utor2 d2" and valid_d: "valid_U1 d" "valid_U2 d2"
  shows "alpha_T2 (f0_2 d2) (raw_T2_ctor (map_T2_pre id id id id id id id (case_sum id f0_1) (case_sum id f0_1) (case_sum id f0_2) (case_sum id f0_2) X'))"
  apply (rule T2.alpha_trans[rotated])
  thm f0_Utor_aux[OF assms]
   apply (rule f0_Utor_aux[OF assms])
  thm f_alpha[OF suitable_pick0 _ _ valid_d, unfolded f0_1_def[symmetric] f0_2_def[symmetric], THEN conjunct2]
    apply (rule f_alpha[OF suitable_pick0 _ _ valid_d, unfolded f0_1_def[symmetric] f0_2_def[symmetric], THEN conjunct2])

(* REPEAT_DETERM *)
     apply (unfold suitable1_def)
  apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
  apply (rule impI)
    apply (insert suitable_pick0(1)[unfolded suitable1_def, THEN spec, THEN mp])[1]
   apply assumption
(* repeated *)
     apply (unfold suitable2_def)
  apply (rule allI)
  apply (rule impI)
     apply (rule if_split[THEN iffD2])
     apply (rule conjI)
      apply (rule impI)
      apply hypsubst
     apply (rule assms)
  apply (rule impI)
    apply (insert suitable_pick0(2)[unfolded suitable2_def, THEN spec, THEN mp])[1]
   apply assumption
(* END REPEAT_DETERM *)
  done

lemmas f0_Utor = f0_Utor1 f0_Utor2

lemma f0_mapD1:
  assumes "valid_U1 d" "valid_U2 d2"
      and "bij (u::'a\<Rightarrow>'a)" and "|supp u| <o |UNIV::'a set|"
      and "bij (v::'b\<Rightarrow>'b)" and "|supp v| <o |UNIV::'b set|"
  shows "alpha_T1 (f0_1 (raw_Umap1 u v d)) (permute_T1_raw u v (f0_1 d))"
  by (rule f_swap_alpha[OF suitable_pick0 suitable_pick0 assms, THEN conjunct1, THEN T1.alpha_sym, unfolded f0_1_def[symmetric]])

lemma f0_mapD2:
  assumes "valid_U1 d" "valid_U2 d2"
      and "bij (u::'a\<Rightarrow>'a)" and "|supp u| <o |UNIV::'a set|"
      and "bij (v::'b\<Rightarrow>'b)" and "|supp v| <o |UNIV::'b set|"
    shows "alpha_T2 (f0_2 (raw_Umap2 u v d2)) (permute_T2_raw u v (f0_2 d2))"
  by (rule f_swap_alpha[OF suitable_pick0 suitable_pick0 assms, THEN conjunct2, THEN T2.alpha_sym, unfolded f0_2_def[symmetric]])

lemmas f0_mapD = f0_mapD1 f0_mapD2 

lemmas f0_FVarsD = f_FVarsD[OF suitable_pick0, unfolded f0_1_def[symmetric] f0_2_def[symmetric]]


(* The following theorems for raw theorems will now be lifted to quotiented terms: *)
thm f0_Utor f0_mapD f0_FVarsD


(*******************)
(* End product: *)

term T1_ctor
thm COREC1_def
thm T1.total_abs_eq_iff

theorem COREC_DDTOR1:
  assumes "X \<in> Udtor1 d" "X' \<in> Udtor2 d2" "valid_U1 d" "valid_U2 d2"
  shows "COREC1 d = T1_ctor (map_T1_pre id id id id id id id (case_sum id COREC1) (case_sum id COREC1) (case_sum id COREC2) (case_sum id COREC2) X)"
  apply (unfold COREC1_def COREC2_def T1_ctor_def)
  apply (unfold o_def[symmetric])
  apply (subst T1_pre.map_comp, (rule supp_id_bound bij_id)+)
  apply (unfold T1.total_abs_eq_iff)
  apply (unfold o_case_sum)
  apply (unfold id_comp comp_id)
  apply (rule T1.alpha_trans)
  thm arg_cong[of _ _ "alpha_T1 (f0_1 d)", THEN iffD1]
   apply (rule arg_cong[of _ _ "alpha_T1 (f0_1 d)", THEN iffD1])
    prefer 2
    apply (rule f0_Utor)
    apply (unfold Utor1_def Utor2_def)
    apply (rule imageI)
       apply (rule assms)+
    apply (rule imageI)
     apply (rule assms)+
   apply (subst T1_pre.map_comp, (rule supp_id_bound bij_id)+)
   apply (unfold case_sum_o_map_sum)
   apply (unfold id_comp comp_id)
   apply (rule refl)
  apply(rule alpha_T1_alpha_T2.intros[of id id], (rule bij_id supp_id_bound)+)
   apply (rule id_on_id)+
  apply (unfold T1_pre.mr_rel_id[symmetric] T1_pre.rel_map)
  apply(rule T1_pre.rel_refl_strong)
  apply (rule refl)?

   apply (rule sumE)
    apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
     apply assumption
    apply hypsubst
    apply (unfold sum.simps)
    apply (rule T1.alpha_refl)
   apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
    apply assumption
   apply hypsubst
   apply (unfold sum.simps)
   apply (unfold comp_apply)[1]
   apply (rule T1.rep_abs_sym)

  apply (rule sumE)
   apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
    apply assumption
   apply hypsubst
   apply (unfold sum.simps)
   apply (unfold T1.permute_raw_id)
   apply (rule T1.alpha_refl)
  apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
   apply assumption
  apply hypsubst
    apply (unfold sum.simps)
    apply (unfold comp_apply)[1]
    apply (rule T1.rep_abs_sym)

   apply (rule sumE)
    apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
     apply assumption
    apply hypsubst
    apply (unfold sum.simps)
    apply (rule T2.alpha_refl)
   apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
    apply assumption
   apply hypsubst
   apply (unfold sum.simps)
   apply (unfold comp_apply)[1]
   apply (rule T2.rep_abs_sym)

  apply (rule sumE)
   apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
    apply assumption
   apply hypsubst
   apply (unfold sum.simps)
   apply (unfold T2.permute_raw_id)
   apply (rule T2.alpha_refl)
  apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
   apply assumption
  apply hypsubst
  apply (unfold sum.simps)
  apply (unfold comp_apply)[1]
  apply (rule T2.rep_abs_sym)
  done

theorem COREC_DDTOR2:
  assumes "X \<in> Udtor1 d" "X' \<in> Udtor2 d2" "valid_U1 d" "valid_U2 d2"
  shows "COREC2 d2 = T2_ctor (map_T2_pre id id id id id id id (case_sum id COREC1) (case_sum id COREC1) (case_sum id COREC2) (case_sum id COREC2) X')"
  apply (unfold COREC1_def COREC2_def T2_ctor_def)
  apply (unfold o_def[symmetric])
  apply (subst T2_pre.map_comp, (rule supp_id_bound bij_id)+)
  apply (unfold T2.total_abs_eq_iff)
  apply (unfold o_case_sum)
  apply (unfold id_comp comp_id)
  apply (rule T2.alpha_trans)
  thm arg_cong[of _ _ "alpha_T1 (f0_1 d)", THEN iffD1]
   apply (rule arg_cong[of _ _ "alpha_T2 (f0_2 d2)", THEN iffD1])
    prefer 2
    apply (rule f0_Utor)
    apply (unfold Utor1_def Utor2_def)
    apply (rule imageI)
       apply (rule assms)+
    apply (rule imageI)
     apply (rule assms)+
   apply (subst T2_pre.map_comp, (rule supp_id_bound bij_id)+)
   apply (unfold case_sum_o_map_sum)
   apply (unfold id_comp comp_id)
   apply (rule refl)
  apply(rule alpha_T1_alpha_T2.intros[of id id], (rule bij_id supp_id_bound)+)
   apply (rule id_on_id)+
  apply (unfold T2_pre.mr_rel_id[symmetric] T2_pre.rel_map)
  apply(rule T2_pre.rel_refl_strong)
  apply (rule refl)?

   apply (rule sumE)
    apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
     apply assumption
    apply hypsubst
    apply (unfold sum.simps)
    apply (rule T1.alpha_refl)
   apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
    apply assumption
   apply hypsubst
   apply (unfold sum.simps)
   apply (unfold comp_apply)[1]
   apply (rule T1.rep_abs_sym)

  apply (rule sumE)
   apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
    apply assumption
   apply hypsubst
   apply (unfold sum.simps)
   apply (unfold T1.permute_raw_id)
   apply (rule T1.alpha_refl)
  apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
   apply assumption
  apply hypsubst
    apply (unfold sum.simps)
    apply (unfold comp_apply)[1]
    apply (rule T1.rep_abs_sym)

   apply (rule sumE)
    apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
     apply assumption
    apply hypsubst
    apply (unfold sum.simps)
    apply (rule T2.alpha_refl)
   apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
    apply assumption
   apply hypsubst
   apply (unfold sum.simps)
   apply (unfold comp_apply)[1]
   apply (rule T2.rep_abs_sym)

  apply (rule sumE)
   apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
    apply assumption
   apply hypsubst
   apply (unfold sum.simps)
   apply (unfold T2.permute_raw_id)
   apply (rule T2.alpha_refl)
  apply (frule arg_cong2[OF _ refl, of _ _ "(\<in>)", THEN iffD1])
   apply assumption
  apply hypsubst
  apply (unfold sum.simps)
  apply (unfold comp_apply)[1]
  apply (rule T2.rep_abs_sym)
  done

lemmas COREC_DDTOR = COREC_DDTOR1 COREC_DDTOR2

lemma COREC_mmapD1:
  assumes "valid_U1 d" "valid_U2 d2"
    and u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a set|"
    and v: "bij (v::'b\<Rightarrow>'b)" "|supp v| <o |UNIV::'b set|"
  shows "COREC1 (Umap1 u v d) = permute_T1 u v (COREC1 d)"
  apply (unfold COREC1_def permute_T1_def)
  apply (unfold T1.total_abs_eq_iff)
  apply (rule T1.alpha_trans)
   apply (rule f0_mapD[OF assms])
  apply (unfold T1.alpha_bij_eq[OF u v])
  apply (rule T1.alpha_sym)
  apply (rule T1.rep_abs)
  done

lemma COREC_mmapD2:
  assumes "valid_U1 d" "valid_U2 d2"
    and u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a set|"
    and v: "bij (v::'b\<Rightarrow>'b)" "|supp v| <o |UNIV::'b set|"
  shows "COREC2 (Umap2 u v d2) = permute_T2 u v (COREC2 d2)"
  apply (unfold COREC2_def permute_T2_def)
  apply (unfold T2.total_abs_eq_iff)
  apply (rule T2.alpha_trans)
   apply (rule f0_mapD[OF assms])
  apply (unfold T2.alpha_bij_eq[OF u v])
  apply (rule T2.alpha_sym)
  apply (rule T2.rep_abs)
  done

lemmas COREC_mmapD = COREC_mmapD1 COREC_mmapD2

term FVars_T1_1
thm T1.alpha_FVars[OF T1.rep_abs]

theorem COREC_FFVarsD1:
  "valid_U1 d \<Longrightarrow> FVars_T1_1 (COREC1 d) \<subseteq> UFVars11 d"
  "valid_U1 d \<Longrightarrow> FVars_T1_2 (COREC1 d) \<subseteq> UFVars12 d"
(* REPEAT_DETERM *)
   apply (unfold COREC1_def FVars_T1_1_def T1.alpha_FVars[OF T1.rep_abs])
   apply (erule f0_FVarsD)
(* repeated *)
  apply (unfold COREC1_def FVars_T1_2_def T1.alpha_FVars[OF T1.rep_abs])
  apply (erule f0_FVarsD)
(* END REPEAT_DETERM *)
  done

theorem COREC_FFVarsD2:
  "valid_U2 d \<Longrightarrow> FVars_T2_1 (COREC2 d) \<subseteq> UFVars21 d"
  "valid_U2 d \<Longrightarrow> FVars_T2_2 (COREC2 d) \<subseteq> UFVars22 d"
(* REPEAT_DETERM *)
   apply (unfold COREC2_def FVars_T2_1_def T2.alpha_FVars[OF T2.rep_abs])
   apply (erule f0_FVarsD)
(* repeated *)
  apply (unfold COREC2_def FVars_T2_2_def T2.alpha_FVars[OF T2.rep_abs])
  apply (erule f0_FVarsD)
(* END REPEAT_DETERM *)
  done

lemmas COREC_FFVarsD = COREC_FFVarsD1 COREC_FFVarsD2

end

end
