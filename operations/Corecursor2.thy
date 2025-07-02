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
  set1_T1_pre X \<union> \<Union>(case_sum FVars_T1_1 UFVars11 ` set8_T1_pre X) \<union> \<Union>(case_sum FVars_T2_1 UFVars21 ` set10_T1_pre X) \<union> (set7_T1_pre X
   \<union> (\<Union>(case_sum FVars_T1_1 UFVars11 ` set9_T1_pre X))
   \<union> (\<Union>(case_sum FVars_T2_1 UFVars21 ` set11_T1_pre X)) - set5_T1_pre X)
   \<subseteq> UFVars11 d"
  and UFVars12_Udtor:
    "\<And> d X. valid_U1 d \<Longrightarrow> X \<in> Udtor1 d \<Longrightarrow>
  set2_T1_pre X
  \<union> \<Union>(case_sum FVars_T1_2 UFVars12 ` set8_T1_pre X) \<union> (\<Union>(case_sum FVars_T1_2 UFVars12 ` set9_T1_pre X) - set6_T1_pre X)
  \<union> \<Union>(case_sum FVars_T2_2 UFVars22 ` set10_T1_pre X) \<union> (\<Union>(case_sum FVars_T2_2 UFVars22 ` set11_T1_pre X) - set6_T1_pre X)
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

term FVars_T1_1
term FVars_T1_2
term set1_T1_pre
term set8_T1_pre
term UFVars21

definition FFVarsBD11 :: "('a, 'b, 'c, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) T1 + 'u1, ('a, 'b, 'c, 'd) T1 + 'u1, ('a, 'b, 'c, 'd) T2 + 'u2, ('a, 'b, 'c, 'd) T2 + 'u2) T1_pre \<Rightarrow> 'a set" where
  "FFVarsBD11 X \<equiv> (set7_T1_pre X \<union> \<Union>(case_sum FVars_T1_1 UFVars11 ` set9_T1_pre X) \<union> \<Union>(case_sum FVars_T2_1 UFVars21 ` set11_T1_pre X)) - set5_T1_pre X"

definition FFVarsBD12 :: "('a, 'b, 'c, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) T1 + 'u1, ('a, 'b, 'c, 'd) T1 + 'u1, ('a, 'b, 'c, 'd) T2 + 'u2, ('a, 'b, 'c, 'd) T2 + 'u2) T1_pre \<Rightarrow> 'b set" where
  "FFVarsBD12 X \<equiv> (\<Union> (case_sum FVars_T1_2 UFVars12 ` set9_T1_pre X) \<union> \<Union> (case_sum FVars_T2_2 UFVars22 ` set11_T1_pre X) - set6_T1_pre X)"

definition FFVarsBD21 :: "('a, 'b, 'c, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) T1 + 'u1, ('a, 'b, 'c, 'd) T1 + 'u1, ('a, 'b, 'c, 'd) T2 + 'u2, ('a, 'b, 'c, 'd) T2 + 'u2) T2_pre \<Rightarrow> 'a set" where
  "FFVarsBD21 X \<equiv> (set7_T2_pre X \<union> \<Union>(case_sum FVars_T1_1 UFVars11 ` set9_T2_pre X) \<union> \<Union>(case_sum FVars_T2_1 UFVars21 ` set11_T2_pre X)) - set5_T2_pre X"

definition FFVarsBD22 :: "('a, 'b, 'c, 'd, 'a, 'b, 'a, ('a, 'b, 'c, 'd) T1 + 'u1, ('a, 'b, 'c, 'd) T1 + 'u1, ('a, 'b, 'c, 'd) T2 + 'u2, ('a, 'b, 'c, 'd) T2 + 'u2) T2_pre \<Rightarrow> 'b set" where
  "FFVarsBD22 X \<equiv> (\<Union> (case_sum FVars_T1_2 UFVars12 ` set9_T2_pre X) \<union> \<Union> (case_sum FVars_T2_2 UFVars22 ` set11_T2_pre X) - set6_T2_pre X)"

lemmas FFVarsBD1 = FFVarsBD11_def FFVarsBD12_def
lemmas FFVarsBD2 = FFVarsBD21_def FFVarsBD22_def

lemmas Udtor_Umap = alpha_Udtor1[folded FFVarsBD1] alpha_Udtor2[folded FFVarsBD2]

thm UFVars11_Udtor FFVarsBD1
lemmas FVars_T1_Udtor = UFVars11_Udtor[folded FFVarsBD1]

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

lemma raw_UFVars_Utor:
  assumes "valid_U d"
  shows "X \<in> Utor d \<Longrightarrow> set1_term_pre X \<union> \<Union>(case_sum FVars_raw_term raw_UFVars ` set4_term_pre X) \<union> raw_UFVarsBD X \<subseteq> raw_UFVars d"
  apply (drule FVars_term_Udtor[OF assms Utor_abs_Udtor])
  apply (subst (asm) term_pre.set_map, (rule supp_id_bound bij_id)+)+
  apply (unfold image_comp case_sum_o_map_sum o_id image_id raw_UFVars_def2)
  apply (unfold FVarsBD_FFVarsBD comp_def)
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
            (\<lambda>t t'. raw_Umap u t = t'))
 (pick d)
 (pick' (raw_Umap u d))"
  apply (rule raw_Umap_Utor[OF u valid_d, unfolded rel_set_def, THEN conjunct2, THEN bspec, THEN bexE])
   apply (rule allE)
    apply (rule pp'(2)[unfolded suitable_def])
   apply (erule impE)
    prefer 2
    apply assumption
   apply (rule valid_Umap, (rule u valid_d)+)
  apply (rule exE)
   apply (rule DTOR_mapD[OF assms(1)])
   apply (unfold insert_subset)
   apply (rule conjI)
    apply (rule assms(2)[unfolded suitable_def, THEN spec, THEN mp, OF assms(1)])
   apply (rule conjI)
    apply assumption
   apply (rule empty_subsetI)
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
            apply assumption
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
    r: "rel_sum (\<lambda>t. alpha_term (permute_raw_term u t)) (\<lambda>d d'. raw_Umap u d = d') ttdL ttdR"
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
    r: "rel_sum (\<lambda>t. alpha_term (permute_raw_term u t)) (\<lambda>d d'. raw_Umap u d = d') ttdL ttdR"
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

lemma f_swap_alpha:
  assumes p: "suitable pick" and p': "suitable pick'"
    and valid_d: "valid_U d"
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o |UNIV::'a::var set|"
  shows "alpha_term (permute_raw_term u (f pick d)) (f pick' (raw_Umap u d))"
   apply (rule alpha_coinduct2[of "\<lambda> tL tR. \<exists> u d. valid_U d \<and> bij u \<and> |supp u| <o |UNIV::'a set| \<and>
   tL = permute_raw_term u (f pick d) \<and> tR = f pick' (raw_Umap u d)"])
  prefer 2
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
   apply (subst comp_def)
   apply (subst FVars_raw_permutes, assumption+)
  apply (subst comp_def[of _ FVars_raw_term, symmetric])
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