theory Linearize_scratch                                                      
  imports "Binders.MRBNF_Composition" "Binders.MRBNF_Recursor" 
    "HOL-Library.FSet" "HOL-Library.Uprod"
  keywords "linearize_mrbnf" :: thy_goal
begin

section "setup"

ML_file "../Tools/mrbnf_linearize_tactics.ML"
ML_file "../Tools/mrbnf_linearize.ML"


declare [[bnf_internals]]
declare [[mrbnf_internals]]
declare [[typedef_overloaded]]
declare [[ML_print_depth=1000]]

section "binder_datatypes & errors"
binder_datatype 'var lterm = Vr 'var | Ap "'var lterm" "'var lterm"
  | Lm x::'var t::"'var lterm" binds x in t

binder_datatype ('a, 'b::var) test = V 'b | B "'a list" | C x::'b t::"('a, 'b) test" binds x in t

(*ML \<open>BNF_Util.permute_like_unique (op =) [0, 1] [0, ~1, ~1, 1, ~1] [Bound 4, Bound 3, Bound 2, Bound 1, Bound 0]\<close>*)

section "Intuition: What is nonrep?"

(* LIST *)
lemma "\<And> R (x :: 'a list) y. list_all2 R x y = (\<exists>z. set z \<subseteq> {(x, y). R x y} \<and> map fst z = x \<and> map snd z = y)"
  subgoal for R x y
    apply (rule list.in_rel[of R x y, unfolded mem_Collect_eq])
    done
  done

definition eq_shape_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where 
  "eq_shape_list x x' \<equiv> list_all2 top x x'"

definition nonrep_list :: "'a list \<Rightarrow> bool" where 
  "nonrep_list x \<equiv> \<forall> x'. eq_shape_list x x' \<longrightarrow> (\<exists> f. x' = map f x)"

lemma eq_shape_list_alt: "list_all2 top xs xs' = (length xs = length xs')"
  by (simp add: list_all2_conv_all_nth)

lemma ex_not: "((\<forall>x. P x) \<longrightarrow> False) = (\<exists>x. \<not>P x)"
  by simp

lemma "nonrep_list ([1, 1, 1]::nat list) \<longrightarrow> False"
  apply (unfold nonrep_list_def eq_shape_list_def eq_shape_list_alt)
  apply (rule ex_not[THEN iffD2])
  apply (rule exI[of _ "[1, 2, 3]"])
  apply (auto)
  done

lemma "nonrep_list ([1, 2, 3]::nat list)"
  apply (unfold nonrep_list_def eq_shape_list_def eq_shape_list_alt)
  apply (rule allI)
  apply (rule impI)
  subgoal for x
    apply (rule exI[of _ "(\<lambda> y. (if y = 1 then (hd x) else (if y = 2 then (hd (tl x)) else (hd (tl (tl x))))))"])
    apply (auto)
    by (metis (lifting) ext length_0_conv length_Suc_conv list.sel(1,3))
  done

typedef 'a nrp_list = "{(xs :: 'a list). nonrep_list xs}"
  apply (rule exI[of _ "[]"])
  apply (auto simp add: nonrep_list_def eq_shape_list_def)
  done

(* PROD *)
definition eq_shape_prod_1 :: "('a \<times> 'b) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> bool" where 
  "eq_shape_prod_1 x x' \<equiv> rel_prod top (=) x x'"

definition nonrep_prod_1 :: "('a \<times> 'b) \<Rightarrow> bool" where 
  "nonrep_prod_1 x \<equiv> \<forall> x'. eq_shape_prod_1 x x' \<longrightarrow> (\<exists> f. x' = map_prod f id x)"

(* any product is nonrep on first position*)
lemma "nonrep_prod_1 (a, b)"
  apply (unfold nonrep_prod_1_def eq_shape_prod_1_def)
  apply (auto)
  done

section "Intuition: What is strong pullback perservation?"
(* fset *)
lemma "rel_fset top (Abs_fset {1, 2}) (Abs_fset {1, 2})"
  unfolding fset.in_rel[unfolded mem_Collect_eq] 
  apply (rule exI[of _ "(Abs_fset {(1, 2), (2, 1)})"], auto)
  apply (subst Abs_fset_inverse[unfolded mem_Collect_eq], simp,
    subst (asm) Abs_fset_inverse[unfolded mem_Collect_eq], auto)+
  done

lemma "rel_fset top (Abs_fset {1, 2}) (Abs_fset {1, 2})"
  unfolding fset.in_rel[unfolded mem_Collect_eq] 
  apply (rule exI[of _ "(Abs_fset {(1, 1), (2, 2)})"], auto)
  apply (subst Abs_fset_inverse[unfolded mem_Collect_eq], simp,
    subst (asm) Abs_fset_inverse[unfolded mem_Collect_eq], auto)+
  done
 (* \<Longrightarrow> NOT \<exists>!z *)

(* uprod *)
lemma "rel_uprod top (Upair 1 2) (Upair 1 2)"
  unfolding uprod.in_rel[unfolded mem_Collect_eq]
  by (rule exI[of _ "Upair (1, 1) (2, 2)"]) auto

lemma "rel_uprod top (Upair 1 2) (Upair 1 2)"
  unfolding uprod.in_rel[unfolded mem_Collect_eq]
  by (rule exI[of _ "Upair (1, 2) (2, 1)"]) auto
 (* \<Longrightarrow> NOT \<exists>!z *)

section "Intuition: Why BNF?"

typedef 'a even_list = "{x :: 'a list. even (length x)}"
  apply (rule exI[of _ "[]"])
  apply (unfold mem_Collect_eq list.size(3))
  apply (rule even_zero)
  done

datatype 'a test_A = F 'a | R "('a test_A) set"
datatype 'a test_B = MK "'a" | MK2 "('a test_B) even_list"

setup_lifting type_definition_even_list
lift_bnf 'a even_list [wits: "[] :: 'a list"] 
  subgoal for f x
    apply (unfold mem_Collect_eq length_map)
    apply (assumption)
    done
  subgoal for z
    apply (unfold mem_Collect_eq)
    apply (intro bexI[of _ z] conjI subset_refl refl)
    apply (unfold mem_Collect_eq length_map)
    apply (assumption)
    done
  subgoal
  apply (unfold mem_Collect_eq list.size(3))
  apply (rule even_zero)
    done
  subgoal for a
    apply (unfold list.set(1) empty_iff)
    apply (assumption)
    done
  done

thm fun.set_bd
(*
bnf "'a set"
  map: image
    sets: "(id :: 'a set \<Rightarrow> 'a set)"
  bd: "natLeq +c card_suc |UNIV|"
  rel: rel_set
           apply (auto simp add: card_order_bd_fun Cinfinite_bd_fun[THEN conjunct1] regularCard_bd_fun)
  subgoal for f g
    by fastforce
  subgoal for x
    using card_of_UNIV ordLeq_ordLess_trans ordLess_bd_fun by blast
  subgoal for R S x y z
    apply (unfold rel_set_def)
    by (meson relcomppI)
  apply (intro ext)
  subgoal for R x y
    sorry
  done
print_theorems
*)


datatype 'a test_A = F 'a | R "('a test_A) set" (* is set a BNF?*)
datatype 'a test_B = MK "'a" | MK2 "('a test_B) even_list"

linearize_mrbnf 'a::var lin_fset = "'a::var fset" on 'a
  done

binder_datatype 'a test_C = Leaf | MK2' "(r::'a) lin_fset" "s::'a test_C" binds r in s


section "Example: Foo"
setup \<open>Sign.qualified_path false (Binding.name "foo")\<close>

codatatype ('a, 'b) foo = Foo "'a" | Bar 'b "('a, 'b) foo"

setup \<open>Sign.parent_path\<close>

mrbnf "('a, 'b) foo"
  map: map_foo
  sets: live: set1_foo live: set2_foo
  bd: "card_suc natLeq"
  wits:
    "wit1_foo" "wit2_foo"
  rel: rel_foo
  by (auto simp add: foo.map_id foo.map_comp foo.set_map infinite_regular_card_order_card_suc[OF natLeq_card_order natLeq_Cinfinite] 
      foo.set_bd[unfolded bd_foo_def] foo.rel_compp foo.in_rel intro: foo.map_cong0 elim: foo.wit1 foo.wit2)

print_mrbnfs

datatype '\<alpha> ex = A "('\<alpha> \<times> ('\<alpha> ex)) list"

primcorec mywit where
  "mywit X = (let y = SOME x. x\<notin>X in Bar y (mywit (insert y X)))"

linearize_mrbnf ('a, 'b::var_foo) foo'' = "('a, 'b::var_foo) foo" 
  [wits: "(mywit {}) :: ('a, 'b::var_foo) foo"] on 'b
  subgoal
    sorry
  subgoal
    sorry
  subgoal
    sorry
  done

section "declaration: L, F, G"

subsection "L"
typedecl ('a, 'b) L
consts map_L :: "('a \<Rightarrow> 'a') \<Rightarrow> ('b \<Rightarrow> 'b') \<Rightarrow> ('a, 'b) L \<Rightarrow> ('a', 'b') L"
consts set1_L :: "('a, 'b) L \<Rightarrow> 'a set"
consts set2_L :: "('a, 'b) L \<Rightarrow> 'b set"
consts rrel_L :: "('a \<Rightarrow> 'a' \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b' \<Rightarrow> bool) \<Rightarrow> ('a, 'b) L \<Rightarrow> ('a', 'b') L \<Rightarrow> bool"

mrbnf "('a, 'b) L"
  map: map_L
  sets: live: set1_L live: set2_L
  bd: natLeq
  rel: rrel_L
  var_class: var
  sorry

consts witL :: "('a::var, 'b) L"


subsection "F"
typedecl ('a, 'b, 'c, 'd, 'e, 'f) F
consts map_F :: "('a \<Rightarrow> 'a') \<Rightarrow> ('b :: var \<Rightarrow> 'b) \<Rightarrow>
  ('c :: var \<Rightarrow> 'c) \<Rightarrow> ('e \<Rightarrow> 'e') \<Rightarrow> ('f \<Rightarrow> 'f') \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) F \<Rightarrow> ('a', 'b, 'c, 'd, 'e', 'f') F"
consts set1_F :: "('a, 'b :: var, 'c :: var, 'd, 'e, 'f) F \<Rightarrow> 'a set"
consts set2_F :: "('a, 'b :: var, 'c :: var, 'd, 'e, 'f) F \<Rightarrow> 'b set"
consts set3_F :: "('a, 'b :: var, 'c :: var, 'd, 'e, 'f) F \<Rightarrow> 'c set"
consts set4_F :: "('a, 'b :: var, 'c :: var, 'd, 'e, 'f) F \<Rightarrow> 'e set"
consts set5_F :: "('a, 'b :: var, 'c :: var, 'd, 'e, 'f) F \<Rightarrow> 'f set"
consts rrel_F :: "('a \<Rightarrow> 'a' \<Rightarrow> bool) \<Rightarrow> ('e \<Rightarrow> 'e' \<Rightarrow> bool) \<Rightarrow> ('f \<Rightarrow> 'f' \<Rightarrow> bool) \<Rightarrow> ('a, 'b :: var, 'c :: var, 'd, 'e, 'f) F \<Rightarrow> ('a', 'b, 'c, 'd, 'e', 'f') F \<Rightarrow> bool"

mrbnf "('a, 'b :: var, 'c :: var, 'd, 'e, 'f) F"
  map: map_F
  sets: live: set1_F bound: set2_F free: set3_F live: set4_F live: set5_F 
  bd: natLeq
  rel: rrel_F
  var_class: var
  sorry

print_theorems

subsection "G"
typedecl ('a, 'b, 'c, 'd, 'e, 'f) G
consts map_G :: "('a \<Rightarrow> 'a') \<Rightarrow> ('b \<Rightarrow> 'b') \<Rightarrow>
  ('c \<Rightarrow> 'c') \<Rightarrow> ('d \<Rightarrow> 'd') \<Rightarrow> ('e  \<Rightarrow> 'e') \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) G \<Rightarrow> ('a', 'b', 'c', 'd', 'e', 'f) G"
consts set1_G :: "('a, 'b , 'c , 'd, 'e , 'f) G \<Rightarrow> 'a set"
consts set2_G :: "('a, 'b , 'c , 'd, 'e , 'f) G \<Rightarrow> 'b set"
consts set3_G :: "('a, 'b , 'c , 'd, 'e , 'f) G \<Rightarrow> 'c set"
consts set4_G :: "('a, 'b , 'c , 'd, 'e , 'f) G \<Rightarrow> 'd set"
consts set5_G :: "('a, 'b , 'c , 'd, 'e , 'f) G \<Rightarrow> 'e set"
consts rrel_G :: "('a \<Rightarrow> 'a' \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b' \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'c' \<Rightarrow> bool) \<Rightarrow> 
  ('d \<Rightarrow> 'd' \<Rightarrow> bool) \<Rightarrow> ('e \<Rightarrow> 'e' \<Rightarrow> bool) \<Rightarrow> ('a, 'b , 'c , 'd, 'e, 'f) G \<Rightarrow> ('a', 'b', 'c', 'd', 'e', 'f) G \<Rightarrow> bool"
consts wit1_G :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) G"
consts wit2_G :: "'c \<Rightarrow> 'd \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) G"
consts wit3_G :: "'b \<Rightarrow> 'e \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) G"

mrbnf "('a, 'b, 'c, 'd, 'e, 'f) G" 
  map: map_G
  sets: live: set1_G live: set2_G live: set3_G live: set4_G live: set5_G
  bd: natLeq
  wits:
    "wit1_G :: 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) G"
    "wit2_G :: 'c \<Rightarrow> 'd \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) G"
    "wit3_G :: 'b \<Rightarrow> 'e \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) G"
  rel: rrel_G
  var_class: var
  sorry


consts wit1_lG :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) G" 
consts wit2_lG :: "'a \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) G"
consts wit3_lG :: "('a, 'b, 'c, 'd, 'e, 'f) G"
consts wit4_lG :: "'c \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) G"


section "linearize"

subsection "L"
linearize_mrbnf ('a::var, 'b) L' = "('a::var, 'b) L" [wits:"witL :: ('a::var, 'b) L"] on 'a
  sorry

linearize_mrbnf ('a, 'b::var) L'' = "('a, 'b::var) L" on 'b 
  for eq_shape: sm_shp_L2 nonrep: nrp_shp_L2
  sorry

subsection "F"
linearize_mrbnf ('a, 'b::var, 'c::var, 'd, 'e::var, 'f::var) F'' = "('a, 'b::var, 'c::var, 'd, 'e::var, 'f::var) F" on 'f and 'e
  sorry

linearize_mrbnf (st1:'b::var, st2:'f , st3:'c::var , 'd, st4:'a::var , st5:'e) F''' = 
  "('a::var, 'b::var, 'c::var, 'd, 'e, 'f) F" on 'a for eq_shape: sm_shp_F3 nonrep: nrp_shp_F3
  sorry

subsection "G"
linearize_mrbnf ('a, 'b, 'c::var, 'd::var, 'e, 'f) lG = "('a, 'b, 'c::var, 'd::var, 'e, 'f) G" 
  [wits:"wit1_lG :: 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c::var, 'd::var, 'e, 'f) G" 
    "wit2_lG :: 'a \<Rightarrow> ('a, 'b, 'c::var, 'd::var, 'e, 'f) G"
    (*"wit3_lG :: ('a, 'b, 'c::var, 'd::var, 'e, 'f) G"*)] on 'd and 'c
  sorry

lemma set_empty_nonrep: "set3_G x = {} \<Longrightarrow> set4_G x = {} \<Longrightarrow> nonrep_G x"
  apply (unfold nonrep_G_def eq_shape_G_def)
  apply (intro allI impI exI[of _ id])
  apply (unfold G.map_id)
  apply (unfold mr_rel_G_def G.in_rel[unfolded mem_Collect_eq])
  apply (elim exE conjE)
  apply (hypsubst_thin)
  apply (unfold G.set_map)
  apply (rule G.map_cong)
       apply (auto)
  done

lemma nonrep_G_wit1: "nonrep_G (wit1_G a b)"
  apply (unfold nonrep_G_def eq_shape_G_def mr_rel_G_def G.in_rel mem_Collect_eq)
  apply (intro allI impI)
  apply (erule exE)
  apply (rule exI[of _ id])
  apply (rule exI[of _ id])
  apply (subst G.map_id)
  apply (elim conjE)
  apply (hypsubst_thin)
  apply (unfold triv_forall_equality) (*?*)
  apply (rule trans[OF sym, rotated])
   apply assumption
  apply (rule G.map_cong; (rule refl)?)
      apply (unfold split_paired_all fst_conv snd_conv)
      defer 3 (* lin_pos - idx *)
      defer 3
      apply (drule rev_subsetD, 
      assumption, 
      drule Set.CollectD, 
      subst (asm) case_prod_conv, 
      assumption)+

  apply (drule arg_cong[of _ _ set3_G])
  apply (subst (asm) G.set_map)
  apply (subst (asm) set_eq_iff)
  apply (subst (asm) image_iff)
  apply (drule spec)
  apply (drule iffD1)
   apply (rule bexI[rotated])
    apply assumption
    apply (rule fst_conv[symmetric])
  apply (drule G.wit1)
   apply (erule FalseE)

  apply (drule arg_cong[of _ _ set4_G])
  apply (subst (asm) G.set_map)
  apply (subst (asm) set_eq_iff)
  apply (subst (asm) image_iff)
  apply (drule spec)
  apply (drule iffD1)
   apply (rule bexI[rotated])
    apply assumption
   apply (rule fst_conv[symmetric])
  apply (drule G.wit1)
  apply (erule FalseE)
  done


lemma "x \<in> set1_lG (Abs_lG (wit1_G a b)) \<Longrightarrow> x = a"
      "x \<in> set2_lG (Abs_lG (wit1_G a b)) \<Longrightarrow> x = b"
      "x \<in> set3_lG (Abs_lG (wit1_G a b)) \<Longrightarrow> False"
      "x \<in> set4_lG (Abs_lG (wit1_G a b)) \<Longrightarrow> False"
     apply (unfold set1_lG_def set2_lG_def set3_lG_def set4_lG_def o_apply)
  apply (unfold Abs_lG_inverse[unfolded mem_Collect_eq, OF nonrep_G_wit1])
  apply (erule G.wit1)+
  done

subsection "dpair"
linearize_mrbnf 'a :: var dpair = "('a ::var \<times> 'a)" on 'a for eq_shape: ident_dpair nonrep: distinct_dpair
proof -
  obtain a where "(a::'a) \<in> UNIV"
    by simp
  define b where bsrc: "b = (SOME b. b \<noteq> a)"
  show ?thesis
    apply (rule exI[of _ "(a, b)"])
    apply (intro allI impI)
    apply (unfold rel_prod.simps map_prod_def)
    apply (elim exE conjE)
    apply (simp)
    apply (hypsubst_thin)
  apply (unfold triv_forall_equality)
    subgoal for a' b'
      apply (rule exI[of _ "(\<lambda>x. if x = a then a' else b')"])
      apply (unfold bsrc)
      by (metis (full_types) verit_sko_forall)
    done
qed

thm distinct_dpair_def
thm ident_dpair_def

lemma ident_dpair_top: "ident_dpair = top"
  apply (unfold ident_dpair_def prod.mr_rel_dpair_prod_def rel_prod.simps 
      map_prod_def id_bnf_apply id_apply top_fun_def top_bool_def)
  apply (simp)
  done

lemma "a \<noteq> (b :: 'a ::var) \<Longrightarrow> distinct_dpair (a, b)"
  apply (unfold distinct_dpair_def ident_dpair_top top_fun_def top_bool_def)
  apply (intro iffI allI)
  apply (simp)
  subgoal for p
    apply (rule exI[of _ "(\<lambda>x. if x = a then fst p else snd p)"])
    apply (simp)
    done
  done




subsection "other"
linearize_mrbnf '\<alpha> :: var distinct_list = "('\<alpha> ::var) list" on '\<alpha>
  done

linearize_mrbnf ('a::var, 'b) pair = "('a \<times> 'b) \<times> ('a::var)" on 'a
  sorry
  

datatype 'a success = S1 | S2 "'a \<Rightarrow> 'a success"
datatype 'a fail = F1 | F2 "'a fail \<Rightarrow> 'a"




end