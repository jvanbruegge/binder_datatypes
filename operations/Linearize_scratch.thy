theory Linearize_scratch                                                      
  imports "Binders.MRBNF_Composition" "Binders.MRBNF_Recursor" "HOL-Library.FSet" "HOL-Library.Uprod"
begin

section "setup"
declare [[bnf_internals]]
declare [[mrbnf_internals]]
declare [[typedef_overloaded]]
declare [[ML_print_depth=1000]]

section "Example: Lambda calculus with parallel let and alist"
(* t := x | t\<^sub>1 t\<^sub>2 | (\<lambda>x. t) | let x\<^sub>1 = t\<^sub>1 and ... and x\<^sub>n = t\<^sub>n in t\<^sub>n\<^sub>+\<^sub>1 *)

linearize_mrbnf ('k::var,'v) alist = "('k::var \<times> 'v) list" on 'k for nonrep: list_distinct eq_shape: length_eq morphisms to_alist of_alist
  by (auto simp: list_eq_iff_nth_eq map_prod_def split_beta prod_eq_iff)

thm of_alist_inverse[unfolded list_distinct_def]
thm to_alist

thm map_alist_def

(* as datatype *)
datatype 'a ltrm' = Var' 'a | App' "'a ltrm'" "'a ltrm'" | Abs' 'a "'a ltrm'" 
  | Let' "('a \<times> 'a ltrm') list" "'a ltrm'"

(* as binder-datatype *)
binder_datatype 'a ltrm = Var 'a | App "'a ltrm" "'a ltrm" | Abs x::'a t::"'a ltrm" binds x in t
  | Let "(fs::'a, t::'a ltrm) alist" u::"'a ltrm" binds fs in t u

print_mrbnfs
print_bnfs

lemma "set_ltrm' (App' (Abs' ''a'' (Var' ''a'')) (Var' ''b'')) = {''a'', ''b''}"
  by auto

lemma "FVars_ltrm (App (Abs ''a'' (Var ''a'')) (Var ''b'')) = {''b''}"
  by auto


binder_datatype ('a, 'b::var) test = V 'b | C x::'b t::"('a, 'b) test" binds x in t

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

typedef 'a nrp_list = "{x :: 'a list. nonrep_list x}" morphisms of_nrp to_nrp
  apply (rule exI[of _ "[]"])
  apply (auto simp add: nonrep_list_def eq_shape_list_def)
  done

definition dist_set :: "'a nrp_list \<Rightarrow> 'a set" where
 "dist_set = set o of_nrp"

definition dist_map :: "('a \<Rightarrow> 'a') \<Rightarrow> 'a nrp_list \<Rightarrow> 'a' nrp_list" where
 "dist_map f x = to_nrp (remdups (map f (of_nrp x)))"


definition dist_rel :: "('a \<Rightarrow> 'a' \<Rightarrow> bool) \<Rightarrow> 'a nrp_list \<Rightarrow> 'a' nrp_list \<Rightarrow> bool" where
 "dist_rel R x y = list_all2 R (of_nrp x) (of_nrp y)"

bnf "'a nrp_list"
  map: "dist_map"
sets: dist_set
  bd: "natLeq"
  rel: "dist_rel"
  sorry

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

(* FAIL - not BNFs *)
(* datatype 'a test_A = F 'a | R "('a test_A) set" *)
(* datatype 'a test_B = MK "'a" | MK2 "('a test_B) even_list" *)

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

datatype 'a test_B = MK "'a" | MK2 "('a test_B) even_list"

linearize_mrbnf 'a::var lin_fset = "'a::var fset" on 'a
  done

binder_datatype 'a test_C = Leaf | MK2' "(r::'a) lin_fset" "s::'a test_C" binds r in s t


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


lemma Grp_conversep: "((Grp g)\<inverse>\<inverse>) = (\<lambda> x y. x = g y)"
  apply (unfold Grp_UNIV_def conversep.simps)
  apply (auto)
  done

(*list_all2 ((Grp fst)\<inverse>\<inverse> OO Grp snd) x y*)
lemma "list_all2 top x y \<Longrightarrow> list_all2 ((Grp fst)\<inverse>\<inverse> OO Grp snd) x y"
  apply (subst (asm) list.in_rel)
  apply (auto simp add: top_fun_def)
  apply (subst (asm) (2) eq_commute)
  apply (subst (asm) list.rel_eq[symmetric])
  apply (subst (asm) list.rel_eq[symmetric])
  apply (unfold list.rel_map)
  apply (unfold Grp_UNIV_def[of snd, symmetric] Grp_conversep[of fst, symmetric])
  subgoal premises prems for z
    apply (insert prems )
    apply (drule relcomppI[of "list_all2 (Grp fst)\<inverse>\<inverse>" x z "list_all2 (Grp snd)" y])
     apply (assumption)
    thm list.rel_compp
    by (simp add: Grp_UNIV_def list_all2_refl relcompp_apply)
  done

subsection "other"
linearize_mrbnf '\<alpha> :: var distinct_list = "('\<alpha> ::var) list" on '\<alpha>
  done

linearize_mrbnf ('a::var, 'b) pair = "('a \<times> 'b) \<times> ('a::var)" on 'a
  sorry
  

datatype 'a success = S1 | S2 "'a \<Rightarrow> 'a success"
(* FAIL - recursion on dead var *)
(* datatype 'a fail = F1 | F2 "'a fail \<Rightarrow> 'a" *)




end