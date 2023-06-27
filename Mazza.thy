theory Mazza
  imports
   "thys/MRBNF_Recursor"
   "HOL-Library.Stream"
   "HOL-Library.Prefix_Order"
   "HOL-Library.Countable_Set_Type"
begin

(*untyped lambda calculus*)
(* binder_datatype 'a lam =
  Var 'a
| App "'a lam" "'a lam"
| Abs x::'a t::"'a lam" binds x in t
*)

ML \<open>
val ctors = [
  (("Var", (NONE : mixfix option)), [@{typ 'var}]),
  (("App", NONE), [@{typ 'rec}, @{typ "'rec"}]),
  (("Abs", NONE), [@{typ "'bvar"}, @{typ 'brec}])
]

val spec = {
  fp_b = @{binding "lam"},
  vars = [
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[0]],
  rec_vars = 2,
  ctors = ctors,
  map_b = @{binding vvsubst},
  tvsubst_b = @{binding tvsubst}
}
\<close>

declare [[mrbnf_internals]]
local_setup \<open> MRBNF_Sugar.create_binder_datatype spec \<close>
print_mrbnfs

abbreviation "fv \<equiv> FFVars_lam"

coinductive sdistinct where
  "x \<notin> sset s \<Longrightarrow> sdistinct s \<Longrightarrow> sdistinct (x ## s)"

lemma sdistinct_stl: "sdistinct s \<Longrightarrow> sdistinct (stl s)"
  by (erule sdistinct.cases) simp

lemma sdistinct_fromN[simp]: "sdistinct (fromN n)"
  by (coinduction arbitrary: n) (subst siterate.code,  auto)

lemma sdistinct_smap: "inj_on f (sset s) \<Longrightarrow> sdistinct s \<Longrightarrow> sdistinct (smap f s)"
  by (coinduction arbitrary: s)
    (auto simp: smap_ctr stream.set_map inj_on_def stream.set_sel sdistinct_stl elim: sdistinct.cases)

class infinite_regular = 
  assumes large: "|Field (card_suc natLeq)| \<le>o |UNIV::'a set|" and regular: "regularCard |UNIV::'a set|"

lemma infinite_natLeq: "natLeq \<le>o |A| \<Longrightarrow> infinite A"
  using infinite_iff_natLeq_ordLeq by blast

lemma infinite: "infinite (UNIV :: 'a ::infinite_regular set)"
  using ordLeq_transitive[OF ordLess_imp_ordLeq[OF card_suc_greater_set[OF natLeq_card_order ordLeq_refl[OF natLeq_Card_order]]]
    ordIso_ordLeq_trans[OF ordIso_symmetric[OF card_of_Field_ordIso[OF Card_order_card_suc[OF natLeq_card_order]]] large]]
  by (rule infinite_natLeq)

lemma infinite_ex_inj: "\<exists>f :: nat \<Rightarrow> 'a :: infinite_regular. inj f"
  by (rule infinite_countable_subset[OF infinite, simplified])

typedef 'a dstream = "{xs :: 'a :: infinite_regular stream. sdistinct xs}"
  by (auto intro!: exI[of _ "smap (SOME f :: nat \<Rightarrow> 'a. inj f) nats"] sdistinct_smap
    someI_ex[OF infinite_ex_inj])

setup_lifting type_definition_dstream

lift_definition dsmap :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a dstream \<Rightarrow> 'a :: infinite_regular dstream" is
  "\<lambda>f xs. if bij f then smap f xs else xs"
  by (auto simp: bij_def intro!: sdistinct_smap elim: inj_on_subset)

lift_definition dsset :: "'a :: infinite_regular dstream \<Rightarrow> 'a set" is "sset" .

lift_definition dsnth :: "'a :: infinite_regular dstream \<Rightarrow> nat \<Rightarrow> 'a" (infixl \<open>!#!\<close> 100) is "snth" .

lemma countable_sset:
  fixes s
  notes * = LeastI[where P="\<lambda>i. s !! i = s !! _", OF refl]
  shows "countable (sset s)"
  unfolding sset_range
  by (intro countableI[where f="\<lambda>x. LEAST i. snth s i = x"] inj_onI, elim imageE, hypsubst_thin)
    (rule box_equals[OF _ * *], simp)

mrbnf "'a ::infinite_regular dstream"
  map: dsmap
  sets: bound: dsset
  bd: "card_suc natLeq"
  var_class: infinite_regular
  subgoal by (rule ext, transfer) (simp add: stream.map_id)
  subgoal by (rule ext, transfer) (simp add: stream.map_comp)
  subgoal by transfer (simp cong: stream.map_cong)
  subgoal by (rule ext, transfer) (simp add: stream.set_map)
  subgoal by (rule infinite_regular_card_order_card_suc[OF natLeq_card_order natLeq_Cinfinite])
  subgoal
    apply (rule card_suc_greater_set[OF natLeq_card_order])
    apply transfer
    apply (simp flip: countable_card_le_natLeq add: countable_sset)
    done
  subgoal by blast
  subgoal by (clarsimp, transfer) (auto simp: stream.map_id)
  done

(*infinitary untyped lambda calculus*)
(* binder_datatype 'a ilam =
  Bot
| Var 'a
| App "'a ilam" "'a ilam stream"
| Abs xs::'a dstream t::"'a ilam" binds xs in t
*)

ML \<open>
val ctors = [
  (("iVar", (NONE : mixfix option)), [@{typ 'var}]),
  (("iApp", NONE), [@{typ 'rec}, @{typ "'rec stream"}]),
  (("iAbs", NONE), [@{typ "'bvar dstream"}, @{typ 'brec}])
]

val spec = {
  fp_b = @{binding "ilam"},
  vars = [
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[0]],
  rec_vars = 2,
  ctors = ctors,
  map_b = @{binding ivvsubst},
  tvsubst_b = @{binding itvsubst}
}
\<close>

declare [[mrbnf_internals]]
local_setup \<open> MRBNF_Sugar.create_binder_datatype spec \<close>
print_mrbnfs

lemma ex_inj_infinite_regular_var_ilam_pre: "\<exists>f :: 'a :: infinite_regular \<Rightarrow> 'b :: var_ilam_pre. inj f"
  sorry

definition embed :: "'a :: {countable, infinite_regular} \<Rightarrow> 'b :: var_ilam_pre"
  ("{{_}}" [999] 1000)  where
  "embed = (SOME f. inj f)"

lemma inj_embed: "inj embed"
  unfolding embed_def
  apply (rule someI_ex[of inj])
  apply (insert ex_inj[where 'a='a] infinite_ex_inj[where 'a='a]
    ex_inj_infinite_regular_var_ilam_pre[where 'a='a and 'b='b])
  apply (elim exE)
  subgoal for to_nat to_inf_reg to_var_ilam_pre
    apply (rule exI[of _ "to_var_ilam_pre o to_inf_reg o to_nat"])
    apply (rule inj_compose | assumption)+
    done
  done

abbreviation "ifv \<equiv> FFVars_ilam"

inductive affine where
  "affine (iVar x)"
| "affine t \<Longrightarrow> affine (iAbs xx t)"
| "affine t \<Longrightarrow>
   \<forall>u \<in> sset uu. affine u \<and> ifv t \<inter> ifv u = {} \<Longrightarrow>
   \<forall>i j. i < j \<longrightarrow> ifv (uu !! i) \<inter> ifv (uu !! j) = {} \<Longrightarrow>
   affine (iApp t uu)"

consts lam_ilam :: "'a :: {countable, infinite_regular, var_lam_pre} lam \<Rightarrow> nat list \<Rightarrow> 'b :: var_ilam_pre ilam"  ("\<lbrakk>_\<rbrakk>_" [999, 1000] 1000)
consts ilam_lam :: "'b :: var_ilam_pre ilam \<Rightarrow> 'a :: {countable, infinite_regular, var_lam_pre} lam"  ("\<lparr>_\<rparr>" [999] 1000)


locale \<VV> =
  fixes super :: "'b ::var_ilam_pre \<Rightarrow> 'b dstream" ("\<lbrace>_\<rbrace>" [999] 1000)
  assumes in_super: "x \<in> dsset \<lbrace>x\<rbrace>"
  and disjoint_super: "\<lbrace>x\<rbrace> \<noteq> \<lbrace>y\<rbrace> \<Longrightarrow> dsset \<lbrace>x\<rbrace> \<inter> dsset \<lbrace>y\<rbrace> = {}"
begin

inductive renaming (infix "\<approx>" 65) where
  "\<lbrace>x\<rbrace> = \<lbrace>y\<rbrace> \<Longrightarrow> iVar x \<approx> iVar y"
| "t \<approx> t' \<Longrightarrow> iAbs \<lbrace>x\<rbrace> t \<approx> iAbs \<lbrace>x\<rbrace> t'"
| "t \<approx> t' \<Longrightarrow> uu !! 0 \<approx> u' !! 0 \<Longrightarrow> (\<forall>i j. uu !! i \<approx> uu !! j) \<Longrightarrow> (\<forall>i j. uu' !! i \<approx> uu' !! j) \<Longrightarrow>
   iApp t uu \<approx> iApp t' uu'"

definition uniform where "uniform t = (t \<approx> t)"

lemma lam_ilam_simps[simp]:
  "\<lbrakk>Var x\<rbrakk>a = iVar (\<lbrace>{{x}}\<rbrace> !#! (list_encode a))"
  "\<lbrakk>Abs x M\<rbrakk>a = iAbs \<lbrace>{{x}}\<rbrace> (\<lbrakk>M\<rbrakk>a)"
  "\<lbrakk>App M N\<rbrakk>a = iApp \<lbrakk>M\<rbrakk>(0#a) (smap (\<lambda>i. \<lbrakk>N\<rbrakk>((i + 1) # a)) nats)"
  sorry

lemma ifv_lam_ilam_disjoint: 
  fixes M N :: "'a :: {countable, infinite_regular, var_lam_pre} lam"
  assumes "\<not>a \<le> a'" "\<not>a' \<le> a"
  shows "ifv (\<lbrakk>M\<rbrakk>a :: 'b ilam) \<inter> ifv (\<lbrakk>N\<rbrakk>a' :: 'b ilam) = {}"
  sorry

lemma
  fixes M :: "'a :: {countable, infinite_regular, var_lam_pre} lam"
  shows "affine (\<lbrakk>M\<rbrakk>a :: 'b ilam)"
  by (induct M arbitrary: a)
    (fastforce simp: stream.set_map intro!: affine.intros
      elim: ifv_lam_ilam_disjoint[unfolded disjoint_iff, rule_format, THEN notE, of _ _ _ _ _ False, rotated 2])+

end

find_theorems list_encode

end


























typedef 'a dlist = "{xs :: 'a list. distinct xs}"
  by auto

setup_lifting type_definition_dlist

lift_definition map_dlist :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist" is
  "\<lambda>f xs. if bij f then map f xs else xs"
  by (auto simp: distinct_map bij_def elim: inj_on_subset)

lift_definition set_dlist :: "'a dlist \<Rightarrow> 'a set" is "set" .

lift_definition dNil :: "'a dlist" is "[]" by simp

mrbnf "'a dlist"
  map: map_dlist
  sets: bound: set_dlist
  bd: natLeq
  wits: dNil
  subgoal by (rule ext, transfer) simp
  subgoal by (rule ext, transfer) simp
  subgoal by transfer simp
  subgoal by (rule ext, transfer) simp
  subgoal by (rule infinite_regular_card_order_natLeq)
  subgoal by transfer (simp flip: finite_iff_ordLess_natLeq)
  subgoal by blast
  subgoal by (clarsimp, transfer) auto
  done

typedef 'a dllist = "{xs :: 'a llist. ldistinct xs}"
  by (auto intro!: exI[of _ "LNil"])

setup_lifting type_definition_dllist

lift_definition map_dllist :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a dllist \<Rightarrow> 'a dllist" is
  "\<lambda>f xs. if bij f then lmap f xs else xs"
  by (auto simp: bij_def  elim: inj_on_subset)

lift_definition set_dllist :: "'a dllist \<Rightarrow> 'a set" is "lset" .

lift_definition dLNil :: "'a dllist" is "LNil" by simp

mrbnf "'a dllist"
  map: map_dllist
  sets: bound: set_dllist
  bd: "card_suc natLeq"
  wits: dLNil
  subgoal by (rule ext, transfer) simp
  subgoal by (rule ext, transfer) (simp add: llist.map_comp)
  subgoal by transfer simp
  subgoal by (rule ext, transfer) simp
  subgoal by (simp add: infinite_regular_card_order_card_suc natLeq_Card_order natLeq_card_order natLeq_cinfinite)
  subgoal apply (rule card_suc_greater_set[OF natLeq_card_order])
    apply transfer
    subgoal for xs
      unfolding countable_card_le_natLeq[symmetric] countable_def inj_on_def
      thm bchoice_iff
      apply (auto simp: inj_on_def)
      find_theorems "Least _ = Least _"
    find_theorems "countable _ \<longleftrightarrow> _"
    find_consts "_ llist \<Rightarrow> _"
  subgoal by blast
  subgoal by (clarsimp, transfer) auto
  done

(*
coinductive sdistinct where
  "x \<notin> sset s \<Longrightarrow> sdistinct s \<Longrightarrow> sdistinct (x ## s)"

lemma sdistinct_stl: "sdistinct s \<Longrightarrow> sdistinct (stl s)"
  by (erule sdistinct.cases) simp

lemma sdistinct_fromN[simp]: "sdistinct (fromN n)"
  by (coinduction arbitrary: n) (subst siterate.code,  auto)

lemma sdistinct_smap: "inj_on f (sset s) \<Longrightarrow> sdistinct s \<Longrightarrow> sdistinct (smap f s)"
  by (coinduction arbitrary: s)
    (auto simp: smap_ctr stream.set_map inj_on_def stream.set_sel sdistinct_stl elim: sdistinct.cases)

class infinite = assumes infinite: "infinite (UNIV :: 'a set)"

lemma infinite_ex_inj: "\<exists>f :: nat \<Rightarrow> 'a :: infinite. inj f"
  by (rule infinite_countable_subset[OF infinite, simplified])

typedef 'a dstream = "{xs :: 'a :: infinite stream. sdistinct xs}"
  by (auto intro!: exI[of _ "smap (SOME f :: nat \<Rightarrow> 'a. inj f) nats"] sdistinct_smap
    someI_ex[OF infinite_ex_inj])

setup_lifting type_definition_dstream

lift_definition map_dstream :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a dstream \<Rightarrow> 'a :: infinite dstream" is
  "\<lambda>f xs. if bij f then smap f xs else xs"
  by (auto simp: bij_def intro!: sdistinct_smap elim: inj_on_subset)

lift_definition set_dstream :: "'a :: infinite dstream \<Rightarrow> 'a set" is "sset" .

mrbnf "'a ::infinite dstream"
  map: map_dstream
  sets: bound: set_dstream
  bd: natLeq
  subgoal apply (rule ext, transfer)
    using [[show_consts]]
    apply simp
(*
  subgoal by (rule ext, transfer) simp
  subgoal by transfer simp
  subgoal by (rule ext, transfer) simp
  subgoal by (rule infinite_regular_card_order_natLeq)
  subgoal by transfer (simp flip: finite_iff_ordLess_natLeq)
  subgoal by blast
  subgoal by (clarsimp, transfer) auto
  done
*)
*)



setup_lifting type_definition_dlist

lift_definition map_dlist :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist" is
  "\<lambda>f xs. if bij f then map f xs else xs"
  by (auto simp: distinct_map bij_def elim: inj_on_subset)

lift_definition set_dlist :: "'a dlist \<Rightarrow> 'a set" is "set" .
  

(*polyadic untyped lambda calculus*)
(* binder_datatype 'a polylc =
  Bot
| Var 'a
| App "'a polylc" "'a polylc list"
| Abs xs::'a dlist t::"'a terms" binds xs in t
*)

ML \<open>
val ctors = [
  (("Var", (NONE : mixfix option)), [@{typ 'var}]),
  (("App", NONE), [@{typ 'rec}, @{typ "'rec llist"}]),
  (("Abs", NONE), [@{typ "('bvar \<times> \<tau>) llist"}, @{typ 'brec}])
]

val spec = {
  fp_b = @{binding "terms"},
  vars = [
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[0]],
  rec_vars = 2,
  ctors = ctors,
  map_b = @{binding vvsubst},
  tvsubst_b = @{binding tvsubst}
}
\<close>

declare [[mrbnf_internals]]
local_setup \<open>fn lthy =>
let
  val lthy' = MRBNF_Sugar.create_binder_datatype spec lthy
in lthy' end\<close>
print_mrbnfs

(*infinitary untyped lambda calculus*)
(* binder_datatype 'a inflc =
  Bot
| Var 'a
| App "'a inflc" "'a inflc stream"
| Abs xs::'a dstream t::"'a inflc" binds xs in t
*)

end
