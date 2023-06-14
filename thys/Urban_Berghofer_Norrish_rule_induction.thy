(* We show that the Urban-Berghofer-Norrish (UBN) syntactic criterion 
for Barendregt-enhanced induction is a particular case 
of (the weak form of) our theorem. 
*)
theory Urban_Berghofer_Norrish_rule_induction 
imports Generic_Barendregt_Enhanced_Rule_Induction 
"Instantiation_Infrastructure/FixedCountableVars"
begin


(* variable-variables and term-variables: *)
type_synonym vvar = nat 
type_synonym tvar = nat 
(* schematic terms *)
datatype 'O sT = Tvar tvar | Sabs vvar "'O sT" | Sop 'O "'O sT list"

type_synonym 'O sT_tuple = "'O sT list"
type_synonym 'T T_tuple = "'T list" 

(* Side-conditions, coming with a "side predicate" and a "side tuple": *)
datatype ('O,'T) scond = Scond (spred: "'T T_tuple \<Rightarrow> bool") (stuple: "'O sT_tuple")

 (* Rules are meant to be intepreted on the type 'T, this is why the side-conditions 
come with predicates on 'T tuples of specified arities *)
datatype ('O,'T) rule = Rule 
  (hyps: "'O sT_tuple list") 
  (side: "('O,'T) scond list")
  (conc: "'O sT_tuple")


(* Well-formed schematic terms according to an arity specification *)
fun wfST :: "('O \<Rightarrow> nat) \<Rightarrow> 'O sT \<Rightarrow> bool" where 
"wfST ar (Tvar tv) \<longleftrightarrow> True"
|
"wfST ar (Sabs vv st) \<longleftrightarrow> wfST ar st"
|
"wfST ar (Sop op sts) \<longleftrightarrow> (length sts = ar op) \<and> (\<forall>st \<in> set sts. wfST ar st)"

fun wfST_tuple :: "('O \<Rightarrow> nat) \<Rightarrow> 'O sT_tuple \<Rightarrow> bool" where 
"wfST_tuple ar sts \<longleftrightarrow> (\<forall>st \<in> set sts. wfST ar st)"


(* well-formed rule according to an operation-arity spec "ar" and a number "n": 
-- they have all tuples well-formed 
-- have all hypotheses and the conclusion of fixed length n 
(NB: the side-conditions are allowed any arities)
*)
definition wfR where 
"wfR ar n rl \<equiv> 
  (\<forall>sts \<in> set (hyps rl) \<union> {conc rl}. wfST_tuple ar sts \<and> length sts = n) \<and> 
  (\<forall>pred ss. Scond pred ss \<in> set (side rl) \<longrightarrow> wfST_tuple ar ss)"

(* It seems that we do need the "vars" operator from UBN; 
they do not use it in their result *)
fun varsbp :: "'O sT \<Rightarrow> vvar set" where 
"varsbp (Tvar tv) = {}"
|
"varsbp (Sabs vv st) = varsbp st - {vv}"
|
"varsbp (Sop op sts) = \<Union> (varsbp ` (set sts))"

fun varsbp_tuple :: "'O sT_tuple \<Rightarrow> vvar set" where 
"varsbp_tuple sTs = \<Union> (varsbp ` (set sTs))"

(* Extension to rules: *)
definition varsbpR where 
"varsbpR rl = 
  (\<Union> (varsbp_tuple ` (set (hyps rl)))) \<union>
  (\<Union> ((varsbp_tuple o stuple) ` (set (side rl)))) \<union>
  varsbp_tuple (conc rl) "

lemma finite_varsbp: "finite (varsbp st)"
by (induct st, auto)

lemma finite_varsbp_tuple: "finite (varsbp_tuple sts)"
using finite_varsbp by auto

lemma finite_varsbpR: "finite (varsbpR rl)"
unfolding varsbpR_def using finite_varsbp_tuple by auto

locale UBN_Components = Small dummy 
for dummy :: 'A 
+
fixes (* 'T: term-like entities *)
Tmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tfvars :: "'T \<Rightarrow> 'A set"
(* *)
and 
Abs :: "'A \<Rightarrow> 'T \<Rightarrow> 'T" 
and 
Op :: "'O \<Rightarrow> 'T list \<Rightarrow> 'T" 
and 
arity :: "'O \<Rightarrow> nat"
assumes  
Tmap_id: "Tmap id = id"
and 
Tmap_comp: "\<And>\<sigma> \<tau>. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Tmap (\<sigma> o \<tau>) = Tmap \<sigma> o Tmap \<tau>"
and 
small_Tfvars: "\<And>t. small (Tfvars t)" 
and (* the weaker, inclusion-based version is sufficient (and similarly for V): *)
Tmap_Tfvars: "\<And>t \<sigma>. ssbij \<sigma> \<Longrightarrow> Tfvars (Tmap \<sigma> t) \<subseteq> \<sigma> ` (Tfvars t)"
and 
Tmap_cong_id: "\<And>t \<sigma>. ssbij \<sigma> \<Longrightarrow> (\<forall>a\<in>Tfvars t. \<sigma> a = a) \<Longrightarrow> Tmap \<sigma> t = t"
(* so far, the above was a common part with our "Components" locale *)
and
(* Equivariance of abstraction and of the operations (the first variable-convention compatibility 
convention from UBN): *)
Abs_equiv: "\<And>\<sigma> a t. ssbij \<sigma> \<Longrightarrow> Tmap \<sigma> (Abs a t) = Abs (\<sigma> a) (Tmap \<sigma> t)"
and
Op_equiv: "\<And>\<sigma> op ts. ssbij \<sigma> \<Longrightarrow> length ts = arity op \<Longrightarrow> Tmap \<sigma> (Op op ts) = Op op (map (Tmap \<sigma>) ts)"
begin

lemma Tmap_comp': "ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Tmap (\<sigma> o \<tau>) t = Tmap \<sigma> (Tmap \<tau> t)"
using Tmap_comp by fastforce 

(* Extension of the term infrastructure to term-tuples: *)
(* *) 
fun Tfvars_tuple :: "'T T_tuple \<Rightarrow> 'A set" where 
"Tfvars_tuple ts = \<Union> (Tfvars ` (set ts))"

fun Tmap_tuple :: "('A \<Rightarrow> 'A) \<Rightarrow> 'T T_tuple \<Rightarrow> 'T T_tuple" where 
"Tmap_tuple f ts = map (Tmap f) ts"

lemma Tmap_tuple_id: "Tmap_tuple id = id"
using Tmap_id by auto

lemma Tmap_tuple_comp: "ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Tmap_tuple (\<sigma> o \<tau>) = Tmap_tuple \<sigma> o Tmap_tuple \<tau>"
using Tmap_comp by auto

lemma small_Tfvars_tuple: "small (Tfvars_tuple ts)" 
by (auto intro: finite_UN_small simp: small_Tfvars)

lemma Tmap_tuple_Tfvars_tuple: 
"ssbij \<sigma> \<Longrightarrow> Tfvars_tuple (Tmap_tuple \<sigma> ts) \<subseteq> \<sigma> ` (Tfvars_tuple ts)"
using Tmap_Tfvars by fastforce

lemma Tmap_tuple_cong_id: "ssbij \<sigma> \<Longrightarrow> (\<forall>a\<in>Tfvars_tuple ts. \<sigma> a = a) \<Longrightarrow> Tmap_tuple \<sigma> ts = ts"
by (simp add: Tmap_cong_id map_idI) 

lemma Tmap_tuple_comp': "ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Tmap_tuple (\<sigma> o \<tau>) ts = Tmap_tuple \<sigma> (Tmap_tuple \<tau> ts)"
using Tmap_tuple_comp by fastforce

(* Interpretation of schematic terms: *)
fun it :: "(vvar \<Rightarrow> 'A) \<Rightarrow> (tvar \<Rightarrow> 'T) \<Rightarrow> 'O sT \<Rightarrow> 'T" where 
"it vval tval (Tvar tv) = tval tv"
|
"it vval tval (Sabs vv st) = Abs (vval vv) (it vval tval st)"
|
"it vval tval (Sop op sts)= Op op (map (it vval tval) sts)"

fun it_tuple :: "(vvar \<Rightarrow> 'A) \<Rightarrow> (tvar \<Rightarrow> 'T) \<Rightarrow> 'O sT_tuple \<Rightarrow> 'T T_tuple" where 
"it_tuple vval tval sts = map (it vval tval) sts"

(* Consequences of the equivariance assumptions: *)

lemma it_Tmap: "ssbij \<sigma> \<Longrightarrow> wfST arity st \<Longrightarrow> Tmap \<sigma> (it vval tval st) = it (\<sigma> \<circ> vval) (Tmap \<sigma> \<circ> tval) st" 
apply(induct st, simp_all) 
using Abs_equiv apply simp_all
by (smt (verit) Op_equiv comp_apply length_map list.map_comp map_eq_conv)

lemma it_tuple_Tmap_tuple: "ssbij \<sigma> \<Longrightarrow> 
wfST_tuple arity sts \<Longrightarrow> 
Tmap_tuple \<sigma> (it_tuple vval tval sts) = it_tuple (\<sigma> \<circ> vval) (Tmap \<sigma> \<circ> tval) sts"
using it_Tmap by auto

end (* locale UBN_Components *)

(* TODO: eventually switch from 'T to "'T list" to better match UBN *)
locale UBN = UBN_Components dummy Tmap Tfvars Abs Op arity 
for dummy :: 'A 
and Tmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T" and Tfvars :: "'T \<Rightarrow> 'A set"
(* *)
and Abs :: "'A \<Rightarrow> 'T \<Rightarrow> 'T" and Op :: "'O \<Rightarrow> 'T list \<Rightarrow> 'T" 
and arity :: "'O \<Rightarrow> nat"
+ 
fixes 
n :: nat
and rules :: "('O,'T) rule set"
assumes
wfR_rules: 
"\<And>rl. rl \<in> rules \<Longrightarrow> wfR arity n rl"
and 
(* *)
side_equiv: (* The side-conditions in the rules must be equivariant: *)
"\<And>rl \<sigma> pred ss. rl \<in> rules \<Longrightarrow> ssbij \<sigma> \<Longrightarrow> 
    Scond pred ss \<in> set (side rl) \<Longrightarrow> pred (it_tuple vval tval ss) \<Longrightarrow> 
    pred (Tmap_tuple \<sigma> (it_tuple vval tval ss))"
and 
VCcomp2: (* the second variable-convention compatibility condition from UBN: *)
"\<And>rl vval tval. rl \<in> rules \<Longrightarrow> 
   (\<forall>pred ss. Scond pred ss \<in> set (side rl) \<longrightarrow> pred (it_tuple vval tval ss)) \<Longrightarrow> 
   vval ` (varsbpR rl) \<inter> Tfvars_tuple (it_tuple vval tval (conc rl)) = {}"
begin

definition G' where 
"G' \<equiv> (\<lambda>R ts. \<exists>rl vval tval.
  ts = it_tuple vval tval (conc rl) \<and>
  rl \<in> rules \<and> 
  (\<forall>pred ss. Scond pred ss \<in> set (side rl) \<longrightarrow> pred (it_tuple vval tval ss)) \<and> 
  (\<forall>ts\<in>set (hyps rl). R (it_tuple vval tval ts)))"

definition G  :: "('T T_tuple \<Rightarrow> bool) \<Rightarrow> 'A list \<Rightarrow> 'T T_tuple \<Rightarrow> bool" where 
"G \<equiv> (\<lambda>R xs ts. \<exists>rl vval tval.
  set xs = vval ` (varsbpR rl) \<and> 
  ts = it_tuple vval tval (conc rl) \<and>
  rl \<in> rules \<and> 
  (\<forall>pred ss. Scond pred ss \<in> set (side rl) \<longrightarrow> pred (it_tuple vval tval ss)) \<and> 
  (\<forall>ts\<in>set (hyps rl). R (it_tuple vval tval ts)))"

lemma ex_comm2: "(\<exists>x y z. P x y z) = (\<exists>y z x . P x y z)" by auto

lemma G'_G: "G' R ts = (\<exists>xs. G R xs ts)"
unfolding G_def G'_def fun_eq_iff apply safe 
  subgoal for rl vval tval
  apply(subst ex_comm2)
  apply(rule exI[of _ rl]) apply(rule exI[of _ vval])
  apply(subgoal_tac "\<exists>xs. set xs = vval ` varsbpR rl")
    subgoal by auto
    subgoal by (simp add: finite_list finite_varsbpR) . 
  subgoal by auto .

inductive II :: "'T T_tuple \<Rightarrow> bool" where 
"rl \<in> rules \<Longrightarrow> 
 (\<forall>pred ss. Scond pred ss \<in> set (side rl) \<longrightarrow> pred (it_tuple vval tval ss)) \<Longrightarrow> 
 (\<forall>ts\<in>set (hyps rl). II (it_tuple vval tval ts)) \<Longrightarrow>
 II (it_tuple vval tval (conc rl))"

lemma II_G': "II = lfp G'"
unfolding II_def G'_def ..

lemma II_def2: "II = lfp (\<lambda>R t. \<exists>xs. G R xs t)"
unfolding II_G' G'_G ..

type_synonym 'a V = "'a list"
definition Vmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'A V \<Rightarrow> 'A V" where "Vmap \<equiv> map"
definition Vfvars :: "'A V \<Rightarrow> 'A set" where "Vfvars \<equiv> set"

lemma Vmap_comp: "ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Vmap (\<sigma> o \<tau>) = Vmap \<sigma> o Vmap \<tau>"
unfolding Vmap_def by auto

lemma small_Vfvars: "small (Vfvars v)" 
unfolding Vfvars_def small_def by (simp add: inf_A)

lemma Vmap_Vfvars: "ssbij \<sigma> \<Longrightarrow> Vfvars (Vmap \<sigma> v) \<subseteq> \<sigma> ` (Vfvars v)"
unfolding Vmap_def Vfvars_def by auto

lemma G_mono: "R \<le> R' \<Longrightarrow> G R v t \<Longrightarrow> G R' v t"
unfolding G_def le_fun_def by auto blast
 
lemma G_equiv: 
assumes "ssbij \<sigma>" "G R v ts" 
shows "G (\<lambda>t'. R (Tmap_tuple (inv \<sigma>) t')) (Vmap \<sigma> v) (Tmap_tuple \<sigma> ts)"
using assms unfolding G_def apply safe subgoal for rl vval tval
apply(rule exI[of _ rl]) apply(rule exI[of _ "\<sigma> o vval"])
apply(rule exI[of _ "Tmap \<sigma> o tval"]) apply(intro conjI)
  subgoal unfolding Vmap_def by auto
  subgoal apply(subst it_tuple_Tmap_tuple) using wfR_rules unfolding wfR_def by auto
  subgoal by auto
  subgoal apply safe subgoal for pred ss
  apply(subst it_tuple_Tmap_tuple[symmetric])
    subgoal by auto
    subgoal using wfR_rules unfolding wfR_def by auto
    subgoal apply(rule side_equiv) by auto . .  
  subgoal apply safe subgoal for ts 
  apply(subst it_tuple_Tmap_tuple[symmetric]) 
    subgoal by auto
    subgoal using wfR_rules unfolding wfR_def by auto
    subgoal apply(subst Tmap_tuple_comp'[symmetric])
      subgoal using ssbij_inv by presburger
      subgoal .
      subgoal by (simp add: Tmap_id ssbij_invR) . . . . .

lemma G_fresh_simple: 
assumes "G R v ts"
shows "Vfvars v \<inter> Tfvars_tuple ts = {}"
using assms unfolding G_def apply(elim exE conjE) 
subgoal for rl vval tval apply(frule VCcomp2) unfolding Vfvars_def by auto . 

end (* context UBN *)

 
(* The UBN result is subm=sumed by ours: *)
sublocale UBN < Induct_simple where dummy = dummy and Tmap = Tmap_tuple 
and Tfvars = Tfvars_tuple and Vmap = Vmap and Vfvars = Vfvars and G = G apply standard
using small_Tfvars_tuple Tmap_tuple_Tfvars_tuple Tmap_tuple_cong_id 
small_Vfvars G_equiv G_fresh_simple
by (auto simp: Tmap_id Tmap_comp' Vmap_comp Vmap_Vfvars G_mono)  




end