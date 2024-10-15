(* We show that the Urban-Berghofer-Norrish (UBN) syntactic criterion 
for Barendregt-enhanced induction is a particular case 
of (the weak form of) our theorem. 
*)
theory Urban_Berghofer_Norrish_Rule_Induction 
imports Generic_Barendregt_Enhanced_Rule_Induction 
  "Prelim.FixedCountableVars"
begin


(* variable-(meta)variables and term-(meta)variables: *)
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

locale UBN_Components =
fixes (* 'T: term-like entities *)
Tperm :: "('A :: infinite \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tsupp :: "'T \<Rightarrow> 'A set"
(* *)
and 
Abs :: "'A \<Rightarrow> 'T \<Rightarrow> 'T" 
and 
Op :: "'O \<Rightarrow> 'T list \<Rightarrow> 'T" 
and 
arity :: "'O \<Rightarrow> nat"
assumes  
Tperm_id: "Tperm id = id"
and 
Tperm_comp: "\<And>\<sigma> \<tau>. isPerm \<sigma> \<Longrightarrow> isPerm \<tau> \<Longrightarrow> Tperm (\<sigma> o \<tau>) = Tperm \<sigma> o Tperm \<tau>"
and 
small_Tsupp: "\<And>t. small (Tsupp t)" 
and (* the weaker, inclusion-based version is sufficient (and similarly for V): *)
Tsupp_seminat: "\<And>t \<sigma>. isPerm \<sigma> \<Longrightarrow> Tsupp (Tperm \<sigma> t) \<subseteq> \<sigma> ` (Tsupp t)"
and 
Tsupp_supporting: "\<And>t \<sigma>. isPerm \<sigma> \<Longrightarrow> (\<forall>a\<in>Tsupp t. \<sigma> a = a) \<Longrightarrow> Tperm \<sigma> t = t"
(* so far, the above was a common part with our "LSNominalSet" locale *)
and
(* Equivariance of abstraction and of the operations (the first variable-convention compatibility 
convention from UBN): *)
Abs_equiv: "\<And>\<sigma> a t. isPerm \<sigma> \<Longrightarrow> Tperm \<sigma> (Abs a t) = Abs (\<sigma> a) (Tperm \<sigma> t)"
and
Op_equiv: "\<And>\<sigma> op ts. isPerm \<sigma> \<Longrightarrow> length ts = arity op \<Longrightarrow> Tperm \<sigma> (Op op ts) = Op op (map (Tperm \<sigma>) ts)"
begin

lemma Tperm_comp': "isPerm \<sigma> \<Longrightarrow> isPerm \<tau> \<Longrightarrow> Tperm (\<sigma> o \<tau>) t = Tperm \<sigma> (Tperm \<tau> t)"
using Tperm_comp by fastforce 

(* Extension of the term infrastructure to term-tuples: *)
(* *) 
fun Tsupp_tuple :: "'T T_tuple \<Rightarrow> 'A set" where 
"Tsupp_tuple ts = \<Union> (Tsupp ` (set ts))"

fun Tperm_tuple :: "('A \<Rightarrow> 'A) \<Rightarrow> 'T T_tuple \<Rightarrow> 'T T_tuple" where 
"Tperm_tuple f ts = map (Tperm f) ts"

lemma Tperm_tuple_id: "Tperm_tuple id = id"
using Tperm_id by auto

lemma Tperm_tuple_comp: "isPerm \<sigma> \<Longrightarrow> isPerm \<tau> \<Longrightarrow> Tperm_tuple (\<sigma> o \<tau>) = Tperm_tuple \<sigma> o Tperm_tuple \<tau>"
using Tperm_comp by auto

lemma small_Tsupp_tuple: "small (Tsupp_tuple ts)" 
by (auto intro: finite_UN_small simp: small_Tsupp)

lemma Tperm_tuple_Tsupp_tuple: 
"isPerm \<sigma> \<Longrightarrow> Tsupp_tuple (Tperm_tuple \<sigma> ts) \<subseteq> \<sigma> ` (Tsupp_tuple ts)"
using Tsupp_seminat by fastforce

lemma Tperm_tuple_cong_id: "isPerm \<sigma> \<Longrightarrow> (\<forall>a\<in>Tsupp_tuple ts. \<sigma> a = a) \<Longrightarrow> Tperm_tuple \<sigma> ts = ts"
by (simp add: Tsupp_supporting map_idI) 

lemma Tperm_tuple_comp': "isPerm \<sigma> \<Longrightarrow> isPerm \<tau> \<Longrightarrow> Tperm_tuple (\<sigma> o \<tau>) ts = Tperm_tuple \<sigma> (Tperm_tuple \<tau> ts)"
using Tperm_tuple_comp by fastforce

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

lemma it_Tperm: "isPerm \<sigma> \<Longrightarrow> wfST arity st \<Longrightarrow> Tperm \<sigma> (it vval tval st) = it (\<sigma> \<circ> vval) (Tperm \<sigma> \<circ> tval) st" 
apply(induct st, simp_all) 
using Abs_equiv apply simp_all
by (smt (verit) Op_equiv comp_apply length_map list.map_comp map_eq_conv)

lemma it_tuple_Tperm_tuple: "isPerm \<sigma> \<Longrightarrow> 
wfST_tuple arity sts \<Longrightarrow> 
Tperm_tuple \<sigma> (it_tuple vval tval sts) = it_tuple (\<sigma> \<circ> vval) (Tperm \<sigma> \<circ> tval) sts"
using it_Tperm by auto

end (* locale UBN_Components *)

locale UBN = UBN_Components Tperm Tsupp Abs Op arity 
for Tperm :: "('A :: infinite \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T" and Tsupp :: "'T \<Rightarrow> 'A set"
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
"\<And>rl \<sigma> pred ss. rl \<in> rules \<Longrightarrow> isPerm \<sigma> \<Longrightarrow> 
    Scond pred ss \<in> set (side rl) \<Longrightarrow> pred (it_tuple vval tval ss) \<Longrightarrow> 
    pred (Tperm_tuple \<sigma> (it_tuple vval tval ss))"
and 
VCcomp2: (* the second variable-convention compatibility condition from UBN: *)
"\<And>rl vval tval. rl \<in> rules \<Longrightarrow> 
   (\<forall>pred ss. Scond pred ss \<in> set (side rl) \<longrightarrow> pred (it_tuple vval tval ss)) \<Longrightarrow> 
   vval ` (varsbpR rl) \<inter> Tsupp_tuple (it_tuple vval tval (conc rl)) = {}"
begin

definition G' where 
"G' \<equiv> (\<lambda>R ts. \<exists>rl vval tval.
  ts = it_tuple vval tval (conc rl) \<and>
  rl \<in> rules \<and> 
  (\<forall>pred ss. Scond pred ss \<in> set (side rl) \<longrightarrow> pred (it_tuple vval tval ss)) \<and> 
  (\<forall>ts\<in>set (hyps rl). R (it_tuple vval tval ts)))"

definition G :: "'A set \<Rightarrow> ('T T_tuple \<Rightarrow> bool) \<Rightarrow> 'T T_tuple \<Rightarrow> bool" where 
"G \<equiv> (\<lambda>B R ts. \<exists>rl vval tval.
  B = vval ` (varsbpR rl) \<and> 
  ts = it_tuple vval tval (conc rl) \<and>
  rl \<in> rules \<and> 
  (\<forall>pred ss. Scond pred ss \<in> set (side rl) \<longrightarrow> pred (it_tuple vval tval ss)) \<and> 
  (\<forall>ts\<in>set (hyps rl). R (it_tuple vval tval ts)))"

lemma ex_comm2: "(\<exists>x y z. P x y z) = (\<exists>y z x . P x y z)" by auto

lemma G'_G: "G' R ts = (\<exists>B. G B R ts)"
unfolding G_def G'_def fun_eq_iff apply safe 
  subgoal for rl vval tval
  apply(subst ex_comm2)
  apply(rule exI[of _ rl]) apply(rule exI[of _ vval]) by auto
  subgoal by auto .

inductive II :: "'T T_tuple \<Rightarrow> bool" where 
"rl \<in> rules \<Longrightarrow>  
 (\<forall>pred ss. Scond pred ss \<in> set (side rl) \<longrightarrow> pred (it_tuple vval tval ss)) \<Longrightarrow> 
 (\<forall>ts\<in>set (hyps rl). II (it_tuple vval tval ts)) \<Longrightarrow>
 II (it_tuple vval tval (conc rl))"

lemma II_G': "II = lfp G'"
unfolding II_def G'_def ..

lemma II_def2: "II = lfp (\<lambda>R t. \<exists>xs. G xs R t)"
unfolding II_G' G'_G ..

lemma G_mono: "R \<le> R' \<Longrightarrow> G B R t \<Longrightarrow> G B R' t"
unfolding G_def le_fun_def by auto blast
 
lemma G_equiv: 
assumes "isPerm \<sigma>" "small B" "G B R ts" 
shows "G  (image \<sigma> B) (\<lambda>t'. R (Tperm_tuple (inv \<sigma>) t')) (Tperm_tuple \<sigma> ts)"
using assms unfolding G_def apply safe subgoal for rl vval tval
apply(rule exI[of _ rl]) apply(rule exI[of _ "\<sigma> o vval"])
apply(rule exI[of _ "Tperm \<sigma> o tval"]) apply(intro conjI)
  subgoal by auto
  subgoal apply(subst it_tuple_Tperm_tuple) using wfR_rules unfolding wfR_def by auto
  subgoal by auto
  subgoal apply safe subgoal for pred ss
  apply(subst it_tuple_Tperm_tuple[symmetric])
    subgoal by auto
    subgoal using wfR_rules unfolding wfR_def by auto
    subgoal apply(rule side_equiv) by auto . .  
  subgoal apply safe subgoal for ts 
  apply(subst it_tuple_Tperm_tuple[symmetric]) 
    subgoal by auto
    subgoal using wfR_rules unfolding wfR_def by auto
    subgoal apply(subst Tperm_tuple_comp'[symmetric])
      subgoal using isPerm_inv by blast
      subgoal .
      subgoal by (simp add: Tperm_id isPerm_invR) . . . . .

lemma G_fresh_simple: 
assumes "small B" "G B R ts"
shows "B \<inter> Tsupp_tuple ts = {}"
using assms unfolding G_def apply(elim exE conjE) 
subgoal for rl vval tval apply(frule VCcomp2) by auto . 

end (* context UBN *)

 
(* The UBN result is subsumed by ours: *)
sublocale UBN < UBN: Induct_simple where Tperm = Tperm_tuple 
and Tsupp = Tsupp_tuple and G = G apply standard
using small_Tsupp_tuple Tperm_tuple_Tsupp_tuple Tperm_tuple_cong_id 
G_equiv G_fresh_simple
by (auto simp: Tperm_id Tperm_comp' G_mono)  



end