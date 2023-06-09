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

 (* Rules are meant to be intepreted on the type 'T, this is why the side-conditions 
come with predicates on 'T *)
datatype ('O,'T) rule = Rule 
  (hyps: "'O sT list") 
  (side: "('O sT \<times> ('T \<Rightarrow> bool)) list")
  (conc: "'O sT")

(* It seems that we do need the "vars" operator from UBN; 
they do not use it in their result *)
fun varsbp :: "'O sT \<Rightarrow> vvar set" where 
"varsbp (Tvar tv) = {}"
|
"varsbp (Sabs vv st) = varsbp st - {vv}"
|
"varsbp (Sop op sts) = \<Union> (varsbp ` (set sts))"

(* Extension to rules: *)
definition varsbpR where 
"varsbpR rl = 
  (\<Union> (varsbp ` (set (hyps rl)))) \<union>
  (\<Union> ((varsbp o fst) ` (set (side rl)))) \<union>
  varsbp (conc rl) "


lemma finite_varsbp: "finite (varsbp st)"
by (induct st, auto)

lemma finite_varsbpR: "finite (varsbpR rl)"
unfolding varsbpR_def using finite_varsbp by auto

(* TODO: eventually switch from 'T to "'T list" to better match UBN *)
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
Op_equiv: "\<And>\<sigma> op ts. ssbij \<sigma> \<Longrightarrow> Tmap \<sigma> (Op op ts) = Op op (map (Tmap \<sigma>) ts)"
begin

lemma Tmap_comp': "\<And>\<sigma> \<tau> t. ssbij \<sigma> \<Longrightarrow> ssbij \<tau> \<Longrightarrow> Tmap (\<sigma> o \<tau>) t = Tmap \<sigma> (Tmap \<tau> t)"
using Tmap_comp by fastforce 

(* Interpretation of schematic terms: *)
fun it :: "(vvar \<Rightarrow> 'A) \<Rightarrow> (tvar \<Rightarrow> 'T) \<Rightarrow> 'O sT \<Rightarrow> 'T" where 
"it vval tval (Tvar tv) = tval tv"
|
"it vval tval (Sabs vv st) = Abs (vval vv) (it vval tval st)"
|
"it vval tval (Sop op sts)= Op op (map (it vval tval) sts)"

(* Consequences of the equivariance assumptions: *)

lemma it_Tmap: "ssbij \<sigma> \<Longrightarrow>  Tmap \<sigma> (it vval tval st) = it (\<sigma> \<circ> vval) (Tmap \<sigma> \<circ> tval) st" 
apply(induct st, simp_all) 
using Abs_equiv Op_equiv 
by (smt (verit) Op_equiv comp_apply list.map_comp map_eq_conv)+

end (* locale UBN_Components *)


locale UBN = UBN_Components dummy Tmap Tfvars Abs Op
for dummy :: 'A 
and Tmap :: "('A \<Rightarrow> 'A) \<Rightarrow> 'T \<Rightarrow> 'T" and Tfvars :: "'T \<Rightarrow> 'A set"
(* *)
and Abs :: "'A \<Rightarrow> 'T \<Rightarrow> 'T" and Op :: "'O \<Rightarrow> 'T list \<Rightarrow> 'T" 
+ 
fixes rules :: "('O,'T) rule set"
assumes
side_equiv: (* The side-conditions in the rules must be equivariant: *)
"\<And>rl \<sigma> ss pred. rl \<in> rules \<Longrightarrow> ssbij \<sigma> \<Longrightarrow> 
    (ss, pred) \<in> set (side rl) \<Longrightarrow> pred (it vval tval ss) \<Longrightarrow> pred (Tmap \<sigma> (it vval tval ss))"
and 
VCcomp2: (* the second variable-convention compatibility condition from UBN: *)
"\<And>rl vval tval. rl \<in> rules \<Longrightarrow> 
   (\<forall>(ss,pred)\<in>set (side rl). pred (it vval tval ss)) \<Longrightarrow> 
   vval ` (varsbpR rl) \<inter> Tfvars (it vval tval (conc rl)) = {}"
begin

definition G' where 
"G' \<equiv> (\<lambda>R t. \<exists>rl vval tval.
  t = it vval tval (conc rl) \<and>
  rl \<in> rules \<and> 
  (\<forall>(ss,pred)\<in>set (side rl). pred (it vval tval ss)) \<and> 
  (\<forall>ts\<in>set (hyps rl). R (it vval tval ts)))"

definition G where 
"G \<equiv> (\<lambda>R xs t. \<exists>rl vval tval.
  set xs = vval ` (varsbpR rl) \<and> 
  t = it vval tval (conc rl) \<and>
  rl \<in> rules \<and> 
  (\<forall>(ss,pred)\<in>set (side rl). pred (it vval tval ss)) \<and> 
  (\<forall>ts\<in>set (hyps rl). R (it vval tval ts)))"

lemma ex_comm2: "(\<exists>x y z. P x y z) = (\<exists>y z x . P x y z)" by auto

lemma G'_G: "G' R t = (\<exists>xs. G R xs t)"
unfolding G_def G'_def fun_eq_iff apply safe 
  subgoal for rl vval tval
  apply(subst ex_comm2)
  apply(rule exI[of _ rl]) apply(rule exI[of _ vval])
  apply(subgoal_tac "\<exists>xs. set xs = vval ` varsbpR rl")
    subgoal by auto
    subgoal by (simp add: finite_list finite_varsbpR) . 
  subgoal by auto .

inductive II :: "'T \<Rightarrow> bool" where 
"rl \<in> rules \<Longrightarrow> 
 (\<forall>(ss,pred)\<in>set (side rl). pred (it vval tval ss)) \<Longrightarrow> 
 (\<forall>ts\<in>set (hyps rl). II (it vval tval ts)) \<Longrightarrow>
 II (it vval tval (conc rl))"

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
assumes "ssbij \<sigma>" "G R v t" 
shows "G (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Vmap \<sigma> v) (Tmap \<sigma> t)"
using assms unfolding G_def apply safe subgoal for rl vval tval
apply(rule exI[of _ rl]) apply(rule exI[of _ "\<sigma> o vval"])
apply(rule exI[of _ "Tmap \<sigma> o tval"]) apply(intro conjI)
  subgoal unfolding Vmap_def by auto
  subgoal using it_Tmap .
  subgoal by auto
  subgoal apply safe subgoal for ss pred
  unfolding it_Tmap[symmetric] apply(rule side_equiv) by auto .
  subgoal apply safe subgoal for ts unfolding it_Tmap[symmetric]
  apply(subst Tmap_comp'[symmetric])
    subgoal using ssbij_inv by presburger
    subgoal .
    subgoal by (simp add: Tmap_id ssbij_invR) . . . .

lemma G_fresh_simple: 
assumes "G R v t"
shows "Vfvars v \<inter> Tfvars t = {}"
using assms unfolding G_def apply(elim exE conjE) 
subgoal for rl vval tval apply(frule VCcomp2) unfolding Vfvars_def by auto . 

end (* context UBN *)

 
(* The UBN result is subm=sumed by ours: *)
sublocale UBN < Induct_simple where dummy = dummy and Tmap = Tmap 
and Tfvars = Tfvars and Vmap = Vmap and Vfvars = Vfvars and G = G apply standard
apply (auto simp: Tmap_id Tmap_comp' small_Tfvars Tmap_Tfvars Tmap_cong_id Vmap_comp 
   small_Vfvars Vmap_Vfvars G_mono G_equiv G_fresh_simple) . 




end