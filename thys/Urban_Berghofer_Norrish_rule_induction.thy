(* Wew show that the Urban-Berghofer-Norrish (UBN) syntactic criterion 
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
  (\<Union> ((varsbp o fst) ` (set (side rl)))) 
  -
  varsbp (conc rl) "
(* \<union> varsbp (conc rl) 
This probably can be subtracte3d rather than Unioned, so we strengthen their result...*)

lemma finite_varsbp: "finite (varsbp st)"
by (induct st, auto)

lemma finite_varsbpR: "finite (varsbpR rl)"
unfolding varsbpR_def using finite_varsbp by auto


locale UBN_Components = Small dummy 
for dummy :: 'V 
+
fixes (* 'T: term-like entities *)
Tmap :: "('V \<Rightarrow> 'V) \<Rightarrow> 'T \<Rightarrow> 'T"
and Tfvars :: "'T \<Rightarrow> 'V set"
(* *)
and 
Abs :: "'V \<Rightarrow> 'T \<Rightarrow> 'T" 
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
fun it :: "(vvar \<Rightarrow> 'V) \<Rightarrow> (tvar \<Rightarrow> 'T) \<Rightarrow> 'O sT \<Rightarrow> 'T" where 
"it vval tval (Tvar tv) = tval tv"
|
"it vval tval (Sabs vv st) = Abs (vval vv) (it vval tval st)"
|
"it vval tval (Sop op sts)= Op op (map (it vval tval) sts)"

end (* locale UBN_Components *)


 




end