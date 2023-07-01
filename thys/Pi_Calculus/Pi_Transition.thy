(* Here we instantiate the general enhanced rule induction to 
the "early" pi-calculus transition system.
the adjective refers to the fact that inputs are instantiated 
at transition time (whereas a "late" semantics would 
have transitons with bound inputs)
 *)
theory Pi_Transition
imports Commitment 
begin

(* INSTANTIATING THE ABSTRACT SETTING: *)

(* INSTATIATING THE Small LOCALE (INDEPENDENTLY OF THE CONSIDERED INDUCTIVE PREDICATE *) 

print_locales
interpretation Small where dummy = "undefined :: var" 
apply standard
by (simp_all add: infinite_var regularCard_var)

datatype (vars:'a) action = finp 'a 'a | fout 'a 'a | bout 'a 'a | tau 

type_synonym act = "var action"

fun Cmt :: "act \<Rightarrow> trm \<Rightarrow> cmt" where 
 "Cmt (finp x y) P = Finp x y P"
|"Cmt (fout x y) P = Fout x y P"
|"Cmt (bout x y) P = Bout x y P"
|"Cmt tau P = Tau P"

fun bvars :: "act \<Rightarrow> var list" where 
 "bvars (bout x y) = [y]"
|"bvars _ = []" 

abbreviation "swapa act x y \<equiv> map_action (id(x:=y,y:=x)) act"
 

(* The "late" transition relation  *)
inductive trans :: "trm \<Rightarrow> cmt \<Rightarrow> bool" where
Inp: "x \<notin> {a,u} \<Longrightarrow> trans (Inp a x P) (Finp a u (usub P u x))"
(* |
Out: "trans (Out a x P) (Fout a x P)"
|
Tau: "trans P (Tau P)"
|
Match: "trans P C \<Longrightarrow> trans (Match a a P) C"
|
Sum1: "trans P1 C \<Longrightarrow> trans (Sum P1 P2) C"
|
Sum2: "trans P2 C \<Longrightarrow> trans (Sum P1 P2) C"
*)
|
Open: "trans P (Fout a x P') \<Longrightarrow> a \<noteq> x \<Longrightarrow> 
       trans (Res x P) (Bout a x P')"
|
ScopeF: "trans P (Cmt act P') \<Longrightarrow> y \<notin> vars act \<Longrightarrow> 
   trans (Res y P) (Cmt act (Res y P'))"
|
ScopeB: "trans P (Bout a x P') \<Longrightarrow> y \<notin> {a,x} \<union> FFVars P \<Longrightarrow> x \<noteq> a
   \<Longrightarrow> 
   trans (Res y P) (Bout a x (Res y P'))"
|
Par1: "trans P1 (Cmt act P1') \<Longrightarrow> set (bvars act) \<inter> FFVars P2 = {} \<Longrightarrow> 
   trans (Par P1 P2) (Cmt act (Par P1' P2))" 
(* |
Par2: "trans P2 (Cmt act P2') \<Longrightarrow> bvars act \<inter> FFVars P1 = {} \<Longrightarrow> 
   trans (Par P1 P2) (Cmt act (Par P1 P2'))" *)
|
Com1: "trans P1 (Finp a x P1') \<Longrightarrow> trans P2 (Fout a x P2') \<Longrightarrow> 
   trans (Par P1 P2) (Tau (Par P1' P2'))" 
(* |
Com2: "trans P1 (Fout a x P1') \<Longrightarrow> trans P2 (Finp a x P2') \<Longrightarrow> 
   trans (Par P1 P2) (Tau (Par P1' P2'))"  *)
|
Close1: "trans P1 (Finp a x P1') \<Longrightarrow> trans P2 (Bout a x P2') \<Longrightarrow> 
   x \<notin> {a} \<union> FFVars P1 \<union> FFVars P2 \<Longrightarrow>
   trans (Par P1 P2) (Bout a x (Par P1' P2'))" 
(* |
Close2: "trans P1 (Bout a x P1') \<Longrightarrow> trans P2 (Finp a x P2') \<Longrightarrow> 
   x \<notin> {a} \<union> FFVars P1 \<union> FFVars P2 \<Longrightarrow>
   trans (Par P1 P2) (Bout a x (Par P1' P2'))" 
|
Bang: "trans (Par P (Bang P)) C \<Longrightarrow> trans (Bang P) C"
*)



(* INSTANTIATING THE Components LOCALE: *)

type_synonym T = "trm \<times> cmt"
type_synonym V = "var list" 


definition Tmap :: "(var \<Rightarrow> var) \<Rightarrow> T \<Rightarrow> T" where 
"Tmap f \<equiv> map_prod (rrename f) (rrename_commit f)"

fun Tfvars :: "T \<Rightarrow> var set" where 
"Tfvars (e1,e2) = FFVars e1 \<union> FFVars_commit e2"

definition Vmap :: "(var \<Rightarrow> var) \<Rightarrow> V \<Rightarrow> V" where 
"Vmap \<equiv> map"

fun Vfvars :: "V \<Rightarrow> var set" where 
"Vfvars v = set v"

lemmas commit_internal.FFVars_rrenames[simp]

interpretation Components where dummy = "undefined :: var" and 
Tmap = Tmap and Tfvars = Tfvars
and Vmap = Vmap and Vfvars = Vfvars 
apply standard unfolding ssbij_def Tmap_def Vmap_def
  using small_Un small_def term.card_of_FFVars_bounds
    commit_internal.card_of_FFVars_bounds(2)
  apply (auto simp: term.rrename_id0s map_prod.comp term.rrename_comp0s 
        commit_internal.rrename_cong_ids(2)
        commit_internal.rrename_id0s commit_internal.rrename_comp0s(2)
          inf_A) 
  by blast 

definition G :: "(T \<Rightarrow> bool) \<Rightarrow> V \<Rightarrow> T \<Rightarrow> bool"
where
"G \<equiv> \<lambda>R v t.  
 (\<exists>x a u P. 
    v = [x] \<and> fst t = Inp a x P \<and> snd t = Finp a u (usub P u x) \<and> 
    x \<notin> {a,u})
 \<or> 
 (\<exists>P a x P'. 
    v = [x] \<and> fst t = Res x P \<and> snd t = Bout a x P' \<and> 
    a \<noteq> x \<and> 
    R (P,Fout a x P')) 
 \<or>
 (\<exists> P act P' y. 
    v = bvars act @ [y] \<and> fst t = Res y P \<and> snd t = Cmt act (Res y P') \<and>  
    y \<notin> vars act \<and> 
    R (P, Cmt act P'))
 \<or>
 (\<exists> P a x P' y. 
    v = [y,x] \<and> fst t = Res y P \<and> snd t = Bout a x (Res y P') \<and>  
    y \<notin> {a,x} \<union> FFVars P \<and> x \<noteq> a \<and>  
    R (Res y P, Bout a x (Res y P')))
 \<or>
 (\<exists>P1 act P1' P2. 
    v = bvars act \<and> fst t = Par P1 P2 \<and> snd t = Cmt act (Par P1' P2) \<and> 
    set (bvars act) \<inter> FFVars P2 = {} \<and> 
    R (P1, Cmt act P1'))
 \<or>
 (\<exists>P1 a x P1' P2 P2'. 
    v = [] \<and> fst t = Par P1 P2 \<and> snd t = Tau (Par P1' P2') \<and>  
    R (P1, Finp a x P1') \<and> R (P2, Fout a x P2'))
 \<or>
 (\<exists>P1 a x P1' P2 P2'. 
    v = [] \<and> fst t = Par P1 P2 \<and> snd t = Bout a x (Par P1' P2') \<and>  
    x \<notin> {a} \<union> FFVars P1 \<union> FFVars P2 \<and> 
    R (P1, Finp a x P1') \<and> R (P2, Bout a x P2'))
"


(* VERIFYING THE HYPOTHESES FOR BARENDREGT-ENHANCED INDUCTION: *)

lemma GG_mono: "R \<le> R' \<Longrightarrow> G R v t \<Longrightarrow> G R' v t"
unfolding G_def by (smt (z3) le_boolE le_funD)

thm term.rrename_comps

find_theorems rrename_commit Finp


lemma rrename_commit_Finp[simp]: "bij \<sigma> \<and> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> 
  rrename_commit \<sigma> (Finp a u P) = Finp (\<sigma> a) (\<sigma> u) (rrename \<sigma> P)"
sorry

lemma rrename_commit_Fout[simp]: "bij \<sigma> \<and> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> 
  rrename_commit \<sigma> (Fout a u P) = Fout (\<sigma> a) (\<sigma> u) (rrename \<sigma> P)"
sorry

lemma rrename_commit_Bout[simp]: "bij \<sigma> \<and> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> 
  rrename_commit \<sigma> (Bout a u P) = Bout (\<sigma> a) (\<sigma> u) (rrename \<sigma> P)"
sorry

lemma rrename_commit_Tau[simp]: "bij \<sigma> \<and> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow> 
  rrename_commit \<sigma> (Tau P) = Tau (rrename \<sigma> P)"
sorry


lemma rrename_usub[simp]: "bij \<sigma> \<and> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow>  
 rrename \<sigma> (usub P u x) = usub (rrename \<sigma> P) (\<sigma> u) (\<sigma> x)"
sorry

lemma bvars_map_action[simp]: "bvars (map_action \<sigma> act) = map \<sigma> (bvars act)"
by (cases act, auto)

lemma rrename_commit_Cmt[simp]: 
"bij \<sigma> \<and> |supp \<sigma>| <o |UNIV::var set| \<Longrightarrow>  
 rrename_commit \<sigma> (Cmt act P) = Cmt (map_action \<sigma> act) (rrename \<sigma> P)"
by (cases act, auto)

lemmas action.set_map[simp]

(* lemma FFVars_commit_Cmt[simp]: "FFVars_commit (Cmt act P) = FFVars P" *)
 

(* NB: Everything is passed \<sigma>-renamed as witnesses to exI *)
lemma GG_equiv: "ssbij \<sigma> \<Longrightarrow> G R v t \<Longrightarrow> G (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Vmap \<sigma> v) (Tmap \<sigma> t)"
unfolding G_def apply(elim disjE)
  (* *)
  subgoal apply(rule disjI1)
  subgoal apply(elim exE) subgoal for x a u P
  apply(rule exI[of _ "\<sigma> x"]) apply(rule exI[of _ "\<sigma> a"]) 
  apply(rule exI[of _ "\<sigma> u"]) apply(rule exI[of _ "rrename \<sigma> P"])
  apply(cases t) unfolding ssbij_def small_def Tmap_def Vmap_def 
  by (simp add: term.rrename_comps) . . 
  (* *)
  subgoal apply(rule disjI2, rule disjI1)
  subgoal apply(elim exE) subgoal for P a x P'
  apply(rule exI[of _ "rrename \<sigma> P"])
  apply(rule exI[of _ "\<sigma> a"]) apply(rule exI[of _ "\<sigma> x"])
  apply(rule exI[of _ "rrename \<sigma> P'"])   
  apply(cases t) unfolding ssbij_def small_def Tmap_def Vmap_def 
  by (simp add: term.rrename_comps) . . 
  (* *)
  subgoal apply(rule disjI2, rule disjI2, rule disjI1)
  subgoal apply(elim exE) subgoal for P act P' y
  apply(rule exI[of _ "rrename \<sigma> P"])
  apply(rule exI[of _ "map_action \<sigma> act"])
  apply(rule exI[of _ "rrename \<sigma> P'"])
  apply(rule exI[of _ "\<sigma> y"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def Vmap_def 
  apply (simp add: term.rrename_comps) 
  by (auto simp add: action.map_id action.map_comp) . .
  (* *)
  subgoal apply(rule disjI2, rule disjI2, rule disjI2, rule disjI1)
  subgoal apply(elim exE) subgoal for P a x P' y
  apply(rule exI[of _ "rrename \<sigma> P"])
  apply(rule exI[of _ "\<sigma> a"]) 
  apply(rule exI[of _ "\<sigma> x"]) 
  apply(rule exI[of _ "rrename \<sigma> P'"])
  apply(rule exI[of _ "\<sigma> y"])   
  apply(cases t) unfolding ssbij_def small_def Tmap_def Vmap_def 
  apply (simp add: term.rrename_comps) 
  by auto . .
  (* *)
  subgoal apply(rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1)
  subgoal apply(elim exE) subgoal for P1 act P1' P2
  apply(rule exI[of _ "rrename \<sigma> P1"])
  apply(rule exI[of _ "map_action \<sigma> act"])
  apply(rule exI[of _ "rrename \<sigma> P1'"])
  apply(rule exI[of _ "rrename \<sigma> P2"])
  apply(cases t) unfolding ssbij_def small_def Tmap_def Vmap_def 
  apply (simp add: term.rrename_comps)  
  by (auto simp add: action.map_id action.map_comp) . .
  (* *)
  subgoal apply(rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI1)
  subgoal apply(elim exE) subgoal for P1 a x P1' P2 P2'
  apply(rule exI[of _ "rrename \<sigma> P1"])
  apply(rule exI[of _ "\<sigma> a"])
  apply(rule exI[of _ "\<sigma> x"])
  apply(rule exI[of _ "rrename \<sigma> P1'"])
  apply(rule exI[of _ "rrename \<sigma> P2"])
  apply(rule exI[of _ "rrename \<sigma> P2'"])
  apply(cases t) unfolding ssbij_def small_def Tmap_def Vmap_def 
  by (simp add: term.rrename_comps) . .
  (* *)
  subgoal apply(rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2, rule disjI2)
  subgoal apply(elim exE) subgoal for P1 a x P1' P2 P2'
  apply(rule exI[of _ "rrename \<sigma> P1"])
  apply(rule exI[of _ "\<sigma> a"])
  apply(rule exI[of _ "\<sigma> x"])
  apply(rule exI[of _ "rrename \<sigma> P1'"])
  apply(rule exI[of _ "rrename \<sigma> P2"])
  apply(rule exI[of _ "rrename \<sigma> P2'"])
  apply(cases t) unfolding ssbij_def small_def Tmap_def Vmap_def 
  apply (simp add: term.rrename_comps)
  by auto . . .
  (* *)

(* *)

lemma Inp_refresh: 
"xx \<notin> FFVars P \<or> xx = x \<Longrightarrow> Inp a x P = Inp a xx (swap P x xx)"
sorry

lemma Res_refresh: 
"xx \<notin> FFVars P \<or> xx = x \<Longrightarrow> Res x P = Res xx (swap P x xx)"
sorry

definition "sw a x y \<equiv> if a = x then y else if a = y then x else a"

lemma swap_usub: 
"swap (usub P u x) z1 z2 = usub (swap P z1 z2) (sw u z1 z2) (sw x z1 z2)"
sorry

lemma usub_refresh: 
"xx \<notin> FFVars P \<or> xx = x \<Longrightarrow> usub P u x = usub (swap P x xx) u xx"
sorry

(*  *)

find_theorems FFVars vvsubst
  

lemma fresh: "\<exists>xx. xx \<notin> Tfvars t"  
using Abs_avoid small_Tfvars small_def by blast 

lemma fresh2: "\<exists>xx1 xx2. xx1 \<noteq> xx2 \<and> {xx1,xx2} \<inter> Tfvars t = {}"  
using fresh[of t] apply safe subgoal for xx apply(rule exI[of _ xx])
apply auto
using Abs_avoid small_Tfvars small_def
by (metis FFVars_commit_simps(1) UnCI commit_internal.card_of_FFVars_bounds(2) 
finite_Un finite_iff_le_card_var insert_iff) .

lemma fresh_n: "\<exists>xxs. length xxs = n \<and> set xxs \<inter> Tfvars t = {}"
sorry

lemma id_upd_same[simp]: "id(y := y) = id"
  by auto

fun permOfAct where 
"permOfAct xx (bout a x) = id(x:=xx)"
|
"permOfAct xx _ = id"

lemma bvars_act_bout: "bvars act = [] \<or> (\<exists>a b. act = bout a b)"
by(cases act, auto)

(* NB: The entities affected by variables are passed as witnesses to exI 
with x and (the fresh) xx swapped, whereas the non-affected ones are passed 
as they are. 
*)
lemma GG_fresh: 
"(\<forall>\<sigma> t. ssbij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t)) \<Longrightarrow> G R v t \<Longrightarrow> 
 \<exists>w. Vfvars w  \<inter> Tfvars t = {} \<and> G R w t"
using fresh2[of t] unfolding G_def Tmap_def Vmap_def apply(elim disjE exE conjE)
  subgoal for xx x xx1 a u P
  apply(rule exI[of _ "[xx]"])  
  apply(rule conjI)
    subgoal unfolding ssbij_def small_def Vmap_def by auto 
    subgoal apply(rule disjI1) 
    apply(rule exI[of _ "xx"]) 
    apply(rule exI[of _ "a"])
    apply(rule exI[of _ "u"]) 
    apply(rule exI[of _ "swap P x xx"])
    apply(cases t) 
    by (simp add: Inp_refresh usub_refresh) . 
  (* *)
  subgoal for xx P xx1 a x P'
  apply(rule exI[of _ "[xx]"])  
  apply(rule conjI)
    subgoal unfolding ssbij_def small_def Vmap_def by auto 
    subgoal apply(rule disjI2, rule disjI1) 
    apply(rule exI[of _ "swap P x xx"])
    apply(rule exI[of _ "a"]) 
    apply(rule exI[of _ "xx"])
    apply(rule exI[of _ "swap P' x xx"]) 
    apply(cases t)  apply simp apply(intro conjI)
      subgoal using Res_refresh by blast
      subgoal by auto
      apply(erule allE[of _ "id(x:=xx,xx:=x)"])
      apply(erule allE[of _ "P"])
      apply(erule allE[of _ "Fout a x P'"]) 
      by (auto simp: ssbij_def split: if_splits ) .
  (* *)
  subgoal for yy P xa act P' y 
  using bvars_act_bout[of act] apply(elim disjE exE)
    subgoal
    apply(rule exI[of _ "[yy]"])  
    apply(rule conjI)
      subgoal unfolding ssbij_def small_def Vmap_def by auto 
      subgoal apply(rule disjI2, rule disjI2, rule disjI1) 
      apply(rule exI[of _ "swap P y yy"])
      apply(rule exI[of _ "swapa act y yy"]) 
      apply(rule exI[of _ "swap P' y yy"])
      apply(rule exI[of _ "yy"]) 
      apply(cases t) apply simp apply(intro conjI)
        subgoal using Res_refresh by blast
        subgoal using Res_refresh apply(cases act, simp_all split: if_splits)  
          by blast+
        subgoal by auto
        subgoal apply(erule allE[of _ "id(y:=yy,yy:=y)"])
        apply(erule allE[of _ "P"])
        apply(erule allE[of _ "Cmt act P'"]) 
        by (auto simp: ssbij_def split: if_splits ) . .
    subgoal for a b
    apply(rule exI[of _ "[xa,yy]"])  
    apply(rule conjI)
      subgoal unfolding ssbij_def small_def Vmap_def by auto 
      subgoal apply(rule disjI2, rule disjI2, rule disjI1) 
      apply(rule exI[of _ "swap (swap P y yy) xa a"]) 
      apply(rule exI[of _ "swapa (swapa act y yy) xa a"]) 
      apply(rule exI[of _ "swap (swap P' y yy) xa a"])
      apply(rule exI[of _ "yy"]) 
      apply(cases t) apply(intro conjI)
        subgoal apply simp  
        subgoal using Res_refresh by blasts
        subgoal using Res_refresh apply(cases act, simp_all split: if_splits)  
          by blast+
        subgoal by auto
        subgoal apply(erule allE[of _ "id(y:=yy,yy:=y)"])
        apply(erule allE[of _ "P"])
        apply(erule allE[of _ "Cmt act P'"]) 
        by (auto simp: ssbij_def split: if_splits ) .
      

      subgoal by auto
      apply(erule allE[of _ "id(x:=xx,xx:=x)"])
      apply(erule allE[of _ "P"])
      apply(erule allE[of _ "Fout a x P'"]) 
      by (auto simp: ssbij_def split: if_splits) .  
  (* *)


(* FINALLY, INTERPRETING THE Induct LOCALE: *)

interpretation Induct where dummy = "undefined :: var" and 
Tmap = Tmap and Tfvars = Tfvars
and Vmap = Vmap and Vfvars = Vfvars and G = G
apply standard 
  using GG_mono GG_equiv GG_fresh by auto

(* *)

lemma trans_I: "trans t1 t2 = I (t1,t2)" 
  unfolding trans_def I_def lfp_curry2 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
  unfolding fun_eq_iff G_def apply safe 
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal apply simp by metis
    subgoal by (metis fst_conv snd_conv)
    subgoal by (metis fst_conv snd_conv)
    subgoal by (metis fst_conv snd_conv)
    subgoal by (metis fst_conv snd_conv) .

(* FROM ABSTRACT BACK TO CONCRETE: *)
thm trans.induct[no_vars]

corollary BE_induct_trans: "(\<And>p. small (Pfvars p)) \<Longrightarrow> 
trans t1 t2 \<Longrightarrow> 
(\<And>e p. R p e e) \<Longrightarrow>
(\<And>e1 e1' e2 e2' p. trans e1 e1' \<Longrightarrow> 
  (\<forall>p'. R p' e1 e1') \<Longrightarrow> (\<forall>p'. R p' e2 e2') \<Longrightarrow> R p (App e1 e2) (App e1' e2')) \<Longrightarrow> 
(\<And>e e' x p. x \<notin> Pfvars p \<Longrightarrow> trans e e' \<Longrightarrow> (\<forall>p'. R p' e e') \<Longrightarrow> R p (Abs x e) (Abs x e')) \<Longrightarrow> 
(\<And>x e e' e2 e2' p. x \<notin> Pfvars p \<Longrightarrow> trans e e' \<Longrightarrow> (\<forall>p'. R p' e e') \<Longrightarrow> trans e2 e2' \<Longrightarrow> (\<forall>p'. R p' e2 e2') \<Longrightarrow> 
   x \<notin> FFVars_term e2 \<Longrightarrow> (x \<in> FFVars_term e' \<Longrightarrow> x \<notin> FFVars_term e2') \<Longrightarrow> 
   R p (App (Abs x e) e2) (tvsubst (VVr(x := e2')) e')) \<Longrightarrow>
 R p t1 t2"
unfolding trans_I
apply(subgoal_tac "case (t1,t2) of (t1, t2) \<Rightarrow> R p t1 t2")
  subgoal by auto
  subgoal apply(erule BE_induct[where R = "\<lambda>p (t1,t2). R p t1 t2"])
  unfolding G_def apply (auto split: if_splits)
    by (metis (no_types, lifting)) .


end