(* Here we instantiate the general enhanced rule induction to 
the "early" pi-calculus transition system.
the adjective refers to the fact that inputs are instantiated 
at transition time (whereas a "late" semantics would 
have transitons with bound inputs)
 *)
theory Pi_Transition
imports Commitment 
begin

hide_const trans




(* INSTANTIATING THE ABSTRACT SETTING: *)

(* INSTATIATING THE Small LOCALE (INDEPENDENTLY OF THE CONSIDERED INDUCTIVE PREDICATE *) 

print_locales
interpretation Small where dummy = "undefined :: var" 
apply standard
by (simp_all add: infinite_var regularCard_var)




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
ScopeF: "trans P (Cmt act P') \<Longrightarrow> x \<notin> vars act \<Longrightarrow> 
   trans (Res x P) (Cmt act (Res x P'))"
|
ScopeB: "trans P (Bout a x P') \<Longrightarrow> y \<notin> {a,x} \<Longrightarrow> x \<notin> {a} \<union> FFVars P
   \<Longrightarrow> 
   trans (Res y P) (Bout a x (Res y P'))"
|
Par1: "trans P1 (Cmt act P1') \<Longrightarrow> 
   \<^cancel>\<open>present in Bengtson but not needed (and will be an 'output' 
      of strong induction) : set (bvars act) \<inter> fvars act = {} \<Longrightarrow> \<close>  
   set (bvars act) \<inter> FFVars P1 = {} \<Longrightarrow> 
   set (bvars act) \<inter> FFVars P2 = {} \<Longrightarrow> 
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
Close1: "trans P1 (Finp a x P1') \<Longrightarrow> trans P2 (Bout a x  P2') \<Longrightarrow>
    \<^cancel>\<open>  x \<noteq> a seems essential, and not an artifact \<close> 
   x \<notin> {a} \<union> FFVars P1 \<^cancel>\<open>\<union> FFVars P2 was in Bengtson\<close>  \<Longrightarrow>
   trans (Par P1 P2) (Bout a x (Par P1' P2'))" 
(*  
x fresh P1  x=/=a
trans (P1=[xx/x]) (Finp a[xx/x[xx/x])] xx P1' \<Longrightarrow> trans P2 (Bout a xx  P2'[xx/x]) 
\<Longrightarrow>
trans (Par P1 P2) (Bout a xx (Par P1'[xx/x] P2'[xx/x])) 
*)
(* |
Close2: "trans P1 (Bout a x P1') \<Longrightarrow> trans P2 (Finp a x P2') \<Longrightarrow> 
   x \<notin> {a} \<union> FFVars P1 \<union> FFVars P2 \<Longrightarrow>
   trans (Par P1 P2) (Bout a x (Par P1' P2'))" 
|
Bang: "trans (Par P (Bang P)) C \<Longrightarrow> trans (Bang P) C"
*)

(* 
lemma 
assumes "trans P (Cmt act P')"
shows "FFVars P \<inter> set (bvars act) = {}" 
proof- 
  define C where "C = Cmt act P'"
  show ?thesis using assms unfolding C_def[symmetric] using C_def
  apply(induct arbitrary: act P' rule: trans.induct) 
    subgoal for x a u P act P' apply(cases act) by (auto elim: trans.cases)
    subgoal for P a x P' act P'a apply(cases act) apply (auto elim: trans.cases)
    subgoal 
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
 \<^cancel>\<open>Inp: \<close>  
 (\<exists>x a u P. 
    v = [x] \<and> fst t = Inp a x P \<and> snd t = Finp a u (usub P u x) \<and> 
    x \<notin> {a,u})
 \<or>  \<^cancel>\<open>Open: \<close> 
 (\<exists>P a x P'. 
    v = [x] \<and> fst t = Res x P \<and> snd t = Bout a x P' \<and> 
    a \<noteq> x \<and> 
    R (P,Fout a x P')) 
 \<or>  \<^cancel>\<open>ScopeF: \<close> 
 (\<exists> P act P' x.  \<^cancel>\<open>Can be made stronger, adding v = bvars act @ [y] \<close> 
    v = [x] \<and> fst t = Res x P \<and> snd t = Cmt act (Res x P') \<and>  
    x \<notin> vars act \<and> 
    R (P, Cmt act P'))
 \<or>  \<^cancel>\<open>ScopeB: \<close> 
 (\<exists> P a x P' y. 
    v = [x,y] \<and> fst t = Res y P \<and> snd t = Bout a x (Res y P') \<and>  
    y \<notin> {a,x} \<and> x \<notin> {a} \<union> FFVars P \<and>  
    R (P, Bout a x P'))
 \<or>  \<^cancel>\<open>Par1: \<close> 
 (\<exists>P1 act P1' P2. 
    v = bvars act \<and> fst t = Par P1 P2 \<and> snd t = Cmt act (Par P1' P2) \<and> 
    set (bvars act) \<inter> FFVars P1 = {} \<and> 
    set (bvars act) \<inter> FFVars P2 = {} \<and> 
    R (P1, Cmt act P1'))
 \<or> \<^cancel>\<open>Com1: \<close> 
 (\<exists>P1 a x P1' P2 P2'. 
    v = [] \<and> fst t = Par P1 P2 \<and> snd t = Tau (Par P1' P2') \<and>  
    R (P1, Finp a x P1') \<and> R (P2, Fout a x P2'))
 \<or> \<^cancel>\<open>Close1: \<close> 
 (\<exists>P1 a x P1' P2 P2'. 
    v = [x] \<and> fst t = Par P1 P2 \<and> snd t = Bout a x (Par P1' P2') \<and> 
    x \<notin> {a} \<union> FFVars P1 \<and> 
    R (P1, Finp a x P1') \<and> R (P2, Bout a x P2'))
"


(* VERIFYING THE HYPOTHESES FOR BARENDREGT-ENHANCED INDUCTION: *)

lemma GG_mono: "R \<le> R' \<Longrightarrow> G R v t \<Longrightarrow> G R' v t"
unfolding G_def by (smt (z3) le_boolE le_funD)


(* *)

(* lemma FFVars_commit_Cmt[simp]: "FFVars_commit (Cmt act P) = FFVars P" *)
 

(* NB: Everything is passed \<sigma>-renamed as witnesses to exI *)
lemma GG_equiv: "ssbij \<sigma> \<Longrightarrow> G R v t \<Longrightarrow> G (\<lambda>t'. R (Tmap (inv \<sigma>) t')) (Vmap \<sigma> v) (Tmap \<sigma> t)"
unfolding G_def apply(elim disjE)
  (* Inp: *)
  subgoal apply(rule disjI7_1)
  subgoal apply(elim exE) subgoal for x a u P
  apply(rule exI[of _ "\<sigma> x"]) apply(rule exI[of _ "\<sigma> a"]) 
  apply(rule exI[of _ "\<sigma> u"]) apply(rule exI[of _ "rrename \<sigma> P"])
  apply(cases t) unfolding ssbij_def small_def Tmap_def Vmap_def 
  by (simp add: term.rrename_comps) . . 
  (* Open: *)
  subgoal apply(rule disjI7_2)
  subgoal apply(elim exE) subgoal for P a x P'
  apply(rule exI[of _ "rrename \<sigma> P"])
  apply(rule exI[of _ "\<sigma> a"]) apply(rule exI[of _ "\<sigma> x"])
  apply(rule exI[of _ "rrename \<sigma> P'"])   
  apply(cases t) unfolding ssbij_def small_def Tmap_def Vmap_def 
  by (simp add: term.rrename_comps) . . 
  (* ScopeF: *)
  subgoal apply(rule disjI7_3)
  subgoal apply(elim exE) subgoal for P act P' x
  apply(rule exI[of _ "rrename \<sigma> P"])
  apply(rule exI[of _ "map_action \<sigma> act"])
  apply(rule exI[of _ "rrename \<sigma> P'"])
  apply(rule exI[of _ "\<sigma> x"]) 
  apply(cases t) unfolding ssbij_def small_def Tmap_def Vmap_def 
  apply (simp add: term.rrename_comps) 
  by (auto simp add: action.map_id action.map_comp) . .
  (* ScopeB: *)
  subgoal apply(rule disjI7_4)
  subgoal apply(elim exE) subgoal for P a x P' y
  apply(rule exI[of _ "rrename \<sigma> P"])
  apply(rule exI[of _ "\<sigma> a"]) 
  apply(rule exI[of _ "\<sigma> x"]) 
  apply(rule exI[of _ "rrename \<sigma> P'"])
  apply(rule exI[of _ "\<sigma> y"])   
  apply(cases t) unfolding ssbij_def small_def Tmap_def Vmap_def 
  apply (simp add: term.rrename_comps) 
  by auto . .
  (* Par1: *)
  subgoal apply(rule disjI7_5)
  subgoal apply(elim exE) subgoal for P1 act P1' P2
  apply(rule exI[of _ "rrename \<sigma> P1"])
  apply(rule exI[of _ "map_action \<sigma> act"])
  apply(rule exI[of _ "rrename \<sigma> P1'"])
  apply(rule exI[of _ "rrename \<sigma> P2"])
  apply(cases t) unfolding ssbij_def small_def Tmap_def Vmap_def 
  apply (simp add: term.rrename_comps)  
  by (auto simp add: action.map_id action.map_comp) . .
  (* Com1: *)
  subgoal apply(rule disjI7_6)
  subgoal apply(elim exE) subgoal for P1 a x P1' P2 P2'
  apply(rule exI[of _ "rrename \<sigma> P1"])
  apply(rule exI[of _ "\<sigma> a"])
  apply(rule exI[of _ "\<sigma> x"])
  apply(rule exI[of _ "rrename \<sigma> P1'"])
  apply(rule exI[of _ "rrename \<sigma> P2"])
  apply(rule exI[of _ "rrename \<sigma> P2'"])
  apply(cases t) unfolding ssbij_def small_def Tmap_def Vmap_def 
  by (simp add: term.rrename_comps) . .
  (* Close1: *)
  subgoal apply(rule disjI7_7)
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



(*  *)

find_theorems FFVars vvsubst


(* Supply of fresh variables: *)

lemma finite_Tfvars: "finite (Tfvars t)"
using finite_iff_le_card_var small_Tfvars small_def by blast

lemma exists_fresh:
"\<exists> z. z \<notin> set xs \<and> (\<forall>t \<in> set ts. z \<notin> Tfvars t)"
proof-
  have 0: "|set xs \<union> \<Union> (Tfvars ` (set ts))| <o |UNIV::var set|" 
  unfolding ls_UNIV_iff_finite  
  using finite_Tfvars by blast
  then obtain x where "x \<notin> set xs \<union> \<Union> (Tfvars ` (set ts))"
  by (meson ex_new_if_finite finite_iff_le_card_var 
    infinite_iff_natLeq_ordLeq var_term_pre_class.large)
  thus ?thesis by auto
qed





fun permOfAct where 
"permOfAct xx (bout a x) = id(x:=xx)"
|
"permOfAct xx _ = id"

lemma bvars_act_bout: "bvars act = [] \<or> (\<exists>a b. act = bout a b)"
by(cases act, auto)



lemma FFVars_swap[simp]: "{x::var,y} \<inter> FFVars P = {} \<Longrightarrow> swap P x y = P"
apply(rule term.rrename_cong_ids) by auto

(* lemma "bij ((id(x := xx, xx := x)) (y := yy, yy := y))"
unfolding bij_def inj_def apply auto

lemma "ssbij (id(x := xx, xx := x, y := yy, yy := y))"
unfolding ssbij_def bij_def inj_def apply auto sledgehammser
*)
lemma rrename_o_swap[simp]: 
"rrename (id(y::var := yy, yy := y) o id(x := xx, xx := x)) P = 
 swap (swap P x xx) y yy"
apply(subst term.rrename_comps[symmetric])
by auto

(* NB: The entities affected by variables are passed as witnesses to exI 
with x and (the fresh) xx swapped, whereas the non-affected ones are passed 
as they are. 
*)
lemma GG_fresh: 
"(\<forall>\<sigma> t. ssbij \<sigma> \<and> R t \<longrightarrow> R (Tmap \<sigma> t)) \<Longrightarrow> G R v t \<Longrightarrow> 
 \<exists>w. Vfvars w  \<inter> Tfvars t = {} \<and> G R w t"
unfolding G_def Tmap_def Vmap_def apply(elim disjE exE conjE)
  (* Inp: *) 
  subgoal for x a u P
  using exists_fresh[of "[]" "[t]"] apply(elim exE conjE)
  subgoal for xx
  apply(rule exI[of _ "[xx]"])  
  apply(rule conjI)
    subgoal unfolding ssbij_def small_def Vmap_def by auto 
    subgoal apply(rule disjI7_1) 
    apply(rule exI[of _ "xx"]) 
    apply(rule exI[of _ "a"])
    apply(rule exI[of _ "u"]) 
    apply(rule exI[of _ "swap P x xx"])
    apply(cases t) 
    by (simp add: Inp_refresh usub_refresh) . .
  (* Open: *)
  subgoal for P a x P'
  using exists_fresh[of "[]" "[t]"] apply(elim exE conjE)
  subgoal for xx
  apply(rule exI[of _ "[xx]"])  
  apply(rule conjI)
    subgoal unfolding ssbij_def small_def Vmap_def by auto 
    subgoal apply(rule disjI7_2) 
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
      by (auto simp: ssbij_def split: if_splits ) . .
  (* ScopeF: *)
  subgoal for P act P' x
  using bvars_act_bout[of act] apply(elim disjE exE)
    subgoal
    using exists_fresh[of "[]" "[t]"] apply(elim exE conjE)
    subgoal for xx
    apply(rule exI[of _ "[xx]"])  
    apply(rule conjI)
      subgoal unfolding ssbij_def small_def Vmap_def by auto 
      subgoal apply(rule disjI7_3) 
      apply(rule exI[of _ "swap P x xx"])
      apply(rule exI[of _ "swapa act x xx"]) 
      apply(rule exI[of _ "swap P' x xx"])
      apply(rule exI[of _ "xx"]) 
      apply(cases t) apply simp apply(intro conjI)
        subgoal using Res_refresh by blast
        subgoal using Res_refresh apply(cases act, simp_all split: if_splits)  
          by blast+
        subgoal by auto
        subgoal apply(erule allE[of _ "id(x:=xx,xx:=x)"])
        apply(erule allE[of _ "P"])
        apply(erule allE[of _ "Cmt act P'"]) 
        by (auto simp: ssbij_def split: if_splits ) . . .
    (* *)
    subgoal for a b
    using exists_fresh[of "[a,b]" "[t]"] apply(elim exE conjE)
    subgoal for xx
    apply(rule exI[of _ "[xx]"])  
    apply(rule conjI)
      subgoal unfolding ssbij_def small_def Vmap_def by auto 
      subgoal apply(rule disjI7_3) 
      apply(rule exI[of _ "swap P x xx"]) 
      apply(rule exI[of _ "act"]) 
      apply(rule exI[of _ "swap P' x xx"])
      apply(rule exI[of _ "xx"]) 
      apply(cases t) apply simp apply(intro conjI)
        subgoal using Res_refresh by blast
        subgoal using Res_refresh[symmetric] by blast           
        subgoal apply(erule allE[of _ "id(x:=xx,xx:=x)"])
        apply(erule allE[of _ "P"])
        apply(erule allE[of _ "Cmt act P'"]) 
        by (auto simp: ssbij_def split: if_splits ) . . . .
  (* ScopeB: *)
  subgoal for P a x P' y
  using exists_fresh[of "[a,x,y]" "[t]"] apply(elim exE conjE)
  subgoal for yy
  using exists_fresh[of "[a,x,y,yy]" "[t]"] apply(elim exE conjE)
  subgoal for xx  
  apply(rule exI[of _ "[xx,yy]"])  
  apply(rule conjI)
    subgoal unfolding ssbij_def small_def Vmap_def by auto 
    subgoal apply(rule disjI7_4)
    apply(rule exI[of _ "swap (swap P x xx) y yy"])
    apply(rule exI[of _ "a"]) 
    apply(rule exI[of _ "xx"])
    apply(rule exI[of _ "swap (swap P' x xx) y yy"]) 
    apply(cases t) apply simp apply(intro conjI)
      subgoal using Res_refresh by auto
      apply(erule allE[of _ "id(x:=xx,xx:=x) o id(y:=yy,yy:=y)"])
      apply(erule allE[of _ "P"])
      apply(erule allE[of _ "Bout a x P'"])      
      apply (auto simp: ssbij_def sw_def split: if_splits) 
        subgoal using infinite_var not_ordLeq_ordLess supp_comp_bound by blast
        subgoal by (metis (no_types, lifting) Res_inject_swap Res_refresh) 
        subgoal apply(subgoal_tac "swap (swap P y yy) x xx = swap P y yy")
        defer subgoal apply(rule FFVars_swap) by (auto simp: sw_def)
        apply(subst swap_commute) apply(auto simp: sw_def)
        sledgehammer sorry . . . .
  (* *)
  subgoal for P1 act P1' P2
  using bvars_act_bout[of act] apply(elim disjE exE)
    subgoal
    using exists_fresh[of "[]" "[t]"] apply(elim exE conjE)
    subgoal for yy
    apply(rule exI[of _ "[]"])  
    apply(rule conjI)
      subgoal unfolding ssbij_def small_def Vmap_def by auto 
      subgoal apply(rule disjI7_5) 
      apply(rule exI[of _ P1])
      apply(rule exI[of _ act]) 
      apply(rule exI[of _ P1'])
      apply(rule exI[of _ P2]) 
      apply(cases t) by simp  . . 
    (* *)
    subgoal for a b
    using exists_fresh[of "[a,b]" "[t]"] apply(elim exE conjE)
    subgoal for bb
    apply(rule exI[of _ "[bb]"])  
    apply(rule conjI)
      subgoal unfolding ssbij_def small_def Vmap_def by auto 
      subgoal apply(rule disjI7_5)
      apply(rule exI[of _ P1]) 
      apply(rule exI[of _ "bout a bb"]) 
      apply(rule exI[of _ "swap P1' b bb"])
      apply(rule exI[of _ P2]) 
      apply(cases t) apply simp  
      by (metis Bout_inj) . . . 
  (* Com1: *)
  subgoal for P1 a x P1' P2 P2'
  apply(rule exI[of _ "[]"])  
  apply(rule conjI)
  subgoal unfolding ssbij_def small_def Vmap_def by auto 
  subgoal apply(rule disjI7_6) 
    apply(rule exI[of _ P1])
    apply(rule exI[of _ a]) 
    apply(rule exI[of _ x])
    apply(rule exI[of _ P1']) 
    apply(rule exI[of _ P2]) 
    apply(rule exI[of _ P2']) 
    apply(cases t) by simp  .  
  (* Par1: *)
  subgoal for P1 a x P1' P2 P2'
  using exists_fresh[of "[a,x]" "[t]"] apply(elim exE conjE)
  subgoal for xx
  apply(rule exI[of _ "[xx]"])  
  apply(rule conjI)
    subgoal unfolding ssbij_def small_def Vmap_def by auto 
    subgoal apply(rule disjI7_7)
    apply(rule exI[of _ "swap P1 x xx"]) 
    apply(rule exI[of _ a]) 
    apply(rule exI[of _ xx])
    apply(rule exI[of _ "swap P1' x xx"])
    apply(rule exI[of _ P2]) 
    apply(rule exI[of _ "swap P2' x xx"]) 
    apply(cases t) apply simp apply(intro conjI)
      subgoal apply(erule allE[of _ "id(x:=xx,xx:=x)"])
      apply(erule allE[of _ "P1"])
      apply(erule allE[of _ "Finp a x P1'"])      
      by (auto simp: ssbij_def split: if_splits) 
      subgoal apply(erule allE[of _ "id(x:=xx,xx:=x)"])
      apply(erule allE[of _ "P1"])
      apply(erule allE[of _ "Bout a x P1'"])      
      apply (auto simp: ssbij_def split: if_splits)  
      by (metis Bout_inj)+ . . . .

(* FINALLY, INTERPRETING THE Induct LOCALE: *)

interpretation Induct where dummy = "undefined :: var" and 
Tmap = Tmap and Tfvars = Tfvars
and Vmap = Vmap and Vfvars = Vfvars and G = G
apply standard 
  using GG_mono GG_equiv GG_fresh by auto


lemma trans_I: "trans t1 t2 = I (t1,t2)" 
  unfolding trans_def I_def lfp_curry2 apply(rule arg_cong2[of _ _ _ _ lfp], simp_all)
  unfolding fun_eq_iff G_def apply clarify
  subgoal for R PP QQ apply(rule iffI)
    subgoal apply(elim disjE exE)
      \<^cancel>\<open>Inp: \<close>
      subgoal apply(rule exI) apply(rule disjI7_1) by auto
      \<^cancel>\<open>Open: \<close>
      subgoal apply(rule exI) apply(rule disjI7_2) by auto
      \<^cancel>\<open>ScopeF: \<close> 
      subgoal apply(rule exI) apply(rule disjI7_3) by auto
      \<^cancel>\<open>ScopeB: \<close> 
      subgoal for P a x P' y 
      apply(rule exI[of _ "[x, y]"]) apply(rule disjI7_4) 
      by (auto simp: sw_def)
      \<^cancel>\<open>Par1: \<close>
      subgoal apply(rule exI) apply(rule disjI7_5) by auto
      \<^cancel>\<open>Com1: \<close> 
      subgoal apply(rule exI) apply(rule disjI7_6) by auto
      \<^cancel>\<open>Close1: \<close> 
      subgoal apply(rule exI) apply(rule disjI7_7) by auto .
    (* *)
    subgoal apply(elim disjE exE)
      \<^cancel>\<open>Inp: \<close>
      subgoal apply(rule disjI7_1) by auto
      \<^cancel>\<open>Open: \<close>
      subgoal apply(rule disjI7_2) by fastforce
      \<^cancel>\<open>ScopeF: \<close> 
      subgoal apply(rule disjI7_3) by auto
      \<^cancel>\<open>ScopeB: \<close> 
      subgoal apply(rule disjI7_4) by (fastforce simp: sw_def)
      \<^cancel>\<open>Par1: \<close>
      subgoal apply(rule disjI7_5) by auto
      \<^cancel>\<open>Com1: \<close> 
      subgoal apply(rule disjI7_6) by auto
      \<^cancel>\<open>Close1: \<close> 
      subgoal apply(rule disjI7_7) by auto . . .

(* FROM ABSTRACT BACK TO CONCRETE: *)
thm trans.induct[of P C \<phi>, no_vars]

corollary BE_induct_trans: 
assumes 
par: "(\<And>p. small (Pfvars p))" 
and tr: "trans P C"
and Inp: 
"\<And>x a u P p. x \<notin> {a, u} \<Longrightarrow> 
    \<phi> p (Inp a x P) (Finp a u (usub P u x))"
and Open:  
"\<And>P a x P' p. x \<notin> Pfvars p \<Longrightarrow> x \<noteq> a \<Longrightarrow> 
    trans P (Fout a x P') \<Longrightarrow> (\<forall>p'. \<phi> p' P (Fout a x P')) \<Longrightarrow> a \<noteq> x \<Longrightarrow> 
    \<phi> p (Res x P) (Bout a x P')"
and ScopeF: 
"\<And>P act P' y p. y \<notin> Pfvars p \<Longrightarrow> y \<notin> fvars act \<Longrightarrow> 
    trans P (Cmt act P') \<Longrightarrow> (\<forall>p'. \<phi> p' P (Cmt act P')) \<Longrightarrow> y \<notin> vars act \<Longrightarrow> 
    \<phi> p (Res y P) (Cmt act (Res y P'))"
and ScopeB: 
"\<And>P a x P' y p. {x,y} \<inter> Pfvars p = {} \<Longrightarrow> a \<notin> {x,y} \<Longrightarrow> 
    trans P (Bout a x P') \<Longrightarrow> (\<forall>p'. \<phi> p' P (Bout a x P')) \<Longrightarrow> y \<notin> {a, x} \<Longrightarrow> x \<notin> {a} \<union> FFVars P \<Longrightarrow>
    \<phi> p (Res y P) (Bout a x (Res y P'))" 
and Par1: 
"\<And>P1 act P1' P2 p. set (bvars act) \<inter> (Pfvars p \<union> fvars act) = {} \<Longrightarrow> 
    trans P1 (Cmt act P1') \<Longrightarrow>
    (\<forall>p'. \<phi> p' P1 (Cmt act P1')) \<Longrightarrow>
    set (bvars act) \<inter> FFVars P1 = {} \<Longrightarrow> 
    set (bvars act) \<inter> FFVars P2 = {} \<Longrightarrow> 
    \<phi> p (Par P1 P2) (Cmt act (Par P1' P2))"
and Com1: 
"\<And>P1 a x P1' P2 P2' p. 
    trans P1 (Finp a x P1') \<Longrightarrow>
    (\<forall>p'. \<phi> p' P1 (Finp a x P1')) \<Longrightarrow> 
    trans P2 (Fout a x P2') \<Longrightarrow> 
    (\<forall>p'. \<phi> p' P2 (Fout a x P2')) \<Longrightarrow> 
    \<phi> p (Par P1 P2) (Tau (Par P1' P2'))"
and Close1: 
"\<And>P1 a x P1' P2 P2' p. x \<notin> Pfvars p \<Longrightarrow> x \<notin> FFVars P2 \<Longrightarrow> 
    trans P1 (Finp a x P1') \<Longrightarrow>
    (\<forall>p'. \<phi> p' P1 (Finp a x P1')) \<Longrightarrow>
    trans P2 (Bout a x P2') \<Longrightarrow>
    (\<forall>p'. \<phi> p' P2 (Bout a x P2')) \<Longrightarrow> 
    x \<notin> {a} \<union> FFVars P1 \<Longrightarrow> 
    \<phi> p (Par P1 P2) (Bout a x (Par P1' P2'))"
shows "\<phi> p P C" 
apply(subgoal_tac "case (P,C) of (P, C) \<Rightarrow> \<phi> p P C")
  subgoal by simp
  subgoal using par tr apply(elim BE_induct[where R = "\<lambda>p (P,C). \<phi> p P C"])
    subgoal unfolding trans_I by simp
    subgoal for p v t apply(subst (asm) G_def) 
    unfolding trans_I[symmetric] apply (auto split: if_splits) 
      subgoal using Inp by auto
      subgoal using Inp by auto (* not clear how this appeared... *)
      subgoal using Open by auto
      subgoal for Pa act P' y using ScopeF[of y p act] by (cases act, auto) 
      subgoal using ScopeB by auto
      subgoal for P1 act P1' P2 using Par1[of act] by (cases act, auto)
      subgoal using Com1 by auto
      subgoal using Close1 by auto . . .



end