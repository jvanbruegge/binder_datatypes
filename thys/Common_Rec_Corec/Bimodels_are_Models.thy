theory Bimodels_are_Models
  imports Bimodels Models
begin

(* Producing a recursion principle for bimodels by organizing them as models.  *)

context Bimodel 
begin 

 
(* definition EEctor' :: "('a::var,'a,'a P\<Rightarrow>'a E','a P\<Rightarrow>'a E') G \<Rightarrow> 'a P\<Rightarrow>'a E'" where 
"EEctor' u \<equiv> if base u then Ector' u else Ector' u"
*)

(* lemma EEctor'_base[simp]: "base u \<Longrightarrow> EEctor' u = Ector' u"
unfolding EEctor'_def by auto

lemma EEctor'_step[simp]: "\<not> base u \<Longrightarrow> EEctor' u = Ector' u"
unfolding EEctor'_def by auto *)

(*
lemma ctorPermM: "ctorPermM Ector' Eperm u"
unfolding ctorPermM_def apply safe
  subgoal for \<sigma> apply(cases "base u") 
    subgoal unfolding EEctor'_base  
    apply(subst ctorPermM_Ector'[unfolded ctorPermM_def, rule_format])
      subgoal by auto
      subgoal apply(subst EEctor'_base )
        subgoal using base_Gmap base_Gren by fastforce
        subgoal unfolding Gmap_comp Gmap_Gren unfolding o_def by simp . .
    subgoal unfolding EEctor'_step  
    apply(subst ctorPermM_Ector'[unfolded ctorPermM_def, rule_format])
      subgoal using base_Gmap by auto
      subgoal apply(subst EEctor'_step)
        subgoal using base_Gmap base_Gren by fastforce
        subgoal unfolding Gmap_comp Gmap_Gren unfolding o_def by simp . . . .

lemma ctorVarsM: "ctorVarsM EEctor' EVrs u"
unfolding ctorVarsM_def  
  apply(cases "base u")
    subgoal unfolding EEctor'_base  apply(intro allI impI)  
    apply(rule subset_trans[OF ctorVarsM_Ector'[unfolded ctorVarsM_def, rule_format]])
    by auto 
    subgoal unfolding EEctor'_step apply(intro allI impI) 
    apply(rule subset_trans[OF ctorVarsM_Ector'[unfolded ctorVarsM_def, rule_format]]) 
    using base_Gmap by auto . 
*)


(* models from special_models: *)
sublocale M : Model where Ector' = Ector' and Eperm' = Eperm and EVrs' = EVrs 
apply standard 
using nom ctorPermM_Ector' ctorVarsM_Ector' ctor_compat_Pvalid_Ector' by auto

(* Borrowing the recursion from models, under the assumption that E 
is inital; I essentially just copy the recursor. (This is expected from the bimodels, which are 
clearly model-like in structure, namely are constructor-based. 
What will be remarkable about these bimodels is that these will also give comodels, 
and extract the same recursion principle from corecursion/finality.) *)

thm M.rec_Ector M.rec_Eperm M.rec_unique M.rec_EVrs[no_vars] M.rec_Eperm[no_vars]
definition "mrec \<equiv> M.rec"

lemmas mrec_Ector = M.rec_Ector[unfolded mrec_def[symmetric]]
lemmas mrec_Eperm = M.rec_Eperm[unfolded mrec_def[symmetric]]
lemmas mrec_EVrs = M.rec_EVrs[unfolded mrec_def[symmetric]]
lemmas mrec_unique = M.rec_unique[unfolded mrec_def[symmetric]]

end (* context Bimodel *)


end