theory Bimodels_are_Models
  imports Bimodels Models
begin

(* Producing a recursion principle for bimodels by organizing them as models.  *)

context Bimodel 
begin 

lemma ctorPermM: "ctorPermM Ector' Eperm u"
  unfolding ctorPermM_def apply safe
  subgoal for \<sigma>
    apply(subst ctor1PermM[unfolded ctorPermM_def, rule_format])
    subgoal by blast
    subgoal unfolding Gmap_comp Gmap_Gren unfolding o_def by simp . .

lemma ctorVarsM: "ctorVarsM Ector' EVrs u"
unfolding ctorVarsM_def  apply(intro allI)
    apply(rule subset_trans[OF ctor1VarsM[unfolded ctorVarsM_def, rule_format]]) 
    by auto


(* models from special_models: *)
sublocale M : Model where Ector' = Ector' and Eperm' = Eperm and EVrs' = EVrs 
apply standard 
using nom ctorPermM ctorVarsM by auto   


(* Borrowing the recursion from models, under the assumption that E 
is inital; I essentially copy the recursor, and I customize it a bit 
for the two constructors. (This is expected from the bimodels, which are 
clearly model-like in structure, namely are constructor-based. 
What will be remarkable about these bimodels is that these will also give comodels, 
and extract the same recursion principle from corecursion/finality.) *)

thm M.rec_Ector M.rec_Eperm M.rec_unique M.rec_EVrs[no_vars] M.rec_Eperm[no_vars]
definition "mrec \<equiv> M.rec"

theorem mrec_Ector_\<phi>: 
shows "GVrs2 u \<inter> PVrs p = {} \<Longrightarrow> mrec (Ector u) p = Ector' (Gmap mrec mrec u) p"
unfolding mrec_def
  apply(rule M.rec_Ector) .

theorem mrec_Eperm: 
"small \<sigma> \<Longrightarrow> bij \<sigma> \<Longrightarrow> mrec(Eperm \<sigma> e) p = Eperm \<sigma> (mrec e (Pperm (inv \<sigma>) p))"
unfolding mrec_def using M.rec_Eperm by auto

theorem mrec_EVrs: "EVrs (mrec e p) \<subseteq> PVrs p \<union> EVrs e"
unfolding mrec_def using M.rec_EVrs by auto

theorem mrec_unique:
assumes "\<And>u p. GVrs2 u \<inter> PVrs p = {} \<Longrightarrow>
 (H (Ector u) p = Ector' (Gmap H H u) p)"
shows "H = mrec" 
unfolding mrec_def
apply(rule M.rec_unique) 
using assms by blast

end (* context Bimodel *)


end