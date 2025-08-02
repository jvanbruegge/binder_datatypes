theory Bimodels_are_Models
  imports Bimodels Models
begin

(* Bimodels are of course particilar cases of models. 
Namely, they are models whose domain is syntactic 
and such that the constructor has some affinities with 
the syntactic constructor. Maybe we should instead call them 
"syntactic models" or "special models". 

NB. The only reason why I don't define Bimodel as an extension of the 
Model locale is because, having syntactic domain, the nominal 
part of the assumptions already hold (hence need not be postulated).  *)

context Bimodel 
begin 

sublocale M : Model where Ector' = Ector' and Eperm' = Eperm and EVrs' = EVrs 
apply standard 
using nom ctorPermM_Ector' ctorVarsM_Ector' 
ctor_compat_Pvalid_Ector' by auto

(* So the recursion principle holds for bimodels, simply by virtue of them being models.  
What will be remarkable about these bimodels is that these will also give comodels, 
and extract the same recursion principle from corecursion/finality.) *)

thm M.rec_Ector M.rec_Eperm M.rec_unique M.rec_EVrs[no_vars] M.rec_Eperm[no_vars]


end (* context Bimodel *)


end