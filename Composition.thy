theory Composition
  imports "thys/MRBNF_Recursor"
begin

declare [[mrbnf_internals]]

datatype \<kappa> =
  Star ("\<star>")
  | KArrow \<kappa> \<kappa> (infixr "\<rightarrow>" 50)

(*
binder_datatype 'var \<tau> =
  | TyVar 'var
  | TyArrow
  | TyApp "'var \<tau>" "'var \<tau>"
  | TyForall a::"'var" \<kappa> t::"'var \<tau>" binds a in t

  \<down>

  'tyvar
+ unit
+ 'rec * 'rec
+ 'btyvar * \<kappa> * 'body
*)

declare [[ML_print_depth=10000000]]
local_setup \<open>fn lthy =>
let
  val systemf_type_name = "\<tau>_pre"
  val systemf_type = @{typ "'tyvar + unit + 'rec * 'rec + 'btyvar * \<kappa> * 'body"}
  val Xs = []
  val resBs = map dest_TFree [@{typ 'tyvar}, @{typ 'btyvar}, @{typ 'body}, @{typ 'rec}]
  fun flatten_tyargs Ass = subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;
  val qualify = Binding.prefix_name (systemf_type_name ^ "_")

  val ((mrbnf, tys), (accum, lthy)) = MRBNF_Comp.mrbnf_of_typ false MRBNF_Def.Smart_Inline qualify flatten_tyargs Xs []
    [(dest_TFree @{typ 'tyvar}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'btyvar}, MRBNF_Def.Bound_Var)] systemf_type
    ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy)
  val ((mrbnf, (Ds, info)), lthy) = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name systemf_type_name) true (fst tys) [] mrbnf lthy
  val (bnf, lthy) = MRBNF_Def.register_mrbnf_as_bnf mrbnf lthy
  val (res, lthy) = MRBNF_FP.construct_binder_fp MRBNF_Util.Least_FP [(("\<tau>", mrbnf), 2)] [[0]] lthy;
  val (rec_mrbnf, lthy) = MRBNF_VVSubst.mrbnf_of_quotient_fixpoint @{binding vvsubst} I (hd res) lthy;
  val lthy = MRBNF_Def.register_mrbnf_raw (fst (dest_Type (#T (#quotient_fp (hd res))))) rec_mrbnf lthy;
in lthy end
\<close>
print_theorems
print_bnfs
print_mrbnfs

(************************************************************************************)

lemma TT_inject:
  fixes t t'::"('a::var_\<tau>_pre, 'a, 'a \<tau>, 'a \<tau>) \<tau>_pre"
  shows "\<tau>_ctor t = \<tau>_ctor t' \<longleftrightarrow> (\<exists>f. bij f \<and> |supp f| <o |UNIV::'a set| \<and> id_on (\<Union>(FFVars_\<tau> ` set3_\<tau>_pre t) - set2_\<tau>_pre t) f \<and> map_\<tau>_pre id f (vvsubst f) id t = t')"
  unfolding \<tau>.TT_injects0 conj_assoc[symmetric]
  apply (rule ex_cong)
  apply (erule conjE)+
  unfolding vvsubst_rrename
  subgoal premises prems for f
    unfolding vvsubst_rrename[OF prems(2,3)]
    apply (rule refl)
    done
  done

end
