signature MRSBNF_COMP = sig

  val id_mrsbnf: MRSBNF_Def.mrsbnf

  val mrsbnf_of_typ: bool -> BNF_Def.inline_policy -> (theory -> BNF_Def.fact_policy)
    -> (binding -> binding) -> ((string * sort) * MRBNF_Def.var_type) list -> typ
    -> (thm list * local_theory) -> MRSBNF_Def.mrsbnf option * (thm list * local_theory)

end

structure MRSBNF_Comp : MRSBNF_COMP = struct

val id_mrsbnf = the (MRSBNF_Def.mrsbnf_of @{context} "BNF_Composition.ID");

fun mrsbnf_of_typ _ _ _ _ var_types (TFree (x, _)) accum = (case AList.lookup ((op=) o apsnd fst) var_types x of
  SOME MRBNF_Def.Free_Var => (SOME id_mrsbnf, accum)
  | _ => (SOME id_mrsbnf, accum))
  | mrsbnf_of_typ _ _ _ _ _ (TVar _) _ = error "unexpected schematic variable"
  | mrsbnf_of_typ optim const_policy inline_policy qualify var_types (T as Type (n, Ts)) (accum, lthy) =
    let
      
    in error "bar" end;

end