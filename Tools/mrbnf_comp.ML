signature MRBNF_COMP =
sig
  type vars = {
    lives: (string * sort) list,
    frees: (string * sort) list,
    bounds: (string * sort) list,
    deads: (string * sort) list
  }

  val ID_mrbnf: MRBNF_Def.mrbnf
  val DEADID_mrbnf: MRBNF_Def.mrbnf

  val mrbnf_of_typ: vars -> typ -> local_theory -> MRBNF_Def.mrbnf * local_theory
  val as_mrbnf: string -> local_theory -> (MRBNF_Def.mrbnf * local_theory) option
end;

structure MRBNF_Comp : MRBNF_COMP =
struct

open MRBNF_Def

type vars = {
  lives: (string * sort) list,
  frees: (string * sort) list,
  bounds: (string * sort) list,
  deads: (string * sort) list
}

val ID_mrbnf = the (mrbnf_of \<^context> "BNF_Composition.ID");
val DEADID_mrbnf = the (mrbnf_of \<^context> "BNF_Composition.DEADID");

fun as_mrbnf name lthy' =
  (case mrbnf_of lthy' name of
    SOME mrbnf => SOME (mrbnf, lthy')
    | NONE =>
      (case BNF_Def.bnf_of lthy' name of
        SOME bnf => SOME (register_bnf_as_mrbnf NONE bnf lthy')
        | NONE => NONE
      )
  )

fun mrbnf_of_typ vars T lthy =
  let val _ = ""
  in (case T of
    Type (name, args) =>
      (case as_mrbnf name lthy of
        SOME (outer_mrbnf, lthy') => (
          writeln ("success: " ^ Pretty.string_of (Syntax.pretty_typ lthy T));
          let val (inner_mrbnfs, lthy'') = List.foldr (fn (t, (xs, lthy1)) => mrbnf_of_typ vars t lthy1 |>> (fn x => x::xs)) ([], lthy') args
          in (outer_mrbnf, lthy'') end (* TODO: Actually compose and don't just return the outer mrbnf *)
        )
        | NONE => (writeln ("TODO: dead type: " ^ Pretty.string_of (Syntax.pretty_typ lthy T)) ; (DEADID_mrbnf, lthy))
      )
    | TVar (i, s) => (error "foo bound", lthy)
    | TFree T' => if member (op =) (#deads vars) T' then
        (DEADID_mrbnf, lthy)
        else
      (ID_mrbnf, lthy)
  ) end;

end;