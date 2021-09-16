theory Composition
  imports "thys/Prelim"
  keywords
    "print_mrbnfs" :: diag and
    "mrbnf" :: thy_goal
begin

ML_file \<open>Tools/mrbnf_util.ML\<close>
ML_file \<open>Tools/mrbnf_def_tactics.ML\<close>
ML_file \<open>Tools/mrbnf_def.ML\<close>

datatype \<kappa> =
  Star ("\<star>")
  | KArrow \<kappa> \<kappa> (infixr "\<rightarrow>" 50)

typedef ('tyvar, 'btyvar, 'c, 'd) pre_\<tau> = "{ x. x \<in> (UNIV :: ('tyvar + unit + 'd * 'd + 'btyvar * \<kappa> * 'c) set) }"
  by simp
(*
  TyVar 'tyvar
  | TyArrow
  | TyApp 'd 'd
  | TyForall 'btyvar \<kappa> 'c
*)

ML \<open>
fun mrbnf_tactics bnf = {
  map_id0 = fn ctxt => HEADGOAL (resolve_tac ctxt [BNF_Def.map_id0_of_bnf bnf]),
  map_comp0 = fn ctxt => HEADGOAL (resolve_tac ctxt [BNF_Def.map_comp0_of_bnf bnf]),
  map_cong0 = fn ctxt => HEADGOAL (SUBGOAL (K (HEADGOAL (resolve_tac ctxt [BNF_Def.map_cong0_of_bnf bnf]) THEN REPEAT (Goal.assume_rule_tac ctxt 1)))),
  set_map0 = map (fn thm => fn ctxt => HEADGOAL (resolve_tac ctxt [thm])) (BNF_Def.set_map0_of_bnf bnf),
  infinite_regular_card_order = fn ctxt => EVERY (map (HEADGOAL o resolve_tac ctxt o single) [@{thm infinite_regular_card_order_card_suc}, BNF_Def.bd_card_order_of_bnf bnf, BNF_Def.bd_Cinfinite_of_bnf bnf]),
  set_bd = map (fn thm => fn ctxt => EVERY (map (HEADGOAL o resolve_tac ctxt o single) [@{thm card_suc_greater_set}, BNF_Def.bd_card_order_of_bnf bnf, thm])) (BNF_Def.set_bd_of_bnf bnf),
  le_rel_OO = fn ctxt => HEADGOAL (resolve_tac ctxt [BNF_Def.le_rel_OO_of_bnf bnf]),
  in_rel = fn ctxt => Local_Defs.unfold_tac ctxt [@{thm OO_Grp_alt}, BNF_Def.map_id_of_bnf bnf, BNF_Def.in_rel_of_bnf bnf, @{thm Set.mem_Collect_eq}] THEN HEADGOAL (resolve_tac ctxt [@{thm refl}]),
  pred_set = fn ctxt => HEADGOAL (resolve_tac ctxt [BNF_Def.pred_set_of_bnf bnf]),
  wit = fn ctxt => EVERY (map (HEADGOAL o eresolve_tac ctxt o single) (BNF_Def.wit_thms_of_bnf bnf))
}

fun mk_sucT T = Type (\<^type_name>\<open>suc\<close>, [T])
fun mk_card_suc r =
  let val T = fst (BNF_Util.dest_relT (fastype_of r));
  in Const (\<^const_name>\<open>card_suc\<close>, BNF_Util.mk_relT (T, T) --> BNF_Util.mk_relT (mk_sucT T, mk_sucT T)) $ r end;

fun mrbnf_of_bnf bnf lthy =
  let val n = BNF_Def.live_of_bnf bnf
      val nwits = BNF_Def.nwits_of_bnf bnf
      val (((lives, lives'), deads), lthy') = lthy
        |> Ctr_Sugar_Util.mk_TFrees n
        ||>> Ctr_Sugar_Util.mk_TFrees n
        ||>> Ctr_Sugar_Util.mk_TFrees' (map Type.sort_of_atyp (BNF_Def.deads_of_bnf bnf))
  in MRBNF_Def.mrbnf_def MRBNF_Def.Do_Inline (K MRBNF_Def.Dont_Note) false I (mrbnf_tactics bnf) (SOME deads) NONE
      Binding.empty Binding.empty Binding.empty []
    (((((((BNF_Def.name_of_bnf bnf, BNF_Def.mk_T_of_bnf deads lives bnf), BNF_Def.mk_map_of_bnf deads lives lives' bnf),
    map (fn x => (MRBNF_Def.Live_Var, x)) (BNF_Def.mk_sets_of_bnf (replicate n deads) (replicate n lives) bnf)),
    mk_card_suc (BNF_Def.mk_bd_of_bnf deads lives bnf)),
    map snd (BNF_Def.mk_wits_of_bnf (replicate nwits deads) (replicate nwits lives) bnf)),
    SOME (BNF_Def.mk_rel_of_bnf deads lives lives' bnf)),
    SOME (BNF_Def.mk_pred_of_bnf deads lives bnf))
    lthy'
  end;

fun bnf_tac ctxt bnf = let val tacs = mrbnf_tactics bnf; in (
  #map_id0 tacs ctxt THEN #map_comp0 tacs ctxt THEN #map_cong0 tacs ctxt THEN EVERY (map (fn f => f ctxt) (#set_map0 tacs))
  THEN #infinite_regular_card_order tacs ctxt THEN EVERY (map (fn f => f ctxt) (#set_bd tacs)) THEN #le_rel_OO tacs ctxt
  THEN #in_rel tacs ctxt THEN #pred_set tacs ctxt
)
end;

fun register_bnf_as_mrbnf bnf lthy =
  let val (mrbnf, lthy') = mrbnf_of_bnf bnf lthy
  in MRBNF_Def.register_mrbnf_raw (Binding.name_of (BNF_Def.name_of_bnf bnf)) mrbnf lthy' end
\<close>

datatype ('a, 'b) sum2 = L 'a | R 'b
datatype ('a, 'b) dead = Test 'b "'a set"

ML \<open>
val SOME sum2 = BNF_Def.bnf_of @{context} \<^type_name>\<open>sum2\<close>
val SOME dead = BNF_Def.bnf_of @{context} \<^type_name>\<open>dead\<close>
\<close>

local_setup \<open>register_bnf_as_mrbnf sum2\<close>
local_setup \<open>register_bnf_as_mrbnf dead\<close>

print_mrbnfs
print_bnfs

end
