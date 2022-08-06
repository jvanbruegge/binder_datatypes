signature MRBNF_UTIL =
sig
  include BNF_UTIL

  val filter_like: 'a list -> ('a -> bool) -> 'b list -> 'b list
  val cond_keep: 'a list -> bool list -> 'a list
  val cond_interlace: 'a list -> 'a list -> bool list -> 'a list
  val cond_automap: ('a -> 'a) -> 'a list -> bool list -> 'a list

  val mk_ordLess: term -> term -> term
  val mk_supp: term -> term
  val mk_inv: term -> term
  val mk_bij: term -> term
  val mk_infinite_regular_card_order: term -> term

  val new_typedef: binding -> term -> (Proof.context -> tactic) -> local_theory ->
    (string * Typedef.info) * local_theory
  val thm_instantiate_terms: Proof.context -> term option list -> thm -> thm
  val thm_instantiate_dummy_terms: Proof.context -> term option list -> thm -> thm
  val thm_instantiate_fixed_terms: Proof.context -> term option list -> term list -> thm -> thm
  val new_definition: binding -> term -> local_theory -> (string * term * thm) * local_theory

  val simp_only_tac: Proof.context -> thm list -> int -> tactic
  val simp_only: Proof.context -> thm list -> int -> tactic
  val simp_only_plus: Proof.context -> thm list -> (int -> tactic) list -> int -> tactic
  val simp_only_subgoal: Proof.context -> thm list -> (int -> tactic) list -> int -> tactic
  val simp_only_all_new: Proof.context -> thm list -> (int -> tactic) list -> int -> tactic

  val asm_simp_only_tac: Proof.context -> thm list -> int -> tactic
  val asm_simp_only: Proof.context -> thm list -> int -> tactic
  val asm_simp_only_plus: Proof.context -> thm list -> (int -> tactic) list -> int -> tactic
  val asm_simp_only_subgoal: Proof.context -> thm list -> (int -> tactic) list -> int -> tactic
  val asm_simp_only_all_new: Proof.context -> thm list -> (int -> tactic) list -> int -> tactic

  val mk_abs_def2: Proof.context -> thm -> thm
end;

structure MRBNF_Util : MRBNF_UTIL =
struct

open BNF_Util

fun filter_like xs P = map snd o filter (P o fst) o map2 pair xs;

fun  cond_interlace _ _ [] = []
        | cond_interlace xs [] _ = xs
        | cond_interlace [] ys _ = ys
        | cond_interlace (x :: xs) ys (true :: bs) = x :: cond_interlace xs ys bs
        | cond_interlace xs (y :: ys) (false :: bs) = y :: cond_interlace xs ys bs

fun cond_keep xs bs = (map fst o filter snd) (xs ~~ bs)

fun cond_automap f xs bs = map (fn (x, b) => if b then f x else x) (xs ~~ bs)

fun mk_ordLess t1 t2 = HOLogic.mk_mem (HOLogic.mk_prod (t1, t2),
  Const (@{const_name ordLess}, mk_relT (fastype_of t1, fastype_of t2)));

fun mk_supp t = let val T = t |> fastype_of |> dest_funT |> fst
  in Const (@{const_name Prelim.supp}, (T --> T) --> HOLogic.mk_setT T) $ t end;

fun mk_inv t =
  let
    val fT = fastype_of t;
    val (finvT, T) = dest_funT fT |> `swap |>> op --> ||> fst;
  in
    Const (@{const_name inv_into}, HOLogic.mk_setT T --> fT --> finvT) $ HOLogic.mk_UNIV T $ t
  end;

fun mk_bij t = t
  |> fastype_of
  |> dest_funT
  |> apply2 HOLogic.mk_UNIV
  |-> BNF_LFP_Util.mk_bij_betw t;

fun mk_infinite_regular_card_order bd =
  let
    val T = fastype_of bd;
  in
    Const (@{const_name infinite_regular_card_order}, T --> HOLogic.boolT) $ bd
  end;

fun new_typedef binding t tac = typedef
  (binding, Term.add_tfreesT (fastype_of t) [] |> rev, Mixfix.NoSyn) t NONE tac;

fun thm_instantiate_terms lthy = Thm.cterm_of lthy |> Option.map |> map #> infer_instantiate' lthy;

fun thm_instantiate_dummy_terms lthy terms thm =
  let
    fun fix_dummies_option (SOME t) = Variable.fix_dummy_patterns t #>> SOME
      | fix_dummies_option NONE = pair NONE;
    val (dterms, lthy') = fold_map fix_dummies_option terms lthy;
  in
    thm_instantiate_terms lthy' dterms thm |> singleton (Variable.export lthy' lthy)
  end;

fun thm_instantiate_fixed_terms lthy terms fixes thm =
  let
    fun mk_var (s, T) = (Binding.name s, SOME T, NoSyn);
    val vars = map (mk_var o dest_Free) fixes;
    val (_, lthy') = Proof_Context.add_fixes vars lthy;
  in
    thm_instantiate_terms lthy' terms thm |> singleton (Variable.export lthy' lthy)
  end;

fun new_definition binding rhs lthy =
  let
    val ((term, (string, raw_def)), lthy1) = Local_Theory.begin_nested lthy |> snd
      |> Local_Theory.define ((binding, NoSyn),
        ((Thm.def_binding binding |> Binding.concealed, []), rhs));
    val lthy2 = Local_Theory.end_nested lthy1;
    val phi = Proof_Context.export_morphism lthy1 lthy2;
    val def_thm = Morphism.thm phi raw_def;
    val term = Morphism.term phi term;
  in
    ((string, term, def_thm), lthy2)
  end;

fun simp_only_tac ctxt thms = BNF_Util.ss_only thms ctxt |> full_simp_tac;
val simp_only = CHANGED ooo simp_only_tac;
fun simp_only_plus ctxt thms tacs = REPEAT_DETERM o FIRST' (simp_only ctxt thms :: tacs);
fun simp_only_subgoal ctxt thms tacs = simp_only_plus ctxt thms tacs |> SELECT_GOAL o HEADGOAL;
fun simp_only_all_new ctxt thms tacs = REPEAT_ALL_NEW (FIRST' (simp_only ctxt thms :: tacs));

fun asm_simp_only_tac ctxt thms = BNF_Util.ss_only thms ctxt |> asm_full_simp_tac;
val asm_simp_only = CHANGED ooo asm_simp_only_tac;
fun asm_simp_only_plus ctxt thms tacs = REPEAT_DETERM o FIRST' (asm_simp_only ctxt thms :: tacs);
fun asm_simp_only_subgoal ctxt thms tacs = asm_simp_only_plus ctxt thms tacs
  |> SELECT_GOAL o HEADGOAL;
fun asm_simp_only_all_new ctxt thms tacs =
  REPEAT_ALL_NEW (DETERM o FIRST' (asm_simp_only ctxt thms :: tacs));

(*transforms f x y = h x y into f = h using first order matches for f, h, x, y*)
fun mk_abs_def2 ctxt thm = thm
  |> Thm.prop_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
  |> apply2 (dest_comb #> fst #> dest_comb #> fst)
  |> mk_Trueprop_eq
  |> (fn goal => Goal.prove_sorry ctxt [] [] goal
    (fn {context=ctxt, prems=_} => rtac ctxt ext 1 THEN rtac ctxt ext 1 THEN rtac ctxt thm 1))
  |> Thm.close_derivation \<^here>;

end;
