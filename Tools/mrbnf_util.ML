signature MRBNF_UTIL =
sig
  include BNF_UTIL

  val filter_like: 'a list -> ('a -> bool) -> 'b list -> 'b list
  val cond_keep: 'a list -> bool list -> 'a list
  val cond_interlace: 'a list -> 'a list -> bool list -> 'a list
  val cond_automap: ('a -> 'a) -> 'a list -> bool list -> 'a list
  val short_type_name: string -> string

  val mk_supp: term -> term
  val mk_imsupp: term -> term
  val mk_inv: term -> term
  val mk_bij: term -> term
  val mk_Un: term * term -> term
  val mk_Int: term * term -> term
  val mk_infinite_regular_card_order: term -> term
  val mk_id_on: term -> term -> term
  val mk_card_suc: term -> term
  val mk_cmin: term * term -> term
  val mk_singleton: term -> term
  val mk_bot: typ -> term
  val mk_int_empty: term * term -> term;

  val mk_case_tuple: (string * typ) list -> term -> term

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

  val unfold_thms_tac': Proof.context -> thm list -> (Proof.context -> tactic) -> tactic

  val mk_abs_def2: Proof.context -> thm -> thm
  val mk_arg_cong: Proof.context -> int -> term -> thm
end;

structure MRBNF_Util : MRBNF_UTIL =
struct

open BNF_Util

fun mk_arg_cong ctxt n t =
  let
    val Us = fastype_of t |> strip_typeN n |> fst;
    val ((xs, ys), _) = ctxt
      |> mk_Frees "x" Us
      ||>> mk_Frees "y" Us;
    val goal = Logic.list_implies (@{map 2} (curry mk_Trueprop_eq) xs ys,
      mk_Trueprop_eq (list_comb (t, xs), list_comb (t, ys)));
    val vars = Variable.add_free_names ctxt goal [];
  in
    Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      HEADGOAL (hyp_subst_tac ctxt THEN' rtac ctxt refl))
    |> Thm.close_derivation \<^here>
  end;

fun mk_case_tuple [] t = t
  | mk_case_tuple [(s, T)] t = Term.absfree (s, T) t
  | mk_case_tuple ((s1, T1)::xs) t = HOLogic.mk_case_prod (Term.absfree (s1, T1) (mk_case_tuple xs t))

fun mk_cmin (t1, t2) =
  let
    val T1 = fastype_of t1;
    val T2 = fastype_of t2;
    val T = mk_sumT (apply2 (fst o dest_relT) (T1, T2));
  in Const (@{const_name cmin}, T1 --> T2 --> mk_relT (T, T)) $ t1 $ t2 end

fun mk_bot T = Const (@{const_name bot}, HOLogic.mk_setT T)

fun mk_singleton t =
  let
    val T = fastype_of t;
    val sT = HOLogic.mk_setT T;
  in Const (@{const_name Set.insert}, T --> sT --> sT) $ t $ mk_bot T end

fun mk_int_empty sets = HOLogic.mk_eq (
  HOLogic.mk_binop @{const_name inf} sets,
  Const (@{const_name bot}, fastype_of (fst sets))
);

fun short_type_name full_name = String.tokens (fn c => c = #".") full_name |> List.last;

fun filter_like xs P = map snd o filter (P o fst) o map2 pair xs;

fun  cond_interlace _ _ [] = []
        | cond_interlace xs [] _ = xs
        | cond_interlace [] ys _ = ys
        | cond_interlace (x :: xs) ys (true :: bs) = x :: cond_interlace xs ys bs
        | cond_interlace xs (y :: ys) (false :: bs) = y :: cond_interlace xs ys bs

fun cond_keep xs bs = (map fst o filter snd) (xs ~~ bs)

fun cond_automap f xs bs = map (fn (x, b) => if b then f x else x) (xs ~~ bs)

fun mk_supp t = let val T = t |> fastype_of |> dest_funT |> fst
  in Const (@{const_name Prelim.supp}, (T --> T) --> HOLogic.mk_setT T) $ t end;
fun mk_imsupp u =
  let val T = fastype_of u
  in Const (@{const_name imsupp}, T --> HOLogic.mk_setT (fst (dest_funT T))) $ u end;

fun mk_inv t =
  let
    val fT = fastype_of t;
    val (finvT, T) = dest_funT fT |> `swap |>> op --> ||> fst;
  in
    Const (@{const_name inv_into}, HOLogic.mk_setT T --> fT --> finvT) $ HOLogic.mk_UNIV T $ t
  end;

val mk_Un = HOLogic.mk_binop @{const_name sup};
val mk_Int = HOLogic.mk_binop @{const_name inf};

fun mk_id_on t1 t2 = let val (T, ST) = fastype_of t1 |> `HOLogic.dest_setT;
  in Const (@{const_name id_on}, ST --> (T --> T) --> HOLogic.boolT) $ t1 $ t2 end;

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

fun unfold_thms_tac' ctxt thms tac = PRIMITIVE (
  Conv.fconv_rule (Conv.prems_conv ~1 (Raw_Simplifier.rewrite_cterm (true, false, true) (SINGLE o tac)
    (Raw_Simplifier.init_simpset (map (Local_Defs.meta_rewrite_rule ctxt) thms) ctxt)))
  );

(*transforms f x y = h x y into f = h using first order matches for f, h, x, y*)
fun mk_abs_def2 ctxt thm = thm
  |> Thm.prop_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
  |> apply2 (dest_comb #> fst #> dest_comb #> fst)
  |> mk_Trueprop_eq
  |> (fn goal => Goal.prove_sorry ctxt [] [] goal
    (fn {context=ctxt, prems=_} => rtac ctxt ext 1 THEN rtac ctxt ext 1 THEN rtac ctxt thm 1))
  |> Thm.close_derivation \<^here>;

fun mk_sucT T = Type (\<^type_name>\<open>suc\<close>, [T])
fun mk_card_suc r =
  let val T = fst (BNF_Util.dest_relT (fastype_of r));
  in Const (\<^const_name>\<open>card_suc\<close>, BNF_Util.mk_relT (T, T) --> BNF_Util.mk_relT (mk_sucT T, mk_sucT T)) $ r end;

end;
