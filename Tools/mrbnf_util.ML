signature MRBNF_UTIL =
sig
  include BNF_UTIL

  datatype ('a, 'b) either = Inl of 'a | Inr of 'b
  val map_sum: ('a -> 'c) -> ('b -> 'd) -> ('a, 'b) either -> ('c, 'd) either
  val either: ('a -> 'c) -> ('b -> 'c) -> ('a, 'b) either -> 'c

  val filter_like: 'a list -> ('a -> bool) -> 'b list -> 'b list
  val cond_keep: 'a list -> bool list -> 'a list
  val cond_interlace: 'a list -> 'a list -> bool list -> 'a list
  val cond_automap: ('a -> 'a) -> 'a list -> bool list -> 'a list
  val short_type_name: string -> string
  val swap: 'a * 'b -> 'b * 'a
  val partition: ('a -> bool) -> 'a list -> 'a list * 'a list

  val subst_typ_morphism: (typ * typ) list -> morphism

  val mk_supp: term -> term
  val mk_supp_bound: term -> term
  val mk_imsupp: term -> term
  val mk_inv: term -> term
  val mk_bij: term -> term
  val mk_Un: term * term -> term
  val mk_Int: term * term -> term
  val mk_infinite_regular_card_order: term -> term
  val mk_id_on: term -> term -> term
  val mk_eq_on: term -> term -> term ->term
  val mk_card_suc: term -> term
  val mk_cmin: term * term -> term
  val mk_singleton: term -> term
  val mk_bot: typ -> term
  val mk_int_empty: term * term -> term;
  val mk_sum_ctors: term list -> term list;
  val mk_minus: term * term -> term;
  val mk_all: string * typ -> term -> term;
  val mk_ex: string * typ -> term -> term;
  val mk_insert: term -> term -> term;

  val dest_ordLess: term -> term * term;
  val dest_ordLeq: term -> term * term;
  val dest_card_of: term -> term;

  val strip_ex: term -> (string * typ) list * term

  val mk_conj_thms: int -> local_theory -> thm * thm * thm
  val mk_case_tuple: (string * typ) list -> term -> term
  val split_conj: int -> thm -> thm list

  val new_typedef: binding -> term -> (Proof.context -> tactic) -> local_theory ->
    (string * Typedef.info) * local_theory
  val thm_instantiate_terms: Proof.context -> term option list -> thm -> thm
  val thm_instantiate_dummy_terms: Proof.context -> term option list -> thm -> thm
  val thm_instantiate_fixed_terms: Proof.context -> term option list -> term list -> thm -> thm
  val new_definition: binding -> term -> local_theory -> (string * term * thm) * local_theory
  val mk_def_t_syn: mixfix -> bool -> binding -> (binding -> binding) -> bstring -> int -> term
    -> local_theory -> ((term * thm) * local_theory);
  val mk_def_t: bool -> binding -> (binding -> binding) -> bstring -> int -> term
    -> local_theory -> ((term * thm) * local_theory);
  val mk_defs_t: bool -> binding -> (binding -> binding) -> bstring -> int -> term list
    -> local_theory -> ((term * thm) list * local_theory);

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

datatype ('a, 'b) either = Inl of 'a | Inr of 'b

fun map_sum f _ (Inl x) = Inl (f x)
  | map_sum _ g (Inr y) = Inr (g y)

fun either f _ (Inl x) = f x
  | either _ g (Inr y) = g y

fun strip_ex (Const (@{const_name Ex}, _) $ Abs (x, T, t)) = apfst (cons (x, T)) (strip_ex t)
  | strip_ex t = ([], t)

fun swap (a, b) = (b, a)
fun partition _ [] = ([], [])
  | partition f (x::xs) = (if f x then apfst else apsnd) (cons x) (partition f xs)

fun partition _ [] = ([], [])
  | partition f (x::xs) = (if f x then apfst else apsnd) (cons x) (partition f xs)

val mk_minus = HOLogic.mk_binop @{const_name minus};
fun mk_all (x, T) t = HOLogic.mk_all (x, T, t);
fun mk_ex (x, T) t = HOLogic.mk_exists (x, T, t);

fun mk_insert x S =
  Const (@{const_name Set.insert}, fastype_of x --> fastype_of S --> fastype_of S) $ x $ S;

fun subst_typ_morphism subst = Morphism.morphism "subst_typ" {
  binding = [], fact = [],
  term = [K (Term.subst_atomic_types subst)],
  typ = [K (Term.typ_subst_atomic subst)]
};

fun dest_ordLess t =
  let val t' = case HOLogic.dest_mem t of
    (t', Const (@{const_name ordLess}, _)) => t'
    | _ => raise TERM ("dest_ordLess", [t])
  in HOLogic.dest_prod t' end
fun dest_ordLeq t =
  let val t' = case HOLogic.dest_mem t of
    (t', Const (@{const_name ordLeq}, _)) => t'
    | _ => raise TERM ("dest_ordLeq", [t])
  in HOLogic.dest_prod t' end
fun dest_card_of (Const (@{const_name card_of}, _) $ t) = t
  | dest_card_of t = raise TERM ("dest_card_of", [t])

fun mk_def_t_syn syn public b qualify name n rhs lthy =
  let
    val b' = qualify (Binding.name name);
    val b'' = if Binding.is_empty b then b' else Binding.prefix_name (Binding.name_of b' ^ "_") b;
    val b' = if public then b' else Binding.concealed b'';
    val ((t, thm), lthy) = apfst (apsnd snd) (Local_Theory.define_internal (
      (b', syn), ((Binding.concealed (Thm.def_binding b'), []), rhs)
    ) lthy);
    val thm' = if n > 0 then
      @{thm eq_reflection} OF [Ctr_Sugar_Util.mk_unabs_def n (@{thm meta_eq_to_obj_eq} OF [thm])]
    else thm;
    val lthy = if (* public *) true then
      snd (Local_Theory.note ((Thm.def_binding b', []), [thm']) lthy)
    else lthy;
  in ((t, thm'), lthy) end;

val mk_def_t = mk_def_t_syn NoSyn;

fun mk_defs_t public b qualify name n [x] = apfst single o mk_def_t public b qualify name n x
  | mk_defs_t public b qualify name n rhss = fold_map (fn (i, x) =>
      mk_def_t public b qualify (name ^ string_of_int i) n x) (1 upto length rhss ~~ rhss)

fun mk_arg_cong ctxt 1 t = infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt t)] arg_cong
  | mk_arg_cong ctxt 2 t = infer_instantiate' ctxt (replicate 4 NONE @ [SOME (Thm.cterm_of ctxt t)]) @{thm arg_cong2}
  | mk_arg_cong ctxt n t =
  let
    val Us = fastype_of t |> strip_typeN n |> fst;
    val ((xs, ys), _) = ctxt
      |> mk_Frees "x" Us
      ||>> mk_Frees "y" Us;
    val goal = Logic.list_implies (@{map 2} (curry mk_Trueprop_eq) xs ys,
      mk_Trueprop_eq (list_comb (t, xs), list_comb (t, ys)));
    val vars = Variable.add_free_names ctxt goal [];
    val vars = case t of
      Free (x, _) => subtract (op=) [x] vars
      | _ => vars;
  in
    Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      HEADGOAL (hyp_subst_tac ctxt THEN' rtac ctxt refl))
    |> Thm.close_derivation \<^here>
  end;

fun split_conj n thm = if n = 1 then [thm]
  else let val (thms, thm) = fold_map
    (K (fn thm => (thm RS conjunct1, thm RS conjunct2))) (1 upto n - 1) thm
  in thms @ [thm] end;

val imp_forward1 = @{lemma "(P \<Longrightarrow> Q) \<Longrightarrow> (Q \<longrightarrow> Z) \<Longrightarrow> (P \<longrightarrow> Z)"
  by blast
}

fun mk_conj_thms n lthy = if n = 1 then (spec, mp, imp_forward1) else
  let
    val (Ts, _) = mk_TFrees n lthy;
    val ((Ps1, xs), _) = lthy
      |> mk_Frees "P" (map (fn a => a --> @{typ bool}) Ts)
      ||>> mk_Frees "x" Ts;

    val (((Ps2, Qs), Zs), _) = lthy
      |> mk_Frees "P" (map (K @{typ bool}) Ts)
      ||>> mk_Frees "Q" (map (K @{typ bool}) Ts)
      ||>> mk_Frees "Z" (map (K @{typ bool}) Ts);

    val conj_spec_goal = Logic.mk_implies (
      HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (
        map (fn P => HOLogic.mk_all ("x", fst (dest_funT (fastype_of P)), P $ Bound 0)) Ps1
      )),
      HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (map2 (curry (op$)) Ps1 xs))
    );
    val conj_spec = Goal.prove_sorry lthy (map (fst o dest_Free) (Ps1 @ xs)) [] conj_spec_goal (fn {context=ctxt, ...} => EVERY1 [
      REPEAT_DETERM o eresolve_tac ctxt [conjE, allE],
      REPEAT_DETERM o EVERY' [
        TRY o rtac ctxt conjI,
        assume_tac ctxt
      ]
    ]);

    val conj_mp_goal = fold_rev (curry Logic.mk_implies o HOLogic.mk_Trueprop) (
      foldr1 HOLogic.mk_conj (map2 (curry HOLogic.mk_imp) Ps2 Qs) :: Ps2
    ) (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj Qs));
    val conj_mp = Goal.prove_sorry lthy (map (fst o dest_Free) (Ps2 @ Qs)) [] conj_mp_goal (fn {context=ctxt, ...} => EVERY1 [
      REPEAT_DETERM o etac ctxt conjE,
      REPEAT_DETERM o (etac ctxt impE THEN' assume_tac ctxt),
      REPEAT_DETERM o EVERY' [
        TRY o rtac ctxt conjI,
        assume_tac ctxt
      ]
    ]);

    val conj_imp_forward1_goal = fold_rev (curry Logic.mk_implies) (
      map (Logic.mk_implies o apply2 HOLogic.mk_Trueprop) (Ps2 ~~ Qs) @ [HOLogic.mk_Trueprop (
        foldr1 HOLogic.mk_conj (map2 (curry HOLogic.mk_imp) Qs Zs)
      )]
    ) (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (map2 (curry HOLogic.mk_imp) Ps2 Zs)));
    val conj_imp_forward1 = Goal.prove_sorry lthy (map (fst o dest_Free) (Ps2 @ Qs @ Zs)) [] conj_imp_forward1_goal (fn {context=ctxt, ...} => REPEAT_DETERM (EVERY1 [
      TRY o etac ctxt @{thm conj_forward},
      etac ctxt @{thm imp_forward},
      Goal.assume_rule_tac ctxt,
      assume_tac ctxt
    ]))
  in (conj_spec, conj_mp, conj_imp_forward1) end;

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

fun mk_sum_ctors [x] = [x]
  | mk_sum_ctors [x, y] =
    [BNF_FP_Util.mk_Inl (fastype_of y) x, BNF_FP_Util.mk_Inr (fastype_of x) y]
  | mk_sum_ctors (x::xs) =
     let val ctors = mk_sum_ctors xs
     in (BNF_FP_Util.mk_Inl (fastype_of (hd ctors)) x::(
      map (BNF_FP_Util.mk_Inr (fastype_of x)) ctors)) end

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

fun mk_supp_bound f = mk_ordLess (mk_card_of (mk_supp f))
  (mk_card_of (HOLogic.mk_UNIV (fst (dest_funT (fastype_of f)))));

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

fun mk_eq_on A f1 f2 =
  let val fT = fastype_of f1
  in Const (@{const_name eq_on}, fastype_of A --> fT --> fT --> @{typ bool}) $ A $ f1 $ f2 end

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

local

val parameter = Parse.position Parse.nat >> (fn (n, pos) =>
  if n > 1 then n else error ("Bad parameter: " ^ string_of_int n ^ Position.here pos));

fun indices n = map string_of_int (1 upto n);
fun cons n = implode (map (fn a => " (x" ^ a ^ " :: xs" ^ a ^ ")") (indices n));
fun vars x n = implode (map (fn a => " " ^ x ^ a) (indices n));

in

val _ = Theory.setup
 (ML_Antiquotation.value \<^binding>\<open>map_filter\<close>
    (Scan.lift parameter >> (fn n =>
      "fn f =>\n\
      \  let\n\
      \    fun map_filter _" ^ replicate_string n " []" ^ " = []\n\
      \      | map_filter f" ^ cons n ^ " = let val ys = map_filter f" ^ vars "xs" n ^ " in the_default ys (Option.map (fn y => y::ys) (f" ^ vars "x" n ^ ")) end\n\
      \      | map_filter _" ^ replicate_string n " _" ^ " = raise ListPair.UnequalLengths\n" ^
      "  in map_filter f end")))
end;

end;
