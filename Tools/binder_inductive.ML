signature BINDER_INDUCTIVE =
sig
  type result =
    {preds: term list, elims: thm list, raw_induct: thm,
     induct: thm, inducts: thm list, intrs: thm list, eqs: thm list}
  val transform_result: morphism -> result -> result
  type info = {names: string list, coind: bool} * result
  val the_inductive: Proof.context -> term -> info
  val the_inductive_global: Proof.context -> string -> info
  val mk_cases_tac: Proof.context -> tactic
  val mk_cases: Proof.context -> term -> thm
  val inductive_forall_def: thm
  val rulify: Proof.context -> thm -> thm
  type flags =
    {quiet_mode: bool, verbose: bool, alt_name: binding,
      no_elim: bool, no_ind: bool, skip_mono: bool}
  val add_inductive:
    flags -> ((binding * typ) * mixfix) list ->
    (string * typ) list -> (Attrib.binding * term) list -> term -> term -> term list -> thm list -> local_theory ->
    result * local_theory
  val add_inductive_cmd: bool ->
    (binding * string option * mixfix) list ->
    (binding * string option * mixfix) list ->
    Specification.multi_specs_cmd ->
    string -> string -> string option list ->
    (Facts.ref * Token.src list) list ->
    local_theory -> result * local_theory
  val arities_of: thm -> (string * int) list
  val params_of: thm -> term list
  val partition_rules: thm -> thm list -> (string * thm list) list
  val partition_rules': thm -> (thm * 'a) list -> (string * (thm * 'a) list) list
  val unpartition_rules: thm list -> (string * 'a list) list -> 'a list
  val infer_intro_vars: theory -> thm -> int -> thm list -> term list list
  val inductive_internals: bool Config.T
  val select_disj_tac: Proof.context -> int -> int -> int -> tactic
  type add_ind_def =
    flags ->
    term list -> (Attrib.binding * term) list -> term -> term -> term list -> thm list ->
    term list -> (binding * mixfix) list ->
    local_theory -> Proof.state
  val declare_rules: binding -> bool -> binding -> string list -> term list ->
    thm list -> binding list -> Token.src list list -> (thm * string list * int) list ->
    thm list -> thm -> local_theory -> thm list * thm list * thm list * thm * thm list * local_theory
  val add_ind_def: add_ind_def
  val gen_add_inductive: add_ind_def -> flags ->
    ((binding * typ) * mixfix) list -> (string * typ) list -> (Attrib.binding * term) list ->
    term -> term -> term list -> thm list -> local_theory -> result * local_theory
  val gen_add_inductive_cmd: add_ind_def -> bool ->
    (binding * string option * mixfix) list ->
    (binding * string option * mixfix) list ->
    Specification.multi_specs_cmd -> string -> string -> string option list -> (Facts.ref * Token.src list) list ->
    local_theory -> result * local_theory
  val gen_ind_decl: add_ind_def -> (local_theory -> local_theory) parser
end;

structure Binder_Inductive =
struct

open BNF_Util
open BNF_FP_Util

(** theory context references **)

val inductive_forall_def = @{thm HOL.induct_forall_def};
val inductive_conj_def = @{thm HOL.induct_conj_def};
val inductive_conj = @{thms induct_conj};
val inductive_atomize = @{thms induct_atomize};
val inductive_rulify = @{thms induct_rulify};
val inductive_rulify_fallback = @{thms induct_rulify_fallback};

val simp_thms1 =
  map mk_meta_eq
    @{lemma "(\<not> True) = False" "(\<not> False) = True"
        "(True \<longrightarrow> P) = P" "(False \<longrightarrow> P) = True"
        "(P \<and> True) = P" "(True \<and> P) = P"
      by (fact simp_thms)+};

val simp_thms2 =
  map mk_meta_eq [@{thm inf_fun_def}, @{thm inf_bool_def}] @ simp_thms1;



(** misc utilities **)

val inductive_internals = Attrib.setup_config_bool \<^binding>\<open>inductive_internals\<close> (K false);

fun message quiet_mode s = if quiet_mode then () else writeln s;

fun clean_message ctxt quiet_mode s =
  if Config.get ctxt quick_and_dirty then () else message quiet_mode s;

fun log (b: int) m n = if m >= n then 0 else 1 + log b (b * m) n;

fun make_bool_args f g [] i = []
  | make_bool_args f g (x :: xs) i =
      (if i mod 2 = 0 then f x else g x) :: make_bool_args f g xs (i div 2);

fun make_bool_args' xs =
  make_bool_args (K \<^term>\<open>False\<close>) (K \<^term>\<open>True\<close>) xs;

fun arg_types_of k c = drop k (binder_types (fastype_of c));

fun find_arg T x [] = raise Fail "find_arg"
  | find_arg T x ((p as (_, (SOME _, _))) :: ps) =
      apsnd (cons p) (find_arg T x ps)
  | find_arg T x ((p as (U, (NONE, y))) :: ps) =
      if (T: typ) = U then (y, (U, (SOME x, y)) :: ps)
      else apsnd (cons p) (find_arg T x ps);

fun make_args Ts xs =
  map (fn (T, (NONE, ())) => Const (\<^const_name>\<open>undefined\<close>, T) | (_, (SOME t, ())) => t)
    (fold (fn (t, T) => snd o find_arg T t) xs (map (rpair (NONE, ())) Ts));

fun make_args' Ts xs Us =
  fst (fold_map (fn T => find_arg T ()) Us (Ts ~~ map (pair NONE) xs));

fun dest_predicate cs params t =
  let
    val k = length params;
    val (c, ts) = strip_comb t;
    val (xs, ys) = chop k ts;
    val i = find_index (fn c' => c' = c) cs;
  in
    if xs = params andalso i >= 0 then
      SOME (c, i, ys, chop (length ys) (arg_types_of k c))
    else NONE
  end;

fun mk_names a 0 = []
  | mk_names a 1 = [a]
  | mk_names a n = map (fn i => a ^ string_of_int i) (1 upto n);

fun select_disj_tac ctxt =
  let
    fun tacs 1 1 = []
      | tacs _ 1 = [resolve_tac ctxt @{thms disjI1}]
      | tacs n i = resolve_tac ctxt @{thms disjI2} :: tacs (n - 1) (i - 1);
  in fn n => fn i => EVERY' (tacs n i) end;

(** context data **)

type result =
  {preds: term list, elims: thm list, raw_induct: thm,
   induct: thm, inducts: thm list, intrs: thm list, eqs: thm list};

fun transform_result phi {preds, elims, raw_induct: thm, induct, inducts, intrs, eqs} =
  let
    val term = Morphism.term phi;
    val thm = Morphism.thm phi;
    val fact = Morphism.fact phi;
  in
   {preds = map term preds, elims = fact elims, raw_induct = thm raw_induct,
    induct = thm induct, inducts = fact inducts, intrs = fact intrs, eqs = fact eqs}
  end;

type info = {names: string list, coind: bool} * result;

val empty_infos =
  Item_Net.init (op = o apply2 (#names o fst)) (#preds o snd)

val empty_equations =
  Item_Net.init Thm.eq_thm_prop
    (single o fst o HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.prop_of);

datatype data = Data of
 {infos: info Item_Net.T,
  equations: thm Item_Net.T};

fun make_data (infos, equations) =
  Data {infos = infos, equations = equations};

structure Data = Generic_Data
(
  type T = data;
  val empty = make_data (empty_infos, empty_equations);
  fun merge (Data {infos = infos1, equations = equations1},
      Data {infos = infos2, equations = equations2}) =
    make_data (Item_Net.merge (infos1, infos2),
      Item_Net.merge (equations1, equations2));
);

fun map_data f =
  Data.map (fn Data {infos, equations} => make_data (f (infos, equations)));

fun rep_data ctxt = Data.get (Context.Proof ctxt) |> (fn Data rep => rep);


(* inductive info *)

fun the_inductive ctxt term =
  Item_Net.retrieve (#infos (rep_data ctxt)) term
  |> the_single
  |> apsnd (transform_result (Morphism.transfer_morphism' ctxt))

fun the_inductive_global ctxt name =
  #infos (rep_data ctxt)
  |> Item_Net.content
  |> filter (fn ({names, ...}, _) => member op = names name)
  |> the_single
  |> apsnd (transform_result (Morphism.transfer_morphism' ctxt))

fun put_inductives info =
  map_data (fn (infos, equations) =>
    (Item_Net.update (apsnd (transform_result Morphism.trim_context_morphism) info) infos, equations));

fun mk_mono ctxt thm =
  let
    fun eq_to_mono thm' = thm' RS (thm' RS @{thm eq_to_mono});
    fun dest_less_concl thm = dest_less_concl (thm RS @{thm le_funD})
      handle THM _ => thm RS @{thm le_boolD}
  in
    (case Thm.concl_of thm of
      Const (\<^const_name>\<open>Pure.eq\<close>, _) $ _ $ _ => eq_to_mono (HOLogic.mk_obj_eq thm)
    | _ $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ _) => eq_to_mono thm
    | _ $ (Const (\<^const_name>\<open>Orderings.less_eq\<close>, _) $ _ $ _) =>
      dest_less_concl (Seq.hd (REPEAT (FIRSTGOAL
        (resolve_tac ctxt [@{thm le_funI}, @{thm le_boolI'}])) thm))
    | _ => thm)
  end handle THM _ => error ("Bad monotonicity theorem:\n" ^ Thm.string_of_thm ctxt thm);


(* equations *)

val equation_add_permissive =
  Thm.declaration_attribute (fn thm =>
    map_data (fn (infos, equations) =>
      (infos, perhaps (try (Item_Net.update (Thm.trim_context thm))) equations)));



(** process rules **)

local

fun err_in_rule ctxt name t msg =
  error (cat_lines ["Ill-formed introduction rule " ^ Binding.print name,
    Syntax.string_of_term ctxt t, msg]);

fun err_in_prem ctxt name t p msg =
  error (cat_lines ["Ill-formed premise", Syntax.string_of_term ctxt p,
    "in introduction rule " ^ Binding.print name, Syntax.string_of_term ctxt t, msg]);

val bad_concl = "Conclusion of introduction rule must be an inductive predicate";

val bad_ind_occ = "Inductive predicate occurs in argument of inductive predicate";

val bad_app = "Inductive predicate must be applied to parameter(s) ";

fun atomize_term thy = Raw_Simplifier.rewrite_term thy inductive_atomize [];

in

fun check_rule ctxt cs params ((binding, att), rule) =
  let
    val params' = Term.variant_frees rule (Logic.strip_params rule);
    val frees = rev (map Free params');
    val concl = subst_bounds (frees, Logic.strip_assums_concl rule);
    val prems = map (curry subst_bounds frees) (Logic.strip_assums_hyp rule);
    val rule' = Logic.list_implies (prems, concl);
    val aprems = map (atomize_term (Proof_Context.theory_of ctxt)) prems;
    val arule = fold_rev (Logic.all o Free) params' (Logic.list_implies (aprems, concl));

    fun check_ind err t =
      (case dest_predicate cs params t of
        NONE => err (bad_app ^
          commas (map (Syntax.string_of_term ctxt) params))
      | SOME (_, _, ys, _) =>
          if exists (fn c => exists (fn t => Logic.occs (c, t)) ys) cs
          then err bad_ind_occ else ());

    fun check_prem' prem t =
      if member (op =) cs (head_of t) then
        check_ind (err_in_prem ctxt binding rule prem) t
      else
        (case t of
          Abs (_, _, t) => check_prem' prem t
        | t $ u => (check_prem' prem t; check_prem' prem u)
        | _ => ());

    fun check_prem (prem, aprem) =
      if can HOLogic.dest_Trueprop aprem then check_prem' prem prem
      else err_in_prem ctxt binding rule prem "Non-atomic premise";

    val _ =
      (case concl of
        Const (\<^const_name>\<open>Trueprop\<close>, _) $ t =>
          if member (op =) cs (head_of t) then
           (check_ind (err_in_rule ctxt binding rule') t;
            List.app check_prem (prems ~~ aprems))
          else err_in_rule ctxt binding rule' bad_concl
       | _ => err_in_rule ctxt binding rule' bad_concl);
  in
    ((binding, att), arule)
  end;

fun rulify ctxt =
  hol_simplify ctxt inductive_conj
  #> hol_simplify ctxt inductive_rulify
  #> hol_simplify ctxt inductive_rulify_fallback
  #> Simplifier.norm_hhf ctxt;

end;



(** proofs for (co)inductive predicates **)

(* prove monotonicity *)

fun prove_mono quiet_mode skip_mono predT fp_fun monos ctxt =
 (message (quiet_mode orelse skip_mono andalso Config.get ctxt quick_and_dirty)
    "  Proving monotonicity ...";
  (if skip_mono then Goal.prove_sorry else Goal.prove_future) ctxt
    [] []
    (HOLogic.mk_Trueprop
      (\<^Const>\<open>monotone_on predT predT for
          \<^Const>\<open>top \<^Type>\<open>set predT\<close>\<close> \<^Const>\<open>less_eq predT\<close> \<^Const>\<open>less_eq predT\<close> fp_fun\<close>))
    (fn _ => EVERY [resolve_tac ctxt @{thms monoI} 1,
      REPEAT (resolve_tac ctxt [@{thm le_funI}, @{thm le_boolI'}] 1),
      REPEAT (FIRST
        [assume_tac ctxt 1,
         resolve_tac ctxt (map (mk_mono ctxt) monos @ Inductive.get_monos ctxt) 1,
         eresolve_tac ctxt @{thms le_funE} 1,
         dresolve_tac ctxt @{thms le_boolD} 1])]));


(* prove introduction rules *)

fun prove_intrs quiet_mode mono fp_def k intr_ts rec_preds_defs ctxt ctxt' =
  let
    val _ = clean_message ctxt quiet_mode "  Proving the introduction rules ...";

    val unfold = funpow k (fn th => th RS fun_cong)
      (mono RS (fp_def RS @{thm def_lfp_unfold}));

    val rules = [refl, TrueI, @{lemma "\<not> False" by (rule notI)}, exI, conjI];

    val intrs = map_index (fn (i, intr) =>
      Goal.prove_sorry ctxt [] [] intr (fn _ => EVERY
       [rewrite_goals_tac ctxt rec_preds_defs,
        resolve_tac ctxt [unfold RS iffD2] 1,
        select_disj_tac ctxt (length intr_ts) (i + 1) 1,
        (*Not ares_tac, since refl must be tried before any equality assumptions;
          backtracking may occur if the premises have extra variables!*)
        DEPTH_SOLVE_1 (resolve_tac ctxt rules 1 APPEND assume_tac ctxt 1)])
       |> singleton (Proof_Context.export ctxt ctxt')) intr_ts

  in (intrs, unfold) end;


(* prove elimination rules *)

fun prove_elims quiet_mode cs params intr_ts intr_names unfold rec_preds_defs ctxt ctxt''' =
  let
    val _ = clean_message ctxt quiet_mode "  Proving the elimination rules ...";

    val ([pname], ctxt') = Variable.variant_fixes ["P"] ctxt;
    val P = HOLogic.mk_Trueprop (Free (pname, HOLogic.boolT));

    fun dest_intr r =
      (the (dest_predicate cs params (HOLogic.dest_Trueprop (Logic.strip_assums_concl r))),
       Logic.strip_assums_hyp r, Logic.strip_params r);

    val intrs = map dest_intr intr_ts ~~ intr_names;

    val rules1 = [disjE, exE, FalseE];
    val rules2 = [conjE, FalseE, @{lemma "\<not> True \<Longrightarrow> R" by (rule notE [OF _ TrueI])}];

    fun prove_elim c =
      let
        val Ts = arg_types_of (length params) c;
        val (anames, ctxt'') = Variable.variant_fixes (mk_names "a" (length Ts)) ctxt';
        val frees = map Free (anames ~~ Ts);

        fun mk_elim_prem ((_, _, us, _), ts, params') =
          Logic.list_all (params',
            Logic.list_implies (map (HOLogic.mk_Trueprop o HOLogic.mk_eq)
              (frees ~~ us) @ ts, P));
        val c_intrs = filter (equal c o #1 o #1 o #1) intrs;
        val prems = HOLogic.mk_Trueprop (list_comb (c, params @ frees)) ::
           map mk_elim_prem (map #1 c_intrs)
      in
        (Goal.prove_sorry ctxt'' [] prems P
          (fn {context = ctxt4, prems} => EVERY
            [cut_tac (hd prems) 1,
             rewrite_goals_tac ctxt4 rec_preds_defs,
             dresolve_tac ctxt4 [unfold RS iffD1] 1,
             REPEAT (FIRSTGOAL (eresolve_tac ctxt4 rules1)),
             REPEAT (FIRSTGOAL (eresolve_tac ctxt4 rules2)),
             EVERY (map (fn prem =>
               DEPTH_SOLVE_1 (assume_tac ctxt4 1 ORELSE
                resolve_tac ctxt [rewrite_rule ctxt4 rec_preds_defs prem, conjI] 1))
                (tl prems))])
          |> singleton (Proof_Context.export ctxt'' ctxt'''),
         map #2 c_intrs, length Ts)
      end

   in map prove_elim cs end;


(* prove simplification equations *)

fun prove_eqs quiet_mode cs params intr_ts intrs
    (elims: (thm * bstring list * int) list) ctxt ctxt'' =  (* FIXME ctxt'' ?? *)
  let
    val _ = clean_message ctxt quiet_mode "  Proving the simplification rules ...";

    fun dest_intr r =
      (the (dest_predicate cs params (HOLogic.dest_Trueprop (Logic.strip_assums_concl r))),
       Logic.strip_assums_hyp r, Logic.strip_params r);
    val intr_ts' = map dest_intr intr_ts;

    fun prove_eq c (elim: thm * 'a * 'b) =
      let
        val Ts = arg_types_of (length params) c;
        val (anames, ctxt') = Variable.variant_fixes (mk_names "a" (length Ts)) ctxt;
        val frees = map Free (anames ~~ Ts);
        val c_intrs = filter (equal c o #1 o #1 o #1) (intr_ts' ~~ intrs);
        fun mk_intr_conj (((_, _, us, _), ts, params'), _) =
          let
            fun list_ex ([], t) = t
              | list_ex ((a, T) :: vars, t) =
                  HOLogic.exists_const T $ Abs (a, T, list_ex (vars, t));
            val conjs = map2 (curry HOLogic.mk_eq) frees us @ map HOLogic.dest_Trueprop ts;
          in
            list_ex (params', if null conjs then \<^term>\<open>True\<close> else foldr1 HOLogic.mk_conj conjs)
          end;
        val lhs = list_comb (c, params @ frees);
        val rhs =
          if null c_intrs then \<^term>\<open>False\<close>
          else foldr1 HOLogic.mk_disj (map mk_intr_conj c_intrs);
        val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
        fun prove_intr1 (i, _) = Subgoal.FOCUS_PREMS (fn {context = ctxt'', params, prems, ...} =>
            select_disj_tac ctxt'' (length c_intrs) (i + 1) 1 THEN
            EVERY (replicate (length params) (resolve_tac ctxt'' @{thms exI} 1)) THEN
            (if null prems then resolve_tac ctxt'' @{thms TrueI} 1
             else
              let
                val (prems', last_prem) = split_last prems;
              in
                EVERY (map (fn prem =>
                  (resolve_tac ctxt'' @{thms conjI} 1 THEN resolve_tac ctxt'' [prem] 1)) prems')
                THEN resolve_tac ctxt'' [last_prem] 1
              end)) ctxt' 1;
        fun prove_intr2 (((_, _, us, _), ts, params'), intr) =
          EVERY (replicate (length params') (eresolve_tac ctxt' @{thms exE} 1)) THEN
          (if null ts andalso null us then resolve_tac ctxt' [intr] 1
           else
            EVERY (replicate (length ts + length us - 1) (eresolve_tac ctxt' @{thms conjE} 1)) THEN
            Subgoal.FOCUS_PREMS (fn {context = ctxt'', prems, ...} =>
              let
                val (eqs, prems') = chop (length us) prems;
                val rew_thms = map (fn th => th RS @{thm eq_reflection}) eqs;
              in
                rewrite_goal_tac ctxt'' rew_thms 1 THEN
                resolve_tac ctxt'' [intr] 1 THEN
                EVERY (map (fn p => resolve_tac ctxt'' [p] 1) prems')
              end) ctxt' 1);
      in
        Goal.prove_sorry ctxt' [] [] eq (fn _ =>
          resolve_tac ctxt' @{thms iffI} 1 THEN
          eresolve_tac ctxt' [#1 elim] 1 THEN
          EVERY (map_index prove_intr1 c_intrs) THEN
          (if null c_intrs then eresolve_tac ctxt' @{thms FalseE} 1
           else
            let val (c_intrs', last_c_intr) = split_last c_intrs in
              EVERY (map (fn ci => eresolve_tac ctxt' @{thms disjE} 1 THEN prove_intr2 ci) c_intrs')
              THEN prove_intr2 last_c_intr
            end))
        |> rulify ctxt'
        |> singleton (Proof_Context.export ctxt' ctxt'')
      end;
  in
    map2 prove_eq cs elims
  end;


(* derivation of simplified elimination rules *)

local

(*delete needless equality assumptions*)
val refl_thin = Goal.prove_global \<^theory>\<open>HOL\<close> [] [] \<^prop>\<open>\<And>P. a = a \<Longrightarrow> P \<Longrightarrow> P\<close>
  (fn {context = ctxt, ...} => assume_tac ctxt 1);
val elim_rls = [asm_rl, FalseE, refl_thin, conjE, exE];
fun elim_tac ctxt = REPEAT o eresolve_tac ctxt elim_rls;

fun simp_case_tac ctxt i =
  EVERY' [elim_tac ctxt,
    asm_full_simp_tac ctxt,
    elim_tac ctxt,
    REPEAT o bound_hyp_subst_tac ctxt] i;

in

fun mk_cases_tac ctxt = ALLGOALS (simp_case_tac ctxt) THEN prune_params_tac ctxt;

fun mk_cases ctxt prop =
  let
    fun err msg =
      error (Pretty.string_of (Pretty.block
        [Pretty.str msg, Pretty.fbrk, Syntax.pretty_term ctxt prop]));

    val elims = Induct.find_casesP ctxt prop;

    val cprop = Thm.cterm_of ctxt prop;
    fun mk_elim rl =
      Thm.implies_intr cprop
        (Tactic.rule_by_tactic ctxt (mk_cases_tac ctxt) (Thm.assume cprop RS rl))
      |> singleton (Proof_Context.export (Proof_Context.augment prop ctxt) ctxt);
  in
    (case get_first (try mk_elim) elims of
      SOME r => r
    | NONE => err "Proposition not an inductive predicate:")
  end;

end;


(* ind_cases *)

fun ind_cases_rules ctxt raw_props raw_fixes =
  let
    val (props, ctxt') = Specification.read_props raw_props raw_fixes ctxt;
    val rules = Proof_Context.export ctxt' ctxt (map (mk_cases ctxt') props);
  in rules end;

val _ =
  Theory.setup
    (Method.setup \<^binding>\<open>ind_cases\<close>
      (Scan.lift (Scan.repeat1 Parse.prop -- Parse.for_fixes) >>
        (fn (props, fixes) => fn ctxt =>
          Method.erule ctxt 0 (ind_cases_rules ctxt props fixes)))
      "case analysis for inductive definitions, based on simplified elimination rule");


(* prove induction rule *)

fun prove_indrule quiet_mode cs argTs bs xs rec_const params intr_ts mono
    fp_def rec_preds_defs ctxt ctxt''' =  (* FIXME ctxt''' ?? *)
  let
    val _ = clean_message ctxt quiet_mode "  Proving the induction rule ...";

    (* predicates for induction rule *)

    val (pnames, ctxt') = Variable.variant_fixes (mk_names "P" (length cs)) ctxt;
    val preds =
      map2 (curry Free) pnames
        (map (fn c => arg_types_of (length params) c ---> HOLogic.boolT) cs);

    (* transform an introduction rule into a premise for induction rule *)

    fun mk_ind_prem r =
      let
        fun subst s =
          (case dest_predicate cs params s of
            SOME (_, i, ys, (_, Ts)) =>
              let
                val k = length Ts;
                val bs = map Bound (k - 1 downto 0);
                val P = list_comb (nth preds i, map (incr_boundvars k) ys @ bs);
                val Q =
                  fold_rev Term.abs (mk_names "x" k ~~ Ts)
                    (HOLogic.mk_binop \<^const_name>\<open>HOL.induct_conj\<close>
                      (list_comb (incr_boundvars k s, bs), P));
              in (Q, case Ts of [] => SOME (s, P) | _ => NONE) end
          | NONE =>
              (case s of
                t $ u => (fst (subst t) $ fst (subst u), NONE)
              | Abs (a, T, t) => (Abs (a, T, fst (subst t)), NONE)
              | _ => (s, NONE)));

        fun mk_prem s prems =
          (case subst s of
            (_, SOME (t, u)) => t :: u :: prems
          | (t, _) => t :: prems);

        val SOME (_, i, ys, _) =
          dest_predicate cs params (HOLogic.dest_Trueprop (Logic.strip_assums_concl r));
      in
        fold_rev (Logic.all o Free) (Logic.strip_params r)
          (Logic.list_implies (map HOLogic.mk_Trueprop (fold_rev mk_prem
            (map HOLogic.dest_Trueprop (Logic.strip_assums_hyp r)) []),
              HOLogic.mk_Trueprop (list_comb (nth preds i, ys))))
      end;

    val ind_prems = map mk_ind_prem intr_ts;


    (* make conclusions for induction rules *)

    val Tss = map (binder_types o fastype_of) preds;
    val (xnames, ctxt'') = Variable.variant_fixes (mk_names "x" (length (flat Tss))) ctxt';
    val mutual_ind_concl =
      HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
        (map (fn (((xnames, Ts), c), P) =>
          let val frees = map Free (xnames ~~ Ts)
          in HOLogic.mk_imp (list_comb (c, params @ frees), list_comb (P, frees)) end)
        (unflat Tss xnames ~~ Tss ~~ cs ~~ preds)));


    (* make predicate for instantiation of abstract induction rule *)

    val ind_pred =
      fold_rev lambda (bs @ xs) (foldr1 HOLogic.mk_conj
        (map_index (fn (i, P) => fold_rev (curry HOLogic.mk_imp)
           (make_bool_args HOLogic.mk_not I bs i)
           (list_comb (P, make_args' argTs xs (binder_types (fastype_of P))))) preds));

    val ind_concl =
      HOLogic.mk_Trueprop
        (HOLogic.mk_binrel \<^const_name>\<open>Orderings.less_eq\<close> (rec_const, ind_pred));

    val raw_fp_induct = mono RS (fp_def RS @{thm def_lfp_induct});

    val induct = Goal.prove_sorry ctxt'' [] ind_prems ind_concl
      (fn {context = ctxt3, prems} => EVERY
        [rewrite_goals_tac ctxt3 [inductive_conj_def],
         DETERM (resolve_tac ctxt3 [raw_fp_induct] 1),
         REPEAT (resolve_tac ctxt3 [@{thm le_funI}, @{thm le_boolI}] 1),
         rewrite_goals_tac ctxt3 simp_thms2,
         (*This disjE separates out the introduction rules*)
         REPEAT (FIRSTGOAL (eresolve_tac ctxt3 [disjE, exE, FalseE])),
         (*Now break down the individual cases.  No disjE here in case
           some premise involves disjunction.*)
         REPEAT (FIRSTGOAL (eresolve_tac ctxt3 [conjE] ORELSE' bound_hyp_subst_tac ctxt3)),
         REPEAT (FIRSTGOAL
           (resolve_tac ctxt3 [conjI, impI] ORELSE'
           (eresolve_tac ctxt3 [notE] THEN' assume_tac ctxt3))),
         EVERY (map (fn prem =>
            DEPTH_SOLVE_1 (assume_tac ctxt3 1 ORELSE
              resolve_tac ctxt3
                [rewrite_rule ctxt3 (inductive_conj_def :: rec_preds_defs @ simp_thms2) prem,
                  conjI, refl] 1)) prems)]);

    val lemma = Goal.prove_sorry ctxt'' [] []
      (Logic.mk_implies (ind_concl, mutual_ind_concl)) (fn {context = ctxt3, ...} => EVERY
        [rewrite_goals_tac ctxt3 rec_preds_defs,
         REPEAT (EVERY
           [REPEAT (resolve_tac ctxt3 [conjI, impI] 1),
            REPEAT (eresolve_tac ctxt3 [@{thm le_funE}, @{thm le_boolE}] 1),
            assume_tac ctxt3 1,
            rewrite_goals_tac ctxt3 simp_thms1,
            assume_tac ctxt3 1])]);

  in singleton (Proof_Context.export ctxt'' ctxt''') (induct RS lemma) end;

(** specification of inductive predicates **)

fun mk_ind_def alt_name cs intros intr_ts mapx setx binds monos params cnames_syn lthy =
  let
    val varT = hd binds |> fastype_of |> HOLogic.dest_setT;
    val argTs = fold (combine (op =) o arg_types_of (length params)) cs [];
    val k = log 2 1 (length cs);
    val argT = mk_tupleT_balanced (replicate k HOLogic.boolT @ argTs)
    val predT = argT --> HOLogic.boolT;
    val mapT = (varT --> varT) --> argT --> argT;
    val setT = argT --> HOLogic.mk_setT varT;
    val B :: p :: xs =
      map Free (Variable.variant_frees lthy intr_ts
        (("B", HOLogic.mk_setT varT) :: ("p", predT) :: (mk_names "x" (length argTs) ~~ argTs)));
    val bs =
      map Free (Variable.variant_frees lthy (B :: p :: xs @ intr_ts)
        (map (rpair HOLogic.boolT) (mk_names "b" k)));

    fun subst p Zs t =
      (case dest_predicate cs params t of
        SOME (_, i, ts, (Ts, Us)) =>
          let
            val l = length Us;
            val zs = map Bound (l - 1 downto 0);
          in
            fold_rev (Term.abs o pair "z") Us
              (p $
                mk_tuple1_balanced (Us @ Zs) (make_bool_args' bs i @ make_args argTs
                  ((map (incr_boundvars l) ts ~~ Ts) @ (zs ~~ Us))))
          end
      | NONE =>
          (case t of
            t1 $ t2 => subst p Zs t1 $ subst p Zs t2
          | Abs (x, T, u) => Abs (x, T, subst p (T :: Zs) u)
          | _ => t));


    (* transform an introduction rule into a conjunction  *)
    (*   [| p_i t; ... |] ==> p_j u                       *)
    (* is transformed into                                *)
    (*   b_j & x_j = u & p b_j t & ...                    *)

    fun transform_rule bind r =
      let
        val SOME (_, i, ts, (Ts, _)) =
          dest_predicate cs params (HOLogic.dest_Trueprop (Logic.strip_assums_concl r));
        val ps =
          HOLogic.mk_eq (B, bind) ::
          make_bool_args HOLogic.mk_not I bs i @
          map HOLogic.mk_eq (make_args' argTs xs Ts ~~ ts) @
          map (subst p (Logic.strip_params r |> map snd |> rev) o HOLogic.dest_Trueprop) (Logic.strip_assums_hyp r);
      in
        fold_rev (fn (x, T) => fn P => HOLogic.exists_const T $ Abs (x, T, P))
          (Logic.strip_params r)
          (if null ps then \<^term>\<open>True\<close> else foldr1 HOLogic.mk_conj ps)
      end;

    (* make a disjunction of all introduction rules *)

    val fp_fun =
      lambda B (lambda p (HOLogic.tupled_lambda (mk_tuple_balanced (bs @ xs))
        (if null intr_ts then \<^term>\<open>False\<close>
         else foldr1 HOLogic.mk_disj (@{map 2} transform_rule binds intr_ts))));

     fun err s t T = s ^ " function\n" ^ Syntax.string_of_term lthy t ^
       "\ndoes not have the expected type\n" ^ Syntax.string_of_typ lthy T;
     val mapx = force_typ lthy mapT (mapx |> singleton (Variable.polymorphic lthy))
       handle ERROR _ => error (err "perm" mapx mapT);
     val setx = force_typ lthy setT (setx |> singleton (Variable.polymorphic lthy))
       handle ERROR _ => error (err "supp" setx setT);

     fun after_qed thms lthy =
       let
         val Induct = thms |> hd |> hd;
         val Induct1 = Induct RS @{thm Induct.axioms(1)};
         val strong_induct_thm = Induct RS @{thm Induct.strong_induct};
         val I_intros = (Induct1 RS @{thm Induct1.I.intros}) |> rotate_prems 1;
         val I_induct = Induct1 RS @{thm Induct1.I.induct};
         val equiv_thm = Induct1 RS @{thm Induct1.I_equiv};

         val flags = {quiet_mode = true, verbose = false, alt_name = alt_name, coind = false,
           no_elim = false, no_ind = false, skip_mono = false};
         val (result, lthy) = Inductive.add_ind_def flags cs intros monos params cnames_syn lthy;

         val G = Induct |> Thm.concl_of |> HOLogic.dest_Trueprop |> strip_comb |> snd |> List.last;  
         val I = Const (@{const_name Induct1.I}, fastype_of G --> argT --> HOLogic.boolT) $ G
           |> Syntax.check_term lthy;

         val preds = result |> #preds;
         val args's = map (fn pred => make_args' argTs xs (pred |> fastype_of |> binder_types)) preds;
         val bargss = map_index (fn (i, _) => make_bool_args' bs i) preds;
         val lhss = @{map 2} (curry list_comb) preds args's;
         val rhss = map (subst I []) lhss;
         val tuples = map (dest_comb #> snd) rhss;
         val lr_goal = @{map 2} (curry HOLogic.mk_imp) lhss rhss
           |> Library.foldr1 HOLogic.mk_conj
           |> HOLogic.mk_Trueprop;
         val intro_thms = result |> #intrs;
         val inducts_thm = result |> #raw_induct;
         val n = length intros;
         val lr_thm = Goal.prove_sorry lthy (map (fst o dest_Free) xs) [] lr_goal
           (fn {context = ctxt, prems = _} =>
             HEADGOAL (rtac ctxt inducts_thm THEN'
               EVERY' (map (fn i => EVERY' [
                 rtac ctxt I_intros,
                 SELECT_GOAL (unfold_tac ctxt @{thms prod.case}),
                 rtac ctxt (mk_disjIN n i),
                 REPEAT_DETERM o (resolve_tac ctxt [exI, conjI, refl, notI, TrueI] ORELSE' assume_tac ctxt),
                 simp_tac ctxt
                 ]) (1 upto n))));
         val (t, _) = yield_singleton (mk_Frees "t") argT lthy;
         val lhss' = @{map 3} (fn preds => fn args' => fn tuple =>
           list_all_free args' (HOLogic.mk_imp (HOLogic.mk_eq (t, tuple),
             list_comb (preds, args')))) preds args's tuples;
         val rl_goal =
           Logic.mk_implies (HOLogic.mk_Trueprop (I $ t),
             HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj lhss'))
         val rl_thm = Goal.prove_sorry lthy [fst (dest_Free t)] [] rl_goal
           (fn {context = ctxt, prems = _} =>
              HEADGOAL (etac ctxt I_induct THEN'
                (REPEAT_ALL_NEW (eresolve_tac ctxt [conjE, @{thm case_prodE}, @{thm case_prodE'},  disjE, exE])
                  THEN_ALL_NEW hyp_subst_tac ctxt) THEN'
                EVERY' (map (fn thm =>
                  asm_full_simp_tac (ss_only (thm :: @{thms prod.inject simp_thms all_simps imp_conjL}) ctxt)) intro_thms)
              ));
         val goal = @{map 2} (curry HOLogic.mk_eq) lhss rhss
           |> Library.foldr1 HOLogic.mk_conj |> HOLogic.mk_Trueprop;
         val thms = Goal.prove_sorry lthy (map (fst o dest_Free) xs) [] goal
           (fn {context = ctxt, prems = _} =>
              HEADGOAL (Method.insert_tac ctxt [lr_thm, rl_thm] THEN' blast_tac ctxt))
           |> split_conj_thm;

         val rec_binding =
           if Binding.is_empty alt_name then Binding.conglomerate (map #1 cnames_syn) else alt_name;
         val notes =
           (Binding.qualify_name true rec_binding "strong_induct", strong_induct_thm) ::
           (Binding.qualify_name true rec_binding "equiv", equiv_thm) ::
           (map (fn (b, _) => Binding.qualify_name true b "alt_def") cnames_syn ~~ thms)
           |> map (fn (b, thm) => ((b, []), [([thm], [])]))
       in
         lthy |> Local_Theory.notes notes |> snd
       end;

     val goal = list_comb (Const (@{const_name Induct}, mapT --> setT --> fastype_of fp_fun --> HOLogic.boolT),
       [mapx, setx, fp_fun])
       |> HOLogic.mk_Trueprop;

   in
      Proof.theorem NONE after_qed [[(goal, [])]] lthy
      |> Proof.refine_singleton
           (Method.Basic (Method.METHOD o Locale.intro_locales_tac {strict = false, eager = true}))
   end;

fun declare_rules rec_binding no_ind spec_name cnames
    preds intrs intr_bindings intr_atts elims eqs raw_induct lthy =
  let
    val rec_name = Binding.name_of rec_binding;
    fun rec_qualified qualified = Binding.qualify qualified rec_name;
    val intr_names = map Binding.name_of intr_bindings;
    val ind_case_names =
      if forall (equal "") intr_names then []
      else [Attrib.case_names intr_names];
    val induct =
      if no_ind orelse length cnames > 1 then
        (raw_induct, ind_case_names @ [Attrib.consumes (~ (Thm.nprems_of raw_induct))])
      else
        (raw_induct RSN (2, rev_mp),
          ind_case_names @ [Attrib.consumes (~ (Thm.nprems_of raw_induct))]);

    val (intrs', lthy1) =
      lthy |>
      Spec_Rules.add spec_name Spec_Rules.Inductive preds intrs |>
      Local_Theory.notes
        (map (rec_qualified false) intr_bindings ~~ intr_atts ~~
          map (fn th => [([th], @{attributes [Pure.intro?]})]) intrs) |>>
      map (hd o snd);
    val (((_, elims'), (_, [induct'])), lthy2) =
      lthy1 |>
      Local_Theory.note ((rec_qualified true (Binding.name "intros"), []), intrs') ||>>
      fold_map (fn (name, (elim, cases, k)) =>
        Local_Theory.note
          ((Binding.qualify true (Long_Name.base_name name) (Binding.name "cases"),
            ((if forall (equal "") cases then [] else [Attrib.case_names cases]) @
              [Attrib.consumes (1 - Thm.nprems_of elim), Attrib.constraints k,
               Attrib.internal \<^here> (K (Induct.cases_pred name))] @ @{attributes [Pure.elim?]})),
            [elim]) #>
        apfst (hd o snd)) (if null elims then [] else cnames ~~ elims) ||>>
      Local_Theory.note
        ((rec_qualified true (Binding.name "induct"), #2 induct),
          [rulify lthy1 (#1 induct)]);

    val (eqs', lthy3) = lthy2 |>
      fold_map (fn (name, eq) => Local_Theory.note
          ((Binding.qualify true (Long_Name.base_name name) (Binding.name "simps"),
            [Attrib.internal \<^here> (K equation_add_permissive)]), [eq])
          #> apfst (hd o snd))
        (if null eqs then [] else (cnames ~~ eqs))
    val (inducts, lthy4) =
      if no_ind then ([], lthy3)
      else
        let val inducts = cnames ~~ Project_Rule.projects lthy3 (1 upto length cnames) induct' in
          lthy3 |>
          Local_Theory.notes [((rec_qualified true (Binding.name "inducts"), []),
            inducts |> map (fn (name, th) => ([th],
              ind_case_names @
                [Attrib.consumes (1 - Thm.nprems_of th),
                 Attrib.internal \<^here> (K (Induct.induct_pred name))])))] |>> snd o hd
        end;
  in (intrs', elims', eqs', induct', inducts, lthy4) end;

type add_ind_def =
  binding ->
  term list -> (Attrib.binding * term) list -> term -> term -> term list -> thm list ->
  term list -> (binding * mixfix) list ->
  local_theory -> Proof.state;

fun add_ind_def alt_name cs intros mapx setx binds monos params cnames_syn lthy =
  let
    val _ = null cnames_syn andalso error "No inductive predicates given";
    val intr_ts = snd (split_list (map (check_rule lthy cs params) intros));

  in
    mk_ind_def alt_name cs intros intr_ts mapx setx binds monos params cnames_syn lthy
  end;

(* external interfaces *)

fun gen_add_inductive mk_def flags cnames_syn pnames spec mapx setx binds monos lthy =
  let

    (* abbrevs *)

    val (_, ctxt1) = Variable.add_fixes (map (Binding.name_of o fst o fst) cnames_syn) lthy;

    fun get_abbrev ((name, atts), t) =
      if can (Logic.strip_assums_concl #> Logic.dest_equals) t then
        let
          val _ = Binding.is_empty name andalso null atts orelse
            error "Abbreviations may not have names or attributes";
          val ((x, T), rhs) = Local_Defs.abs_def (snd (Local_Defs.cert_def ctxt1 (K []) t));
          val var =
            (case find_first (fn ((c, _), _) => Binding.name_of c = x) cnames_syn of
              NONE => error ("Undeclared head of abbreviation " ^ quote x)
            | SOME ((b, T'), mx) =>
                if T <> T' then error ("Bad type specification for abbreviation " ^ quote x)
                else (b, mx));
        in SOME (var, rhs) end
      else NONE;

    val abbrevs = map_filter get_abbrev spec;
    val bs = map (Binding.name_of o fst o fst) abbrevs;


    (* predicates *)

    val pre_intros = filter_out (is_some o get_abbrev) spec;
    val cnames_syn' = filter_out (member (op =) bs o Binding.name_of o fst o fst) cnames_syn;
    val cs = map (Free o apfst Binding.name_of o fst) cnames_syn';
    val ps = map Free pnames;

    val (_, ctxt2) = lthy |> Variable.add_fixes (map (Binding.name_of o fst o fst) cnames_syn');
    val ctxt3 = ctxt2 |> fold (snd oo Local_Defs.fixed_abbrev) abbrevs;
    val expand = Assumption.export_term ctxt3 lthy #> Proof_Context.cert_term lthy;

    fun close_rule r =
      fold (Logic.all o Free) (fold_aterms
        (fn t as Free (v as (s, _)) =>
            if Variable.is_fixed ctxt1 s orelse
              member (op =) ps t then I else insert (op =) v
          | _ => I) r []) r;

    val intros = map (apsnd (Syntax.check_term lthy #> close_rule #> expand)) pre_intros;
    val preds = map (fn ((c, _), mx) => (c, mx)) cnames_syn';
  in
    lthy
    |> mk_def flags cs intros mapx setx binds monos ps preds
  end;

fun get_positions ctxt x =
  let
    fun get Cs (Const ("_type_constraint_", C) $ t) = get (C :: Cs) t
      | get Cs (Free (y, T)) =
          if x = y then
            map_filter Term_Position.decode_positionT
              (T :: map (Type.constraint_type ctxt) Cs)
          else []
      | get _ (t $ u) = get [] t @ get [] u
      | get _ (Abs (_, _, t)) = get [] t
      | get _ _ = [];
  in get [] end;

fun prep_decls prep_var raw_vars ctxt =
  let
    val (vars, ctxt') = fold_map prep_var raw_vars ctxt;
    val (xs, ctxt'') = ctxt'
      |> Context_Position.set_visible false
      |> Proof_Context.add_fixes vars
      ||> Context_Position.restore_visible ctxt';
    val _ =
      Context_Position.reports ctxt''
        (map (Binding.pos_of o #1) vars ~~
          map (Variable.markup_entity_def ctxt'' ##> Properties.remove Markup.kindN) xs);
  in ((vars, xs), ctxt'') end;

fun close_form ctxt ys prems concl =
  let
    val xs = rev (fold (Variable.add_free_names ctxt) (prems @ [concl]) (rev ys));

    val pos_props = Logic.strip_imp_concl concl :: Logic.strip_imp_prems concl @ prems;
    fun get_pos x = maps (get_positions ctxt x) pos_props;
    val _ = Context_Position.reports ctxt (maps (Syntax_Phases.reports_of_scope o get_pos) xs);
  in Logic.close_prop_constraint (Variable.default_type ctxt) (xs ~~ xs) prems concl end;

fun dummy_frees ctxt xs tss =
  let
    val names =
      Variable.names_of ((fold o fold) Variable.declare_term tss ctxt)
      |> fold Name.declare xs;
    val (tss', _) = (fold_map o fold_map) Term.free_dummy_patterns tss names;
  in tss' end;

fun prep_specs prep_var parse_prop prep_term prep_att raw_vars raw_specss raw_mapx raw_setx raw_binds ctxt =
  let
    val ((vars, xs), vars_ctxt) = prep_decls prep_var raw_vars ctxt;

    val propss0 =
      raw_specss |> map (fn ((_, raw_concl), raw_prems, raw_params) =>
        let val (ys, ctxt') = vars_ctxt |> fold_map prep_var raw_params |-> Proof_Context.add_fixes
        in (ys, map (pair ctxt') (raw_concl :: raw_prems)) end);
    val props =
      burrow (grouped 10 Par_List.map_independent (uncurry parse_prop)) (map #2 propss0)
      |> dummy_frees vars_ctxt xs
      |> map2 (fn (ys, _) => fn concl :: prems => close_form vars_ctxt ys prems concl) propss0;

    val specs = Syntax.check_props vars_ctxt props;
    val paramss = specs |> map (Logic.strip_params #> map Free);
    val vars_ctxts = paramss |> map (fn ts => fold Variable.declare_term ts vars_ctxt);
    fun repair xs = 
      let val T = List.find is_some xs |> the |> the |> fastype_of |> HOLogic.dest_setT;
      in map (the_default (HOLogic.mk_set T [])) xs end;
    val binds' = repair (@{map 2} (Option.map o prep_term) vars_ctxts raw_binds);
    val binds = @{map 2} (fold_rev Term.lambda) paramss binds' |> map Term.strip_abs_body;
    val specs_ctxt = vars_ctxt |> fold Variable.declare_term specs;
    val mapx = prep_term vars_ctxt raw_mapx;
    val setx = prep_term vars_ctxt raw_setx;

    val ps = specs_ctxt |> fold_map Proof_Context.inferred_param xs |> fst;
    val params = map2 (fn (b, _, mx) => fn (_, T) => ((b, T), mx)) vars ps;
    val name_atts: Attrib.binding list =
      map (fn ((name, atts), _) => (name, map (prep_att ctxt) atts)) (map #1 raw_specss);
  in ((params, name_atts ~~ specs, mapx, setx, binds), specs_ctxt) end;

val read_multi_specs = prep_specs Proof_Context.read_var Syntax.parse_prop Syntax.read_term Attrib.check_src;

fun gen_add_inductive_cmd mk_def cnames_syn pnames_syn intro_srcs raw_mapx raw_setx raw_binds raw_monos lthy =
  let
    val ((vars, intrs, mapx, setx, binds), _) = lthy
      |> Proof_Context.set_mode Proof_Context.mode_abbrev
      |> read_multi_specs (cnames_syn @ pnames_syn) intro_srcs raw_mapx raw_setx raw_binds;
    val (cs, ps) = chop (length cnames_syn) vars;

    val monos = Attrib.eval_thms lthy raw_monos;
  in
    lthy
    |> gen_add_inductive mk_def Binding.empty cs (map (apfst Binding.name_of o fst) ps) intrs mapx setx binds monos
  end;

val add_inductive = gen_add_inductive add_ind_def;
val add_inductive_cmd = gen_add_inductive_cmd add_ind_def;


(* read off arities of inductive predicates from raw induction rule *)
fun arities_of induct =
  map (fn (_ $ t $ u) =>
      (fst (dest_Const (head_of t)), length (snd (strip_comb u))))
    (HOLogic.dest_conj (HOLogic.dest_Trueprop (Thm.concl_of induct)));

(* read off parameters of inductive predicate from raw induction rule *)
fun params_of induct =
  let
    val (_ $ t $ u :: _) = HOLogic.dest_conj (HOLogic.dest_Trueprop (Thm.concl_of induct));
    val (_, ts) = strip_comb t;
    val (_, us) = strip_comb u;
  in
    List.take (ts, length ts - length us)
  end;

val pname_of_intr =
  Thm.concl_of #> HOLogic.dest_Trueprop #> head_of #> dest_Const #> fst;

(* partition introduction rules according to predicate name *)
fun gen_partition_rules f induct intros =
  fold_rev (fn r => AList.map_entry op = (pname_of_intr (f r)) (cons r)) intros
    (map (rpair [] o fst) (arities_of induct));

val partition_rules = gen_partition_rules I;
fun partition_rules' induct = gen_partition_rules fst induct;

fun unpartition_rules intros xs =
  fold_map (fn r => AList.map_entry_yield op = (pname_of_intr r)
    (fn x :: xs => (x, xs)) #>> the) intros xs |> fst;

(* infer order of variables in intro rules from order of quantifiers in elim rule *)
fun infer_intro_vars thy elim arity intros =
  let
    val _ :: cases = Thm.prems_of elim;
    val used = map (fst o fst) (Term.add_vars (Thm.prop_of elim) []);
    fun mtch (t, u) =
      let
        val params = Logic.strip_params t;
        val vars =
          map (Var o apfst (rpair 0))
            (Name.variant_list used (map fst params) ~~ map snd params);
        val ts =
          map (curry subst_bounds (rev vars))
            (List.drop (Logic.strip_assums_hyp t, arity));
        val us = Logic.strip_imp_prems u;
        val tab =
          fold (Pattern.first_order_match thy) (ts ~~ us) (Vartab.empty, Vartab.empty);
      in
        map (Envir.subst_term tab) vars
      end
  in
    map (mtch o apsnd Thm.prop_of) (cases ~~ intros)
  end;



(** outer syntax **)

val opt_binders = Scan.option (\<^keyword>\<open>binds\<close> |-- Parse.term)

fun rearrange (((x, y), z), w) = ((x, y, w), z);

val multi_specs =
  Parse.enum1 "|"
    ((Parse_Spec.opt_thm_name ":" -- Parse.prop -- Parse_Spec.if_assumes -- opt_binders -- Parse.for_fixes >> rearrange) --|
      Scan.option (Scan.ahead (Parse.name || Parse.$$$ "[") -- Parse.!!! (Parse.$$$ "|"))) >> split_list;

val parse_map = Parse.reserved "perm" --| \<^keyword>\<open>:\<close> |-- Parse.term;
val parse_set = Parse.reserved "supp" --| \<^keyword>\<open>:\<close> |-- Parse.term;

val parse_map_set = @{keyword where} |-- (parse_map -- parse_set);

val where_multi_specs = Parse.where_ |-- Parse.!!! multi_specs;

fun gen_ind_decl mk_def =
  Parse.vars -- Parse.for_fixes --
  Scan.optional where_multi_specs ([], []) --
  parse_map_set --
  Scan.optional (\<^keyword>\<open>monos\<close> |-- Parse.!!! Parse.thms1) []
  >> (fn ((((preds, params), (specs, binds)), (mapx, setx)), monos) =>
      gen_add_inductive_cmd mk_def preds params specs mapx setx binds monos);

val ind_decl = gen_ind_decl add_ind_def;

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>binder_inductive\<close> "define binding-aware inductive predicates"
    ind_decl;

end;
