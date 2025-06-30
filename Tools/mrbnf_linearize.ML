

signature MRBNF_LINEARIZE =
sig
  datatype linearize_mrbnf_option =
    Plugins_Option of Proof.context -> Plugin_Name.filter
  | No_Warn_Wits
  | No_Warn_Transfer
  val linearize_mrbnf:
    (((((linearize_mrbnf_option list * (binding option * (string * sort option)) list) *
      binding) * typ) * term list option) * string) * (binding * binding * binding) ->
      ({context: Proof.context, prems: thm list} -> tactic) list ->
      local_theory -> local_theory
  val linearize_mrbnf_cmd:
     (((((linearize_mrbnf_option list * (binding option * (string * string option)) list) *
       binding) * string) * string list) * string) *
       (binding * binding * binding) -> local_theory -> Proof.state
end

structure MRBNF_Linearize : MRBNF_LINEARIZE =
struct

open Ctr_Sugar_Tactics
open BNF_Util
open BNF_Comp
open BNF_Def


datatype linearize_mrbnf_option =
  Plugins_Option of Proof.context -> Plugin_Name.filter
| No_Warn_Wits
| No_Warn_Transfer;

datatype equiv_thm = Typedef | Quotient of thm

(** Util **)

fun last2 [x, y] = ([], (x, y))
  | last2 (x :: xs) = last2 xs |>> (fn y => x :: y)
  | last2 [] = raise Match;

fun strip3 thm = (case Term.strip_comb (HOLogic.dest_Trueprop (Thm.prop_of thm)) of
    (_, [x1, x2, x3]) => (x1, x2, x3)
  | _ => error "strip3: wrong number of arguments");

val mk_Free = yield_singleton o mk_Frees;

fun prove lthy fvars tm tac =
  Goal.prove_sorry lthy (map (fst o dest_Free) fvars) [] tm (fn {context, ...} => tac context);

(** Term construction **)

fun mk_relT aT bT = aT --> bT --> HOLogic.boolT;
fun mk_relcompp r s = let
    val (rT, sT) = apply2 fastype_of (r, s);
    val ((xT, _), (_, zTs)) = apply2 dest_funT (rT, sT);
    val T = rT --> sT --> mk_relT xT (fst (dest_funT zTs));
  in Const (@{const_name relcompp}, T) $ r $ s end;


(** witnesses **)
fun prepare_wits is_quotient RepT wits opts alphas wits_F var_as var_as' sets lthy =
  let
    fun binder_types_until_eq V T =
      let
        fun strip (TU as Type ("fun", [T, U])) = if V = TU then [] else T :: strip U
          | strip T = if V = T then [] else
              error ("Bad type for witness: " ^ quote (Syntax.string_of_typ lthy T));
      in strip T end;

    val Iwits = the_default wits_F (Option.map (map (`(map (fn T =>
      find_index (fn U => T = U) alphas) o binder_types_until_eq RepT o fastype_of))) wits);

    val Iwits = if is_quotient then
        let
          val subsumed_Iwits =
            filter (fn (J, _) => exists (fn (I, _) => subset (op =) (I, J)) wits_F) Iwits;
          val _ =  if null subsumed_Iwits orelse exists (fn No_Warn_Wits => true | _ => false) opts
            then ()
            else
              let
                val (suffix1, suffix2, be) =
                  (if length subsumed_Iwits = 1 then ("", "", "is") else ("s", "es", "are"))
              in
                subsumed_Iwits
                |> map (Syntax.pretty_typ lthy o fastype_of o snd)
                |> Pretty.big_list
                  ("The following type" ^ suffix1 ^ " of nonemptiness witness" ^ suffix2 ^
                    " of the raw type's BNF " ^ be ^ " subsumed by the existing raw witnesses:")
                |> (fn pt => Pretty.chunks [pt,
                  Pretty.para ("You do not need to lift these subsumed witnesses.")])
                |> Pretty.string_of
                |> warning
              end;
        in
          filter_out (fn (J, _) => exists (fn (I, _) => subset (op =) (I, J)) wits_F) Iwits
        end
      else Iwits;

    val wit_goals = maps (BNF_Def.mk_wit_goals var_as var_as' sets) Iwits;

    val lost_wits = if is_quotient then [] else
      filter_out (fn (J, _) => exists (fn (I, _) => subset (op =) (I, J)) Iwits) wits_F;

    val _ =
      if null lost_wits orelse exists (fn No_Warn_Wits => true | _ => false) opts then ()
      else
        let
          val what = (if is_quotient then "quotient type" else "typedef");
          val (suffix1, suffix2, be) =
            (if length lost_wits = 1 then ("", "", "was") else ("s", "es", "were"))
        in
          lost_wits
          |> map (Syntax.pretty_typ lthy o fastype_of o snd)
          |> Pretty.big_list
            ("The following type" ^ suffix1 ^ " of nonemptiness witness" ^ suffix2 ^
              " of the raw type's BNF " ^ be ^ " lost:")
          |> (fn pt => Pretty.chunks [pt,
            Pretty.para ("You can specify a liftable witness (e.g., a term of one of the above types\
              \ that satisfies the " ^ what ^ "'s invariant)\
              \ using the annotation [wits: <term>].")])
          |> Pretty.string_of
          |> warning
        end;
  in (Iwits, wit_goals) end;



(** linearize **)
fun linearize b repT on_tvar wits specs map_b rel_b pred_b opts lthy =
  let
    val set_bs = map fst specs;
    val vars = map snd specs;

    val (F_name, F_vars) = dest_Type repT ||> map dest_TFree |> @{print};  

    val mrbnf' = F_name |> MRBNF_Def.mrbnf_of lthy |> the

    val alpha0s = map TFree F_vars;

    fun flatten_tyargs Ass =
      map dest_TFree alpha0s
      |> filter (fn T => exists (fn Ts => member op= Ts T) Ass);

    val ((mrbnf,(Ds, As)), (_,lthy)) = MRBNF_Comp.mrbnf_of_typ true MRBNF_Def.Smart_Inline
      (Binding.prefix_name F_name) flatten_tyargs F_vars [] [] repT
      ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy);

    val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf |> @{print};

    val deads = MRBNF_Def.deads_of_mrbnf mrbnf |> @{print};
    val frees = MRBNF_Def.frees_of_mrbnf mrbnf |> @{print};
    val bounds = MRBNF_Def.bounds_of_mrbnf mrbnf |> @{print};
    val lives = MRBNF_Def.lives_of_mrbnf mrbnf |> @{print};
    val lives' = MRBNF_Def.lives'_of_mrbnf mrbnf |> @{print};
    val all_vars = MRBNF_Def.interlace lives bounds frees var_types |> @{print};

    val nr_lives = MRBNF_Def.live_of_mrbnf mrbnf;
    val nr_frees = MRBNF_Def.free_of_mrbnf mrbnf;
    val nr_bounds = MRBNF_Def.bound_of_mrbnf mrbnf;

    fun select_one types types' pos = map_index (fn (i, (t, t')) => if i = pos then t' else t) (types ~~ types')

    fun get_lin_pos [] _ = ~1
      | get_lin_pos (v::vars) i = if (dest_TVar v |> fst |> fst) = on_tvar then i else get_lin_pos vars (i+1) 

    val lin_pos = get_lin_pos all_vars 0 |> @{print} (*while in Linearize.thy I had lin_pos starting at 1, it is here more reasonable to start at 0 *)
    val lin_live_pos = get_lin_pos lives 0 |> @{print};

    (*ex_nonrep *)
    val map_lives' = select_one lives lives' lin_live_pos;

    val map_F = MRBNF_Def.mk_map_of_mrbnf deads lives map_lives' bounds frees mrbnf;
    val (typ_fs, typ_F_F') = fastype_of map_F |> strip_typeN (length var_types);
    val typ_F = typ_F_F' |> domain_type;
    val typ_F' = typ_F_F' |> range_type;
    val typ_f = nth typ_fs lin_pos;
    val (var_f, lthy) = mk_Frees "f" [typ_f] lthy |>> the_single;
    val (var_x, lthy) = mk_Frees "x" [typ_F] lthy |>> the_single;
    val map_funs = map_index (fn (i, t) => if i = lin_pos then var_f else HOLogic.id_const t) all_vars;
    val map_f_x = Term.list_comb (map_F, map_funs @ [var_x]);

    val rrel_F = MRBNF_Def.mk_rel_of_mrbnf deads lives map_lives' bounds frees mrbnf;
    val typ_R = [nth lives lin_live_pos, nth lives' lin_live_pos] ---> HOLogic.boolT;
    val (var_R, lthy) = mk_Frees "R" [typ_R] lthy |>> the_single;
    val (var_x', lthy) = mk_Frees "x'" [typ_F'] lthy |>> the_single;
    val var_Rs = map_index (fn (i, t) => if i = lin_live_pos then var_R else HOLogic.eq_const t) lives
    val rrel_R_x_x' = Term.list_comb (rrel_F, var_Rs @ [var_x, var_x']);

    val ex_f = HOLogic.mk_exists (dest_Free var_f |> fst, typ_f, 
      HOLogic.mk_eq (var_x', map_f_x))
    val ex_R = HOLogic.mk_exists (dest_Free var_R |> fst, typ_R, rrel_R_x_x')
    val ex_R_imp_ex_f = HOLogic.mk_imp (ex_R, ex_f)
    val ex_nonrep = HOLogic.mk_exists (dest_Free var_x |> fst, typ_F,
      HOLogic.mk_all (dest_Free var_x' |> fst, typ_F', ex_R_imp_ex_f))
    val Tp_ex_nonrep = HOLogic.mk_Trueprop ex_nonrep |> @{print}

    (*F_rel_map_set2_strong (maybe rename?)*)
    val typ_Rs = map (fn (t, t') => [t, t'] ---> HOLogic.boolT) (lives ~~ lives')
    val (var_Rs, lthy) = mk_Frees "R" typ_Rs lthy |> @{print};
    val lives_pair = map (fn var_R => 
      let 
        val typ_fs = fst (fastype_of var_R |> strip_typeN 2) 
      in
        HOLogic.mk_prodT (nth typ_fs 0, nth typ_fs 1)
      end
      ) var_Rs

    val typ_z = MRBNF_Def.mk_T_of_mrbnf deads lives_pair bounds frees mrbnf;
    val (var_z, lthy) = mk_Frees "z" [typ_z] lthy |>> the_single;

    val map_fst_z = MRBNF_Def.mk_map_comb_of_mrbnf deads (map BNF_Util.fst_const lives_pair) 
      (map HOLogic.id_const bounds) (map HOLogic.id_const frees) mrbnf $ var_z;
    val typ_y = fastype_of map_fst_z;
    val (var_y, lthy) = mk_Frees "y" [typ_y] lthy |>> the_single;
    val map_eq_y = HOLogic.mk_eq (map_fst_z, var_y);

    val map_snd_z = MRBNF_Def.mk_map_comb_of_mrbnf deads (map BNF_Util.snd_const lives_pair) 
      (map HOLogic.id_const bounds) (map HOLogic.id_const frees) mrbnf $ var_z;
    val typ_y' = fastype_of map_snd_z;
    val (var_y', lthy) = mk_Frees "y'" [typ_y'] lthy |>> the_single;
    val map_eq_y' = HOLogic.mk_eq (map_snd_z, var_y');
    val map_eq_conj = HOLogic.mk_conj (map_eq_y, map_eq_y');
    
    val count = nr_lives + nr_frees + nr_bounds;
    val set_Fs = MRBNF_Def.mk_sets_of_mrbnf (replicate count deads) (replicate count lives_pair) 
      (replicate count bounds) (replicate count frees) mrbnf;
    val set_Fs_live = filter (fn (_, vtype) => vtype = MRBNF_Def.Live_Var) (set_Fs ~~ var_types) |> map fst;
    val (set_map_conj, lthy) = fold (fn (set, var_R) => (fn (conj, lthy) =>
      let 
        val set_z = set $ var_z;
        val typ_xys = fst (fastype_of var_R |> strip_typeN 2);
        val typ_x_pair = nth typ_xys 0;
        val typ_y_pair = nth typ_xys 1;
        val (var_x_pair, lthy) = mk_Frees "x" [typ_x_pair] lthy |>> the_single;
        val (var_y_pair, lthy) = mk_Frees "y" [typ_y_pair] lthy |>> the_single;
        val R_xy = Term.list_comb (var_R, [var_x_pair, var_y_pair]);
        val absfree_R_xy = R_xy |> absfree (dest_Free var_y_pair |> fst, typ_y_pair) |>
          absfree (dest_Free var_x_pair |> fst, typ_x_pair);
        val case_prod_R_xy = HOLogic.mk_case_prod absfree_R_xy;
        val collect_set = HOLogic.Collect_const (HOLogic.mk_prodT (typ_x_pair, typ_y_pair)) $ case_prod_R_xy;
        val set_leq_collect = mk_leq set_z collect_set;
      in
        (HOLogic.mk_conj (set_leq_collect, conj), lthy)
      end)) (rev (set_Fs_live ~~ var_Rs)) (map_eq_conj, lthy) ;

    val ex1_z = Const ("HOL.Ex1", (typ_z --> HOLogic.boolT) --> HOLogic.boolT) $ 
      absfree (dest_Free var_z |> fst, typ_z) set_map_conj;

    val rrel_F_R = MRBNF_Def.mk_rel_of_mrbnf deads 
      (map (fst o HOLogic.dest_prodT) lives_pair) 
      (map (snd o HOLogic.dest_prodT) lives_pair) bounds frees mrbnf
    val rrel_R_y_y' = Term.list_comb (rrel_F_R, var_Rs @ [var_y, var_y']);
    val rrel_eq_ex1 = HOLogic.mk_eq (rrel_R_y_y', ex1_z);
    val all_y_y' = HOLogic.mk_Trueprop rrel_eq_ex1 |> Logic.all var_y' |> Logic.all var_y;
    val F_rel_map_set2_strong = fold (fn var_R => (fn all => Logic.all var_R all)) var_Rs all_y_y';

    val plugins =
      get_first (fn Plugins_Option f => SOME (f lthy) | _ => NONE) (rev opts)
        |> the_default Plugin_Name.default_filter;


    val goals = [F_rel_map_set2_strong, Tp_ex_nonrep];

    fun after_qed ([F_rel_map_set2_strong_thm] :: [ex_nonrep_thm] :: wit_thms) lthy = 
      let
        (*mk theorem*)
        val map_id = MRBNF_Def.map_id_of_mrbnf mrbnf |> @{print}

        (* sameShape *)
        val (var_R, lthy) = mk_Frees "R" [typ_R] lthy |>> the_single;
        val (var_x, lthy) = mk_Frees "x" [typ_F] lthy |>> the_single;
        val (var_x', lthy) = mk_Frees "x'" [typ_F'] lthy |>> the_single;
        val mr_rel_F = MRBNF_Def.mk_mr_rel_of_mrbnf deads lives map_lives' bounds frees mrbnf |> @{print}
        val mr_rel_args = map_index (fn (i, (t, vt)) => if i = lin_pos then var_R else 
          (if vt = MRBNF_Def.Live_Var then HOLogic.eq_const t else HOLogic.id_const t)) (all_vars ~~ var_types)
        val mr_rel_F_R_x_x' = Term.list_comb (mr_rel_F, mr_rel_args @ [var_x, var_x']);
        val ex_R = HOLogic.mk_exists (dest_Free var_R |> fst, typ_R, mr_rel_F_R_x_x') |> @{print};
        val ss_rhs = ex_R;
        val ss_binding = (Binding.prefix_name ("sameShape_") (MRBNF_Def.name_of_mrbnf mrbnf)) |> @{print}
        val ((string, ss_term, ss_def_thm), lthy) = MRBNF_Util.new_definition ss_binding ss_rhs lthy |> @{print}
(*  "sameShape1 x x' \<equiv> \<exists> R. rel_F R id id (=) id x x'"  *)

        (* nonrep *)
        val nrp_rhs = @{term True}
        val nrp_binding = (Binding.prefix_name ("nonrep_") (MRBNF_Def.name_of_mrbnf mrbnf)) |> @{print}
        val ((string, nrp_term, nrp_def_thm), lthy) = MRBNF_Util.new_definition nrp_binding nrp_rhs lthy |> @{print}
(* "nonrep2 x \<equiv> \<forall> x'. sameShape1 x x' \<longrightarrow> (\<exists> f. x' = map_F f id id id id x)" *)

        (* typedef F'*)
        val (var_x, lthy) = mk_Frees "x" [typ_F] lthy |>> the_single
        val nrp_x = Term.list_comb (nrp_term, [var_x])
        val td_term = HOLogic.mk_Collect (dest_Free var_x |> fst, typ_F, nrp_x) |> @{print}
(*"{x :: ('a1,'a2,'a3,'a4,'a5,'a6) F. nonrep2 x}"*)
        val td = MRBNF_Util.new_typedef b td_term;
        val _ = F_rel_map_set2_strong_thm |> @{print}
        val _ = ex_nonrep_thm |> @{print}
        val _ = wit_thms |> @{print}
      in
        lthy
      end
      | after_qed _ _ = raise Match;
  in
    (goals, after_qed, [], lthy)
  end;


(** main commands **)

local

fun prepare_common prepare_sort prepare_typ prepare_term
    ((((((plugins, raw_specs), b), raw_repT), raw_wits), on_tvar), (map_b, rel_b, pred_b)) lthy =
  let
    val _ = b
      |> @{print};
    val repT = prepare_typ lthy raw_repT
      |> @{print};

    val _ = on_tvar
      |> @{print};

    val wits = (Option.map o map) (prepare_term lthy) raw_wits;
    val specs =
      map (apsnd (apsnd (the_default @{sort type} o Option.map (prepare_sort lthy)))) raw_specs
      |> @{print};
  in
    linearize b repT on_tvar wits specs map_b rel_b pred_b plugins lthy
  end;

fun prepare_linearize_mrbnf prepare_sort prepare_typ prepare_term =
  (fn (goals, after_qed, definitions, lthy) =>
    lthy
    |> Proof.theorem NONE after_qed (map (single o rpair []) goals)
    |> Proof.refine_singleton
        (Method.Basic (fn ctxt => SIMPLE_METHOD (unfold_thms_tac ctxt definitions)))
    |> Proof.refine_singleton (Method.primitive_text (K I))) oo
  prepare_common prepare_sort prepare_typ prepare_term o apfst (apfst (apsnd SOME));

fun prepare_solve prepare_sort prepare_typ prepare_term tacs =
  (fn (goals, after_qed, definitions, lthy) =>
    lthy
    |> after_qed (map2 (fn goal => fn tac => [Goal.prove_sorry lthy [] [] goal
        (fn (ctxtprems as {context = ctxt, prems = _}) =>
          unfold_thms_tac ctxt definitions THEN tac ctxtprems)])
      goals (tacs (length goals)))) oo
  prepare_common prepare_sort prepare_typ prepare_term;

in

val linearize_mrbnf_cmd = prepare_linearize_mrbnf Syntax.read_sort Syntax.read_typ Syntax.read_term;

fun linearize_mrbnf args tacs = prepare_solve (K I) (K I) (K I) (K tacs) args;

end;

(** outer syntax **)

local

(* parsers *)

val parse_wits =
  @{keyword "["} |-- (Parse.name --| @{keyword ":"} -- Scan.repeat Parse.term >>
    (fn ("wits", Ts) => Ts
      | (s, _) => error ("Unknown label " ^ quote s ^ " (expected \"wits\")"))) --|
  @{keyword "]"} || Scan.succeed [];

fun parse_common_opts p =
  Scan.optional (@{keyword "("} |--
    Parse.list1 (Parse.group (K "option")
      (Scan.first (p :: [Plugin_Name.parse_filter >> Plugins_Option,
          Parse.reserved "no_warn_transfer" >> K No_Warn_Transfer])))
    --| @{keyword ")"}) [];

val parse_lift_opts = Parse.reserved "no_warn_wits" >> K No_Warn_Wits |> parse_common_opts;

val parse_on_clause = Parse.reserved "on" |-- Parse.type_ident;

in

(* exposed commands *)

val _ =
  Outer_Syntax.local_theory_to_proof @{command_keyword linearize_mrbnf}
    "register a quotient type/subtype of a bounded natural functor (BNF) as a BNF"
    ((parse_lift_opts -- parse_type_args_named_constrained -- Parse.binding --
      (\<^keyword>\<open>=\<close> |-- Parse.typ) -- 
      parse_wits -- parse_on_clause -- parse_map_rel_pred_bindings) >> linearize_mrbnf_cmd);

end;

end;
