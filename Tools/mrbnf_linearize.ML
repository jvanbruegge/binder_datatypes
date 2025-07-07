

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

(** Util **)

fun last2 [x, y] = ([], (x, y))
  | last2 (x :: xs) = last2 xs |>> (fn y => x :: y)
  | last2 [] = raise Match;

val mk_Free = yield_singleton o mk_Frees;

fun prove lthy fvars =
  Goal.prove lthy (map (fst o dest_Free) fvars);

(** Term construction **)
fun mk_asBij f = let val typ_f = fastype_of f in
  Const ("Prelim.asBij", typ_f --> typ_f) $ f end;

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
    val tfrees = map (TFree o snd) specs;
    val on_tfree = TFree (on_tvar, @{sort type});
    val lin_pos = find_index (fn x => x = on_tfree) tfrees |> @{print};
(*
    val (F_name, F_vars) = dest_Type repT ||> map dest_TFree |> @{print};  
*)
(*
    val mrbnf = F_name |> MRBNF_Def.mrbnf_of lthy |> the
*)

    fun flatten_tyargs Ass =
      map dest_TFree tfrees
      |> filter (fn T => exists (fn Ts => member op= Ts T) Ass);
    val ((mrbnf,(Ds, As)), (_,lthy)) = MRBNF_Comp.mrbnf_of_typ true MRBNF_Def.Smart_Inline
      (Binding.prefix_name (Binding.name_of b)) flatten_tyargs [] [] [] repT
      ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy);

    val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf |> @{print};

    val deads = MRBNF_Def.deads_of_mrbnf mrbnf;

    val nr_lives = MRBNF_Def.live_of_mrbnf mrbnf;
    val nr_frees = MRBNF_Def.free_of_mrbnf mrbnf;
    val nr_bounds = MRBNF_Def.bound_of_mrbnf mrbnf;
    val nr_ABFs = nr_lives + nr_frees + nr_bounds;
    val class = MRBNF_Def.class_of_mrbnf mrbnf;

    val (((((Ds, As), As'), Fs), Bs), names_lthy) = lthy
      |> mk_TFrees' (map Type.sort_of_atyp deads)
      ||>> mk_TFrees nr_lives
      ||>> mk_TFrees nr_lives
      ||>> mk_TFrees' (replicate nr_frees class)
      ||>> mk_TFrees' (replicate nr_bounds class);
    val ABFs = MRBNF_Def.interlace As Bs Fs var_types |> @{print};
    val ABFs' = MRBNF_Def.interlace As' Bs Fs var_types |> @{print};

    fun select_one types types' pos = map_index (fn (i, (t, t')) => if i = pos then t' else t) (types ~~ types')
    
    (* TODO: This section has to be fixed! for now assume that deads are all at the end*)
    val lives = MRBNF_Def.lives_of_mrbnf mrbnf;
    val lin_live_pos = find_index (fn v => (dest_TVar v |> fst |> fst) = on_tvar) lives |> @{print};
    val set_bs_non_dead = take (nr_lives + nr_bounds + nr_frees) set_bs
    val set_bs_non_dead = map_index (fn (i, b_opt) => if Option.getOpt (b_opt, Binding.empty) |> Binding.is_empty |> not then
              the b_opt else
              Binding.prefix_name ("set" ^ (Int.toString (i+1)) ^ "_") b) set_bs_non_dead
    (*ex_nonrep *)
    val map_As' = select_one As As' lin_live_pos;

    val map_F = MRBNF_Def.mk_map_of_mrbnf Ds As map_As' Bs Fs mrbnf;
    val (typ_fs, typ_F_F') = fastype_of map_F |> strip_typeN (length var_types);
    val typ_F = typ_F_F' |> domain_type;
    val typ_F' = typ_F_F' |> range_type;
    val typ_f = nth typ_fs lin_pos;
    val (var_f, lthy) = mk_Free "f" typ_f lthy;
    val (var_x, lthy) = mk_Free "x" typ_F lthy;
    val map_funs = map_index (fn (i, t) => if i = lin_pos then var_f else HOLogic.id_const t) ABFs;
    val map_f_x = Term.list_comb (map_F, map_funs @ [var_x]);

    val rrel_F = MRBNF_Def.mk_rel_of_mrbnf Ds As map_As' Bs Fs mrbnf;
    val typ_R = [nth As lin_live_pos, nth As' lin_live_pos] ---> HOLogic.boolT;
    val (var_R, lthy) = mk_Free "R" typ_R lthy;
    val (var_x', lthy) = mk_Free "x'" typ_F' lthy;
    val var_Rs = map_index (fn (i, t) => if i = lin_live_pos then var_R else HOLogic.eq_const t) As
    val rrel_R_x_x' = Term.list_comb (rrel_F, var_Rs @ [var_x, var_x']);

    val ex_f = HOLogic.mk_exists (dest_Free var_f |> fst, typ_f, 
      HOLogic.mk_eq (var_x', map_f_x))
    val ex_R = HOLogic.mk_exists (dest_Free var_R |> fst, typ_R, rrel_R_x_x')
    val ex_R_imp_ex_f = HOLogic.mk_imp (ex_R, ex_f)
    val ex_nonrep = HOLogic.mk_exists (dest_Free var_x |> fst, typ_F,
      HOLogic.mk_all (dest_Free var_x' |> fst, typ_F', ex_R_imp_ex_f))
    val Tp_ex_nonrep = HOLogic.mk_Trueprop ex_nonrep

    (*F_rel_map_set2_strong (maybe rename?)*)
    val typ_Rs = map (fn (t, t') => [t, t'] ---> HOLogic.boolT) (As ~~ As')
    val (var_Rs, lthy) = mk_Frees "R" typ_Rs lthy;
    val As_pair = map (fn var_R => 
      let 
        val typ_fs = fst (fastype_of var_R |> strip_typeN 2) 
      in
        HOLogic.mk_prodT (nth typ_fs 0, nth typ_fs 1)
      end
      ) var_Rs

    val typ_z = MRBNF_Def.mk_T_of_mrbnf Ds As_pair Bs Fs mrbnf;
    val (var_z, lthy) = mk_Free "z" typ_z lthy;

    val map_fst_z = MRBNF_Def.mk_map_comb_of_mrbnf Ds (map BNF_Util.fst_const As_pair) 
      (map HOLogic.id_const Bs) (map HOLogic.id_const Fs) mrbnf $ var_z;
    val typ_y = fastype_of map_fst_z;
    val (var_y, lthy) = mk_Free "y" typ_y lthy;
    val map_eq_y = HOLogic.mk_eq (map_fst_z, var_y);

    val map_snd_z = MRBNF_Def.mk_map_comb_of_mrbnf Ds (map BNF_Util.snd_const As_pair) 
      (map HOLogic.id_const Bs) (map HOLogic.id_const Fs) mrbnf $ var_z;
    val typ_y' = fastype_of map_snd_z;
    val (var_y', lthy) = mk_Free "y'" typ_y' lthy;
    val map_eq_y' = HOLogic.mk_eq (map_snd_z, var_y');
    val map_eq_conj = HOLogic.mk_conj (map_eq_y, map_eq_y');
    
    val set_Fs = MRBNF_Def.mk_sets_of_mrbnf (replicate nr_ABFs Ds) (replicate nr_ABFs As_pair) 
      (replicate nr_ABFs Bs) (replicate nr_ABFs Fs) mrbnf;
    val set_Fs_live = filter (fn (_, vtype) => vtype = MRBNF_Def.Live_Var) (set_Fs ~~ var_types) |> map fst;
    val (set_map_conj, lthy) = fold (fn (set, var_R) => (fn (conj, lthy) =>
      let 
        val set_z = set $ var_z;
        val typ_xys = fst (fastype_of var_R |> strip_typeN 2);
        val typ_x_pair = nth typ_xys 0;
        val typ_y_pair = nth typ_xys 1;
        val (var_x_pair, lthy) = mk_Free "x" typ_x_pair lthy;
        val (var_y_pair, lthy) = mk_Free "y" typ_y_pair lthy;
        val R_xy = Term.list_comb (var_R, [var_x_pair, var_y_pair]);
        val absfree_R_xy = R_xy |> absfree (dest_Free var_y_pair) |>
          absfree (dest_Free var_x_pair);
        val case_prod_R_xy = HOLogic.mk_case_prod absfree_R_xy;
        val collect_set = HOLogic.Collect_const (HOLogic.mk_prodT (typ_x_pair, typ_y_pair)) $ case_prod_R_xy;
        val set_leq_collect = mk_leq set_z collect_set;
      in
        (HOLogic.mk_conj (set_leq_collect, conj), lthy)
      end)) (rev (set_Fs_live ~~ var_Rs)) (map_eq_conj, lthy) ;

    val ex1_z = Const ("HOL.Ex1", (typ_z --> HOLogic.boolT) --> HOLogic.boolT) $ 
      absfree (dest_Free var_z) set_map_conj;

    val rrel_F_R = MRBNF_Def.mk_rel_of_mrbnf Ds 
      (map (fst o HOLogic.dest_prodT) As_pair) 
      (map (snd o HOLogic.dest_prodT) As_pair) Bs Fs mrbnf
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
        (* sameShape *)
        val F_types = dest_Type typ_F |> snd;
        val lin_type = (nth F_types lin_pos)
        val typ_R = [lin_type, lin_type] ---> HOLogic.boolT
        val (var_R, lthy) = mk_Free "R" typ_R lthy;
        val (var_x, lthy) = mk_Free "x" typ_F lthy;
        val (var_x', lthy) = mk_Free "x'" typ_F lthy;
        val mr_rel_F = MRBNF_Def.mk_mr_rel_of_mrbnf Ds As As Bs Fs mrbnf
        val mr_rel_args = map_index (fn (i, (t, vt)) => if i = lin_pos then var_R else 
          (if vt = MRBNF_Def.Live_Var then HOLogic.eq_const t else HOLogic.id_const t)) (ABFs ~~ var_types)
        val mr_rel_F_R_x_x' = Term.list_comb (mr_rel_F, mr_rel_args @ [var_x, var_x']);
        val ex_R = HOLogic.mk_exists (dest_Free var_R |> fst, typ_R, mr_rel_F_R_x_x');
        val ss_rhs = ex_R |> absfree (dest_Free var_x') |>
          absfree (dest_Free var_x);
        val ss_binding = Binding.prefix_name ("sameShape_") (MRBNF_Def.name_of_mrbnf mrbnf);
        val ((_, ss_term, ss_def_thm), lthy) = MRBNF_Util.new_definition ss_binding ss_rhs lthy;

        val ss_arg_types = fastype_of ss_term |> strip_typeN 2 |> fst |> map (snd o dest_Type);
        val ss_TFree = subst_atomic_types (((nth ss_arg_types 0) ~~ F_types) @ ((nth ss_arg_types 1) ~~ F_types)) ss_term;
        
        (* nonrep *)
        val (var_x, lthy) = mk_Free "x" typ_F lthy;
        val (var_x', lthy) = mk_Free "x'" typ_F lthy;
        val typ_f = lin_type --> lin_type;
        val (var_f, lthy) = mk_Free "f" typ_f lthy;
        val ss_x_x' = Term.list_comb (ss_TFree, [var_x, var_x']);
        val map_funs = map_index (fn (i, t) => if i = lin_pos then var_f else HOLogic.id_const t) ABFs;
        val map_F = MRBNF_Def.mk_map_of_mrbnf Ds As As Bs Fs mrbnf;
        val map_f_x = Term.list_comb (map_F, map_funs @ [var_x]);
        val ex_f = HOLogic.mk_exists (dest_Free var_f |> fst, typ_f, 
          HOLogic.mk_eq (var_x', map_f_x));
        val forall_x' = HOLogic.mk_all (dest_Free var_x' |> fst, typ_F,
          HOLogic.mk_imp (ss_x_x', ex_f));
        val nrp_rhs = absfree (dest_Free var_x) forall_x';
        val nrp_binding = Binding.prefix_name ("nonrep_") (MRBNF_Def.name_of_mrbnf mrbnf);
        val ((_, nrp_term, nrp_def_thm), lthy) = MRBNF_Util.new_definition nrp_binding nrp_rhs lthy;

        val nrp_arg_types = fastype_of nrp_term |> domain_type |> dest_Type |> snd
        val nrp_TFree = subst_atomic_types (nrp_arg_types ~~ F_types) nrp_term

        (* typedef F'*)
        val (var_x, lthy) = mk_Free "x" typ_F lthy
        val nrp_x = Term.list_comb (nrp_TFree, [var_x])
        val td_term = HOLogic.mk_Collect (dest_Free var_x |> fst, typ_F, nrp_x)

        fun mk_typedef_tac ctxt = 
          let
            val mr_rel_F_def = MRBNF_Def.rel_def_of_mrbnf mrbnf
            val F_map_id = MRBNF_Def.map_id_of_mrbnf mrbnf
          in
            unfold_thms_tac ctxt [nrp_def_thm, ss_def_thm, @{thm mem_Collect_eq}, mr_rel_F_def, F_map_id] THEN
            HEADGOAL (rtac ctxt ex_nonrep_thm)
          end;
        val ((_, (td_info1, td_info2)), lthy) = MRBNF_Util.new_typedef b td_term mk_typedef_tac lthy;

        (* F' definitions *)
        (* asSS *)
        val (typ_arg, lthy) = mk_TFrees 1 lthy |>> the_single;
        val typ_f = typ_arg --> typ_arg;
        val (var_f, lthy) = mk_Free "f" typ_f lthy;
        val supp_f_bound = MRBNF_Util.mk_supp_bound var_f;
        val if_f_id = Const ("HOL.If", [HOLogic.boolT, typ_f, typ_f] ---> typ_f) $ 
          supp_f_bound $ var_f $ (HOLogic.id_const typ_arg);
        val asSS_rhs = absfree (dest_Free var_f) if_f_id;
        val asSS_binding = Binding.prefix_name ("asSS_") b;
        val ((_, asSS_term, asSS_def_thm), lthy) = MRBNF_Util.new_definition asSS_binding asSS_rhs lthy;

        val asSS_arg_type = fastype_of asSS_term |> domain_type |> domain_type;
        fun mk_asSS f = (subst_atomic_types [(asSS_arg_type, fastype_of f |> domain_type)] asSS_term) $ f;

        (* set_F's *)
        val typ_AbsF = #abs_type td_info1;
        val set_Fs = MRBNF_Def.mk_sets_of_mrbnf (replicate nr_ABFs Ds) (replicate nr_ABFs As)
          (replicate nr_ABFs Bs) (replicate nr_ABFs Fs) mrbnf;
        val (set_defs, lthy) = fold (fn (set, set_binding) => (fn (acc, lthy) =>
          let
            val Rep_const = Const (#Rep_name td_info1, (typ_AbsF) --> (typ_F));
            val set_rhs = HOLogic.mk_comp (set, Rep_const);
            val ((_, set_term, set_def_thm), lthy) = MRBNF_Util.new_definition set_binding set_rhs lthy;
          in
            ((set_term, set_def_thm)::acc, lthy)
          end)) ((set_Fs ~~ set_bs_non_dead) |> rev) ([], lthy);
        val (set_terms, set_def_thms) = split_list set_defs

        (* map_F' *)
        val typ_f = (nth As lin_live_pos) --> (nth As lin_live_pos)
        val (var_f, lthy) = mk_Free "f" typ_f lthy
        val typ_Afs = map (fn (A, A') => A --> A') (As ~~ As')
        val (var_Afs, lthy) = mk_Frees "g" typ_Afs lthy
        val var_Afs = nth_map lin_live_pos (fn _ => var_f) var_Afs
        val typ_Bfs = map (fn B => B --> B) Bs
        val (var_Bfs, lthy) = mk_Frees "u" typ_Bfs lthy
        val typ_Ffs = map (fn F => F --> F) Fs
        val (var_Ffs, lthy) = mk_Frees "v" typ_Ffs lthy
        val var_fs = MRBNF_Def.interlace var_Afs var_Bfs var_Ffs var_types

        val map_F = MRBNF_Def.mk_map_comb_of_mrbnf Ds (nth_map lin_live_pos mk_asBij var_Afs)
          (map (mk_asSS o mk_asBij) var_Bfs) (map mk_asSS var_Ffs) mrbnf;
        val Ftyp_map = fastype_of map_F;
        val typ_F = Ftyp_map |> domain_type;
        val typ_F' = Ftyp_map |> range_type;
        val typ_AbsF' = typ_subst_atomic ((dest_Type typ_F |> snd) ~~ (dest_Type typ_F' |> snd)) typ_AbsF;
        val Rep_const = Const (#Rep_name td_info1, (typ_AbsF) --> (typ_F));
        val Abs_const = Const (#Abs_name td_info1, (typ_F') --> (typ_AbsF'));
        val abs_map_rep = HOLogic.mk_comp (Abs_const, HOLogic.mk_comp (map_F, Rep_const));
        val map_F'_rhs = fold (fn var => (fn rhs => absfree (dest_Free var) rhs)) (rev var_fs) abs_map_rep;
        val map_F'_binding = Binding.prefix_name ("map_") b;
        val ((_, map_F'_term, map_F'_def_thm), lthy) = MRBNF_Util.new_definition map_F'_binding map_F'_rhs lthy;
        
        val F'typ_map = fastype_of map_F'_term |> strip_typeN nr_ABFs |> snd;
        val F_subst = (domain_type F'typ_map |> dest_Type |> snd) ~~ (dest_Type typ_AbsF |> snd);
        val F'_subst = (range_type F'typ_map |> dest_Type |> snd) ~~ (dest_Type typ_AbsF' |> snd);
        val map_F'_TFree = subst_atomic_types (F_subst @ F'_subst) map_F'_term;

        (* rrel_F' *)
        val (var_x, lthy) = mk_Free "x" typ_AbsF lthy;
        val (var_x', lthy) = mk_Free "x'" typ_AbsF' lthy;
        val (var_Rs, lthy) = mk_Frees "R" typ_Rs lthy;
        val var_Rs = nth_map lin_live_pos (fn R => fastype_of R |> domain_type |> HOLogic.eq_const) var_Rs;

        val Rep_x = Const (#Rep_name td_info1, (typ_AbsF) --> (typ_F)) $ var_x;
        val Rep_x' = Const (#Rep_name td_info1, (typ_AbsF') --> (typ_F')) $ var_x';
        val rrel_F = MRBNF_Def.mk_rel_of_mrbnf Ds As (select_one As' As lin_live_pos) Bs Fs mrbnf;
        val rrel_F_R_x_x' = Term.list_comb (rrel_F, var_Rs @ [Rep_x, Rep_x']);
        val vars = [var_x', var_x] @ (nth_drop lin_live_pos var_Rs |> rev);
        val rrel_F'_rhs = fold (fn var => (fn rhs => absfree (dest_Free var) rhs)) vars rrel_F_R_x_x';
        val rrel_F'_binding = Binding.prefix_name ("rrel_") b;
        val ((_, rrel_F'_term, rrel_F'_def_thm), lthy) = MRBNF_Util.new_definition rrel_F'_binding rrel_F'_rhs lthy;
        
        val rrel_F'_arg_types = fastype_of rrel_F'_term |> strip_typeN (nr_lives + 1) |> fst |> drop (nr_lives - 1);
        val F_subst = (nth rrel_F'_arg_types 0 |> dest_Type |> snd) ~~ (dest_Type typ_AbsF |> snd);
        val F'_subst = (nth rrel_F'_arg_types 1 |> dest_Type |> snd) ~~ (dest_Type typ_AbsF' |> snd);
        val rrel_F'_TFree = subst_atomic_types (F_subst @ F'_subst) rrel_F'_term;

        (* proving lemmas *)
        fun print_skip ctxt msg = print_tac ctxt msg THEN HEADGOAL (Skip_Proof.cheat_tac ctxt) (*TODO: remove*)
        
        (* make theorems & util *)
        val id_prems = MRBNF_Comp_Tactics.mk_id_prems mrbnf;

        val mr_rel_F_def = MRBNF_Def.rel_def_of_mrbnf mrbnf;
        val F_in_rel = MRBNF_Def.in_rel_of_mrbnf mrbnf;
        val F_map_id = MRBNF_Def.map_id_of_mrbnf mrbnf;
        val F_map_cong = MRBNF_Def.map_cong_of_mrbnf mrbnf;
        val F_rel_compp = MRBNF_Def.rel_OO_of_mrbnf mrbnf;
        val F_mr_rel_mono_strong0 = MRBNF_Def.mr_rel_mono_strong0_of_mrbnf mrbnf;
        val Rep_F'_inverse = #Rep_inverse td_info2;
        
        (* F_strong *)
        val typ_F' = typ_subst_atomic (As ~~ As') typ_F;
        val typ_RQs = map (fn (a, a') => [a, a'] ---> HOLogic.boolT) (As ~~ As');
        val (var_x, lthy) = mk_Free "x" typ_F lthy;
        val (var_y, lthy) = mk_Free "y" typ_F' lthy;
        val (var_Rs, lthy) = mk_Frees "R" typ_RQs lthy;
        val (var_Qs, lthy) = mk_Frees "Q" typ_RQs lthy;
        val mr_rel = MRBNF_Def.mk_mr_rel_of_mrbnf Ds As As' Bs Fs mrbnf;
        val id_Bs = (map HOLogic.id_const Bs);
        val id_Fs = (map HOLogic.id_const Fs);
        val R_args = MRBNF_Def.interlace var_Rs id_Bs id_Fs var_types;
        val Q_args = MRBNF_Def.interlace var_Qs id_Bs id_Fs var_types;
        val inf_args = MRBNF_Def.interlace (map (fn (R, Q) => 
            Const ("Lattices.inf_class.inf", [fastype_of R, fastype_of Q] ---> fastype_of R) $ R $ Q
          ) (var_Rs ~~ var_Qs)) id_Bs id_Fs var_types;
        val mr_rel_R = Term.list_comb (mr_rel, R_args @ [var_x, var_y]) |> HOLogic.mk_Trueprop;
        val mr_rel_Q = Term.list_comb (mr_rel, Q_args @ [var_x, var_y]) |> HOLogic.mk_Trueprop;
        val mr_rel_inf = Term.list_comb (mr_rel, inf_args @ [var_x, var_y]) |> HOLogic.mk_Trueprop;
        val F_strong_term = Logic.mk_implies (Logic.mk_implies (mr_rel_R, mr_rel_Q), mr_rel_inf);

        val F_strong_thm = Goal.prove_sorry lthy (*(map (fst o dest_Free) (var_Rs @ var_Qs @ [var_x, var_y]))*) [] 
          [mr_rel_R, mr_rel_Q] mr_rel_inf
          (fn {context = ctxt, prems} => 
            HEADGOAL (EVERY' [
              Method.insert_tac ctxt prems,
              forward_tac ctxt [F_mr_rel_mono_strong0 OF flat (replicate 2 id_prems)] THEN_ALL_NEW (
                TRY o (rtac ctxt ballI THEN_ALL_NEW 
                  resolve_tac ctxt [ballI, refl]) THEN_ALL_NEW
                TRY o (rtac ctxt impI THEN_ALL_NEW
                  rtac ctxt (trans OF [@{thm top_apply} RS fun_cong, trans OF @{thms top_apply top_bool_def}]))),
              K (unfold_thms_tac ctxt [F_map_id, mr_rel_F_def, @{thm eq_True}]),
              rotate_tac 2,
              dtac ctxt (iffD1 OF [F_rel_map_set2_strong_thm]),
              K (unfold_thms_tac ctxt ([eqTrueI OF [subset_UNIV]] @ @{thms top_apply top_bool_def 
                Collect_const_case_prod if_True simp_thms(22)})),
              K (unfold_thms_tac ctxt ([unfold_thms ctxt [id_apply, F_map_id, @{thm OO_Grp_alt}] 
                (F_in_rel OF id_prems), sym OF @{thms id_def}, mem_Collect_eq])),
              etac ctxt exE,
              etac ctxt exE,
              etac ctxt @{thm alt_ex1E}
            ]) THEN
            REPEAT_DETERM_N (3+2*nr_lives) (HEADGOAL (etac ctxt conjE)) THEN
            HEADGOAL (Subgoal.FOCUS
              (fn {prems, context = ctxt, params, ...} => 
                HEADGOAL (Method.insert_tac ctxt [
                  infer_instantiate' ctxt [SOME (snd (nth params 1)), SOME (snd (nth params 0))] (@{thm spec2} OF [nth prems 0]),
                  infer_instantiate' ctxt [SOME (snd (nth params 2)), SOME (snd (nth params 0))] (@{thm spec2} OF [nth prems 0])] THEN_ALL_NEW
                  etac ctxt impE THEN_ALL_NEW
                  etac ctxt impE) THEN
                REPEAT_DETERM_N 3 (HEADGOAL (
                  rtac ctxt conjI THEN_ALL_NEW
                  rtac ctxt conjI THEN_ALL_NEW
                  resolve_tac ctxt prems)) THEN
                HEADGOAL (rtac ctxt exI) THEN
                unfold_thms_tac ctxt @{thms inf_fun_def inf_bool_def} THEN
                HEADGOAL (rtac ctxt conjI) THEN
                HEADGOAL (Method.insert_tac ctxt prems) THEN
                HEADGOAL (hyp_subst_tac_thin true ctxt) THEN
                REPEAT_DETERM_N nr_lives (HEADGOAL (EVERY' [
                  TRY o rtac ctxt conjI,
                  rtac ctxt @{thm subrelI},
                  rtac ctxt CollectI,
                  rtac ctxt @{thm case_prodI},
                  rtac ctxt conjI THEN_ALL_NEW 
                    etac ctxt (@{thm rev_subsetD} RS (iffD1 OF @{thms prod_in_Collect_iff})),
                assume_tac ctxt,
                assume_tac ctxt])) THEN
                HEADGOAL (rtac ctxt conjI THEN_ALL_NEW resolve_tac ctxt prems)
              ) ctxt))


        val _ = F_strong_thm |> @{print}

        (* mr_rel_F_exchange *)
        (* lemma rel_F_exchange: 
  fixes x :: "('a, 'b :: var, 'c :: var, 'd, 'e :: var, 'f) F" and x' :: "('a', 'b, 'c, 'd', 'e, 'f) F"
  assumes "mr_rel_F R1 id id R4 id x x'" and "mr_rel_F Q1 id id Q4 id x x'"
  shows "mr_rel_F R1 id id Q4 id x x'"  *)
        
        (* register MRBNF *)
        val tacs = {
          map_id0 = fn ctxt =>
            unfold_thms_tac ctxt ([map_F'_def_thm, 
              eqTrueI OF @{thms bij_id}, eqTrueI OF @{thms supp_id_bound}] @ 
              (asSS_def_thm :: @{thms asBij_def if_True})) THEN
            HEADGOAL (rtac ctxt ext) THEN
            unfold_thms_tac ctxt [F_map_id, Rep_F'_inverse, @{thm o_apply}] THEN
            unfold_thms_tac ctxt @{thms id_def} THEN
            HEADGOAL (rtac ctxt refl),
          map_comp0 = fn ctxt => print_skip ctxt "map_comp0",
          map_cong0 = fn ctxt => 
            HEADGOAL (Subgoal.FOCUS (fn {prems, context = ctxt, ...} =>
              unfold_thms_tac ctxt ([map_F'_def_thm, asSS_def_thm] @ map (fn thm => thm RS eqTrueI) prems @
                @{thms asBij_def if_True o_apply}) THEN
              HEADGOAL (EqSubst.eqsubst_tac ctxt [0] [F_map_cong] THEN_ALL_NEW
                TRY o resolve_tac ctxt (rev prems)) THEN
              HEADGOAL (rtac ctxt refl) THEN
              unfold_thms_tac ctxt (@{thm o_apply} :: set_def_thms) THEN
              REPEAT_DETERM_N (length set_def_thms) (
                HEADGOAL (assume_tac ctxt)) THEN
              HEADGOAL (rtac ctxt refl)
            ) ctxt),
          set_map0 = map (fn thm => fn ctxt => print_skip ctxt "set_map0") (MRBNF_Def.set_map0_of_mrbnf mrbnf),
          infinite_regular_card_order = fn ctxt => HEADGOAL (rtac ctxt 
            (MRBNF_Def.bd_infinite_regular_card_order_of_mrbnf mrbnf)),
          set_bd = map (fn (set_F'_def, set_bd_thm) => fn ctxt => 
            unfold_thms_tac ctxt [set_F'_def, o_apply] THEN
            HEADGOAL (rtac ctxt set_bd_thm)) 
            (set_def_thms ~~ (MRBNF_Def.set_bd_of_mrbnf mrbnf)),
          le_rel_OO = fn ctxt =>
            HEADGOAL (Subgoal.FOCUS (fn {context = ctxt, ...} => 
              HEADGOAL (EVERY' [
                rtac ctxt @{thm predicate2I},
                etac ctxt @{thm relcomppE},
                K (unfold_thms_tac ctxt [rrel_F'_def_thm]),
                EqSubst.eqsubst_tac ctxt [1] @{thms eq_OO[symmetric]},
                EqSubst.eqsubst_tac ctxt [1] [F_rel_compp],
                K (unfold_thms_tac ctxt [rrel_F'_def_thm]),
                rtac ctxt @{thm relcomppI} THEN_ALL_NEW assume_tac ctxt
              ])
            ) ctxt),
          in_rel = fn ctxt => print_skip ctxt "in_rel",
          pred_set = fn ctxt => HEADGOAL (rtac ctxt refl),
          wit = fn ctxt => print_skip ctxt "wit"
        }
        val var_types_Abs = nth_map lin_pos (fn _ => MRBNF_Def.Bound_Var) var_types;

        (* TODO: replace schematic variables in terms *)
        val _ = MRBNF_Def.mrbnf_def MRBNF_Def.Do_Inline (MRBNF_Def.user_policy MRBNF_Def.Note_Some) 
          false I tacs (SOME Ds) NONE map_F'_binding rrel_F'_binding Binding.empty set_bs_non_dead 
          (((((((b, typ_AbsF), map_F'_term), (var_types_Abs ~~ set_terms)),
            MRBNF_Def.mk_bd_of_mrbnf Ds Bs Fs mrbnf),
            []),
            SOME rrel_F'_term),
            NONE)
          lthy

       (*mrbnf_def Do_Inline (K Dont_Note) false I mrbnf_tactics (SOME deads) NONE
      Binding.empty Binding.empty Binding.empty []
    (((((((BNF_Def.name_of_bnf bnf, BNF_Def.mk_T_of_bnf deads lives bnf), BNF_Def.mk_map_of_bnf deads lives lives' bnf),
    map (fn x => (Live_Var, x)) (BNF_Def.mk_sets_of_bnf (replicate n deads) (replicate n lives) bnf)),
    BNF_Def.mk_bd_of_bnf deads lives bnf),
    map snd (BNF_Def.mk_wits_of_bnf (replicate nwits deads) (replicate nwits lives) bnf)),
    SOME (BNF_Def.mk_rel_of_bnf deads lives lives' bnf)),
    SOME (BNF_Def.mk_pred_of_bnf deads lives bnf))
    lthy*)

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
