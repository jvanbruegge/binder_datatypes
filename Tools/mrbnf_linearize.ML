

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
val mk_Free = yield_singleton o mk_Frees;

fun dest_Type_atomic T = if not (is_Type T) then [T] else dest_Type T |> snd |> map dest_Type_atomic |> flat

(** Term construction **)
fun mk_asBij f = let val typ_f = fastype_of f; in
  Const (@{const_name asBij}, typ_f --> typ_f) $ f end;

fun mk_asSS f = let val typ_f = fastype_of f; in 
  Const (@{const_name asSS}, typ_f --> typ_f) $ f end;

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
    val _ = wits |> @{print}
    val set_bs = map fst specs;
    val tfrees = map (TFree o snd) specs |> @{print};
    val on_tfree = TFree (on_tvar, @{sort type}) |> @{print};
    val lin_pos' = find_index (fn x => x = on_tfree) tfrees |> @{print};

(*
    val (F_name, F_vars) = dest_Type repT ||> map dest_TFree |> @{print};  

    val mrbnf = F_name |> MRBNF_Def.mrbnf_of lthy |> the
*)

    fun flatten_tyargs Ass =
      map dest_TFree tfrees
      |> filter (fn T => exists (fn Ts => member op= Ts T) Ass);
    val ((mrbnf,(orig_Ds, orig_ABFs)), (_,lthy)) = MRBNF_Comp.mrbnf_of_typ true MRBNF_Def.Smart_Inline
      (Binding.prefix_name (Binding.name_of b)) flatten_tyargs [] [] [] repT
      ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy);

      
    val _ = (orig_Ds, orig_ABFs) |> @{print}
    val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf |> @{print};
    val lin_pos = find_index (fn x => x = on_tfree) orig_ABFs |> @{print};
    val orig_As = map_filter (fn (v, vt) => if vt = MRBNF_Def.Live_Var then SOME v else NONE) 
      (orig_ABFs ~~ var_types) |> @{print};
    val lin_live_pos = find_index (fn x => x = on_tfree) orig_As |> @{print};

    val deads = MRBNF_Def.deads_of_mrbnf mrbnf;

    val nr_lives = MRBNF_Def.live_of_mrbnf mrbnf;
    val nr_frees = MRBNF_Def.free_of_mrbnf mrbnf;
    val nr_bounds = MRBNF_Def.bound_of_mrbnf mrbnf;
    val nr_ABFs = nr_lives + nr_frees + nr_bounds;
    val class = MRBNF_Def.class_of_mrbnf mrbnf;

    val (((((Ds, As), As'), Fs), Bs), n_lthy) = lthy
      |> mk_TFrees' (map Type.sort_of_atyp deads)
      ||>> mk_TFrees nr_lives
      ||>> mk_TFrees nr_lives
      ||>> mk_TFrees' (replicate nr_frees class)
      ||>> mk_TFrees' (replicate nr_bounds class);
    val ABFs = MRBNF_Def.interlace As Bs Fs var_types;

    fun select_one types types' pos = map_index (fn (i, (t, t')) => if i = pos then t' else t) (types ~~ types')
    
    (* TODO: This section has to be fixed! for now assume that deads are all at the end*)
    val lives = MRBNF_Def.lives_of_mrbnf mrbnf;
    val lin_live_pos' = find_index (fn v => (dest_TVar v |> fst |> fst) = on_tvar) lives |> @{print};
    val set_bs_non_dead = take (nr_lives + nr_bounds + nr_frees) set_bs |> @{print}
    val set_bs_non_dead = map_index (fn (i, b_opt) => if Option.getOpt (b_opt, Binding.empty) |> Binding.is_empty |> not then
              the b_opt else
              Binding.prefix_name ("set" ^ (Int.toString (i+1)) ^ "_") b) set_bs_non_dead

    (* make Frees*)
    val As_pair = map (fn (A, A') => HOLogic.mk_prodT (A, A')) (As ~~ As');

    val typ_x = MRBNF_Def.mk_T_of_mrbnf Ds As Bs Fs mrbnf;
    val typ_xl' = MRBNF_Def.mk_T_of_mrbnf Ds (select_one As As' lin_live_pos) Bs Fs mrbnf; (* lin_pos changes typ *)
    val typ_x'l = MRBNF_Def.mk_T_of_mrbnf Ds (select_one As' As lin_live_pos) Bs Fs mrbnf; (* other lives change typ *)
    val typ_x' = MRBNF_Def.mk_T_of_mrbnf Ds As' Bs Fs mrbnf;
    val typ_z = MRBNF_Def.mk_T_of_mrbnf Ds As_pair Bs Fs mrbnf; (* z: F with (A, A') as lives *)
    val typ_f_As = map (fn A => A --> A) As;
    val typ_f'_As = map (fn (A, A') => A --> A') (As ~~ As');
    val typ_u_Bs = map (fn B => B --> B) Bs;
    val typ_v_Fs = map (fn F => F --> F) Fs;
    val typ_R_As = map (fn A => [A, A] ---> HOLogic.boolT) As;
    val typ_R'_As = map (fn (A, A') => [A, A'] ---> HOLogic.boolT) (As ~~ As');
    
    val (var_as, n_lthy) = mk_Frees "a" As n_lthy;
    val (var_bs, n_lthy) = mk_Frees "b" As' n_lthy;
    val (var_x, n_lthy) = mk_Free "x" typ_x n_lthy;
    val (var_x2, n_lthy) = mk_Free "x" typ_x n_lthy;
    val (var_xl', n_lthy) = mk_Free "xl'" typ_xl' n_lthy;
    val (var_x'l, n_lthy) = mk_Free "x'l" typ_x'l n_lthy;
    val (var_x', n_lthy) = mk_Free "x'" typ_x' n_lthy;
    val (var_z, n_lthy) = mk_Free "z" typ_z n_lthy;
    val (var_f_As, n_lthy) = mk_Frees "f" typ_f_As n_lthy;
    val (var_f'_As, n_lthy) = mk_Frees "f'" typ_f'_As n_lthy;
    val (var_u_Bs, n_lthy) = mk_Frees "u" typ_u_Bs n_lthy;
    val (var_v_Fs, n_lthy) = mk_Frees "v" typ_v_Fs n_lthy;
    val (var_R_As, n_lthy) = mk_Frees "R" typ_R_As n_lthy;
    val (var_R'_As, n_lthy) = mk_Frees "R'" typ_R'_As n_lthy;
    val (var_R'_As2, n_lthy) = mk_Frees "R'" typ_R'_As n_lthy;

    (* ex_nonrep *)
    val map_F = MRBNF_Def.mk_map_of_mrbnf Ds As As Bs Fs mrbnf;
    val f = nth var_f_As lin_live_pos;
    val map_funs = map_index (fn (i, t) => if i = lin_pos then f else HOLogic.id_const t) ABFs;
    val map_f_x = Term.list_comb (map_F, map_funs @ [var_x]);

    val rrel_F = MRBNF_Def.mk_rel_of_mrbnf Ds As As Bs Fs mrbnf;
    val eqs = map HOLogic.eq_const As;
    val R = nth var_R_As lin_live_pos;
    val Rs = map_index (fn (i, eq) => if i = lin_live_pos then R else eq) eqs;
    val rrel_R_x_x' = Term.list_comb (rrel_F, Rs @ [var_x, var_x2]);

    val ex_f = HOLogic.mk_exists (dest_Free f |> fst, dest_Free f |> snd, 
      HOLogic.mk_eq (var_x2, map_f_x));
    val ex_R_rrel = HOLogic.mk_exists (dest_Free R |> fst, dest_Free R |> snd, rrel_R_x_x');
    val ex_R_imp_ex_f = HOLogic.mk_imp (ex_R_rrel, ex_f);
    val ex_nonrep = HOLogic.mk_exists (dest_Free var_x |> fst, dest_Free var_x |> snd,
      HOLogic.mk_all (dest_Free var_x2 |> fst, dest_Free var_x2 |> snd, ex_R_imp_ex_f));
    val Tp_ex_nonrep = HOLogic.mk_Trueprop ex_nonrep;

    (*F_rel_map_set2_strong (maybe rename?)*)
    val map_fst_z = MRBNF_Def.mk_map_comb_of_mrbnf Ds (map BNF_Util.fst_const As_pair) 
      (map HOLogic.id_const Bs) (map HOLogic.id_const Fs) mrbnf $ var_z;
    val map_eq_x = HOLogic.mk_eq (map_fst_z, var_x);

    val map_snd_z = MRBNF_Def.mk_map_comb_of_mrbnf Ds (map BNF_Util.snd_const As_pair) 
      (map HOLogic.id_const Bs) (map HOLogic.id_const Fs) mrbnf $ var_z;
    val map_eq_x' = HOLogic.mk_eq (map_snd_z, var_x');
    val map_eq_conj = HOLogic.mk_conj (map_eq_x, map_eq_x');
    
    val set_Fs = MRBNF_Def.mk_sets_of_mrbnf (replicate nr_ABFs Ds) (replicate nr_ABFs As_pair) 
      (replicate nr_ABFs Bs) (replicate nr_ABFs Fs) mrbnf;
    val set_Fs_live = filter (fn (_, vtype) => vtype = MRBNF_Def.Live_Var) (set_Fs ~~ var_types) |> map fst;
    val set_map_conj = fold (fn (set, (R, (var_a, var_b))) => (fn conj =>
      let 
        val set_z = set $ var_z;
        val R_xy = R $ var_a $ var_b;
        val absfree_R_xy = R_xy |> absfree (dest_Free var_b) |>
          absfree (dest_Free var_a);
        val case_prod_R_xy = HOLogic.mk_case_prod absfree_R_xy;
        val collect_set = HOLogic.Collect_const 
          (HOLogic.mk_prodT (fastype_of var_a, fastype_of var_b)) $ case_prod_R_xy;
        val set_leq_collect = mk_leq set_z collect_set;
      in
        HOLogic.mk_conj (set_leq_collect, conj)
      end)) (rev (set_Fs_live ~~ (var_R'_As ~~ (var_as ~~ var_bs)))) map_eq_conj;

    val ex1_z = Const ("HOL.Ex1", (typ_z --> HOLogic.boolT) --> HOLogic.boolT) $ 
      absfree (dest_Free var_z) set_map_conj;

    val rrel_F_R = MRBNF_Def.mk_rel_of_mrbnf Ds 
      (map (fst o HOLogic.dest_prodT) As_pair) 
      (map (snd o HOLogic.dest_prodT) As_pair) Bs Fs mrbnf
    val rrel_R_x_x' = Term.list_comb (rrel_F_R, var_R'_As @ [var_x, var_x']);
    val rrel_eq_ex1 = HOLogic.mk_eq (rrel_R_x_x', ex1_z);
    val all_x_x' = HOLogic.mk_Trueprop rrel_eq_ex1 |> Logic.all var_x' |> Logic.all var_x;
    val F_rel_map_set2_strong = fold (fn R => (fn all => Logic.all R all)) var_R'_As all_x_x';

    val plugins =
      get_first (fn Plugins_Option f => SOME (f lthy) | _ => NONE) (rev opts)
        |> the_default Plugin_Name.default_filter;


    val goals = [F_rel_map_set2_strong, Tp_ex_nonrep];

    fun after_qed ([F_rel_map_set2_strong_thm] :: [ex_nonrep_thm] :: wit_thms) lthy = 
      let
        (* sameShape *)
        val R = nth var_R_As lin_live_pos;
        val mr_rel_F = MRBNF_Def.mk_mr_rel_of_mrbnf Ds As As Bs Fs mrbnf
        val mr_rel_args = map_index (fn (i, (t, vt)) => if i = lin_pos then R else 
          (if vt = MRBNF_Def.Live_Var then HOLogic.eq_const t else HOLogic.id_const t)) (ABFs ~~ var_types)
        val mr_rel_F_R_x_x' = Term.list_comb (mr_rel_F, mr_rel_args @ [var_x, var_x2]);
        val ex_R = HOLogic.mk_exists (dest_Free R |> fst, dest_Free R |> snd, mr_rel_F_R_x_x');
        val ss_rhs = ex_R |> absfree (dest_Free var_x2) |>
          absfree (dest_Free var_x);
        val ss_binding = Binding.prefix_name ("sameShape'_") (MRBNF_Def.name_of_mrbnf mrbnf);
        val ((_, ss_term, ss_def_thm), lthy) = MRBNF_Util.new_definition ss_binding ss_rhs lthy;

        val x_atomics = dest_Type_atomic typ_x;
        val ss_arg_atomics = fastype_of ss_term |> domain_type |> dest_Type_atomic;
        val ss_TFree = subst_atomic_types (ss_arg_atomics ~~ x_atomics) ss_term;

        (* nonrep *)
        val f = nth var_f_As lin_live_pos;
        val map_funs = map_index (fn (i, t) => if i = lin_pos then f else HOLogic.id_const t) ABFs;
        val map_F = MRBNF_Def.mk_map_of_mrbnf Ds As As Bs Fs mrbnf;
        val map_f_x = Term.list_comb (map_F, map_funs @ [var_x]);
        val ex_f = HOLogic.mk_exists (dest_Free f |> fst, dest_Free f |> snd, 
          HOLogic.mk_eq (var_x2, map_f_x));
        val forall_x' = HOLogic.mk_all (dest_Free var_x2 |> fst, dest_Free var_x2 |> snd,
          HOLogic.mk_imp (ss_TFree $ var_x $ var_x2, ex_f));
        val nrp_rhs = absfree (dest_Free var_x) forall_x';
        val nrp_binding = Binding.prefix_name ("nonrep'_") (MRBNF_Def.name_of_mrbnf mrbnf);
        val ((_, nrp_term, nrp_def_thm), lthy) = MRBNF_Util.new_definition nrp_binding nrp_rhs lthy;

        val nrp_arg_atomics = fastype_of nrp_term |> domain_type |> dest_Type_atomic
        val nrp_TFree = subst_atomic_types (nrp_arg_atomics ~~ x_atomics) nrp_term

        (* typedef F'*)
        val nrp_x = nrp_TFree $ var_x
        val td_term = HOLogic.mk_Collect (dest_Free var_x |> fst, dest_Free var_x |> snd, nrp_x)

        fun mk_typedef_tac ctxt = 
          let
            val mr_rel_F_def = MRBNF_Def.rel_def_of_mrbnf mrbnf
            val F_map_id = MRBNF_Def.map_id_of_mrbnf mrbnf
          in
            unfold_thms_tac ctxt [nrp_def_thm, ss_def_thm, @{thm mem_Collect_eq}, mr_rel_F_def, F_map_id] THEN
            HEADGOAL (rtac ctxt ex_nonrep_thm)
          end;
        val ((_, (td_info1, td_info2)), lthy) = MRBNF_Util.new_typedef b td_term mk_typedef_tac lthy;

        (* mk F' Frees *)
        val typ_y = #abs_type td_info1;
        val typ_y' = typ_subst_atomic (nth_drop lin_live_pos (As ~~ As')) typ_y;
        val (var_y, n_lthy) = mk_Free "y" typ_y n_lthy;
        val (var_y', _) = mk_Free "y'" typ_y' n_lthy;

        (* F' definitions *)
        (* set_F's *)
        val set_Fs = MRBNF_Def.mk_sets_of_mrbnf (replicate nr_ABFs Ds) (replicate nr_ABFs As)
          (replicate nr_ABFs Bs) (replicate nr_ABFs Fs) mrbnf;
        val (set_defs, lthy) = fold (fn (set, set_binding) => (fn (acc, lthy) =>
          let
            val Rep_const = Const (#Rep_name td_info1, (typ_y) --> (typ_x));
            val set_rhs = HOLogic.mk_comp (set, Rep_const);
            val ((_, set_term, set_def_thm), lthy) = MRBNF_Util.new_definition set_binding set_rhs lthy;
          in
            ((set_term, set_def_thm)::acc, lthy)
          end)) ((set_Fs ~~ set_bs_non_dead) |> rev) ([], lthy);
        val (set_terms, set_def_thms) = split_list set_defs

        (* map_F' *)
        val ff'_As = nth_map lin_live_pos (fn _ => nth var_f_As lin_live_pos) var_f'_As
        val fs = MRBNF_Def.interlace ff'_As var_u_Bs var_v_Fs var_types

        val map_F = MRBNF_Def.mk_map_comb_of_mrbnf Ds (nth_map lin_live_pos mk_asBij ff'_As)
          (map (mk_asSS o mk_asBij) var_u_Bs) (map mk_asSS var_v_Fs) mrbnf;
        val Rep_const = Const (#Rep_name td_info1, (typ_y) --> (typ_x));
        val Abs_const = Const (#Abs_name td_info1, (typ_x'l) --> (typ_y'));
        val abs_map_rep = HOLogic.mk_comp (Abs_const, HOLogic.mk_comp (map_F, Rep_const));
        val map_F'_rhs = fold (fn var => (fn rhs => absfree (dest_Free var) rhs)) (rev fs) abs_map_rep;
        val map_F'_binding = if Binding.is_empty map_b then Binding.prefix_name ("map_") b else map_b;
        val ((_, map_F'_term, map_F'_def_thm), lthy) = MRBNF_Util.new_definition map_F'_binding map_F'_rhs lthy;

        (* rrel_F' *)
        val eq_Rs = nth_map lin_live_pos (fn R => fastype_of R |> domain_type |> HOLogic.eq_const) var_R'_As;

        val Rep_x = Const (#Rep_name td_info1, (typ_y) --> (typ_x)) $ var_y;
        val Rep_x' = Const (#Rep_name td_info1, (typ_y') --> (typ_x'l)) $ var_y';
        val rrel_F = MRBNF_Def.mk_rel_of_mrbnf Ds As (select_one As' As lin_live_pos) Bs Fs mrbnf;
        val rrel_F_R_x_x' = Term.list_comb (rrel_F, eq_Rs @ [Rep_x, Rep_x']);
        val vars = [var_y', var_y] @ (nth_drop lin_live_pos eq_Rs |> rev);
        val rrel_F'_rhs = fold (fn var => (fn rhs => absfree (dest_Free var) rhs)) vars rrel_F_R_x_x';
        val rrel_F'_binding = if Binding.is_empty rel_b then Binding.prefix_name ("rrel_") b else rel_b;
        val ((_, rrel_F'_term, rrel_F'_def_thm), lthy) = MRBNF_Util.new_definition rrel_F'_binding rrel_F'_rhs lthy;

        (** proving lemmas **)        
        (* make theorems & util *)
        val id_prems = MRBNF_Comp_Tactics.mk_id_prems mrbnf;

        val mr_rel_F_def = MRBNF_Def.rel_def_of_mrbnf mrbnf;
        val F_in_rel = MRBNF_Def.in_rel_of_mrbnf mrbnf;
        val F_map_id = MRBNF_Def.map_id_of_mrbnf mrbnf;
        val F_map_cong = MRBNF_Def.map_cong_of_mrbnf mrbnf;  
        val F_map_comp = MRBNF_Def.map_comp_of_mrbnf mrbnf;
        val F_map_comp0 = MRBNF_Def.map_comp0_of_mrbnf mrbnf;
        val F_set_maps = MRBNF_Def.set_map_of_mrbnf mrbnf;
        val F_rel_eq = MRBNF_Def.rel_eq_of_mrbnf mrbnf;
        val F_rel_compp = MRBNF_Def.rel_OO_of_mrbnf mrbnf;
        val F_rel_Grp = MRBNF_Def.rel_Grp_of_mrbnf mrbnf;
        val F_rel_maps = MRBNF_Def.rel_map_of_mrbnf mrbnf;
        val F_rel_refl_strong = MRBNF_Def.rel_refl_strong_of_mrbnf mrbnf;
        val F_rel_mono_strong = MRBNF_Def.rel_mono_strong_of_mrbnf mrbnf;
        val F_mr_rel_id = MRBNF_Def.mr_rel_id_of_mrbnf mrbnf;
        val F_mr_rel_Grp = MRBNF_Def.mr_rel_Grp_of_mrbnf mrbnf;
        val F_mr_rel_flip = MRBNF_Def.mr_rel_flip_of_mrbnf mrbnf;
        val F_mr_rel_maps = MRBNF_Def.mr_rel_map_of_mrbnf mrbnf;
        val F_mr_rel_mono_strong0 = MRBNF_Def.mr_rel_mono_strong0_of_mrbnf mrbnf;

        val Rep_F'_inverse = #Rep_inverse td_info2;
        fun mk_Rep_F' ctxt = #Rep td_info2 |> unfold_thms ctxt [@{thm mem_Collect_eq}];
        fun mk_Abs_F'_inverse ctxt = #Abs_inverse td_info2 |> unfold_thms ctxt [@{thm mem_Collect_eq}];
        
        (* rrel_F_alt *) (*not used yet*)
        val rrel_F_l' = MRBNF_Def.mk_rel_of_mrbnf Ds As (select_one As As' lin_live_pos) Bs Fs mrbnf;
        val R = nth var_R'_As lin_live_pos;
        val Rtop = Const ("Orderings.top_class.top", dest_Free R |> snd)
        val R_eqs = map_index (fn (i, eq) => if i = lin_live_pos then R else eq) eqs;
        val top_eqs = map_index (fn (i, eq) => if i = lin_live_pos then Rtop else eq) eqs;
        val rrel_R = Term.list_comb (rrel_F_l', R_eqs @ [var_x, var_xl']);
        val ex_R = HOLogic.mk_exists (dest_Free R |> fst, dest_Free R |> snd, rrel_R);
        val rrel_top = Term.list_comb (rrel_F_l', top_eqs @ [var_x, var_xl'])
        val rrel_top_eq_ex_R = HOLogic.mk_eq (rrel_top, ex_R) |> HOLogic.mk_Trueprop;
        val rrel_F_alt_thm = Goal.prove_sorry lthy (map (fst o dest_Free) [var_x, var_xl'])
          [] rrel_top_eq_ex_R
          (fn {context = ctxt, prems = _} => 
            HEADGOAL (EVERY' [
                rtac ctxt iffI,
                rtac ctxt exI,
                assume_tac ctxt,
                etac ctxt exE,
                rtac ctxt F_rel_mono_strong
            ]) THEN
            unfold_thms_tac ctxt @{thms top_apply top_bool_def} THEN
            REPEAT_DETERM_N (nr_lives+1) (
              HEADGOAL (assume_tac ctxt ORELSE' rtac ctxt TrueI)));

        (* F_strong *)
        val mr_rel = MRBNF_Def.mk_mr_rel_of_mrbnf Ds As As' Bs Fs mrbnf;
        val id_Bs = (map HOLogic.id_const Bs);
        val id_Fs = (map HOLogic.id_const Fs);
        val R_args = MRBNF_Def.interlace var_R'_As id_Bs id_Fs var_types;
        val Q_args = MRBNF_Def.interlace var_R'_As2 id_Bs id_Fs var_types;
        val inf_args = MRBNF_Def.interlace (map (fn (R, Q) => 
            Const ("Lattices.inf_class.inf", [fastype_of R, fastype_of Q] ---> fastype_of R) $ R $ Q
          ) (var_R'_As ~~ var_R'_As2)) id_Bs id_Fs var_types;
        val mr_rel_R = Term.list_comb (mr_rel, R_args @ [var_x, var_x']) |> HOLogic.mk_Trueprop;
        val mr_rel_Q = Term.list_comb (mr_rel, Q_args @ [var_x, var_x']) |> HOLogic.mk_Trueprop;
        val mr_rel_inf = Term.list_comb (mr_rel, inf_args @ [var_x, var_x']) |> HOLogic.mk_Trueprop;

        val F_strong_thm = Goal.prove_sorry lthy (map (fst o dest_Free) (var_R'_As @ var_R'_As2 @ [var_x, var_x'])) 
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
              ) ctxt));

        (* mr_rel_F_exchange *)
        val RQ_args = select_one Q_args R_args lin_pos;
        val mr_rel_RQ = Term.list_comb (mr_rel, RQ_args @ [var_x, var_x']) |> HOLogic.mk_Trueprop;
        val mr_rel_F_exchange_thm = Goal.prove_sorry lthy (map (fst o dest_Free) (var_R'_As @ var_R'_As2 @ [var_x, var_x'])) 
          [mr_rel_R, mr_rel_Q] mr_rel_RQ
          (fn {context = ctxt, prems} => 
            HEADGOAL (EVERY' [
              rtac ctxt ((F_mr_rel_mono_strong0 OF flat (replicate 2 id_prems))),
              rtac ctxt (F_strong_thm OF prems),
              K (unfold_thms_tac ctxt ([id_apply, eqTrueI OF [refl]] @ @{thms ball_triv inf_apply inf_bool_def}))
            ]) THEN
            ALLGOALS (
              (rtac ctxt impI THEN' 
              rtac ctxt TrueI) ORELSE'
              (rtac ctxt ballI THEN' 
              rtac ctxt ballI THEN'
              rtac ctxt impI THEN'
              eresolve_tac ctxt [conjunct1, conjunct2])));
        
        (* nonrep_map_F *)
        val u_props_raw = map (fn u => [MRBNF_Util.mk_bij u |> HOLogic.mk_Trueprop, 
            MRBNF_Util.mk_supp_bound u |> HOLogic.mk_Trueprop]) var_u_Bs;
        val v_props_raw = map (fn v => [MRBNF_Util.mk_supp_bound v |> HOLogic.mk_Trueprop]) var_v_Fs;
        val uv_props = filter (fn v => v <> MRBNF_Def.Live_Var) var_types |> 
          MRBNF_Def.interlace [] u_props_raw v_props_raw |> flat;
        val nrp_x_prop = HOLogic.mk_Trueprop nrp_x;
        val nrp_TFree' = subst_atomic_types (nth_drop lin_live_pos (As ~~ As')) nrp_TFree
        val id_f'_As = nth_map lin_live_pos (fn f => fastype_of f |> domain_type |> HOLogic.id_const) var_f'_As;
        val map_uv = MRBNF_Def.mk_map_comb_of_mrbnf Ds id_f'_As var_u_Bs var_v_Fs mrbnf;
        val nonrep_map_uv_prop = nrp_TFree' $ (map_uv $ var_x) |> HOLogic.mk_Trueprop;
        
        val nonrep_map_F_thm = Goal.prove_sorry lthy
          (map (fst o dest_Free) (var_x :: var_u_Bs @ var_v_Fs @ (nth_drop lin_live_pos var_f'_As))) 
          (uv_props @ [nrp_x_prop]) nonrep_map_uv_prop
          (fn {context = ctxt, prems} => 
            let
              val switch_poses = map_range (fn i => if i < (lin_pos-(lin_live_pos)) then i+1 else i+2) (nr_bounds + nr_frees);
              val switch = (fn thm1 => (fn thm2 => trans OF [thm1, thm2 RS sym]));
              val o_id = @{thm o_id};
              val id_o = @{thm id_o};
            in
              unfold_thms_tac ctxt [nrp_def_thm, ss_def_thm] THEN
              HEADGOAL (EVERY' [
                rtac ctxt allI,
                rtac ctxt impI,
                etac ctxt exE,
                EqSubst.eqsubst_tac ctxt [0] [F_map_comp] THEN_ALL_NEW
                  TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
                K (unfold_thms_tac ctxt [switch id_o o_id]),
                EqSubst.eqsubst_tac ctxt [lin_pos+1] [switch o_id id_o], (*move all id to the right except for lin_pos*)
                EqSubst.eqsubst_tac ctxt [0] [F_map_comp RS sym] THEN_ALL_NEW
                  TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
                dtac ctxt (rotate_prems ~1 (nth F_mr_rel_maps 0 RS iffD1)) THEN_ALL_NEW
                  TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
                K (unfold_thms_tac ctxt [switch id_o o_id, @{thm Grp_UNIV_id}]),
                K (unfold_thms_tac ctxt [switch @{thm OO_eq} @{thm eq_OO}]),
                EqSubst.eqsubst_asm_tac ctxt [lin_live_pos+1] [switch @{thm eq_OO} @{thm OO_eq}], (*move all (=) to the left except for lin_live_pos*)
                K (unfold_thms_tac ctxt @{thms eq_alt}),   
                EqSubst.eqsubst_tac ctxt [0] @{thms Grp_UNIV_id}
              ]) THEN
              unfold_thms_tac ctxt [mr_rel_F_def, o_id, F_rel_compp, F_rel_Grp] THEN
              unfold_thms_tac ctxt [eqTrueI OF @{thms subset_UNIV}, @{thm simp_thms(21)}, id_o, @{thm UNIV_def} RS sym] THEN
              unfold_thms_tac ctxt ([eqTrueI OF [@{thm UNIV_I}], id_apply] @ @{thms Grp_UNIV_id OO_def Grp_def simp_thms(21)}) THEN
              HEADGOAL (EVERY' [
                etac ctxt exE,
                etac ctxt conjE,
                dtac ctxt (rotate_prems ~1 (F_in_rel RS iffD1)) THEN_ALL_NEW
                  TRY o resolve_tac ctxt prems,
                Method.insert_tac ctxt [unfold_thms ctxt [nrp_def_thm, ss_def_thm, mr_rel_F_def, F_map_id] 
                  (nth prems (length prems -1))],
                etac ctxt exE,
                etac ctxt conjE,
                etac ctxt CollectE,
                etac ctxt conjE
              ]) THEN
              REPEAT_DETERM_N (nr_lives-1) (HEADGOAL (
                etac ctxt conjE)) THEN
              HEADGOAL (hyp_subst_tac_thin true ctxt) THEN
              HEADGOAL (Subgoal.FOCUS 
                (fn {prems = subprems, context = ctxt, params, ...} => 
                  HEADGOAL (EVERY' [
                    Method.insert_tac ctxt [nth subprems 0],
                    etac ctxt allE,
                    etac ctxt impE,
                    rtac ctxt (infer_instantiate' ctxt [NONE, SOME (snd (nth params 1))] exI),
                    EqSubst.eqsubst_tac ctxt [1] [nth F_rel_maps 0],
                    EqSubst.eqsubst_tac ctxt [1] [nth F_rel_maps 1]
                  ]) THEN
                  HEADGOAL (rtac ctxt F_rel_refl_strong) THEN
                  REPEAT_DETERM_N nr_lives (HEADGOAL (
                      (dresolve_tac ctxt (map (fn p => subsetD OF [p] RS @{thm Collect_case_prodD}) (drop 1 subprems)) THEN'
                        (assume_tac ctxt ORELSE' 
                        (rtac ctxt sym THEN' assume_tac ctxt))))) THEN
                  HEADGOAL (EVERY' [
                    etac ctxt exE,
                    EqSubst.eqsubst_tac ctxt [0] [F_map_comp] THEN_ALL_NEW
                      TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
                    EqSubst.eqsubst_tac ctxt switch_poses [switch id_o o_id],
                    EqSubst.eqsubst_tac ctxt [0] [F_map_comp RS sym] THEN_ALL_NEW
                      TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
                    rtac ctxt exI,
                    dtac ctxt arg_cong,
                    assume_tac ctxt
                  ]) 
                ) ctxt)
            end)
        
        (* nonrep_map_F_rev *)
        val map_u = MRBNF_Def.mk_map_comb_of_mrbnf Ds id_f'_As var_u_Bs (map HOLogic.id_const Fs) mrbnf
        val nonrep_map_u_prop = nrp_TFree' $ (map_u $ var_x) |> HOLogic.mk_Trueprop
        val nonrep_map_F_rev_thm = Goal.prove_sorry lthy 
          (map (fst o dest_Free) (var_x :: var_u_Bs @ (nth_drop lin_live_pos var_f'_As))) 
          ((flat u_props_raw) @ [nonrep_map_u_prop]) nrp_x_prop
          (fn {context = ctxt, prems} =>
            let
              val switch = (fn thm1 => (fn thm2 => trans OF [thm1, thm2 RS sym]));
            in
              unfold_thms_tac ctxt [nrp_def_thm, ss_def_thm] THEN
              HEADGOAL (EVERY' [
                rtac ctxt allI,
                rtac ctxt impI,
                etac ctxt exE,
                forward_tac ctxt [rotate_prems ~1 (nth F_mr_rel_maps 1)] THEN_ALL_NEW
                  TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
                rotate_tac 1,
                EqSubst.eqsubst_asm_tac ctxt (map_range (fn i => i+1) (nr_bounds + nr_frees)) [switch @{thm o_id} @{thm id_o}],
                EqSubst.eqsubst_asm_tac ctxt [lin_live_pos+1] @{thms Grp_UNIV_id},
                K (unfold_thms_tac ctxt [switch @{thm eq_OO} @{thm OO_eq}]),
                EqSubst.eqsubst_asm_tac ctxt [lin_live_pos+1] [switch @{thm OO_eq} @{thm eq_OO}], (*move all (=) to the right and then lin_live_pos back*)
                EqSubst.eqsubst_asm_tac ctxt [lin_live_pos+1] @{thms eq_alt},
                EqSubst.eqsubst_asm_tac ctxt [0] [nth F_mr_rel_maps 0 RS sym] THEN_ALL_NEW
                  TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
                Method.insert_tac ctxt [unfold_thms ctxt [nrp_def_thm, ss_def_thm] (nth prems (length prems - 1))],
                etac ctxt allE,
                etac ctxt impE,
                rtac ctxt exI,
                assume_tac ctxt,
                etac ctxt thin_rl,
                etac ctxt exE,
                EqSubst.eqsubst_asm_tac ctxt [0] [F_map_comp] THEN_ALL_NEW
                  TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
                K (unfold_thms_tac ctxt @{thms id_o o_id}),
                EqSubst.eqsubst_asm_tac ctxt [1] [F_rel_eq RS sym],
                EqSubst.eqsubst_asm_tac ctxt [1] [F_mr_rel_id],
                dtac ctxt (rotate_prems ~1 (iffD1 OF [nth F_mr_rel_maps 0])) THEN_ALL_NEW
                  TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
                K (unfold_thms_tac ctxt @{thms id_o OO_eq}),
                dtac ctxt (rotate_prems 1 mr_rel_F_exchange_thm),
                rtac ctxt (F_mr_rel_flip RS iffD1) THEN_ALL_NEW
                  TRY o resolve_tac ctxt @{thms supp_id_bound bij_id},
                K (unfold_thms_tac ctxt @{thms inv_id}),
                EqSubst.eqsubst_asm_tac ctxt [0] [nth F_mr_rel_maps 2] THEN_ALL_NEW
                  TRY o resolve_tac ctxt (prems @ @{thms supp_id_bound bij_id}),
                EqSubst.eqsubst_asm_tac ctxt (map_range (fn i => i+1) (2 * nr_lives)) @{thms Grp_def},
                EqSubst.eqsubst_asm_tac ctxt (map_range (fn i => i+1) (nr_bounds + nr_frees)) @{thms inv_o_simp1} THEN_ALL_NEW
                  TRY o resolve_tac ctxt (@{thm bij_id}::prems),
                K (unfold_thms_tac ctxt ((eqTrueI OF @{thms UNIV_I}):: @{thms id_apply simp_thms(21)})),
                EqSubst.eqsubst_asm_tac ctxt [lin_live_pos+1] @{thms eq_commute},
                K (unfold_thms_tac ctxt @{thms eq_OO conversep_def}),
                etac ctxt (rotate_prems (~1 - (length var_types)) F_mr_rel_mono_strong0) THEN_ALL_NEW
                  TRY o resolve_tac ctxt @{thms supp_id_bound bij_id}
              ]) THEN
              REPEAT_DETERM_N (length var_types) (
                (HEADGOAL (
                  (* for bound and free *)
                  rtac ctxt ballI THEN'
                  rtac ctxt refl)) 
                ORELSE 
                (HEADGOAL (
                  (* for lives*)
                  rtac ctxt ballI THEN'
                  rtac ctxt ballI THEN'
                  rtac ctxt impI THEN'
                  rotate_tac 2 THEN'
                  EqSubst.eqsubst_asm_tac ctxt [0] @{thms eq_commute} THEN'
                  assume_tac ctxt))
              ) THEN
              HEADGOAL (EVERY' [
                etac ctxt thin_rl,
                EqSubst.eqsubst_asm_tac ctxt [lin_live_pos+1] [@{thm Grp_UNIV_def} RS sym],
                rtac ctxt exI,
                EqSubst.eqsubst_asm_tac ctxt (map_range (fn i => i+1) (nr_lives -1)) @{thms eq_alt},
                EqSubst.eqsubst_asm_tac ctxt [0] [F_mr_rel_Grp] THEN_ALL_NEW
                  TRY o resolve_tac ctxt @{thms supp_id_bound bij_id}
              ]) THEN
              unfold_thms_tac ctxt ([eqTrueI OF @{thms subset_UNIV}, eqTrueI OF @{thms UNIV_I}, @{thm UNIV_def} RS sym] @ 
                @{thms simp_thms(21) Grp_def}) THEN
              HEADGOAL (assume_tac ctxt)
            end)

        (* nonrep_map_F_bij *)
        val bij_f_prop = MRBNF_Util.mk_bij f |> HOLogic.mk_Trueprop;
        val f_id_As = nth_map lin_live_pos (fn _ => f) (map HOLogic.id_const As);
        val map_f = MRBNF_Def.mk_map_comb_of_mrbnf Ds f_id_As (map HOLogic.id_const Bs) (map HOLogic.id_const Fs) mrbnf;
        val nonrep_map_f_prop = nrp_TFree $ (map_f $ var_x) |> HOLogic.mk_Trueprop;
        val nonrep_map_F_bij_thm = Goal.prove_sorry lthy 
          (map (fst o dest_Free) ([var_x, f])) [bij_f_prop, nrp_x_prop] nonrep_map_f_prop
          (fn {context = ctxt, prems} =>
            let
              val id_prems_v = MRBNF_Comp_Tactics.mk_prems mrbnf @{thms bij_id supp_id_bound} @{thms bij_id supp_id_bound}
              val o_id_poses = map_range (fn i => if i < lin_pos then i*2 + 7 else (i+1)*2 + 7) (length var_types-1) |> filter (fn n => n >= 0);
            in
              unfold_thms_tac ctxt [nrp_def_thm, ss_def_thm] THEN
              HEADGOAL (EVERY' [
                rtac ctxt allI,
                rtac ctxt impI,
                etac ctxt exE,
                dtac ctxt (rotate_prems ~1 ((nth F_mr_rel_maps 0) RS iffD1)) THEN_ALL_NEW
                  TRY o resolve_tac ctxt @{thms bij_id supp_id_bound},
                K (unfold_thms_tac ctxt @{thms o_id Grp_UNIV_id}),
                (*when we linearize on the last non-dead variable, this substitution has to be one further*)
                EqSubst.eqsubst_asm_tac ctxt 
                  [if lin_pos + 1 < nr_ABFs then lin_live_pos*3 + 2 else lin_live_pos*3 + 3] [@{thm OO_eq} RS sym],
                EqSubst.eqsubst_asm_tac ctxt (map_range (fn i => i+1) (nr_lives*2 -1)) [@{thm conversep_eq} RS sym],
                EqSubst.eqsubst_asm_tac ctxt (map_range (fn i => i+1) (nr_lives*2 -1)) @{thms eq_alt},
                EqSubst.eqsubst_asm_tac ctxt [1] [@{thm inv_o_simp2} OF [(nth prems 0)] RS sym],
                K (unfold_thms_tac ctxt @{thms Grp_o converse_relcompp}),
                EqSubst.eqsubst_asm_tac ctxt [1] [@{thm relcompp_assoc} RS sym],
                dtac ctxt ((unfold_thms ctxt @{thms inv_id o_id} ((nth F_mr_rel_maps 2) OF 
                  (id_prems @ id_prems_v) RS sym)) RS iffD1),
                K (unfold_thms_tac ctxt @{thms Grp_UNIV_id conversep_eq}),
                dtac ctxt (Object_Logic.rulify ctxt (unfold_thms ctxt [nrp_def_thm, ss_def_thm] (nth prems 1)) OF [exI]),
                etac ctxt exE
              ]) THEN
              HEADGOAL (Subgoal.FOCUS 
                (fn {prems = subprems, context = ctxt, ...} => 
                  HEADGOAL (EVERY' [
                    EqSubst.eqsubst_tac ctxt [0] [F_map_id RS sym],
                    EqSubst.eqsubst_tac ctxt o_id_poses [@{thm o_id} RS sym],
                    EqSubst.eqsubst_tac ctxt [1] [@{thm inv_o_simp2} OF [(nth prems 0)] RS sym],
                    K (unfold_thms_tac ctxt [F_map_comp OF flat (replicate 2 id_prems) RS sym]),
                    EqSubst.eqsubst_tac ctxt [1] subprems,
                    EqSubst.eqsubst_tac ctxt [2*lin_pos + 8 + 2*(length var_types)] [@{thm o_id} RS sym],
                    EqSubst.eqsubst_tac ctxt [1] [@{thm inv_o_simp1} OF [(nth prems 0)] RS sym],
                    K (unfold_thms_tac ctxt [F_map_comp OF flat (replicate 2 id_prems)]),
                    EqSubst.eqsubst_tac ctxt [1, 2] @{thms o_assoc},
                    rtac ctxt exI,
                    rtac ctxt refl
                  ])
                ) ctxt)
            end)

        (* nonrep2_mapF_bij_2 *)
        val ff'_As = select_one var_f'_As var_f_As lin_live_pos;
        val map_fuv = MRBNF_Def.mk_map_comb_of_mrbnf Ds ff'_As var_u_Bs var_v_Fs mrbnf;
        val nonrep_map_fuv_prop = nrp_TFree' $ (map_fuv $ var_x) |> HOLogic.mk_Trueprop;
        val nonrep_map_F_bij_2_thm = Goal.prove_sorry lthy
          (map (fst o dest_Free) (ff'_As @ var_u_Bs @ var_v_Fs @[var_x])) (uv_props @ [bij_f_prop, nrp_x_prop]) nonrep_map_fuv_prop
          (fn {context = ctxt, prems} =>
            let val nr_prems = length prems; in
              HEADGOAL (rtac ctxt (unfold_thms ctxt ((F_map_comp OF ((take (nr_prems-2) prems) @ id_prems)) :: @{thms id_o o_id}) 
                (nonrep_map_F_bij_thm OF [nth prems (nr_prems-2), nonrep_map_F_thm OF (nth_drop (nr_prems-2) prems)])))
            end)

        (* rrel_F_map_F3 *)   
        val Grp_f = BNF_Util.mk_Grp (HOLogic.mk_UNIV (nth As lin_live_pos)) f;
        val Grp_Rs = nth_map lin_live_pos (fn _ => Grp_f) eq_Rs;
        val rrel_F_Grp = Term.list_comb (rrel_F, Grp_Rs @ [var_x, var_x'l]);
        val rrel_F_map = Term.list_comb (rrel_F, eq_Rs @ [map_f $ var_x, var_x'l]);
        val rrel_F_map_F_prop = HOLogic.mk_eq (rrel_F_Grp, rrel_F_map) |> HOLogic.mk_Trueprop
        val rrel_F_map_F_thm = Goal.prove_sorry lthy (map (fst o dest_Free) 
          ((nth_drop lin_live_pos eq_Rs) @ [f, var_x, var_x'l])) [] rrel_F_map_F_prop
          (fn {context = ctxt, prems = _} =>
            unfold_thms_tac ctxt ([nth F_rel_maps 0, eqTrueI OF @{thms UNIV_I}] @ @{thms Grp_def id_apply simp_thms(21)}) THEN
            HEADGOAL (rtac ctxt @{thm iffI}) THEN
            ALLGOALS (etac ctxt F_rel_mono_strong THEN_ALL_NEW
               (assume_tac ctxt ORELSE' etac ctxt sym))
            )
        
        val _ = nonrep_map_F_bij_2_thm |> @{print} (* why is nonrep yellow? *)

        (* register MRBNF *)
        val tacs = {
          map_id0 = fn ctxt =>
            unfold_thms_tac ctxt ([map_F'_def_thm, 
              eqTrueI OF @{thms bij_id}, eqTrueI OF @{thms supp_id_bound}] @ 
              @{thms asSS_def asBij_def if_True}) THEN
            HEADGOAL (rtac ctxt ext) THEN
            unfold_thms_tac ctxt [F_map_id, Rep_F'_inverse, @{thm o_apply}] THEN
            unfold_thms_tac ctxt @{thms id_def} THEN
            HEADGOAL (rtac ctxt refl),
          map_comp0 = fn ctxt =>
            HEADGOAL (Subgoal.FOCUS (fn {prems = prems, context = ctxt, ...} =>
              unfold_thms_tac ctxt (map_F'_def_thm:: @{thms asSS_def asBij_def}) THEN
              HEADGOAL(EqSubst.eqsubst_tac ctxt (map_range (fn i => i+1) (1 + 2*nr_bounds)) @{thms bij_comp} THEN_ALL_NEW
                TRY o resolve_tac ctxt prems) THEN
              unfold_thms_tac ctxt @{thms if_True} THEN
              HEADGOAL (EqSubst.eqsubst_tac ctxt (map_range (fn i => i+1) (nr_bounds + nr_frees)) @{thms supp_comp_bound} THEN_ALL_NEW
                TRY o resolve_tac ctxt (@{thm infinite_UNIV} ::prems)) THEN
              unfold_thms_tac ctxt (@{thm if_True} :: map (fn thm => thm RS eqTrueI) prems) THEN
              HEADGOAL (rtac ctxt ext) THEN
              HEADGOAL (EqSubst.eqsubst_tac ctxt [1] [F_map_comp0] THEN_ALL_NEW
                TRY o resolve_tac ctxt prems) THEN
              unfold_thms_tac ctxt [o_apply] THEN
              HEADGOAL (EVERY' [EqSubst.eqsubst_tac ctxt [0] [mk_Abs_F'_inverse ctxt],
                rtac ctxt nonrep_map_F_bij_2_thm THEN_ALL_NEW resolve_tac ctxt (mk_Rep_F' ctxt :: prems),
                rtac ctxt refl])
              ) ctxt),
          map_cong0 = fn ctxt =>
            HEADGOAL (Subgoal.FOCUS (fn {prems, context = ctxt, ...} =>
              unfold_thms_tac ctxt ([map_F'_def_thm] @ map (fn thm => thm RS eqTrueI) prems @
                @{thms asSS_def asBij_def if_True o_apply}) THEN
              HEADGOAL (EqSubst.eqsubst_tac ctxt [0] [F_map_cong] THEN_ALL_NEW
                TRY o resolve_tac ctxt (rev prems)) THEN
              HEADGOAL (rtac ctxt refl) THEN
              unfold_thms_tac ctxt (@{thm o_apply} :: set_def_thms) THEN
              REPEAT_DETERM_N (length set_def_thms) (
                HEADGOAL (assume_tac ctxt)) THEN
              HEADGOAL (rtac ctxt refl)
            ) ctxt),
          set_map0 = map (fn (set_F'_def, set_map_thm) => fn ctxt =>
            HEADGOAL (rtac ctxt ext) THEN
            unfold_thms_tac ctxt [o_apply] THEN
            HEADGOAL (Subgoal.FOCUS (fn {prems, context = ctxt, ...} =>
              unfold_thms_tac ctxt ([set_F'_def, map_F'_def_thm] @ map (fn thm => thm RS eqTrueI) prems @
                @{thms asSS_def asBij_def if_True o_apply}) THEN
              HEADGOAL (EVERY' [EqSubst.eqsubst_tac ctxt [0] [mk_Abs_F'_inverse ctxt],
                rtac ctxt nonrep_map_F_bij_2_thm THEN_ALL_NEW resolve_tac ctxt (mk_Rep_F' ctxt :: prems),
                rtac ctxt set_map_thm THEN_ALL_NEW
                  resolve_tac ctxt prems])
            ) ctxt))
            (set_def_thms ~~ (MRBNF_Def.set_map_of_mrbnf mrbnf)),
          infinite_regular_card_order = fn ctxt =>
            HEADGOAL (rtac ctxt (MRBNF_Def.bd_infinite_regular_card_order_of_mrbnf mrbnf)),
          set_bd = map (fn (set_F'_def, set_bd_thm) => fn ctxt =>
              unfold_thms_tac ctxt [set_F'_def, o_apply] THEN
              HEADGOAL (rtac ctxt set_bd_thm))
            (set_def_thms ~~ (MRBNF_Def.set_bd_of_mrbnf mrbnf)),
          le_rel_OO = fn ctxt => 
            (* when we linearize on the last live, offset has to be greater by 1 *)
            let val offset = if length As = lin_live_pos+1 then 2+(3*lin_live_pos) else 1+(3*lin_live_pos) in
              HEADGOAL (Subgoal.FOCUS (fn {context = ctxt, ...} => 
                HEADGOAL (EVERY' [
                  rtac ctxt @{thm predicate2I},
                  etac ctxt @{thm relcomppE},
                  K (unfold_thms_tac ctxt [rrel_F'_def_thm]),
                  EqSubst.eqsubst_tac ctxt [offset] @{thms eq_OO[symmetric]},
                  EqSubst.eqsubst_tac ctxt [1] [F_rel_compp],
                  K (unfold_thms_tac ctxt [rrel_F'_def_thm]),
                  rtac ctxt @{thm relcomppI} THEN_ALL_NEW assume_tac ctxt
                ])
              ) ctxt) end,
          in_rel = fn ctxt => HEADGOAL (Subgoal.FOCUS (fn {prems, context = ctxt, params, ...} =>
            unfold_thms_tac ctxt @{thms Grp_def conversep_def relcompp_apply mem_Collect_eq} THEN
            unfold_thms_tac ctxt ([rrel_F'_def_thm, map_F'_def_thm, o_apply] @ set_def_thms @ @{thms asSS_def asBij_def if_True} @ 
              map (fn thm => thm RS eqTrueI) (prems @ @{thms supp_id_bound bij_id})) THEN
            HEADGOAL (EVERY' [
              EqSubst.eqsubst_tac ctxt [0] [mk_Abs_F'_inverse ctxt],
              rtac ctxt nonrep_map_F_bij_2_thm THEN_ALL_NEW resolve_tac ctxt (mk_Rep_F' ctxt :: prems),
              EqSubst.eqsubst_tac ctxt (map_range (fn i => 7+2*(i+nr_lives)) (length var_types)) [@{thm id_o} RS sym],
              EqSubst.eqsubst_tac ctxt [lin_pos+1] [trans OF [@{thm id_o}, @{thm o_id} RS sym]],
              EqSubst.eqsubst_tac ctxt [1] [F_map_comp RS sym] THEN_ALL_NEW
                TRY o resolve_tac ctxt (prems @ @{thms bij_id supp_id_bound}),
              EqSubst.eqsubst_tac ctxt [1] [rrel_F_map_F_thm RS sym],
              EqSubst.eqsubst_tac ctxt [1] [F_in_rel] THEN_ALL_NEW
                TRY o resolve_tac ctxt prems
            ]) THEN
            unfold_thms_tac ctxt ((eqTrueI OF @{thms UNIV_I}):: @{thms Grp_def simp_thms(21)}) THEN
            HEADGOAL (rtac ctxt iffI) THEN
            (* 1st Subgoal *)
            REPEAT_DETERM_N (3+nr_lives) (HEADGOAL (eresolve_tac ctxt [exE, conjE, CollectE])) THEN
            HEADGOAL (Subgoal.FOCUS
              (fn {prems = subprems, context = ctxt, ...} =>
                  (* setup *)
                  HEADGOAL (EVERY' [
                    rtac ctxt exI,
                    EqSubst.eqsubst_tac ctxt (map_range (fn i => i+1) (2*nr_lives)) [mk_Abs_F'_inverse ctxt],
                    Method.insert_tac ctxt [unfold_thms ctxt [nth subprems 0 RS sym] 
                      (infer_instantiate' ctxt [SOME (nth params nr_ABFs |> snd)] (mk_Rep_F' ctxt))],
                    EqSubst.eqsubst_asm_tac ctxt (map_range (fn i => 4+2*i) (length var_types)) [@{thm o_id} RS sym],
                    EqSubst.eqsubst_asm_tac ctxt [lin_pos+1] [trans OF [@{thm o_id}, @{thm id_o} RS sym]],
                    EqSubst.eqsubst_asm_tac ctxt [0] [F_map_comp RS sym] THEN_ALL_NEW
                      TRY o resolve_tac ctxt @{thms bij_id supp_id_bound},
                    dtac ctxt (rotate_prems ~1 nonrep_map_F_rev_thm) THEN_ALL_NEW
                      TRY o resolve_tac ctxt @{thms bij_id supp_id_bound},
                    assume_tac ctxt
                  ]) THEN
                  (* solve *)
                  HEADGOAL (EqSubst.eqsubst_tac ctxt [1, 2] [F_map_comp] THEN_ALL_NEW
                      TRY o resolve_tac ctxt (prems @ @{thms bij_id supp_id_bound})) THEN
                  unfold_thms_tac ctxt @{thms id_o o_id} THEN
                  HEADGOAL (EVERY' [
                    EqSubst.eqsubst_tac ctxt [1, 3] [Rep_F'_inverse RS sym],
                    rtac ctxt conjI,
                    (COND (fn _ => nr_lives=1) all_tac) o rtac ctxt conjI, (*skip this if we linearize on the only live*)
                    EqSubst.eqsubst_tac ctxt [0] [nth subprems 0],
                    rtac ctxt refl
                  ]) THEN
                  REPEAT_DETERM_N (nr_lives-1) (HEADGOAL (EVERY' [
                    TRY o rtac ctxt conjI,
                    EqSubst.eqsubst_tac ctxt [0] F_set_maps THEN_ALL_NEW 
                      TRY o resolve_tac ctxt @{thms bij_id supp_id_bound},
                    EqSubst.eqsubst_tac ctxt [0] @{thms image_id},
                    resolve_tac ctxt subprems
                  ])) THEN
                  HEADGOAL (EVERY' [
                    (COND (fn _ => nr_lives=1) all_tac) o rtac ctxt conjI, (*skip this if we linearize on the only live*)
                    EqSubst.eqsubst_tac ctxt [0] [nth subprems 1 RS sym],
                    rtac ctxt (F_map_cong RS arg_cong) THEN_ALL_NEW
                      TRY o resolve_tac ctxt (refl::prems),
                    dtac ctxt (@{thm rev_subsetD} RS @{thm Collect_case_prodD}),
                    resolve_tac ctxt subprems,
                    EqSubst.eqsubst_tac ctxt [0] [o_apply],
                    assume_tac ctxt
                  ]) THEN
                  REPEAT_DETERM_N (nr_lives-1) (HEADGOAL (EVERY' [
                    TRY o rtac ctxt conjI,
                    EqSubst.eqsubst_tac ctxt [0] F_set_maps THEN_ALL_NEW 
                      TRY o resolve_tac ctxt @{thms bij_id supp_id_bound},
                    EqSubst.eqsubst_tac ctxt [0] @{thms image_id},
                    resolve_tac ctxt subprems
                  ]))
                ) 
              ctxt) THEN
            (* 2nd Subgoal *)
            HEADGOAL (etac ctxt exE) THEN
            REPEAT_DETERM_N (Int.max(1, 2*nr_lives-1)) (HEADGOAL (etac ctxt conjE)) THEN
            HEADGOAL (Subgoal.FOCUS
              (fn {prems = subprems, context = ctxt, ...} =>
                unfold_thms_tac ctxt subprems THEN
                HEADGOAL (EVERY' [
                  rtac ctxt exI,
                  EqSubst.eqsubst_tac ctxt [0] [mk_Abs_F'_inverse ctxt],
                  rtac ctxt nonrep_map_F_bij_2_thm THEN_ALL_NEW
                    TRY o resolve_tac ctxt (mk_Rep_F' ctxt :: @{thms supp_id_bound bij_id}),
                  rtac ctxt conjI THEN_ALL_NEW TRY o rtac ctxt conjI 
                ]) THEN
                prefer_tac 3 THEN
                HEADGOAL (EVERY' [
                  EqSubst.eqsubst_tac ctxt [0] [mk_Abs_F'_inverse ctxt],
                  rtac ctxt nonrep_map_F_bij_2_thm THEN_ALL_NEW    
                    TRY o resolve_tac ctxt (mk_Rep_F' ctxt :: prems),
                  EqSubst.eqsubst_tac ctxt [0] [F_map_comp] THEN_ALL_NEW
                    TRY o resolve_tac ctxt (@{thms bij_id supp_id_bound} @ prems),
                  K (unfold_thms_tac ctxt @{thms o_id}),
                  K (unfold_thms_tac ctxt @{thms o_def}),
                  rtac ctxt F_map_cong THEN_ALL_NEW
                    TRY o resolve_tac ctxt (refl::prems),
                  rtac ctxt @{thm snd_conv},
                  rtac ctxt CollectI
                ]) THEN
                REPEAT_DETERM_N (nr_lives) (
                  HEADGOAL (EqSubst.eqsubst_tac ctxt [0] F_set_maps THEN_ALL_NEW
                    TRY o resolve_tac ctxt @{thms bij_id supp_id_bound})) THEN
                unfold_thms_tac ctxt @{thms image_ident} THEN
                (*we have a chain of conjunctions, one goal for each live. 
                  All of them are solved by subprems, except for the lin_live goal *)
                REPEAT_DETERM_N (nr_lives) (
                  TRY (HEADGOAL (rtac ctxt conjI)) THEN 
                  (HEADGOAL (resolve_tac ctxt subprems) ORELSE 
                    (COND (fn _ => lin_live_pos = nr_lives-1) all_tac (prefer_tac 2)))
                ) THEN
                HEADGOAL (EVERY' [
                  rtac ctxt subsetI,
                  etac ctxt imageE,
                  rtac ctxt CollectI,
                  rtac ctxt @{thm case_prodI2},
                  dtac ctxt (trans OF [sym] RS (iffD1 OF @{thms prod.inject})),
                  assume_tac ctxt,
                  etac ctxt conjE,
                  rtac ctxt (trans OF [sym]),
                  assume_tac ctxt,
                  etac ctxt arg_cong,
                  EqSubst.eqsubst_tac ctxt [0] [F_map_comp] THEN_ALL_NEW
                    TRY o resolve_tac ctxt @{thms supp_id_bound bij_id},
                  K (unfold_thms_tac ctxt @{thms o_def id_def fst_conv}),
                  rtac ctxt refl
                ])) 
              ctxt) 
            ) ctxt),
          pred_set = fn ctxt => HEADGOAL (rtac ctxt refl),
          wit = fn ctxt => print_tac ctxt "wit"
        }
        val var_types_Abs = nth_map lin_pos (fn _ => MRBNF_Def.Bound_Var) var_types;

        val (mrbnf', lthy) = MRBNF_Def.mrbnf_def MRBNF_Def.Do_Inline (MRBNF_Def.user_policy MRBNF_Def.Note_Some) 
          false I tacs (SOME Ds) NONE map_F'_binding rrel_F'_binding pred_b set_bs_non_dead 
          (((((((b, typ_y), map_F'_term), (var_types_Abs ~~ set_terms)),
            MRBNF_Def.mk_bd_of_mrbnf Ds Bs Fs mrbnf),
            []),
            SOME rrel_F'_term),
            NONE)
          lthy
        val _ = @{print} mrbnf'

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
