signature MRBNF_LINEARIZE =
sig
  datatype linearize_mrbnf_option =
    Plugins_Option of Proof.context -> Plugin_Name.filter
  | No_Warn_Wits
  | No_Warn_Transfer
  val linearize_mrbnf:
    (((((linearize_mrbnf_option list * (binding option * (string * sort option)) list) *
      binding) * typ) * term list option) * string list) * (binding * binding * binding * binding * binding) ->
      ({context: Proof.context, prems: thm list} -> tactic) list ->
      local_theory -> local_theory
  val linearize_mrbnf_cmd:
     (((((linearize_mrbnf_option list * (binding option * (string * string option)) list) *
       binding) * string) * string list) * string list) *
       (binding * binding * binding * binding * binding) -> local_theory -> Proof.state
end

structure MRBNF_Linearize : MRBNF_LINEARIZE =
struct

open Ctr_Sugar_Tactics
open BNF_Util
open BNF_Comp
open BNF_Def
open MRBNF_Linearize_Tactics

datatype linearize_mrbnf_option =
  Plugins_Option of Proof.context -> Plugin_Name.filter
| No_Warn_Wits
| No_Warn_Transfer;

(** Util **)
val mk_Free = yield_singleton o mk_Frees;

fun select_n xs xs' poses = map_index (fn (i, (x, x')) => if member (op =) poses i then x' else x) (xs ~~ xs');
fun nths_drop is xs = fold_rev (fn i => (fn xs => nth_drop i xs)) is xs;

(* TODO replace with the version from tactics*)
val dest_Type_atomic = MRBNF_Linearize_Tactics.dest_Type_atomic;

(** Term construction **)
fun top_rel T = Const ("Orderings.top_class.top", [T, T] ---> HOLogic.boolT);

fun mk_asBij f = let val typ_f = fastype_of f; in
  Const (@{const_name asBij}, typ_f --> typ_f) $ f end;

fun mk_asSS f = let val typ_f = fastype_of f; in 
  Const (@{const_name asSS}, typ_f --> typ_f) $ f end;

(** linearize **)
fun linearize b repT on_tvars wits specs map_b rel_b pred_b ss_b nrp_b opts lthy =
  let
    val tfrees = map (TFree o snd) specs |> @{print};

    fun flatten_tyargs Ass =
      (map dest_TFree tfrees
      |> filter (fn T => exists (fn Ts => member op= Ts T) Ass));
    
    val ((mrbnf,(Ds, ABFs)), (_,lthy)) = MRBNF_Comp.mrbnf_of_typ true MRBNF_Def.Smart_Inline
      (Binding.prefix_name (Binding.name_of b ^ "_")) flatten_tyargs [] [] [] repT
      ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy);

    val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf |> @{print};
    val (As, Bs, Fs) = fold_rev (fn (T, vt) => (fn (acc_As, acc_Bs, acc_Fs) => 
      case vt of
        MRBNF_Def.Live_Var => (T::acc_As, acc_Bs, acc_Fs)
      | MRBNF_Def.Bound_Var => (acc_As, T::acc_Bs, acc_Fs)
      | MRBNF_Def.Free_Var => (acc_As, acc_Bs, T::acc_Fs)
      | _ => error "Dead_Var!" ))
      (ABFs ~~ var_types) ([], [], []) |> @{print};

    val deads = MRBNF_Def.deads_of_mrbnf mrbnf;
    val lives = MRBNF_Def.lives_of_mrbnf mrbnf;
    val bounds = MRBNF_Def.bounds_of_mrbnf mrbnf;
    val frees = MRBNF_Def.frees_of_mrbnf mrbnf;

    val mrbnf_subst = ((Ds @ As @ Bs @ Fs) ~~ (deads @ lives @ bounds @ frees)) |> @{print}

    val nr_As = MRBNF_Def.live_of_mrbnf mrbnf;
    val nr_Fs = MRBNF_Def.free_of_mrbnf mrbnf;
    val nr_Bs = MRBNF_Def.bound_of_mrbnf mrbnf;
    val nr_ABFs = nr_As + nr_Fs + nr_Bs;
    val class = MRBNF_Def.class_of_mrbnf mrbnf;

    val names_lthy = fold Variable.declare_typ (Ds @ ABFs) lthy;
    val (As', names_lthy) = mk_TFrees nr_As names_lthy;
    val (As'', names_lthy) = mk_TFrees nr_As names_lthy;

    val on_tfrees = map (fn tv => TFree (tv, class)) on_tvars |> distinct (op =) |> @{print tracing};

    val l_ABFs = subtract (op =) Ds tfrees;
    val l_Ds = subtract (op =) ABFs tfrees;
    val l_As = subtract (op =) (Bs @ Fs @ on_tfrees) l_ABFs |> @{print};
    val l_Bs = subtract (op =) (l_As @ Fs) l_ABFs |> @{print};
    val l_Fs = subtract (op =) (As @ Bs) l_ABFs |> @{print};

    val nr_lin = length on_tfrees;
    val l_nr_As = nr_As - nr_lin;
    val l_nr_Bs = nr_Bs + nr_lin;
    val lin_poses = map (fn tv => find_index (fn x => x = tv) ABFs) on_tfrees |> (sort int_ord) |> @{print tracing};
    val lin_live_poses = map (fn tv => find_index (fn x => x = tv) As) on_tfrees |> (sort int_ord) |> @{print tracing};
    val l_lin_poses = map (fn tv => find_index (fn x => x = tv) l_ABFs) on_tfrees |> (sort int_ord) |> @{print tracing};
    val l_lin_bound_poses = map (fn tv => find_index (fn x => x = tv) l_Bs) on_tfrees |> (sort int_ord) |> @{print tracing};

    val l_var_types = map (fn l_T => find_first (fn (T, _) => T = l_T) (ABFs ~~ var_types) |> the) l_ABFs |> map snd;
    val l_var_types = select_n l_var_types (replicate nr_ABFs MRBNF_Def.Bound_Var) l_lin_poses;

    val specs_non_dead = subtract (fn (d, (_, x)) => d = TFree x) Ds specs |> @{print}
    val set_bs_non_dead = map_index (fn (i, (b_opt, _)) => if Option.getOpt (b_opt, Binding.empty) |> Binding.is_empty |> not then
              the b_opt else
              Binding.prefix_name ("set" ^ (Int.toString (i+1)) ^ "_") b) specs_non_dead;


    (* make Frees*)
    val As_pair = map (fn (A, A') => HOLogic.mk_prodT (A, A')) (As ~~ As');

    val typ_x = MRBNF_Def.mk_T_of_mrbnf Ds As Bs Fs mrbnf;
    val typ_x'l = MRBNF_Def.mk_T_of_mrbnf Ds (select_n As' As lin_live_poses) Bs Fs mrbnf; (* other lives change typ *)
    val typ_x' = MRBNF_Def.mk_T_of_mrbnf Ds As' Bs Fs mrbnf;
    val typ_z = MRBNF_Def.mk_T_of_mrbnf Ds As_pair Bs Fs mrbnf; (* z: F with (A, A') as lives *)
    val typ_f_As = map (fn A => A --> A) As;
    val typ_f'_As = map (fn (A, A') => A --> A') (As ~~ As');
    val typ_u_Bs = map (fn B => B --> B) Bs;
    val typ_v_Fs = map (fn F => F --> F) Fs;
    val typ_R'_As = map (fn (A, A') => [A, A'] ---> HOLogic.boolT) (As ~~ As');
    
    val (var_as, names_lthy) = mk_Frees "a" As names_lthy;    
    val (var_as2, names_lthy) = mk_Frees "a" As names_lthy;
    val (var_as', names_lthy) = mk_Frees "a'" As' names_lthy;
    val (var_x, names_lthy) = mk_Free "x" typ_x names_lthy;
    val (var_x2, names_lthy) = mk_Free "x" typ_x names_lthy;
    val (var_x'l, names_lthy) = mk_Free "x'l" typ_x'l names_lthy;
    val (var_x', names_lthy) = mk_Free "x'" typ_x' names_lthy;
    val (var_z, names_lthy) = mk_Free "z" typ_z names_lthy;
    val (var_f_As, names_lthy) = mk_Frees "f" typ_f_As names_lthy;
    val (var_f'_As, names_lthy) = mk_Frees "f'" typ_f'_As names_lthy;
    val (var_u_Bs, names_lthy) = mk_Frees "u" typ_u_Bs names_lthy;
    val (var_v_Fs, names_lthy) = mk_Frees "v" typ_v_Fs names_lthy;
    val (var_R'_As, names_lthy) = mk_Frees "R'" typ_R'_As names_lthy;
    val (var_R'_As2, names_lthy) = mk_Frees "R'" typ_R'_As names_lthy;
   
    (* wits *)
    val nwits = MRBNF_Def.nwits_of_mrbnf mrbnf;
    val Iwits_F_thms = (MRBNF_Def.mk_wits_of_mrbnf (replicate nwits Ds) (replicate nwits As) 
      (replicate nwits Bs) (replicate nwits Fs) mrbnf ~~ MRBNF_Def.wit_thmss_of_mrbnf mrbnf) |> 
      filter (fn ((I, _),_) => null (inter (op =) I lin_live_poses)); (* keep only those that don't intersect with lin_live_poses *)

    fun binder_types_until_eq V T =
      let
        fun strip (TU as Type ("fun", [T, U])) = if V = TU then [] else T :: strip U
          | strip T = if V = T then [] else error ("Bad type for witness: " ^ quote (Syntax.string_of_typ lthy T));
      in strip T end;

    val Iwits_new = the_default [] (Option.map (map (`(map (fn T =>
      find_index (fn U => T = U) ABFs) o binder_types_until_eq repT o fastype_of))) wits);
    
    (* filter and warn user for new wits subsumed by F wits *)
    val subsumed_Iwits_new =
      filter (fn (J, _) => exists (fn ((I, _),_) => subset (op =) (I, J)) Iwits_F_thms) Iwits_new;
    val _ =  if null subsumed_Iwits_new orelse exists (fn No_Warn_Wits => true | _ => false) opts
      then ()
      else
        let
          val (suffix1, suffix2, be, this) =
            (if length subsumed_Iwits_new = 1 then ("", "", "is", "this") else ("s", "es", "are", "these"))
        in
          subsumed_Iwits_new
          |> map (Syntax.pretty_typ lthy o fastype_of o snd)
          |> Pretty.big_list
            ("The following type" ^ suffix1 ^ " of nonemptiness witness" ^ suffix2 ^
              be ^ " subsumed by the existing witnesses of the MRBNF:")
          |> (fn pt => Pretty.chunks [pt,
            Pretty.para ("You do not need to lift " ^ this ^ " subsumed witness" ^ suffix2 ^ ".")])
          |> Pretty.string_of
          |> warning
        end;
    val Iwits_new = filter_out (fn (J, _) => exists (fn ((I, _),_) => subset (op =) (I, J)) Iwits_F_thms) Iwits_new

    (* filter and warn user for new wits subsumed by other new wits *)
    val subsumed_Iwits_F =
      filter (fn ((J, _)) => exists (fn (I, _) => (subset (op =) (I, J)) 
      andalso (not (subset (op =) (J, I)))) Iwits_new) Iwits_new;
    val _ =  if null subsumed_Iwits_F orelse exists (fn No_Warn_Wits => true | _ => false) opts
      then ()
      else
        let
          val (suffix1, suffix2, be, this) =
            (if length subsumed_Iwits_F = 1 then ("", "", "is", "this") else ("s", "es", "are", "these"))
        in
          subsumed_Iwits_F
          |> map (Syntax.pretty_typ lthy o fastype_of o snd)
          |> Pretty.big_list
            ("The following type" ^ suffix1 ^ " of specified nonemptiness witness" ^ suffix2 ^
              be ^ " subsumed by other specified witnesses:")
          |> (fn pt => Pretty.chunks [pt,
            Pretty.para ("You do not need to lift " ^ this ^ " subsumed witness" ^ suffix2 ^ ".")])
          |> Pretty.string_of
          |> warning
        end;
    val Iwits_new = filter_out (fn ((J, _)) => exists (fn (I, _) => (subset (op =) (I, J)) 
      andalso (not (subset (op =) (J, I)))) Iwits_new) Iwits_new;

    (* remove subsumed F witnesses and inform user about automatically lifted wits from F *)
    val (Iwits_F, wits_F_thmss) = filter_out (fn ((J, _), _) => exists (fn (I, _) => (subset (op =) (I, J)) 
      andalso (not (subset (op =) (J, I)))) Iwits_new) Iwits_F_thms |> split_list;

    val _ =  if null Iwits_F then ()
      else
        let
          val (suffix1, suffix2, be, this) =
            (if length Iwits_F = 1 then ("", "", "is", "this") else ("s", "es", "are", "these"))
        in
          Iwits_F
          |> map (Syntax.pretty_typ lthy o fastype_of o snd)
          |> Pretty.big_list
            ("The following type" ^ suffix1 ^ " of existing nonemptiness witness" ^ suffix2 ^
              " of the MRBNF " ^ be ^ " independent of the linearized variables and " ^ be ^ " automatically lifted.")
          |> (fn pt => Pretty.chunks [pt,
            Pretty.para ("The existance of a nonrepetitive element is proven with " ^ this ^ " existing witness" ^ suffix2 ^ ".")])
          |> Pretty.string_of
          |> Output.information
        end;

    val set_Fs = MRBNF_Def.mk_sets_of_mrbnf (replicate nr_ABFs Ds) (replicate nr_ABFs As) 
      (replicate nr_ABFs Bs) (replicate nr_ABFs Fs) mrbnf;
    val set_Fs_A = map_filter (fn (vt, set) => if vt = MRBNF_Def.Live_Var then SOME set else NONE) (var_types ~~ set_Fs);

    val ((var_as_nl, var_as2_nl), set_Fs_A_nl) = nths_drop lin_live_poses ((var_as ~~ var_as2) ~~ set_Fs_A) |> split_list |>> split_list;

    val wit_goals = maps (mk_wit_goals var_as_nl var_as2_nl set_Fs_A_nl) Iwits_new; 

    (* ex_nonrep *)
    val map_F = MRBNF_Def.mk_map_of_mrbnf Ds As As Bs Fs mrbnf;
    val live_funs = select_n (map HOLogic.id_const As) var_f_As lin_live_poses;
    val map_funs = MRBNF_Def.interlace live_funs (map HOLogic.id_const Bs) (map HOLogic.id_const Fs) var_types;
    val map_f_x = Term.list_comb (map_F, map_funs @ [var_x]);
    val fs = map (nth var_f_As) lin_live_poses;
    val ex_fs = fold_rev (fn f => (fn ex_term => HOLogic.mk_exists (dest_Free f |> fst, dest_Free f |> snd, ex_term)))
      fs (HOLogic.mk_eq (var_x2, map_f_x));

    val rrel_F = MRBNF_Def.mk_rel_of_mrbnf Ds As As Bs Fs mrbnf;
    val top_eqs = map_index (fn (i, A) => if member (op =) lin_live_poses i then top_rel A else HOLogic.eq_const A) As;
    val rrel_top_x_x' = Term.list_comb (rrel_F, top_eqs @ [var_x, var_x2]);
    val rrel_top_imp_ex_f = HOLogic.mk_imp (rrel_top_x_x', ex_fs);
    val ex_nonrep = HOLogic.mk_exists (dest_Free var_x |> fst, dest_Free var_x |> snd,
      HOLogic.mk_all (dest_Free var_x2 |> fst, dest_Free var_x2 |> snd, rrel_top_imp_ex_f));
    val Tp_ex_nonrep = HOLogic.mk_Trueprop ex_nonrep;

    (* nonrep_wits *)
    fun mk_nonrep_wit (I, wit_term) = 
      let
        fun mk_args [] args = args
          | mk_args (pos::I) args = (nth var_as pos)::(mk_args I args)

        val wit_args = mk_args I [];
        val wit_F = Term.list_comb (wit_term, wit_args);
        val rrel_top_wit_x = Term.list_comb (rrel_F, top_eqs @ [wit_F, var_x]);
        val map_f_wit = Term.list_comb (map_F, map_funs @ [wit_F]);
        val ex_fs = fold_rev (fn f => (fn ex_term => HOLogic.mk_exists (dest_Free f |> fst, dest_Free f |> snd, ex_term)))
          fs (HOLogic.mk_eq (var_x, map_f_wit));
        val nonrep_wit = HOLogic.mk_all (dest_Free var_x |> fst, typ_x, HOLogic.mk_imp (rrel_top_wit_x, ex_fs));
      in
        HOLogic.mk_Trueprop nonrep_wit |> fold_rev (fn arg => (fn term => Logic.all arg term)) wit_args
      end;

    val nonrep_wit_goals = map (mk_nonrep_wit) Iwits_new;

    (*F_rel_map_set_live_strong *)
    val map_fst_z = MRBNF_Def.mk_map_comb_of_mrbnf Ds (map BNF_Util.fst_const As_pair) 
      (map HOLogic.id_const Bs) (map HOLogic.id_const Fs) mrbnf $ var_z;
    val map_eq_x = HOLogic.mk_eq (map_fst_z, var_x);

    val map_snd_z = MRBNF_Def.mk_map_comb_of_mrbnf Ds (map BNF_Util.snd_const As_pair) 
      (map HOLogic.id_const Bs) (map HOLogic.id_const Fs) mrbnf $ var_z;
    val map_eq_x' = HOLogic.mk_eq (map_snd_z, var_x');
    val map_eq_conj = HOLogic.mk_conj (map_eq_x, map_eq_x');
    
    val set_Fs_P = MRBNF_Def.mk_sets_of_mrbnf (replicate nr_ABFs Ds) (replicate nr_ABFs As_pair) 
      (replicate nr_ABFs Bs) (replicate nr_ABFs Fs) mrbnf;
    val set_Fs_P_live = filter (fn (_, vtype) => vtype = MRBNF_Def.Live_Var) (set_Fs_P ~~ var_types) |> map fst;
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
      end)) (rev (set_Fs_P_live ~~ (var_R'_As ~~ (var_as ~~ var_as')))) map_eq_conj;

    val ex1_z = Const ("HOL.Ex1", (typ_z --> HOLogic.boolT) --> HOLogic.boolT) $ 
      absfree (dest_Free var_z) set_map_conj;

    val rrel_F_R = MRBNF_Def.mk_rel_of_mrbnf Ds 
      (map (fst o HOLogic.dest_prodT) As_pair) 
      (map (snd o HOLogic.dest_prodT) As_pair) Bs Fs mrbnf;
    val rrel_R_x_x' = Term.list_comb (rrel_F_R, var_R'_As @ [var_x, var_x']);
    val rrel_eq_ex1 = HOLogic.mk_eq (rrel_R_x_x', ex1_z);
    val all_x_x' = HOLogic.mk_Trueprop rrel_eq_ex1 |> Logic.all var_x' |> Logic.all var_x;
    val F_rel_map_set_live_strong = fold (fn R => (fn all => Logic.all R all)) var_R'_As all_x_x';

    val goals = 
      if null (Iwits_new @ Iwits_F) then
        [F_rel_map_set_live_strong, Tp_ex_nonrep] @ nonrep_wit_goals @ wit_goals
      else
        [F_rel_map_set_live_strong] @ nonrep_wit_goals @ wit_goals;

    fun after_qed thmss lthy = 
      let
        (* prepare thms *)
        val (F_rel_map_set_live_strong_thm, thmss) = chop 1 thmss |> apfst (the_single o the_single);
        val (ex_nonrep_opt, wit_new_thmss) = if null (Iwits_new @ Iwits_F) then chop 1 thmss |> apfst (SOME o the_single o the_single) else (NONE, thmss);
        val wits_new_thms = map the_single wit_new_thmss;
        val (raw_nonrep_thms, wit_new_thms) = chop (length Iwits_new) wits_new_thms;
        val wits_new_thmss = chop_groups l_nr_As wit_new_thms;

        (* F thms used in proofs *)
        val mr_rel_F_def = MRBNF_Def.rel_def_of_mrbnf mrbnf;
        val F_map_id = MRBNF_Def.map_id_of_mrbnf mrbnf;
        val F_in_rel = MRBNF_Def.in_rel_of_mrbnf mrbnf;
        val F_map_cong = MRBNF_Def.map_cong_of_mrbnf mrbnf;  
        val F_map_comp = MRBNF_Def.map_comp_of_mrbnf mrbnf;
        val F_map_comp0 = MRBNF_Def.map_comp0_of_mrbnf mrbnf;
        val F_set_maps = MRBNF_Def.set_map_of_mrbnf mrbnf;
        val F_set_bds = MRBNF_Def.set_bd_of_mrbnf mrbnf;
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

        (* sameShape *) (* why use mr_rel_F here, when we use rrel_F in ex_nonrep? *)
        val mr_rel_F = MRBNF_Def.mk_mr_rel_of_mrbnf Ds As As Bs Fs mrbnf;
        val mr_rel_args = MRBNF_Def.interlace top_eqs (map HOLogic.id_const Bs) (map HOLogic.id_const Fs) var_types;
        val mr_rel_F_top_x_x' = Term.list_comb (mr_rel_F, mr_rel_args @ [var_x, var_x2]);
        val ss_rhs = mr_rel_F_top_x_x' |> absfree (dest_Free var_x2) |>
          absfree (dest_Free var_x);
        val ss_binding = if Binding.is_empty ss_b then
          Binding.prefix_name "sameShape_" (MRBNF_Def.name_of_mrbnf mrbnf) else ss_b;
        val ((_, ss_term, ss_def_thm), lthy) = MRBNF_Util.new_definition ss_binding ss_rhs lthy;

        val x_atomics = dest_Type_atomic typ_x;
        val ss_arg_atomics = fastype_of ss_term |> domain_type |> dest_Type_atomic;
        val ss_TFree = subst_atomic_types (ss_arg_atomics ~~ x_atomics) ss_term;

        (* nonrep *)
        val forall_x' = HOLogic.mk_all (dest_Free var_x2 |> fst, dest_Free var_x2 |> snd,
          HOLogic.mk_imp (ss_TFree $ var_x $ var_x2, ex_fs));
        val nrp_rhs = absfree (dest_Free var_x) forall_x';
        val nrp_binding = if Binding.is_empty nrp_b then
          Binding.prefix_name "nonrep_" (MRBNF_Def.name_of_mrbnf mrbnf) else nrp_b;
        val ((_, nrp_term, nrp_def_thm), lthy) = MRBNF_Util.new_definition nrp_binding nrp_rhs lthy;

        val nrp_arg_atomics = fastype_of nrp_term |> domain_type |> dest_Type_atomic
        val nrp_TFree = subst_atomic_types (nrp_arg_atomics ~~ x_atomics) nrp_term

        (* nonrep_wits *)
        fun mk_nonrep_wit_prop_args (I, wit) =
          let
            fun mk_args [] args = args
              | mk_args (pos::I) args = (nth var_as pos)::(mk_args I args)
    
            val wit_args = mk_args I [];
            val wit_F = Term.list_comb (wit, wit_args);
          in
            (nrp_TFree $ wit_F |> HOLogic.mk_Trueprop, wit_args)
          end;

        val inst_ids = map (HOLogic.id_const o (nth As)) lin_live_poses;
        val inst_sets = map (nth set_Fs) lin_poses;

        fun prove_nonrep_wit_F ((prop, args), wit_thms) = 
          Goal.prove_sorry lthy (map (fst o dest_Free) args) [] prop
            (fn {context = ctxt, ...} => mk_nonrep_wit_F_tac ctxt nr_As lin_live_poses inst_ids inst_sets nrp_def_thm 
              ss_def_thm mr_rel_F_def F_map_id F_in_rel F_map_cong F_set_maps wit_thms);

        fun prove_nonrep_wit_new ((prop, args), raw_nonrep_thm) = 
          Goal.prove_sorry lthy (map (fst o dest_Free) args) [] prop
            (fn {context = ctxt, ...} => mk_nonrep_wit_new_tac ctxt nrp_def_thm ss_def_thm mr_rel_F_def F_map_id raw_nonrep_thm)

        val nonrep_wit_F_thms = map (prove_nonrep_wit_F o (apfst mk_nonrep_wit_prop_args)) (Iwits_F ~~ wits_F_thmss);
        val nonrep_wit_new_thms = map (prove_nonrep_wit_new o (apfst mk_nonrep_wit_prop_args)) (Iwits_new ~~ raw_nonrep_thms);

        val ex_nonrep_thm = if null (Iwits_new @ Iwits_F) then the ex_nonrep_opt else
          Goal.prove_sorry lthy [] [] Tp_ex_nonrep
            (fn {context = ctxt, ...} => 
              HEADGOAL (rtac ctxt exI) THEN
              HEADGOAL (resolve_tac ctxt (map (unfold_thms ctxt [nrp_def_thm, ss_def_thm, mr_rel_F_def, F_map_id]) 
                (nonrep_wit_F_thms @ nonrep_wit_new_thms))));

        (* typedef F'*)
        val nrp_x = nrp_TFree $ var_x
        val td_term = HOLogic.mk_Collect (dest_Free var_x |> fst, dest_Free var_x |> snd, nrp_x)

        fun mk_typedef_tac ctxt = 
          unfold_thms_tac ctxt [nrp_def_thm, ss_def_thm, @{thm mem_Collect_eq}, mr_rel_F_def, F_map_id] THEN
          HEADGOAL (rtac ctxt ex_nonrep_thm)

        val ((_, (td_info1, td_info2)), lthy) = typedef (b, map (snd) specs, 
          Mixfix.NoSyn) td_term NONE mk_typedef_tac lthy;


        (* mk F' Frees *)
        val typ_y = #abs_type td_info1;
        val typ_y' = typ_subst_atomic (nths_drop lin_live_poses (As ~~ As')) typ_y;
        val typ_y'' = typ_subst_atomic (nths_drop lin_live_poses (As ~~ As'')) typ_y;
        val (var_y, names_lthy) = mk_Free "y" typ_y names_lthy;
        val (var_y', names_lthy) = mk_Free "y'" typ_y' names_lthy;

        (* F' definitions *)
        (* set_F's *)
        val l_set_Fs = map (fn T => find_first (fn set => (fastype_of set |> body_type |> dest_Type_args |> the_single) = T) set_Fs |> the) l_ABFs;
        val (set_defs, lthy) = fold (fn (set, set_binding) => (fn (acc, lthy) =>
          let
            val Rep_const = Const (#Rep_name td_info1, (typ_y) --> (typ_x));
            val set_rhs = HOLogic.mk_comp (set, Rep_const);
            val ((_, set_term, set_def_thm), lthy) = MRBNF_Util.new_definition set_binding set_rhs lthy;
          in
            ((set_term, set_def_thm)::acc, lthy)
          end)) ((l_set_Fs ~~ set_bs_non_dead) |> rev) ([], lthy);
        val (set_F'_terms, set_F'_def_thms) = split_list set_defs

        (* map_F' *)
        val f_As = select_n var_f'_As (map mk_asBij var_f_As) lin_live_poses;

        val map_F = MRBNF_Def.mk_map_comb_of_mrbnf Ds f_As (map (mk_asSS o mk_asBij) var_u_Bs) (map mk_asSS var_v_Fs) mrbnf;
        val Rep_const = Const (#Rep_name td_info1, (typ_y) --> (typ_x));
        val Abs_const = Const (#Abs_name td_info1, (typ_x'l) --> (typ_y'));
        val abs_map_rep = HOLogic.mk_comp (Abs_const, HOLogic.mk_comp (map_F, Rep_const));

        val fs = MRBNF_Def.interlace (select_n var_f'_As var_f_As lin_live_poses) var_u_Bs var_v_Fs var_types;
        val l_fs = map (fn T => find_first (fn f => (fastype_of f |> domain_type) = T) fs |> the) l_ABFs;
        val map_F'_rhs = fold (fn var => (fn rhs => absfree (dest_Free var) rhs)) (rev l_fs) abs_map_rep;
        val map_F'_binding = if Binding.is_empty map_b then Binding.prefix_name ("map_") b else map_b;
        val ((_, map_F'_term, map_F'_def_thm), lthy) = MRBNF_Util.new_definition map_F'_binding map_F'_rhs lthy;

        val map_atomics = fastype_of map_F'_term |> dest_Type_atomic |> drop (2*nr_ABFs);
        fun mk_map_F' T T' = subst_atomic_types (map_atomics ~~ ((dest_Type_atomic T) @ (dest_Type_atomic T'))) map_F'_term;

        (* rrel_F' *)
        val eq_Rs = select_n var_R'_As (map HOLogic.eq_const As) lin_live_poses
        val l_Rs = map (fn T => find_first (fn f => (fastype_of f |> domain_type) = T) var_R'_As |> the) l_As;

        val Rep_x = Const (#Rep_name td_info1, (typ_y) --> (typ_x)) $ var_y;
        val Rep_x' = Const (#Rep_name td_info1, (typ_y') --> (typ_x'l)) $ var_y';
        val rrel_F = MRBNF_Def.mk_rel_of_mrbnf Ds As (select_n As' As lin_live_poses) Bs Fs mrbnf;
        val rrel_F_R_x_x' = Term.list_comb (rrel_F, eq_Rs @ [Rep_x, Rep_x']);
        val vars = [var_y', var_y] @ (l_Rs |> rev);
        val rrel_F'_rhs = fold (fn var => (fn rhs => absfree (dest_Free var) rhs)) vars rrel_F_R_x_x';
        val rrel_F'_binding = if Binding.is_empty rel_b then Binding.prefix_name ("rrel_") b else rel_b;
        val ((_, rrel_F'_term, rrel_F'_def_thm), lthy) = MRBNF_Util.new_definition rrel_F'_binding rrel_F'_rhs lthy;

        (** proving lemmas **)
        val id_prems = MRBNF_Comp_Tactics.mk_id_prems mrbnf;
        val Rep_F'_inverse = #Rep_inverse td_info2;
        fun mk_Rep_F' ctxt = #Rep td_info2 |> unfold_thms ctxt [@{thm mem_Collect_eq}];
        fun mk_Abs_F'_inverse ctxt = #Abs_inverse td_info2 |> unfold_thms ctxt [@{thm mem_Collect_eq}];

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
          (fn {context = ctxt, prems} => mk_F_strong_tac ctxt prems nr_As id_prems mr_rel_F_def F_mr_rel_mono_strong0 
            F_map_id F_in_rel F_rel_map_set_live_strong_thm);

        (* mr_rel_F_exchange *)
        val RQ_args = select_n Q_args R_args lin_poses;
        val mr_rel_RQ = Term.list_comb (mr_rel, RQ_args @ [var_x, var_x']) |> HOLogic.mk_Trueprop;
        val mr_rel_F_exchange_thm = Goal.prove_sorry lthy (map (fst o dest_Free) (var_R'_As @ var_R'_As2 @ [var_x, var_x'])) 
          [mr_rel_R, mr_rel_Q] mr_rel_RQ
          (fn {context = ctxt, prems} => mk_mr_rel_F_exchange_tac ctxt prems id_prems F_mr_rel_mono_strong0 F_strong_thm);
        
        (* nonrep_map_F *)
        val u_props_raw = map (fn u => [MRBNF_Util.mk_bij u |> HOLogic.mk_Trueprop, 
            MRBNF_Util.mk_supp_bound u |> HOLogic.mk_Trueprop]) var_u_Bs;
        val v_props_raw = map (fn v => [MRBNF_Util.mk_supp_bound v |> HOLogic.mk_Trueprop]) var_v_Fs;
        val uv_props = filter (fn v => v <> MRBNF_Def.Live_Var) var_types |> 
          MRBNF_Def.interlace [] u_props_raw v_props_raw |> flat;
        val nrp_x_prop = HOLogic.mk_Trueprop nrp_x;
        val nrp_TFree' = subst_atomic_types (nths_drop lin_live_poses (As ~~ As')) nrp_TFree;
        val id_f'_As = select_n var_f'_As (map HOLogic.id_const As) lin_live_poses;
        val map_uv = MRBNF_Def.mk_map_comb_of_mrbnf Ds id_f'_As var_u_Bs var_v_Fs mrbnf;
        val nonrep_map_uv_prop = nrp_TFree' $ (map_uv $ var_x) |> HOLogic.mk_Trueprop;

        val nonrep_map_F_thm = Goal.prove_sorry lthy
          (map (fst o dest_Free) (var_x :: var_u_Bs @ var_v_Fs @ (nths_drop lin_live_poses var_f'_As))) 
          (uv_props @ [nrp_x_prop]) nonrep_map_uv_prop
          (fn {context = ctxt, prems} => mk_nonrep_map_F_tac ctxt prems id_prems nr_lin nr_As (map top_rel on_tfrees)
            nrp_def_thm ss_def_thm mr_rel_F_def F_map_comp F_mr_rel_maps F_rel_compp F_rel_Grp F_in_rel F_map_id F_rel_maps F_rel_refl_strong);
        
        (* nonrep_map_F_rev *)
        val inst_ids = (map_index (fn (i, A) => if member (op=) lin_live_poses i then SOME (HOLogic.id_const A) else NONE) As)
        val map_u = MRBNF_Def.mk_map_comb_of_mrbnf Ds id_f'_As var_u_Bs (map HOLogic.id_const Fs) mrbnf;
        val nonrep_map_u_prop = nrp_TFree' $ (map_u $ var_x) |> HOLogic.mk_Trueprop;
        val nonrep_map_F_rev_thm = Goal.prove_sorry lthy 
          (map (fst o dest_Free) (var_x :: var_u_Bs @ (nths_drop lin_live_poses var_f'_As))) 
          ((flat u_props_raw) @ [nonrep_map_u_prop]) nrp_x_prop
          (fn {context = ctxt, prems} => mk_nonrep_map_F_rev_tac ctxt prems nr_As nr_Bs nr_Fs lin_live_poses inst_ids nrp_def_thm ss_def_thm
            F_mr_rel_maps F_map_comp F_rel_eq F_mr_rel_id F_mr_rel_flip F_mr_rel_mono_strong0 F_mr_rel_Grp mr_rel_F_exchange_thm);

        (* nonrep_map_F_bij *)
        val l_f_As = (map (nth var_f_As) lin_live_poses)
        val bij_f_props = map (HOLogic.mk_Trueprop o MRBNF_Util.mk_bij) l_f_As;
        val f_id_As = select_n (map HOLogic.id_const As) var_f_As lin_live_poses;
        val map_f = MRBNF_Def.mk_map_comb_of_mrbnf Ds f_id_As (map HOLogic.id_const Bs) (map HOLogic.id_const Fs) mrbnf;
        val nonrep_map_f_prop = nrp_TFree $ (map_f $ var_x) |> HOLogic.mk_Trueprop;
        val nonrep_map_F_bij_thm = Goal.prove_sorry lthy 
          (map (fst o dest_Free) ([var_x] @ l_f_As)) (bij_f_props @ [nrp_x_prop]) nonrep_map_f_prop
          (fn {context = ctxt, prems} => mk_nonrep_map_F_bij_tac ctxt prems nr_lin l_f_As nrp_def_thm ss_def_thm F_mr_rel_maps F_map_comp);

        (* nonrep2_mapF_bij_2 *)
        val ff'_As = select_n var_f'_As var_f_As lin_live_poses;
        val map_fuv = MRBNF_Def.mk_map_comb_of_mrbnf Ds ff'_As var_u_Bs var_v_Fs mrbnf;
        val nonrep_map_fuv_prop = nrp_TFree' $ (map_fuv $ var_x) |> HOLogic.mk_Trueprop;
        val nonrep_map_F_bij_2_thm = Goal.prove_sorry lthy
          (map (fst o dest_Free) (ff'_As @ var_u_Bs @ var_v_Fs @[var_x])) (uv_props @ bij_f_props @ [nrp_x_prop]) nonrep_map_fuv_prop
          (fn {context = ctxt, prems} => mk_nonrep2_mapF_bij_2_tac ctxt prems id_prems nr_lin F_map_comp 
            nonrep_map_F_bij_thm nonrep_map_F_thm);

        (* rrel_F_map_onVar *) 
        val Grp_fs = map (fn f => BNF_Util.mk_Grp (HOLogic.mk_UNIV (fastype_of f |> domain_type)) f) var_f_As
        val Grp_Rs = select_n var_R'_As Grp_fs lin_live_poses;
        val rrel_F_Grp = Term.list_comb (rrel_F, Grp_Rs @ [var_x, var_x'l]);
        val rrel_F_map = Term.list_comb (rrel_F, eq_Rs @ [map_f $ var_x, var_x'l]);
        val rrel_F_map_onVar_prop = HOLogic.mk_eq (rrel_F_Grp, rrel_F_map) |> HOLogic.mk_Trueprop;
        val rrel_F_map_onVar_thm = Goal.prove_sorry lthy (map (fst o dest_Free) 
          ((select_n eq_Rs var_f_As lin_live_poses) @ [var_x, var_x'l])) [] rrel_F_map_onVar_prop
          (fn {context = ctxt, ...} => mk_rrel_F_map_onVar_tac ctxt F_rel_maps F_rel_mono_strong);

        (* F'_map_cong *)
        val l_var_u_Bs = map (fn T => find_first (fn u => (fastype_of u |> domain_type) = T) (var_u_Bs @ var_f_As) |> the) l_Bs
        val (l_var_u2_Bs, names_lthy) = mk_Frees "u" (map (fastype_of) l_var_u_Bs) names_lthy
        val l_var_v_Fs = map (fn T => find_first (fn v => (fastype_of v |> domain_type) = T) var_v_Fs |> the) l_Fs
        val (l_var_v2_Fs, names_lthy) = mk_Frees "v" (map (fastype_of) l_var_v_Fs) names_lthy

        val l_var_f'_As = map (fn T => find_first (fn f => (fastype_of f |> domain_type) = T) var_f'_As |> the) l_As
        val l_As' = map (fn f => fastype_of f |> range_type) l_var_f'_As
        val l_As'' = map (fn T => find_first (fn (A, _) => T = A) (As ~~ As'') |> the |> snd) l_As

        val l_typ_f''_As = map (fn (T', T'') => T' --> T'') (l_As' ~~ l_As'')
        val (var_f''_As, _) = mk_Frees "lf''" l_typ_f''_As names_lthy;

        val l_fs = MRBNF_Def.interlace l_var_f'_As l_var_u_Bs l_var_v_Fs l_var_types;
        val l_f2s = MRBNF_Def.interlace var_f''_As l_var_u2_Bs l_var_v2_Fs l_var_types;

        val map_comp_f = Term.list_comb (mk_map_F' typ_y typ_y'', (map HOLogic.mk_comp (l_f2s ~~ l_fs)));
        val map_inner_f = Term.list_comb (mk_map_F' typ_y typ_y', l_fs);
        val map_outer_f = Term.list_comb (mk_map_F' typ_y' typ_y'', l_f2s);
        val F'_map_cong_prop = HOLogic.mk_eq (map_comp_f, HOLogic.mk_comp (map_outer_f, map_inner_f)) |> HOLogic.mk_Trueprop;
        
        val bij_props = map (fn f => MRBNF_Util.mk_bij f |> HOLogic.mk_Trueprop) (l_var_u_Bs @ l_var_u2_Bs);
        val supp_props = map (fn f => MRBNF_Util.mk_supp_bound f |> HOLogic.mk_Trueprop) 
          ((nths_drop l_lin_bound_poses l_var_u_Bs) @ l_var_v_Fs @ (nths_drop l_lin_bound_poses l_var_u2_Bs) @ l_var_v2_Fs);

        val F'_map_cong_thm = Goal.prove_sorry lthy (map (fst o dest_Free) (l_fs @ l_f2s)) (bij_props @ supp_props)
          F'_map_cong_prop (fn {context = ctxt, prems} => mk_F'_map_comp0_tac ctxt prems nr_lin l_nr_Bs nr_Fs map_F'_def_thm F_map_comp0 
            nonrep_map_F_bij_2_thm mk_Rep_F' mk_Abs_F'_inverse);

        val wits_F_thmss = map (nths_drop lin_live_poses) wits_F_thmss;

        (* register MRBNF *)
        val Abs_const = Const (#Abs_name td_info1, (repT) --> (typ_y));
        val Abs_mrbnf = subst_atomic_types mrbnf_subst Abs_const;
        val tacs = {
          map_id0 = mk_F'_map_id0_tac map_F'_def_thm F_map_id Rep_F'_inverse,
          map_comp0 = (fn ctxt => HEADGOAL (rtac ctxt F'_map_cong_thm THEN_ALL_NEW assume_tac ctxt)),
          map_cong0 = mk_F'_map_cong0_tac map_F'_def_thm set_F'_def_thms F_map_cong,
          set_map0 = map (fn set_F'_def => mk_F'_set_map0_tac set_F'_def map_F'_def_thm 
              nonrep_map_F_bij_2_thm F_set_maps mk_Rep_F' mk_Abs_F'_inverse) set_F'_def_thms,
          infinite_regular_card_order = fn ctxt =>
            HEADGOAL (rtac ctxt (MRBNF_Def.bd_infinite_regular_card_order_of_mrbnf mrbnf)),
          set_bd = map (fn set_F'_def => fn ctxt =>
              unfold_thms_tac ctxt [set_F'_def, o_apply] THEN HEADGOAL (resolve_tac ctxt F_set_bds))
            set_F'_def_thms,
          le_rel_OO = mk_F'_le_rel_OO_tac l_nr_As rrel_F'_def_thm F_rel_compp Rep_const,
          in_rel = mk_F'_in_rel_tac mrbnf lives bounds frees lin_live_poses rrel_F'_def_thm 
            map_F'_def_thm set_F'_def_thms nonrep_map_F_bij_2_thm F_map_comp rrel_F_map_onVar_thm F_in_rel 
            nonrep_map_F_rev_thm F_set_maps F_map_cong Rep_F'_inverse mk_Rep_F' mk_Abs_F'_inverse 
            Abs_mrbnf,
          pred_set = fn ctxt => HEADGOAL (rtac ctxt refl),
          wit = mk_F'_wit_tac set_F'_def_thms (nonrep_wit_F_thms @ nonrep_wit_new_thms) 
            (flat (wits_F_thmss @ wits_new_thmss)) mk_Abs_F'_inverse
        }

        (* make F' wits *)
        val Abs_const = Const (#Abs_name td_info1, (repT) --> (typ_y));

        val wits_F' =
          map (fn (I, wit_F) =>
            let
              val vs = map (nth var_as) I;
            in fold_rev absfree (map dest_Free vs) (Abs_const $ (list_comb (wit_F, vs))) end)
          (Iwits_F @ Iwits_new);

        val (mrbnf', lthy) = MRBNF_Def.mrbnf_def MRBNF_Def.Do_Inline (MRBNF_Def.user_policy MRBNF_Def.Note_Some) 
          false I tacs (SOME l_Ds) (SOME (MRBNF_Def.class_of_mrbnf mrbnf, MRBNF_Def.coclass_of_mrbnf mrbnf)) 
          map_F'_binding rrel_F'_binding pred_b set_bs_non_dead (((((((b, typ_y), map_F'_term), 
          (l_var_types ~~ set_F'_terms)), MRBNF_Def.mk_bd_of_mrbnf Ds Bs Fs mrbnf), wits_F'), SOME rrel_F'_term), NONE)
          lthy

      in
        lthy |> MRBNF_Def.register_mrbnf Plugin_Name.default_filter (Local_Theory.full_name lthy b) mrbnf'
      end;
  in
    (goals, after_qed, [], lthy)
  end;


(** main commands **)

local

fun prepare_common prepare_sort prepare_typ prepare_term
    ((((((plugins, raw_specs), b), raw_repT), raw_wits), on_tvars), (map_b, rel_b, pred_b, ss_b, nrp_b)) lthy =
  let
    val repT = prepare_typ lthy raw_repT
    val wits = (Option.map o map) (prepare_term lthy) raw_wits;
    val specs = map (apsnd (apsnd (the_default @{sort type} o Option.map (prepare_sort lthy)))) raw_specs;
  in
    linearize b repT on_tvars wits specs map_b rel_b pred_b ss_b nrp_b plugins lthy
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

val parse_on_clause = apfst (fn (h, t) => h::t) o Parse.reserved "on" |-- Parse.type_ident -- Scan.repeat (@{keyword "and"} |-- Parse.type_ident);

fun extract_map_rel_pred_suff ("map", m) = (fn (_, r, p, ss, n) => (m, r, p, ss, n))
  | extract_map_rel_pred_suff ("rel", r) = (fn (m, _, p, ss, n) => (m, r, p, ss, n))
  | extract_map_rel_pred_suff ("pred", p) = (fn (m, r, _, ss, n) => (m, r, p, ss, n))
  | extract_map_rel_pred_suff ("sameShape", ss) = (fn (m, r, p , _, n) => (m, r, p, ss, n))
  | extract_map_rel_pred_suff ("nonrep", n) = (fn (m, r, p , ss, _) => (m, r, p, ss, n))
  | extract_map_rel_pred_suff (s, _) = error ("Unknown label " ^ quote s ^ " (expected \"map\", \"rel\", \"pred\", \"sameShape\" or \"nonrep\")");

val binding_empty_5 = (Binding.empty, Binding.empty, Binding.empty, Binding.empty, Binding.empty);

val parse_map_rel_pred_suff_bindings =
  \<^keyword>\<open>for\<close> |-- Scan.repeat (Parse.name --| \<^keyword>\<open>:\<close> -- Parse.binding)
    >> (fn ps => fold extract_map_rel_pred_suff ps binding_empty_5)
  || Scan.succeed binding_empty_5;

in

(* exposed commands *)

val _ =
  Outer_Syntax.local_theory_to_proof @{command_keyword linearize_mrbnf}
    "linearize an existing MRBNF on a list of live variables"
    ((parse_lift_opts -- parse_type_args_named_constrained -- Parse.binding --
      (\<^keyword>\<open>=\<close> |-- Parse.typ) -- 
      parse_wits -- parse_on_clause -- parse_map_rel_pred_suff_bindings) >> linearize_mrbnf_cmd);

end;

end;
