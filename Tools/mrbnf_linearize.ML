

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
open MRBNF_Linearize_Tactics

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


(** linearize **)
fun linearize b repT on_tvar wits specs map_b rel_b pred_b opts lthy =
  let
    val set_bs = map fst specs;
    val tfrees = map (TFree o snd) specs |> @{print};

    fun flatten_tyargs Ass =
      map dest_TFree tfrees
      |> filter (fn T => exists (fn Ts => member op= Ts T) Ass);
    val ((mrbnf,(Ds, ABFs)), (_,lthy)) = MRBNF_Comp.mrbnf_of_typ true MRBNF_Def.Smart_Inline
      (Binding.prefix_name (Binding.name_of b)) flatten_tyargs [] [] [] repT
      ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy);

    val _ = (Ds, ABFs) |> @{print}
    val var_types = MRBNF_Def.var_types_of_mrbnf mrbnf |> @{print};
    val (As, Bs, Fs) = fold_rev (fn (T, vt) => (fn (acc_As, acc_Bs, acc_Fs) => 
      case vt of
        MRBNF_Def.Live_Var => (T::acc_As, acc_Bs, acc_Fs)
      | MRBNF_Def.Bound_Var => (acc_As, T::acc_Bs, acc_Fs)
      | MRBNF_Def.Free_Var => (acc_As, acc_Bs, T::acc_Fs)
      | _ => error "Dead_Var!" ))
      (ABFs ~~ var_types) ([], [], []) |> @{print};


    val nr_As = MRBNF_Def.live_of_mrbnf mrbnf;
    val nr_Fs = MRBNF_Def.free_of_mrbnf mrbnf;
    val nr_Bs = MRBNF_Def.bound_of_mrbnf mrbnf;
    val nr_ABFs = nr_As + nr_Fs + nr_Bs;
    val class = MRBNF_Def.class_of_mrbnf mrbnf;
    val on_tfree = TFree (on_tvar, class);

    val names_lthy = fold Variable.declare_typ (Ds @ ABFs) lthy;
    val (As', names_lthy) = mk_TFrees nr_As names_lthy;

    fun select_one types types' pos = map_index (fn (i, (t, t')) => if i = pos then t' else t) (types ~~ types')

    val l_ABFs = subtract (op =) Ds tfrees |> @{print};
    val l_Ds = subtract (op =) ABFs tfrees;
    val l_As = subtract (op =) (Bs @ Fs) l_ABFs;
    val l_Bs = subtract (op =) (As @ Fs) l_ABFs;
    val l_Fs = subtract (op =) (As @ Bs) l_ABFs;
    val lin_pos = find_index (fn x => x = on_tfree) ABFs |> @{print};
    val l_lin_pos = find_index (fn x => x = on_tfree) l_ABFs |> @{print};
    val lin_live_pos = find_index (fn x => x = on_tfree) As |> @{print};
    val l_lin_live_pos = find_index (fn x => x = on_tfree) l_As |> @{print};

    val specs_non_dead = subtract (fn (d, (_, x)) => d = TFree x) Ds specs |> @{print}
    val set_bs_non_dead = map_index (fn (i, (b_opt, _)) => if Option.getOpt (b_opt, Binding.empty) |> Binding.is_empty |> not then
              the b_opt else
              Binding.prefix_name ("set" ^ (Int.toString (i+1)) ^ "_") b) specs_non_dead |> @{print}


    (* make Frees*)
    val As_pair = map (fn (A, A') => HOLogic.mk_prodT (A, A')) (As ~~ As');

    val typ_x = MRBNF_Def.mk_T_of_mrbnf Ds As Bs Fs mrbnf;
    val typ_x'l = MRBNF_Def.mk_T_of_mrbnf Ds (select_one As' As lin_live_pos) Bs Fs mrbnf; (* other lives change typ *)
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
    (*TODO: messages for
      - lost wits due to lin_pos dependency?
      - lin_pos dependent user specified wits?
      - F wits subsumed by user specified?
      - user specified wits subsumed by F
    *)
    val nwits = MRBNF_Def.nwits_of_mrbnf mrbnf;
    val Iwits_F = MRBNF_Def.mk_wits_of_mrbnf (replicate nwits Ds) (replicate nwits As) 
      (replicate nwits Bs) (replicate nwits Fs) mrbnf |> filter_out (fn (I, _) => member (op =) I lin_pos);

    fun binder_types_until_eq V T =
      let
        fun strip (TU as Type ("fun", [T, U])) = if V = TU then [] else T :: strip U
          | strip T = if V = T then [] else
              let val _ = (T, V) |> @{print} in
              error ("Bad type for witness: " ^ quote (Syntax.string_of_typ lthy T)) end;
      in strip T end;

    val Iwits_new = the_default [] (Option.map (map (`(map (fn T =>
      find_index (fn U => T = U) ABFs) o binder_types_until_eq repT o fastype_of))) wits);
    
    (* filter and warn user for specified, but subsumed Iwits *)
    val subsumed_Iwits =
      filter (fn (J, _) => exists (fn (I, _) => subset (op =) (I, J)) Iwits_F) Iwits_new;
    val _ =  if null subsumed_Iwits orelse exists (fn No_Warn_Wits => true | _ => false) opts
      then ()
      else
        let
          val (suffix1, suffix2, be, this) =
            (if length subsumed_Iwits = 1 then ("", "", "is", "this") else ("s", "es", "are", "these"))
        in
          subsumed_Iwits
          |> map (Syntax.pretty_typ lthy o fastype_of o snd)
          |> Pretty.big_list
            ("The following type" ^ suffix1 ^ " of nonemptiness witness" ^ suffix2 ^
              " of the raw type's BNF " ^ be ^ " subsumed by the existing raw witnesses:")
          |> (fn pt => Pretty.chunks [pt,
            Pretty.para ("You do not need to lift " ^ this ^ " subsumed witness" ^ suffix2 ^ ".")])
          |> Pretty.string_of
          |> warning
        end;
    val Iwits_new = filter_out (fn (J, _) => exists (fn (I, _) => subset (op =) (I, J)) Iwits_F) Iwits_new

    (* Filter subsumed F witnesses? *)
    val Iwits_F = filter_out (fn (J, _) => exists (fn (I, _) => (subset (op =) (I, J)) 
      andalso (not (subset (op =) (J, I)))) Iwits_new) Iwits_F
    
    val Iwits = Iwits_F @ Iwits_new

    val set_Fs = MRBNF_Def.mk_sets_of_mrbnf (replicate nr_ABFs Ds) (replicate nr_ABFs As) 
      (replicate nr_ABFs Bs) (replicate nr_ABFs Fs) mrbnf;
    val set_Fs_A = map_filter (fn (vt, set) => if vt = MRBNF_Def.Live_Var then SOME set else NONE) (var_types ~~ set_Fs)
    val ((var_as_nl, var_as2_nl), set_Fs_A_nl) = nth_drop lin_live_pos ((var_as ~~ var_as2) ~~ set_Fs_A) 
      |> ListPair.unzip |>> ListPair.unzip

    val wit_goals = maps (mk_wit_goals var_as_nl var_as2_nl set_Fs_A_nl) Iwits_new; 

    (* ex_nonrep *)
    val map_F = MRBNF_Def.mk_map_of_mrbnf Ds As As Bs Fs mrbnf;
    val f = nth var_f_As lin_live_pos;
    val map_funs = map_index (fn (i, t) => if i = lin_pos then f else HOLogic.id_const t) ABFs;
    val map_f_x = Term.list_comb (map_F, map_funs @ [var_x]);

    val rrel_F = MRBNF_Def.mk_rel_of_mrbnf Ds As As Bs Fs mrbnf;
    val top_eqs = map_index (fn (i, A) => if i = lin_live_pos then 
      Const ("Orderings.top_class.top", [A, A] ---> HOLogic.boolT) else HOLogic.eq_const A) As;
    val rrel_top_x_x' = Term.list_comb (rrel_F, top_eqs @ [var_x, var_x2]);
    val ex_f = HOLogic.mk_exists (dest_Free f |> fst, dest_Free f |> snd, 
      HOLogic.mk_eq (var_x2, map_f_x));
    val rrel_top_imp_ex_f = HOLogic.mk_imp (rrel_top_x_x', ex_f);
    val ex_nonrep = HOLogic.mk_exists (dest_Free var_x |> fst, dest_Free var_x |> snd,
      HOLogic.mk_all (dest_Free var_x2 |> fst, dest_Free var_x2 |> snd, rrel_top_imp_ex_f));
    val Tp_ex_nonrep = HOLogic.mk_Trueprop ex_nonrep;


    (* nonrep_wits *)
    fun mk_nonrep_wit (I, wit_term) = 
      let
        fun mk_wit_F [] wit = wit
          | mk_wit_F (pos::I) wit = mk_wit_F I (wit $ (nth var_as pos));
    
        fun mk_all_wit_args [] term = term
          | mk_all_wit_args (pos::I) term = Logic.all (nth var_as pos) term |> mk_all_wit_args I;

        val wit_F = mk_wit_F I wit_term;
        val rrel_top_wit_x = Term.list_comb (rrel_F, top_eqs @ [wit_F, var_x]);
        val map_f_wit = Term.list_comb (map_F, map_funs @ [wit_F]);
        val ex_f = HOLogic.mk_exists (dest_Free f |> fst, dest_Free f |> snd, 
          HOLogic.mk_eq (var_x, map_f_wit));
        val nonrep_wit = HOLogic.mk_all (dest_Free var_x |> fst, typ_x, HOLogic.mk_imp (rrel_top_wit_x, ex_f));
      in
        HOLogic.mk_Trueprop nonrep_wit |> mk_all_wit_args (rev I)
      end;

    val nonrep_wit_goals = map (mk_nonrep_wit) Iwits_new

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
      (map (snd o HOLogic.dest_prodT) As_pair) Bs Fs mrbnf
    val rrel_R_x_x' = Term.list_comb (rrel_F_R, var_R'_As @ [var_x, var_x']);
    val rrel_eq_ex1 = HOLogic.mk_eq (rrel_R_x_x', ex1_z);
    val all_x_x' = HOLogic.mk_Trueprop rrel_eq_ex1 |> Logic.all var_x' |> Logic.all var_x;
    val F_rel_map_set_live_strong = fold (fn R => (fn all => Logic.all R all)) var_R'_As all_x_x';

    val goals = [F_rel_map_set_live_strong, Tp_ex_nonrep] @ nonrep_wit_goals @ wit_goals;

    fun after_qed ([F_rel_map_set_live_strong_thm] :: [ex_nonrep_thm] :: wit_thmss) lthy = 
      let
        (* sameShape *)
        val mr_rel_F = MRBNF_Def.mk_mr_rel_of_mrbnf Ds As As Bs Fs mrbnf
        val mr_rel_args = map_index (fn (i, (T, vt)) => if i = lin_pos then 
          Const ("Orderings.top_class.top", [T, T] ---> HOLogic.boolT) else 
          (if vt = MRBNF_Def.Live_Var then HOLogic.eq_const T else HOLogic.id_const T)) (ABFs ~~ var_types)
        val mr_rel_F_top_x_x' = Term.list_comb (mr_rel_F, mr_rel_args @ [var_x, var_x2]);
        val ss_rhs = mr_rel_F_top_x_x' |> absfree (dest_Free var_x2) |>
          absfree (dest_Free var_x);
        val ss_binding = Binding.prefix_name ("sameShape_") (MRBNF_Def.name_of_mrbnf mrbnf);
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
        val nrp_binding = Binding.prefix_name ("nonrep_") (MRBNF_Def.name_of_mrbnf mrbnf);
        val ((_, nrp_term, nrp_def_thm), lthy) = MRBNF_Util.new_definition nrp_binding nrp_rhs lthy;

        val nrp_arg_atomics = fastype_of nrp_term |> domain_type |> dest_Type_atomic
        val nrp_TFree = subst_atomic_types (nrp_arg_atomics ~~ x_atomics) nrp_term

        (* typedef F'*)
        val nrp_x = nrp_TFree $ var_x
        val td_term = HOLogic.mk_Collect (dest_Free var_x |> fst, dest_Free var_x |> snd, nrp_x)

        val mr_rel_F_def = MRBNF_Def.rel_def_of_mrbnf mrbnf;
        val F_map_id = MRBNF_Def.map_id_of_mrbnf mrbnf;

        fun mk_typedef_tac ctxt = 
          unfold_thms_tac ctxt [nrp_def_thm, ss_def_thm, @{thm mem_Collect_eq}, mr_rel_F_def, F_map_id] THEN
          HEADGOAL (rtac ctxt ex_nonrep_thm)

        val ((_, (td_info1, td_info2)), lthy) = typedef (b, map (snd) specs, 
          Mixfix.NoSyn) td_term NONE mk_typedef_tac lthy |> @{print};


        (* mk F' Frees *)
        val typ_y = #abs_type td_info1;
        val typ_y' = typ_subst_atomic (nth_drop lin_live_pos (As ~~ As')) typ_y;
        val (var_y, names_lthy) = mk_Free "y" typ_y names_lthy;
        val (var_y', _) = mk_Free "y'" typ_y' names_lthy;

        (* F' definitions *)
        (* set_F's *)
        val l_set_Fs = map (fn T => find_first (fn set => (fastype_of set |> body_type |> dest_Type_args |> the_single) = T) set_Fs |> the) l_ABFs |> @{print}
        val (set_defs, lthy) = fold (fn (set, set_binding) => (fn (acc, lthy) =>
          let
            val Rep_const = Const (#Rep_name td_info1, (typ_y) --> (typ_x));
            val set_rhs = HOLogic.mk_comp (set, Rep_const);
            val ((_, set_term, set_def_thm), lthy) = MRBNF_Util.new_definition set_binding set_rhs lthy;
          in
            ((set_term, set_def_thm)::acc, lthy)
          end)) ((l_set_Fs ~~ set_bs_non_dead) |> rev) ([], lthy);
        val (set_terms, set_def_thms) = split_list set_defs

        (* map_F' *)
        val ff'_As = nth_map lin_live_pos (fn _ => nth var_f_As lin_live_pos) var_f'_As;
        val fs = MRBNF_Def.interlace ff'_As var_u_Bs var_v_Fs var_types;
        val l_fs = map (fn T => find_first (fn f => (fastype_of f |> domain_type) = T) fs |> the) l_ABFs;

        val map_F = MRBNF_Def.mk_map_comb_of_mrbnf Ds (nth_map lin_live_pos mk_asBij ff'_As)
          (map (mk_asSS o mk_asBij) var_u_Bs) (map mk_asSS var_v_Fs) mrbnf;
        val Rep_const = Const (#Rep_name td_info1, (typ_y) --> (typ_x));
        val Abs_const = Const (#Abs_name td_info1, (typ_x'l) --> (typ_y'));
        val abs_map_rep = HOLogic.mk_comp (Abs_const, HOLogic.mk_comp (map_F, Rep_const));
        val map_F'_rhs = fold (fn var => (fn rhs => absfree (dest_Free var) rhs)) (rev l_fs) abs_map_rep;
        val map_F'_binding = if Binding.is_empty map_b then Binding.prefix_name ("map_") b else map_b;
        val ((_, map_F'_term, map_F'_def_thm), lthy) = MRBNF_Util.new_definition map_F'_binding map_F'_rhs lthy;

        (* rrel_F' *)
        val eq_Rs = nth_map lin_live_pos (fn R => fastype_of R |> domain_type |> HOLogic.eq_const) var_R'_As |> @{print};
        val l_Rs = map (fn T => find_first (fn f => (fastype_of f |> domain_type) = T) eq_Rs |> the) (nth_drop l_lin_live_pos l_As) |> @{print};

        val Rep_x = Const (#Rep_name td_info1, (typ_y) --> (typ_x)) $ var_y;
        val Rep_x' = Const (#Rep_name td_info1, (typ_y') --> (typ_x'l)) $ var_y';
        val rrel_F = MRBNF_Def.mk_rel_of_mrbnf Ds As (select_one As' As lin_live_pos) Bs Fs mrbnf;
        val rrel_F_R_x_x' = Term.list_comb (rrel_F, eq_Rs @ [Rep_x, Rep_x']);
        val vars = [var_y', var_y] @ (l_Rs |> rev);
        val rrel_F'_rhs = fold (fn var => (fn rhs => absfree (dest_Free var) rhs)) vars rrel_F_R_x_x';
        val rrel_F'_binding = if Binding.is_empty rel_b then Binding.prefix_name ("rrel_") b else rel_b;
        val ((_, rrel_F'_term, rrel_F'_def_thm), lthy) = MRBNF_Util.new_definition rrel_F'_binding rrel_F'_rhs lthy;
        val _ = rrel_F'_term |> @{print}
        val _ = rrel_F'_def_thm |> @{print}

        (** proving lemmas **)        
        (* make theorems & util (mr_rel_F_def and F_map_id made for typedef already) *)
        val id_prems = MRBNF_Comp_Tactics.mk_id_prems mrbnf;
        val id_prems_bij_As = MRBNF_Comp_Tactics.mk_prems mrbnf @{thms bij_id supp_id_bound} @{thms bij_id supp_id_bound};

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
        val RQ_args = select_one Q_args R_args lin_pos;
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
        val nrp_TFree' = subst_atomic_types (nth_drop lin_live_pos (As ~~ As')) nrp_TFree;
        val id_f'_As = nth_map lin_live_pos (fn f => fastype_of f |> domain_type |> HOLogic.id_const) var_f'_As;
        val map_uv = MRBNF_Def.mk_map_comb_of_mrbnf Ds id_f'_As var_u_Bs var_v_Fs mrbnf;
        val nonrep_map_uv_prop = nrp_TFree' $ (map_uv $ var_x) |> HOLogic.mk_Trueprop;
        
        val nonrep_map_F_thm = Goal.prove_sorry lthy
          (map (fst o dest_Free) (var_x :: var_u_Bs @ var_v_Fs @ (nth_drop lin_live_pos var_f'_As))) 
          (uv_props @ [nrp_x_prop]) nonrep_map_uv_prop
          (fn {context = ctxt, prems} => mk_nonrep_map_F_tac ctxt prems nr_As nr_Bs nr_Fs lin_pos lin_live_pos nrp_def_thm 
            ss_def_thm mr_rel_F_def F_map_comp F_mr_rel_maps F_rel_compp F_rel_Grp F_in_rel F_map_id F_rel_maps F_rel_refl_strong);
        
        (* nonrep_map_F_rev *)
        val map_u = MRBNF_Def.mk_map_comb_of_mrbnf Ds id_f'_As var_u_Bs (map HOLogic.id_const Fs) mrbnf;
        val nonrep_map_u_prop = nrp_TFree' $ (map_u $ var_x) |> HOLogic.mk_Trueprop;
        val nonrep_map_F_rev_thm = Goal.prove_sorry lthy 
          (map (fst o dest_Free) (var_x :: var_u_Bs @ (nth_drop lin_live_pos var_f'_As))) 
          ((flat u_props_raw) @ [nonrep_map_u_prop]) nrp_x_prop
          (fn {context = ctxt, prems} => mk_nonrep_map_F_rev_tac ctxt prems nr_As nr_Bs nr_Fs lin_live_pos nrp_def_thm ss_def_thm
            F_mr_rel_maps F_map_comp F_rel_eq F_mr_rel_id F_mr_rel_flip F_mr_rel_mono_strong0 F_mr_rel_Grp mr_rel_F_exchange_thm);

        (* nonrep_map_F_bij *)
        val bij_f_prop = MRBNF_Util.mk_bij f |> HOLogic.mk_Trueprop;
        val f_id_As = nth_map lin_live_pos (fn _ => f) (map HOLogic.id_const As);
        val map_f = MRBNF_Def.mk_map_comb_of_mrbnf Ds f_id_As (map HOLogic.id_const Bs) (map HOLogic.id_const Fs) mrbnf;
        val nonrep_map_f_prop = nrp_TFree $ (map_f $ var_x) |> HOLogic.mk_Trueprop;
        val nonrep_map_F_bij_thm = Goal.prove_sorry lthy 
          (map (fst o dest_Free) ([var_x, f])) [bij_f_prop, nrp_x_prop] nonrep_map_f_prop
          (fn {context = ctxt, prems} => mk_nonrep_map_F_bij_tac ctxt prems nr_As nr_Bs nr_Fs lin_pos lin_live_pos 
            id_prems id_prems_bij_As nrp_def_thm ss_def_thm mr_rel_F_def F_mr_rel_maps F_rel_mono_strong F_map_id F_map_comp);

        (* nonrep2_mapF_bij_2 *)
        val ff'_As = select_one var_f'_As var_f_As lin_live_pos;
        val map_fuv = MRBNF_Def.mk_map_comb_of_mrbnf Ds ff'_As var_u_Bs var_v_Fs mrbnf;
        val nonrep_map_fuv_prop = nrp_TFree' $ (map_fuv $ var_x) |> HOLogic.mk_Trueprop;
        val nonrep_map_F_bij_2_thm = Goal.prove_sorry lthy
          (map (fst o dest_Free) (ff'_As @ var_u_Bs @ var_v_Fs @[var_x])) (uv_props @ [bij_f_prop, nrp_x_prop]) nonrep_map_fuv_prop
          (fn {context = ctxt, prems} => mk_nonrep2_mapF_bij_2_tac ctxt prems id_prems F_map_comp nonrep_map_F_bij_thm 
            nonrep_map_F_thm);

        (* rrel_F_map_onVar *)   
        val Grp_f = BNF_Util.mk_Grp (HOLogic.mk_UNIV (nth As lin_live_pos)) f;
        val Grp_Rs = nth_map lin_live_pos (fn _ => Grp_f) eq_Rs;
        val rrel_F_Grp = Term.list_comb (rrel_F, Grp_Rs @ [var_x, var_x'l]);
        val rrel_F_map = Term.list_comb (rrel_F, eq_Rs @ [map_f $ var_x, var_x'l]);
        val rrel_F_map_onVar_prop = HOLogic.mk_eq (rrel_F_Grp, rrel_F_map) |> HOLogic.mk_Trueprop
        val rrel_F_map_onVar_thm = Goal.prove_sorry lthy (map (fst o dest_Free) 
          ((nth_drop lin_live_pos eq_Rs) @ [f, var_x, var_x'l])) [] rrel_F_map_onVar_prop
          (fn {context = ctxt, ...} => mk_rrel_F_map_onVar_tac ctxt F_rel_maps F_rel_mono_strong);

        (* register MRBNF *)
        val tacs = {
          map_id0 = mk_F'_map_id0_tac map_F'_def_thm F_map_id Rep_F'_inverse,
          map_comp0 = mk_F'_map_comp0_tac nr_Fs nr_Bs map_F'_def_thm F_map_comp0 nonrep_map_F_bij_2_thm mk_Rep_F' 
            mk_Abs_F'_inverse,
          map_cong0 = mk_F'_map_cong0_tac map_F'_def_thm set_def_thms F_map_cong,
          set_map0 = map (fn set_F'_def => mk_F'_set_map0_tac set_F'_def map_F'_def_thm 
              nonrep_map_F_bij_2_thm F_set_maps mk_Rep_F' mk_Abs_F'_inverse) set_def_thms,
          infinite_regular_card_order = fn ctxt =>
            HEADGOAL (rtac ctxt (MRBNF_Def.bd_infinite_regular_card_order_of_mrbnf mrbnf)),
          set_bd = map (fn set_F'_def => fn ctxt =>
              unfold_thms_tac ctxt [set_F'_def, o_apply] THEN HEADGOAL (resolve_tac ctxt F_set_bds))
            set_def_thms,
          le_rel_OO = mk_F'_le_rel_OO_tac nr_As lin_live_pos rrel_F'_def_thm F_rel_compp,
          in_rel = mk_F'_in_rel_tactic nr_As nr_Bs nr_Fs lin_pos lin_live_pos rrel_F'_def_thm map_F'_def_thm set_def_thms 
            nonrep_map_F_bij_2_thm F_map_comp rrel_F_map_onVar_thm F_in_rel nonrep_map_F_rev_thm F_set_maps F_map_cong 
            Rep_F'_inverse mk_Rep_F' mk_Abs_F'_inverse,
          pred_set = fn ctxt => HEADGOAL (rtac ctxt refl),
          wit = fn ctxt => print_tac ctxt "wit"
        }

        val l_var_types = map (fn l_T => find_first (fn (T, _) => T = l_T) (ABFs ~~ var_types) |> the) l_ABFs |> map snd |> @{print};
        val var_types_Abs = nth_map l_lin_pos (fn _ => MRBNF_Def.Bound_Var) l_var_types |> @{print};

        (* make F' wits *)
        val Abs_const = Const (#Abs_name td_info1, (repT) --> (typ_y));

        val wits_F' =
          map (fn (I, wit_F) =>
            let
              val vs = map (nth var_as) I;
            in fold_rev absfree (map dest_Free vs) (Abs_const $ (list_comb (wit_F, vs))) end)
          Iwits;
        
        val _ = wit_thmss |> @{print}
        val _ = Iwits |> @{print}
        val _ = wits_F' |> @{print}

        (*TODO: ISSUE*)
        val wits_F' = []

        val (mrbnf', lthy) = MRBNF_Def.mrbnf_def MRBNF_Def.Do_Inline (MRBNF_Def.user_policy MRBNF_Def.Note_Some) 
          false I tacs (SOME l_Ds) NONE map_F'_binding rrel_F'_binding pred_b set_bs_non_dead 
          (((((((b, typ_y), map_F'_term), (var_types_Abs ~~ set_terms)),
            MRBNF_Def.mk_bd_of_mrbnf l_Ds l_Bs l_Fs mrbnf),
            wits_F'),
            SOME rrel_F'_term),
            NONE)
          lthy

      val _ = mrbnf' |> @{print}

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
    val repT = prepare_typ lthy raw_repT
    val wits = (Option.map o map) (prepare_term lthy) raw_wits;
    val specs = map (apsnd (apsnd (the_default @{sort type} o Option.map (prepare_sort lthy)))) raw_specs;
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
