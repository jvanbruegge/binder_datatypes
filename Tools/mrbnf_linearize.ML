

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


(** transfer theorems **)

fun mk_transfer_thms' bnf_F bnf_G name consts Tss crel_def pcrel_def defs lthy = let

    val live = length (#alphas Tss);

    val (pcrel_tm, crel_tm) = apply2 (Thm.prop_of #> Logic.dest_equals #> fst #> head_of)
      (pcrel_def, crel_def);

    val (var_Qs, var_Rs) = lthy
      |> fold Variable.declare_typ (#alphas Tss @ Library.union (op =) (#deads Tss) (#Ds0 Tss))
      |> mk_Frees "Q" (map2 mk_relT (#alphas Tss) (#betas Tss))
      ||>> mk_Frees "R" (map2 mk_relT (#gammas Tss) (#deltas Tss))
      |> fst;

    (* get the "pcrel :: args_raw => rep => abs \<Rightarrow> bool" term and instantiate types *)
    val (args_raw, (rep, abs)) = pcrel_tm
      |> fastype_of
      |> binder_types
      |> last2;
    val thy = Proof_Context.theory_of lthy;
    val tyenv_match = Vartab.empty
      |> Sign.typ_match thy ((rep, #rep Tss))
      |> Sign.typ_match thy ((abs, #abs Tss));
    val args = map (Envir.subst_type tyenv_match) args_raw;
    val (pcrel_a, pcrel_b) = Envir.subst_term (tyenv_match, Vartab.empty) pcrel_tm
      |> `(subst_atomic_types (#alphas Tss @ #betas Tss ~~ #gammas Tss @ #deltas Tss));

    (* match "crel :: ?a F \<Rightarrow> {a G} \<Rightarrow> bool" with "a G" *)
    val tyenv_match = Vartab.empty |> Sign.typ_match thy
      (crel_tm |> fastype_of |> binder_types |> tl |> hd, #abs Tss);
    val crel_b = Envir.subst_term (tyenv_match, Vartab.empty) crel_tm
      |> subst_atomic_types (#alphas Tss ~~ #betas Tss);
    val crel_d = subst_atomic_types (#betas Tss ~~ #deltas Tss) crel_b;

    (* instantiate pcrel with Qs and Rs*)
    val dead_args = map binder_types args
      |> map (fn [T,U] => if T = U then SOME T else NONE | _ => NONE);
    val parametrize = let
        fun go (SOME T :: dTs) tms = HOLogic.eq_const T :: go dTs tms
          | go (_ :: dTs) (tm :: tms) = tm :: go dTs tms
          | go (_ :: dTs) tms = go dTs tms
          | go _ _ = [];
      in go dead_args end;
    val pcrel_Qs = list_comb (pcrel_b, parametrize var_Qs);
    val pcrel_Rs = list_comb (pcrel_a, parametrize var_Rs);

    (* get the order of the dead variables right *)
    val Ds0 = Library.union (op =) (maps the_list dead_args) (#Ds0 Tss);
    val permute_Ds = (mk_T_of_bnf Ds0 (#betas Tss) bnf_G, nth (binder_types (type_of pcrel_Qs)) 1)
      |> apply2 (fn Type (_, Ts) => Ts | _ => []) |> op~~ |> typ_subst_atomic;
    val Ds0 = map permute_Ds Ds0;

    (* terms for sets of the set_transfer thms *)
    val rel_sets_Q = @{map 3} (fn aT => fn bT => fn Q =>
      mk_rel 1 [aT] [bT] @{term rel_set} $ Q) (#alphas Tss) (#betas Tss) var_Qs;

    (* rewrite rules for pcrel and BNF's relator: "pcrel Q = rel_F OO crel" *)
    fun mk_pcr_rel_F_eq Ts Us pcrel vs crel =
      let
        val thm = HOLogic.mk_Trueprop (HOLogic.mk_eq (pcrel, mk_relcompp (list_comb
          (mk_rel_of_bnf (#deads Tss) (Ts Tss) (Us Tss) bnf_F, vs)) crel));
        fun tac ctxt = unfold_thms_tac ctxt (pcrel_def :: defs @ @{thm id_bnf_apply} ::
          Transfer.get_relator_eq ctxt) THEN (HEADGOAL (rtac ctxt refl))
      in prove lthy vs thm tac |> mk_abs_def end;

    val pcr_rel_F_eqs =
      [mk_pcr_rel_F_eq #alphas #betas pcrel_Qs var_Qs crel_b,
       mk_pcr_rel_F_eq #gammas #deltas pcrel_Rs var_Rs crel_d];

    (* create transfer-relations from term('s type) *)
    fun mk_transfer_rel' i tm =
      let
        fun go T' (n, q) = case T' of
            Type ("fun", [T as Type ("fun", _), U]) =>
              go U (n+1, q) |>> mk_rel_fun (fst (go T (n, q)))
          | Type ("fun", [T, U]) =>
              go T (n, q) |-> (fn x => fn st => go U st |>> mk_rel_fun x)
          | Type (@{type_name bool}, _) => (HOLogic.eq_const HOLogic.boolT, (n, q))
          | Type (@{type_name set}, _) => (nth rel_sets_Q n, (n, q))
          | Type _ => (if q then pcrel_Qs else pcrel_Rs, (n, not q))
          | TFree _ => (nth (if q then var_Qs else var_Rs) n, (n, not q))
          | _ => raise Match
      in go (fastype_of tm) (i, true) |> fst end;

    (* prove transfer rules *)
    fun prove_transfer_thm' i vars new_tm const =
      let
        val tm = HOLogic.mk_Trueprop (mk_transfer_rel' i new_tm $ #raw const $ new_tm);
        val tac = (fn ctxt => unfold_thms_tac ctxt (pcr_rel_F_eqs @ [crel_def]) THEN
          #tac const {Rs=var_Rs,Qs=var_Qs} ctxt);
      in prove lthy vars tm tac end;
    val prove_transfer_thm = prove_transfer_thm' 0;
    (* map transfer: "((Q ===> R) ===> pcr_G Q ===> pcr_G R) map_F' map_G" *)
    val map_G = mk_map_of_bnf Ds0 (#betas Tss) (#deltas Tss) bnf_G;
    val map_transfer = prove_transfer_thm (var_Qs @ var_Rs) map_G (#map consts);
    (* pred_transfer: "((Q ===> (=)) ===> pcr_G Q ===> (=)) pred_F' pred_G" *)
    val pred_G = mk_pred_of_bnf Ds0 (#betas Tss) bnf_G;
    val pred_transfer = #pred consts |> Option.map (fn p =>
      ("pred", [prove_transfer_thm (var_Qs @ var_Rs) pred_G p]));
    (* rel_transfer: "((Q ===> R ===> (=)) ===> pcr_G Q ===> pcr_G R ===> (=)) rel_F' rel_G" *)
    val rel_G = mk_rel_of_bnf Ds0 (#betas Tss) (#deltas Tss) bnf_G;
    val rel_transfer = prove_transfer_thm (var_Qs @ var_Rs) rel_G (#rel consts);
    (* set_transfer: "(pcr_G Q ===> rel_set Q) set_F' set_G" *)
    val sets_G = mk_sets_of_bnf (replicate live Ds0) (replicate live (#betas Tss)) bnf_G;
    fun mk_set_transfer i set_G raw tac = prove_transfer_thm' i var_Qs set_G {raw=raw, tac=tac};
    val sets_transfer = @{map 4} mk_set_transfer
      (0 upto (live-1)) sets_G (#raws (#sets consts)) (#tacs (#sets consts));
    (* export transfer theorems *)
    val transform = Morphism.thm (Morphism.thm_morphism "BNF" (unfold_thms lthy defs)) |> map;
    val b = Binding.qualified_name name;
    val qualify =
      let val qs = Binding.path_of b;
      in fold_rev (fn (s, mand) => Binding.qualify mand s) qs end;
    fun mk_binding n = Binding.name (n ^ "_transfer_raw")
      |> Binding.qualify true (Binding.name_of b) |> qualify;
    val notes = [("map", [map_transfer]), ("rel", [rel_transfer])] @ the_list pred_transfer @
      [("set", sets_transfer)] |> map (fn (n, thms) =>
        ((mk_binding n, []), [(transform thms, @{attributes [transfer_rule]})]));

  in lthy |> Local_Theory.notes notes |> snd end;

(* transfer theorems for map, pred (in case of a typedef), rel and sets *)
fun mk_transfer_thms quiet bnf_F bnf_G name consts thm Tss defs lthy = let

    fun mk_crel_def quot_thm =
      (case thm of
        Quotient equiv => @{thm Quotient_crel_quotient} OF [quot_thm, equiv]
      | Typedef => hd ([quot_thm] RL @{thms Quotient_crel_typedef Quotient_crel_typecopy}));
    fun no_quotient _ = [Pretty.para ("No quotient theorem has been registered for " ^
        Binding.name_of (name_of_bnf bnf_G) ^ "."),
      Pretty.para "Use setup_lifting to register a quotient or type definition theorem."];
    fun wrong_quotient T lthy = [Pretty.para ("A wrong quotient theorem has been registered for " ^
        Binding.name_of (name_of_bnf bnf_G) ^ "."),
      Pretty.para ("Expected raw type " ^
        Pretty.string_of (Syntax.pretty_typ lthy (T_of_bnf bnf_F)) ^
        " but the quotient theorem has raw type " ^
        Pretty.string_of (Syntax.pretty_typ lthy T) ^ "."),
      Pretty.para "Use setup_lifting to register a different quotient or type definition theorem."];
    fun pcr_why _ = [Pretty.para ("The pcr_" ^ Binding.name_of (name_of_bnf bnf_G) ^
      " relator has not been defined.")];
    fun warn_transfer why lthy =
      (Pretty.para "The transfer theorems can't be generated:" ::  why lthy)
      |> Pretty.chunks |> Pretty.string_of |> warning |> K lthy;
    fun maybe_warn_transfer why = not quiet ? warn_transfer why;
  in
    case Lifting_Info.lookup_quotients lthy name of
      SOME {pcr_info, quot_thm} =>
        (let
          val crel_def = mk_crel_def quot_thm;
          val rty = Lifting_Util.quot_thm_rty_qty quot_thm |> fst;
          val thy = Proof_Context.theory_of lthy;
        in
          if Sign.typ_instance thy (rty, T_of_bnf bnf_F) then
          (case pcr_info of
            SOME {pcrel_def, ...} =>
              mk_transfer_thms' bnf_F bnf_G name consts Tss crel_def pcrel_def defs lthy
          | _ => maybe_warn_transfer pcr_why lthy)
          else maybe_warn_transfer (wrong_quotient rty) lthy
        end)
    | _ => maybe_warn_transfer no_quotient lthy
  end;


(** linearize **)

fun mk_typedef_transfer_tacs bnf_F bnf_G thms old_defs
  map_raw rel_raw pred_raw sets_raw = let

    val live = live_of_bnf bnf_G;
    val Abs_G_inverse = @{thm type_definition.Abs_inverse} OF [#typedef thms];
    val Rep_G = @{thm type_definition.Rep} OF [#typedef thms];

    fun common_tac addefs tac = (fn _ => fn ctxt =>
      HEADGOAL (EVERY' [SELECT_GOAL (unfold_thms_tac ctxt addefs),
        REPEAT_DETERM o rtac ctxt rel_funI,
        SELECT_GOAL (unfold_thms_tac ctxt @{thms o_apply}),
        REPEAT_DETERM o eresolve_tac ctxt @{thms relcomppE exE conjE},
        hyp_subst_tac ctxt]) THEN tac ctxt)

    fun map_tac ctxt = (HEADGOAL o EVERY')
      [rtac ctxt @{thm relcomppI},
      etac ctxt (mk_rel_funDN (live+1) (map_transfer_of_bnf bnf_F)),
      REPEAT_DETERM_N live o assume_tac ctxt,
      SELECT_GOAL (unfold_thms_tac ctxt [Abs_G_inverse OF [#map_closed thms] OF [Rep_G]]),
      REPEAT_DETERM o rtac ctxt refl];
    val map_tac = common_tac [#map old_defs] map_tac;

    fun rel_tac ctxt =
      HEADGOAL (etac ctxt (mk_rel_funDN (live+2) (rel_transfer_of_bnf bnf_F)) THEN'
        REPEAT_DETERM_N (live+1) o assume_tac ctxt);
    val rel_tac = common_tac (#rel old_defs :: @{thms vimage2p_def}) rel_tac;

    fun pred_tac ctxt =
      HEADGOAL (etac ctxt (mk_rel_funDN (live+1) (pred_transfer_of_bnf bnf_F)) THEN'
        REPEAT_DETERM_N live o (assume_tac ctxt));
    val pred_tac = common_tac [#pred old_defs] pred_tac;

    fun set_tac set_transfer_thm ctxt =
      HEADGOAL (etac ctxt (rel_funD OF [set_transfer_thm]));
    fun mk_set_tac set_def set_transfer = common_tac [set_def] (set_tac set_transfer);
    val set_tacs = map2 mk_set_tac (#sets old_defs) (set_transfer_of_bnf bnf_F);

  in {map={raw=map_raw,tac=map_tac},rel={raw=rel_raw,tac=rel_tac},
      sets={raws=sets_raw,tacs=set_tacs},pred=SOME{raw=pred_raw,tac=pred_tac}} end;

fun linearize b repT on_tvar wits specs map_b rel_b pred_b opts lthy =
  let
    val set_bs = map fst specs;
    val vars = map snd specs;
    val name = Binding.name_of b;
(*
    val mrbnf = MRBNF_Comp.mrbnf_of_typ true MRBNF_Def.Smart_Inline
      (Binding.prefix_name name) flat [] [] [] repT
      ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy)
      |> @{print};
*)
    val mrbnf = repT |> dest_Type |> fst |> MRBNF_Def.mrbnf_of lthy |> the |> @{print};

    val plugins =
      get_first (fn Plugins_Option f => SOME (f lthy) | _ => NONE) (rev opts)
        |> the_default Plugin_Name.default_filter;

    val thm = TrueI;
    (* extract Rep Abs F RepT AbsT *)
    val (Rep_G, Abs_G, F) = strip3 thm;
    val typ_Abs_G = dest_funT (fastype_of Abs_G);
    val RepT = fst typ_Abs_G; (* F *)
    val AbsT = snd typ_Abs_G; (* G *)
    val AbsT_name = dest_Type_name AbsT;
    val tvs = AbsT |> dest_Type_args |> map (fst o dest_TVar);
    val alpha0s = map (TFree o snd) specs;

    val _ = length tvs = length alpha0s orelse
      error ("Expected " ^ string_of_int (length tvs) ^ " type argument(s) to " ^ quote AbsT_name);

    (* instantiate the new type variables newtvs to oldtvs *)
    val subst = subst_TVars (tvs ~~ alpha0s);
    val typ_subst = typ_subst_TVars (tvs ~~ alpha0s);

    val Rep_G = subst Rep_G;
    val Abs_G = subst Abs_G;
    val F = subst F;
    val RepT = typ_subst RepT;
    val AbsT = typ_subst AbsT;

    fun flatten_tyargs Ass =
      map dest_TFree alpha0s
      |> filter (fn T => exists (fn Ts => member op= Ts T) Ass);

    val Ds0 = filter (is_none o fst) specs |> map snd;

    (* get the bnf for RepT *)
    val ((bnf_F, (deads, alphas)), ((_, unfolds), lthy)) =
      bnf_of_typ true Hardly_Inline (Binding.qualify true AbsT_name) flatten_tyargs []
        Ds0 RepT ((empty_comp_cache, empty_unfolds), lthy);

    val set_bs =
      map (fn T => find_index (fn U => T = U) alpha0s) alphas
      |> map (the_default Binding.empty o fst o nth specs);

    val _ = (case alphas of [] => error "No live variables" | _ => ());

    val defs = #map_unfolds unfolds @ flat (#set_unfoldss unfolds) @ #rel_unfolds unfolds @ #pred_unfolds unfolds;

    (* number of live variables *)
    val live = length alphas;

    (* state the three required properties *)
    val sorts = map Type.sort_of_atyp alphas;
    val names_lthy = fold Variable.declare_typ (alphas @ Library.union (op =) deads (map TFree Ds0)) lthy;
    val (((alphas', betas), betas'), names_lthy) = names_lthy
      |> mk_TFrees' sorts
      ||>> mk_TFrees' sorts
      ||>> mk_TFrees' sorts;

    val map_F = mk_map_of_bnf deads alphas betas bnf_F;

    val (typ_fs, typ_aF) = fastype_of map_F |> strip_typeN live ||> domain_type;
    val typ_pairs = map HOLogic.mk_prodT (alphas ~~ alphas');
    val typ_subst_pair = typ_subst_atomic (alphas ~~ typ_pairs);
    val typ_pair = typ_subst_pair RepT;
    val subst_b = subst_atomic_types (alphas ~~ betas);
    val subst_a' = subst_atomic_types (alphas ~~ alphas');
    val subst_pair = subst_atomic_types (alphas ~~ typ_pairs);
    val aF_set = F;
    val aF_set' = subst_a' F;
    val pairF_set = subst_pair F;
    val bF_set = subst_b F;
    val map_F_fst = mk_map_of_bnf deads typ_pairs alphas bnf_F;
    val map_F_snd = mk_map_of_bnf deads typ_pairs alphas' bnf_F
    val sets_F_pairs = mk_sets_of_bnf (replicate live deads) (replicate live typ_pairs) bnf_F
    val wits_F = mk_wits_of_bnf
      (replicate (nwits_of_bnf bnf_F) deads)
      (replicate (nwits_of_bnf bnf_F) alphas) bnf_F;

    (* val map_closed_F = @{term "\<And>f x. x \<in> F \<Longrightarrow> map_F f x \<in> F"}; *)
    val (var_fs, names_lthy) = mk_Frees "f" typ_fs names_lthy;
    val (var_x, names_lthy) = mk_Frees "x" [typ_aF] names_lthy |>> the_single;
    val mem_x = HOLogic.mk_Trueprop (HOLogic.mk_mem (var_x, aF_set));
    val map_f = list_comb (map_F, var_fs);
    val mem_map = HOLogic.mk_Trueprop (HOLogic.mk_mem (map_f $ var_x, bF_set));
    val imp_map = Logic.mk_implies (mem_x, mem_map);
    val map_closed_F = fold_rev Logic.all var_fs (Logic.all var_x imp_map);

    (* val zip_closed_F =
      @{term "\<And>z. \<lbrakk>map_F fst z \<in> F; map_F snd z \<in> F\<rbrakk> \<Longrightarrow>
        \<exists>z' \<in> F. set_F z' \<subseteq> set_F z \<and> map_F fst z' = map_F fst z \<and> map_F snd z' = map_F snd z"}; *)
    val (var_z, names_lthy) = mk_Free "z" typ_pair names_lthy;
    val (var_z', names_lthy) = mk_Free "z'" typ_pair names_lthy;
    val (pairs, names_lthy) = mk_Frees "tmp" typ_pairs names_lthy;

    fun mk_map mfs f z = Term.list_comb (mfs, map (fst o Term.strip_comb o f) pairs) $ z;
    fun mk_set var = map (fn t => t $ var) sets_F_pairs;

    val (map_fst', map_fst) = apply2 (mk_map map_F_fst HOLogic.mk_fst) (var_z', var_z);
    val (map_snd', map_snd) = apply2 (mk_map map_F_snd HOLogic.mk_snd) (var_z', var_z);
    val mem_map_fst = HOLogic.mk_Trueprop (HOLogic.mk_mem (map_fst, aF_set));
    val mem_map_snd = HOLogic.mk_Trueprop (HOLogic.mk_mem (map_snd, aF_set'));
    val ex_conj = foldr1 HOLogic.mk_conj (map2 mk_leq (mk_set var_z') (mk_set var_z) @
      [HOLogic.mk_eq (map_fst', map_fst), HOLogic.mk_eq (map_snd', map_snd)]);
    val zip_concl = HOLogic.mk_Trueprop (mk_Bex pairF_set (absfree (dest_Free var_z') ex_conj));
    val zip_closed_F = Logic.all var_z (Logic.list_implies ([mem_map_fst, mem_map_snd], zip_concl));

    (* val wit_closed_F = @{term "wit_F a \<in> F"}; *)
    val (var_as, names_lthy) = mk_Frees "a" alphas names_lthy;
    val (var_bs, _) = mk_Frees "a" alphas names_lthy;
    val sets = mk_sets_of_bnf (replicate live deads) (replicate live alphas) bnf_F;
    val (Iwits, wit_goals) =
      prepare_wits false RepT wits opts alphas wits_F var_as var_bs sets lthy;
    val wit_closed_Fs =
      Iwits |> map (fn (I, wit_F) =>
        let
          val vars = map (nth var_as) I;
          val wit_a = list_comb (wit_F, vars);
        in fold_rev Logic.all vars (HOLogic.mk_Trueprop (HOLogic.mk_mem (wit_a, aF_set))) end);

    val goals = [map_closed_F, zip_closed_F] @ wit_closed_Fs @
      (case wits of NONE => [] | _ => wit_goals);

    fun after_qed ([map_closed_thm] :: [zip_closed_thm] :: wit_thmss) lthy =
          let
            val (wit_closed_thms, wit_thms) =
              (case wits of
                NONE => (map the_single wit_thmss, wit_thms_of_bnf bnf_F)
              | _ => chop (length wit_closed_Fs) (map the_single wit_thmss))

            (*  construct map set bd rel wit *)
            (* val map_G = @{term "\<lambda>f. Abs_G o map_F f o Rep_G"}; *)
            val Abs_Gb = subst_b Abs_G;
            val map_G = fold_rev lambda var_fs
                (HOLogic.mk_comp (HOLogic.mk_comp (Abs_Gb, map_f), Rep_G));
            val map_raw = fold_rev lambda var_fs map_f;

            (* val sets_G = [@{term "set_F o Rep_G"}]; *)
            val sets_F = mk_sets_of_bnf (replicate live deads) (replicate live alphas) bnf_F;
            val sets_G = map (fn set_F => HOLogic.mk_comp (set_F, Rep_G)) sets_F;

            (* val bd_G = @{term "bd_F"}; *)
            val bd_F = mk_bd_of_bnf deads alphas bnf_F;
            val bd_G = bd_F;

            (* val rel_G = @{term "\<lambda>R. BNF_Def.vimage2p Rep_G Rep_G (rel_F R)"}; *)
            val rel_F = mk_rel_of_bnf deads alphas betas bnf_F;
            val (typ_Rs, _) = strip_typeN live (fastype_of rel_F);

            val (var_Rs, names_lthy) = mk_Frees "R" typ_Rs lthy;
            val Rep_Gb = subst_b Rep_G;
            val rel_G = fold_rev absfree (map dest_Free var_Rs)
              (mk_vimage2p Rep_G Rep_Gb $ list_comb (rel_F, var_Rs));
            val rel_raw = fold_rev absfree (map dest_Free var_Rs) (list_comb (rel_F, var_Rs));

            (* val pred_G = @{term "\<lambda>P. pred_F P o Rep_G"}; *)
            val pred_F = mk_pred_of_bnf deads alphas bnf_F;
            val (typ_Ps, _) = strip_typeN live (fastype_of pred_F);

            val (var_Ps, names_lthy) = mk_Frees "P" typ_Ps names_lthy;
            val pred_G = fold_rev absfree (map dest_Free var_Ps)
              (HOLogic.mk_comp (list_comb (pred_F, var_Ps), Rep_G));
            val pred_raw = fold_rev absfree (map dest_Free var_Ps) (list_comb (pred_F, var_Ps));

            (* val wits_G = [@{term "Abs_G o wit_F"}]; *)
            val (var_as, _) = mk_Frees "a" alphas names_lthy;
            val wits_G =
              map (fn (I, wit_F) =>
                let
                  val vs = map (nth var_as) I;
                in fold_rev absfree (map dest_Free vs) (Abs_G $ (list_comb (wit_F, vs))) end)
              Iwits;

            (* tactics *)
            val Rep_thm = thm RS @{thm type_definition.Rep};
            val Abs_inverse_thm = thm RS @{thm type_definition.Abs_inverse};
            val Abs_inject_thm = thm RS @{thm type_definition.Abs_inject};
            val Rep_cases_thm = thm RS @{thm type_definition.Rep_cases};
            val Rep_inverse_thm = thm RS @{thm type_definition.Rep_inverse};

            fun map_id0_tac ctxt =
              HEADGOAL (EVERY' [rtac ctxt ext,
                SELECT_GOAL (unfold_thms_tac ctxt [map_id0_of_bnf bnf_F, id_apply, o_apply,
                  Rep_inverse_thm]),
                rtac ctxt refl]);

            fun map_comp0_tac ctxt =
              HEADGOAL (EVERY' [rtac ctxt ext,
                SELECT_GOAL (unfold_thms_tac ctxt [map_comp0_of_bnf bnf_F, o_apply,
                  Rep_thm RS (map_closed_thm RS Abs_inverse_thm)]),
                rtac ctxt refl]);

            fun map_cong0_tac ctxt =
              HEADGOAL (EVERY' ([SELECT_GOAL (unfold_thms_tac ctxt [o_apply]),
                rtac ctxt (([Rep_thm RS map_closed_thm, Rep_thm RS map_closed_thm] MRS
                  Abs_inject_thm) RS iffD2),
                rtac ctxt (map_cong0_of_bnf bnf_F)] @ replicate live (Goal.assume_rule_tac ctxt)));

            val set_map0s_tac =
              map (fn set_map => fn ctxt =>
                HEADGOAL (EVERY' [rtac ctxt ext,
                  SELECT_GOAL (unfold_thms_tac ctxt [set_map, o_apply,
                    Rep_thm RS (map_closed_thm RS Abs_inverse_thm)]),
                  rtac ctxt refl]))
              (set_map_of_bnf bnf_F);

            fun card_order_bd_tac ctxt = HEADGOAL (rtac ctxt (bd_card_order_of_bnf bnf_F));

            fun cinfinite_bd_tac ctxt = HEADGOAL (rtac ctxt (bd_cinfinite_of_bnf bnf_F));

            fun regularCard_bd_tac ctxt = HEADGOAL (rtac ctxt (bd_regularCard_of_bnf bnf_F));

            val set_bds_tac =
              map (fn set_bd => fn ctxt =>
                HEADGOAL (EVERY' [SELECT_GOAL (unfold_thms_tac ctxt [o_apply]), rtac ctxt set_bd]))
              (set_bd_of_bnf bnf_F);

            fun le_rel_OO_tac ctxt =
              HEADGOAL (EVERY' [rtac ctxt @{thm vimage2p_relcompp_mono},
                rtac ctxt ((rel_OO_of_bnf bnf_F RS sym) RS @{thm ord_eq_le_trans}),
                rtac ctxt @{thm order_refl}]);

            fun rel_OO_Grp_tac ctxt =
              HEADGOAL (EVERY' ([SELECT_GOAL (REPEAT_DETERM (HEADGOAL (rtac ctxt ext))),
                SELECT_GOAL (unfold_thms_tac ctxt [@{thm OO_Grp_alt}, mem_Collect_eq,
                  o_apply, @{thm vimage2p_def}, in_rel_of_bnf bnf_F, Bex_def, mem_Collect_eq]),
                rtac ctxt iffI,
                SELECT_GOAL (REPEAT_DETERM (HEADGOAL (eresolve_tac ctxt [exE, conjE]))),
                forward_tac ctxt
                  [zip_closed_thm OF (replicate 2 (Rep_thm RSN (2, @{thm ssubst_mem})))],
                assume_tac ctxt,
                SELECT_GOAL (REPEAT_DETERM (HEADGOAL (eresolve_tac ctxt [bexE, conjE]))),
                etac ctxt Rep_cases_thm,
                hyp_subst_tac ctxt,
                SELECT_GOAL (REPEAT_DETERM (HEADGOAL (rtac ctxt exI))),
                rtac ctxt conjI] @
                replicate live
                  (EVERY' [TRY o rtac ctxt conjI, etac ctxt @{thm order_trans}, assume_tac ctxt]) @
                [SELECT_GOAL (REPEAT_DETERM (HEADGOAL (rtac ctxt conjI))),
                REPEAT_DETERM_N 2 o EVERY'
                  [rtac ctxt (trans OF [iffD2 OF [Abs_inject_thm OF
                      [map_closed_thm OF [Rep_thm], Rep_thm]], Rep_inverse_thm]),
                  etac ctxt trans, assume_tac ctxt],
                SELECT_GOAL (REPEAT_DETERM (HEADGOAL (eresolve_tac ctxt [exE, conjE]))),
                rtac ctxt exI,
                rtac ctxt conjI] @
                replicate (live-1) (rtac ctxt conjI THEN' assume_tac ctxt) @
                [assume_tac ctxt,
                rtac ctxt conjI,
                REPEAT_DETERM_N 2 o EVERY'
                  [rtac ctxt (iffD1 OF [Abs_inject_thm OF [map_closed_thm OF [Rep_thm], Rep_thm]]),
                  etac ctxt (Rep_inverse_thm RS sym RSN (2, trans))]]));

            fun pred_set_tac ctxt =
              HEADGOAL (EVERY'
                [rtac ctxt (pred_set_of_bnf bnf_F RS @{thm arg_cong[of _ _ "\<lambda>f. f \<circ> _"]} RS trans),
                SELECT_GOAL (unfold_thms_tac ctxt (@{thms Ball_comp_iff conj_comp_iff})),
                rtac ctxt refl]);

            fun wit_tac ctxt =
              HEADGOAL (EVERY'
                (map (fn thm => (EVERY'
                  [SELECT_GOAL (unfold_thms_tac ctxt (o_apply ::
                    (wit_closed_thms RL [Abs_inverse_thm]))),
                  dtac ctxt thm, assume_tac ctxt]))
                wit_thms));

            val tactics = [map_id0_tac, map_comp0_tac, map_cong0_tac] @ set_map0s_tac @
              [card_order_bd_tac, cinfinite_bd_tac, regularCard_bd_tac] @ set_bds_tac @
              [le_rel_OO_tac, rel_OO_Grp_tac, pred_set_tac];

            val (bnf_G, lthy) = bnf_def Hardly_Inline (user_policy Note_Some) true I
              tactics wit_tac NONE map_b rel_b pred_b set_bs
              (((((((Binding.empty, AbsT), map_G), sets_G), bd_G), wits_G), SOME rel_G), SOME pred_G)
              lthy;

            val old_defs =
              {sets = set_defs_of_bnf bnf_G, map = map_def_of_bnf bnf_G, rel = rel_def_of_bnf bnf_G,
               pred = pred_def_of_bnf bnf_G};

            val unfold_morphism = Morphism.thm_morphism "BNF" (unfold_thms lthy defs);
            val (bnf_G, lthy) = morph_bnf_defs unfold_morphism bnf_G
              |> (fn bnf => note_bnf_defs bnf lthy);

            val quiet = exists (fn No_Warn_Transfer => true | _ => false) opts;

            val transfer_consts = mk_typedef_transfer_tacs bnf_F bnf_G
              {map_closed=map_closed_thm,typedef=thm} old_defs map_raw rel_raw pred_raw sets_F;
          in
            lthy |> BNF_Def.register_bnf plugins AbsT_name bnf_G |>
              mk_transfer_thms quiet bnf_F bnf_G AbsT_name transfer_consts Typedef
              {abs=typ_subst_atomic (alphas ~~ alphas') AbsT, rep=RepT, Ds0=map TFree Ds0,
               deads = deads, alphas=alphas, betas=alphas', gammas=betas, deltas=betas'} defs
          end
      | after_qed _ _ = raise Match;
  in
    (goals, after_qed, defs, lthy)
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
(* generalize Parse.type_const? *)
    ((parse_lift_opts -- parse_type_args_named_constrained -- Parse.binding --
      (\<^keyword>\<open>=\<close> |-- Parse.typ) -- 
      parse_wits -- parse_on_clause -- parse_map_rel_pred_bindings) >> linearize_mrbnf_cmd);

end;

end;
