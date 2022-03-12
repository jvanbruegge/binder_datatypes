theory MRBNF_Composition_Tests
  imports "../thys/MRBNF_Composition"
begin

ML \<open>
  val num_tests = 1
  val num_max_vars = 14
\<close>

declare [[ML_print_depth = 10000]]

ML_file \<open>../Tools/mrbnf_comp_tactics.ML\<close>
ML_file \<open>../Tools/mrbnf_comp.ML\<close>

ML \<open>
open MRBNF_Def

val possible_vars = [@{typ 'a}, @{typ 'b}, @{typ 'c}, @{typ 'd}, @{typ 'e}, @{typ 'f}, @{typ 'g}, @{typ 'h}, @{typ 'i}, @{typ 'j}, @{typ 'k}, @{typ 'l}, @{typ 'm}, @{typ 'n}, @{typ 'o}, @{typ 'p}, @{typ 'q}, @{typ 'r}, @{typ 's}, @{typ 't}, @{typ 'u}, @{typ 'v}, @{typ 'w}, @{typ 'x}, @{typ 'y}, @{typ 'z}]

fun mk_vars random_range force_live =
  let
    val vars =
      fold (fn i => fn vars =>
        let
          val possible_vars' = subtract (fn (a, b) => fst a = b) vars possible_vars
          val var = nth possible_vars' (random_range 0 (length possible_vars' - 1))

          val var_type = case random_range 0 3 of
            0 => Live_Var
            | 1 => Free_Var
            | 2 => Bound_Var
            | 3 => Dead_Var
        in
          (var, var_type)::vars
        end
      ) (1 upto random_range 1 num_max_vars) []
    val idx = random_range 0 (length vars - 1)
    val vars' =
      if not (member (op=) (map snd vars) Live_Var) then
        take idx vars @ [(fst (nth vars idx), Live_Var)] @ drop (idx+1) vars
      else
        vars
    val _ = \<^assert> (member (op=) (map snd vars') Live_Var)
  in
    vars'
  end;

fun count_live vars = length (filter (equal Live_Var o snd) vars)
fun cheat ctxt = Skip_Proof.cheat_tac ctxt 1

fun seperate_deads [] = ([], [])
  | seperate_deads ((x as (_,Dead_Var))::xs) = apsnd (cons x) (seperate_deads xs)
  | seperate_deads (x::xs) = apfst (cons x) (seperate_deads xs)

fun mk_tacs num_nondead =
  {
    map_id0 = cheat,
    map_comp0 = cheat,
    map_cong0 = cheat,
    set_map0 = replicate num_nondead cheat,
    infinite_regular_card_order = cheat,
    set_bd = replicate num_nondead cheat,
    le_rel_OO = cheat,
    in_rel = cheat,
    pred_set = cheat,
    wit = REPEAT_DETERM o cheat
  };

val bnf_parser = BNF_FP_Def_Sugar.parse_co_datatype_cmd BNF_Util.Least_FP BNF_LFP.construct_lfp
fun filtered_input str =
  filter Token.is_proper (Token.explode (Thy_Header.get_keywords' @{context}) Position.none str)
fun parse p input = Scan.finite Token.stopper (Scan.error p) input

fun define_mrbnf name vars lthy =
  let
    fun var_type_letter v = case v of
      Live_Var => "L" | Free_Var => "F" | Bound_Var => "B"
    fun var_type_prefix v i name = case v of
      Dead_Var => "dead "
      | _ => "set" ^ var_type_letter v ^ string_of_int i ^ "_" ^ name ^ ": "
    val var_strs = map_index (fn (i, (TFree (s, _), var_type)) => var_type_prefix var_type i name ^ s) vars
    val var_str = fold (fn s => fn str => str ^ ", " ^ s) (tl var_strs) (hd var_strs)
    val str = "(" ^ var_str ^ ") " ^ name ^ " = Ctor for map: map_" ^ name ^ " rel: rel_" ^ name
    val lthy' = fst (parse bnf_parser (filtered_input str)) lthy
    val (nondeads, deads) = seperate_deads vars
    val num_nondead = length nondeads
    val num_live = length (filter (equal Live_Var o snd) vars)
    val tacs = mk_tacs num_nondead;
    val bnf = the (BNF_Def.bnf_of lthy' ("MRBNF_Composition_Tests." ^ name))
    val (((lives, lives''), deads), lthy'') = lthy'
      |> Ctr_Sugar_Util.mk_TFrees num_nondead
      ||>> Ctr_Sugar_Util.mk_TFrees (length (filter (equal Live_Var o snd) nondeads))
      ||>> Ctr_Sugar_Util.mk_TFrees' (map (Type.sort_of_atyp o fst) deads)
    fun mk_lives' ((_, Live_Var)::vs) (_::AS) (B::BS) = B::mk_lives' vs AS BS
      | mk_lives' (_::vs) (A::AS) BS = A::mk_lives' vs AS BS
      | mk_lives' [] _ _ = []
    val lives' = mk_lives' nondeads lives lives''
    val nwits = BNF_Def.nwits_of_bnf bnf
    val rel_body = fold (fn (A, B) => fn (t, n) => if A = B then
      (t $ HOLogic.eq_const A, n) else
      (t $ Bound n, n - 1)
    ) (lives ~~ lives') (BNF_Def.mk_rel_of_bnf deads lives lives' bnf, num_live - 1) |> fst
    val rel = fold_rev (fn (A, B) => fn t =>
      if A = B then t else Term.absdummy (A --> B --> @{typ bool}) t
    ) (lives ~~ lives') rel_body
    val pred_body = fold (fn (A, B) => fn (t, n) => if A = B then
      (t $ Term.absdummy A @{term True}, n) else
      (t $ Bound n, n - 1)
    ) (lives ~~ lives') (BNF_Def.mk_pred_of_bnf deads lives bnf, num_live - 1) |> fst
    val pred = fold_rev (fn (A, B) => fn t =>
      if A = B then t else Term.absdummy (A --> @{typ bool}) t
    ) (lives ~~ lives') pred_body
  in
    mrbnf_def Do_Inline (K Dont_Note) false I tacs (SOME deads) NONE
      Binding.empty Binding.empty Binding.empty []
    (((((((BNF_Def.name_of_bnf bnf,
    BNF_Def.mk_T_of_bnf deads lives bnf), BNF_Def.mk_map_of_bnf deads lives lives' bnf),
    map (fn ((_, var_type), x) => (var_type, x)) (nondeads ~~ BNF_Def.mk_sets_of_bnf (replicate num_nondead deads) (replicate num_nondead lives) bnf)),
    BNF_Def.mk_bd_of_bnf deads lives bnf),
    map snd (BNF_Def.mk_wits_of_bnf (replicate nwits deads) (replicate nwits lives) bnf)),
    SOME rel), SOME pred)
    lthy''
  end

exception RANDOM;

fun gen_pseudorandom seed =
  let
    val random_seed = Synchronized.var "random_seed" seed
    val a = 16807.0;
    val m = 2147483647.0;

    fun rmod x y = x - y * Real.realFloor (x / y);

    fun random () =
      Synchronized.change_result random_seed
        (fn s =>
          let val r = rmod (a * s) m
          in (r, r) end);

    fun random_range l h =
      if h < l orelse l < 0 then raise RANDOM
      else l + Real.floor (rmod (random ()) (real (h - l + 1)))
  in random_range end

fun run_testcase seed i lthy =
  let
    val random_range = gen_pseudorandom seed
    val G_vars = mk_vars random_range true
    val (G_nondeads, G_deads) = seperate_deads G_vars
    val G_num_live = count_live G_vars
    val F_varss = map (fn _ => mk_vars random_range false) (1 upto G_num_live)
    val (lthy1, Fs) = fold_index (fn (j, vars) => fn (lthy1, Fs') =>
        let
          val name = "F_" ^ string_of_int i ^ "_" ^ string_of_int j
          val (mrbnf, lthy2) = define_mrbnf name vars lthy1
        in
          (lthy2, Fs' @ [mrbnf])
        end
      ) F_varss (lthy, [])
    val name = "G_" ^ string_of_int i
    val (G, lthy2) = define_mrbnf name G_vars lthy1
    fun qualify i =
      let val namei = name ^ BNF_Util.nonzero_string_of_int i;
            in Binding.qualify true namei end
    fun flatten_tyargs Ass = fold (fn As => fn res => res @ subtract (uncurry equal) res As) Ass []
    val G_Ts = map (fn (x, var_type) => if var_type = Live_Var then NONE else SOME x) G_nondeads
    val ((mrbnf, tys), (_, lthy3)) = (MRBNF_Comp.compose_mrbnf Do_Inline qualify flatten_tyargs
      G Fs (map fst G_deads) (map (map fst o snd o seperate_deads) F_varss) G_Ts (map (map fst o fst o seperate_deads) F_varss)
      ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy2))
  in
    ((mrbnf, tys), lthy3)
  end

fun void f lthy = (f lthy ; lthy)
\<close>

(*ML \<open>
Multithreading.parallel_proofs := 1;
\<close>*)
(*local_setup \<open>fn lthy =>
let
  val xs = map (fn i =>
    let
      val seed = Random.random ()
      val lthy'_opt = try (run_testcase seed i) lthy
      val str = (case lthy'_opt of
        NONE => "failure: "
        | SOME x => "success: ")
       ^ "run with local_setup \\" ^ "<open>void (run_testcase " ^ string_of_real seed ^ " 1)\\" ^ "<close>"
      val _ = Output.system_message str
    in str
  end
  ) (1 upto num_tests)
  val _ = @{print} xs
in
  lthy
end
\<close>*)

(********************)
(* regression tests *)
(********************)

(* passing *)
(*local_setup \<open>void (run_testcase 1123455898.0 1)\<close>*)
(*local_setup \<open>void (run_testcase 1509285558.0 1)\<close>*)
(*local_setup \<open>void (run_testcase 849404232.0 1)\<close>*)
(*local_setup \<open>void (run_testcase 18657239.0 1)\<close>*)
(*local_setup \<open>void (run_testcase 39603411.0 1)\<close>*)
(*local_setup \<open>void (run_testcase 1968651577.0 1)\<close>*)
(*local_setup \<open>void (run_testcase 276693098.0 1)\<close>*)
(*local_setup \<open>void (run_testcase 235821654.0 1)\<close>*)
(*local_setup \<open>void (run_testcase 2105919395.0 1)\<close>*)
(*local_setup \<open>void (run_testcase 1931263361.0 1)\<close>*)
(*local_setup \<open>void (run_testcase 1192521015.0 1)\<close>*)
(*local_setup \<open>void (run_testcase 1791380479.0 1)\<close>*)
(*local_setup \<open>void (run_testcase 10979613.0 1)\<close>*)
(*local_setup \<open>void (run_testcase 1078802331.0 1)\<close>*)
(*local_setup \<open>void (run_testcase 1675467569.0 1)\<close>*)
(*local_setup \<open>void (run_testcase 803435212.0 1)\<close>*)
(*local_setup \<open>void (run_testcase 1347210063.0 1)\<close>*)
(*local_setup \<open>void (run_testcase 1998245696.0 1)\<close>*)
(*local_setup \<open>void (run_testcase 1392378882.0 1)\<close>*)
(*local_setup \<open>void (run_testcase 846505310.0 1)\<close>*)
(*local_setup \<open>void (run_testcase 135583795.0 1)\<close>*)
(*local_setup \<open>void (run_testcase 226345496.0 1)\<close>*)

end
