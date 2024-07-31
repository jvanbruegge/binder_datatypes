signature BINDER_DATATYPE_PARSER =
sig
end
structure Binder_Datatype_Parser : BINDER_DATATYPE_PARSER =
struct

open Ctr_Sugar_Util

fun parse_selector_typ s =
  let val ((sel, T), s') =
    (Parse.name --| @{keyword "::"} -- Parse.typ
    || Parse.typ >> pair "") s
  in ((if sel = "" then NONE else SOME (Symbol.trim_blanks sel), T), s') end

val parse_spec_arg = @{keyword "("} |-- BNF_Util.parse_binding_colon -- parse_selector_typ --| @{keyword ")"}
  || parse_selector_typ >> pair Binding.empty

val parse_binder_specs = Parse.enum1 "|" (Ctr_Sugar.parse_ctr_spec Parse.binding parse_spec_arg -- Parse.opt_mixfix
  -- Scan.option (@{keyword binds} |-- (*Parse.enum1 ";"*) (Parse.list1 Parse.name --| @{keyword in} -- Parse.list1 Parse.name))
  )

val parse_type_arg_constrained =
  Parse.type_ident -- Scan.option (\<^keyword>\<open>::\<close> |-- Parse.!!! Parse.sort);

val parse_type_arg_named_constrained =
   (Parse.reserved "dead" >> K (SOME MRBNF_Def.Dead_Var, Binding.empty)
     || (Scan.option (Parse.reserved "free" || Parse.reserved "bound") >>
          Option.map (fn "free" => MRBNF_Def.Free_Var | _ => MRBNF_Def.Bound_Var)
        ) -- BNF_Util.parse_opt_binding_colon
   ) -- parse_type_arg_constrained;

val parse_type_args_named_constrained =
  parse_type_arg_constrained >> (single o pair (NONE, Binding.empty)) ||
  \<^keyword>\<open>(\<close> |-- Parse.!!! (Parse.list1 parse_type_arg_named_constrained --| \<^keyword>\<open>)\<close>) ||
  Scan.succeed [];

val parse_subst_binding = Parse.name --| \<^keyword>\<open>:\<close> -- Parse.binding;

fun extract_map_rel_pred ("vvsubst", m) = (fn (_, r) => (m, r))
  | extract_map_rel_pred ("tvsubst", r) = (fn (m, _) => (m, r))
  | extract_map_rel_pred (s, _) = error ("Unknown label " ^ quote s ^ " (expected \"vvsubst\" or \"tvsubst\")");

val parse_subst_bindings =
  @{keyword for} |-- Scan.repeat parse_subst_binding
    >> (fn ps => fold extract_map_rel_pred ps (Binding.empty, Binding.empty))
  || Scan.succeed (Binding.empty, Binding.empty);

val parse_binder_datatype = Parse.and_list1 (
  parse_type_args_named_constrained -- Parse.binding -- Parse.opt_mixfix --
  (@{keyword =} |-- parse_binder_specs) -- parse_subst_bindings
);

fun create_ctor_spec T_names ((((sel, name), xs), mixfix), binds) (lthy, params) =
  let
    fun find_names' [] _ _ = []
      | find_names' (x::xs) curr b =
        if Symbol.is_letter x
        then find_names' xs (x::curr) b
        else
          if b
          then (if x = ":" then implode (rev curr) :: find_names' xs [] false else find_names' xs [] false)
          else (if x = ":" then find_names' xs curr true else find_names' xs [] false)
    fun find_names s = find_names' (Symbol.explode s) [] false

    val names = maps (find_names o YXML.content_of o snd o snd) xs;
    fun mk_typedecl name = Typedecl.basic_typedecl {final = true} (Binding.name name, 0, NoSyn)
    val (fake_names, lthy) = fold_map mk_typedecl names lthy;

    val (sels, Ts) = split_list (map (apsnd (Syntax.read_typ lthy) o snd) xs);

    fun fold_map_typ f (Type (n, Ts)) x =
      let val (Ts', x') = fold_map (fold_map_typ f) Ts x
      in f (Type (n, Ts')) x' end
      | fold_map_typ f T x = f T x;

    val (Ts, (params, lthy)) = case binds of
      NONE => (Ts, (params, lthy))
      | SOME (vrs, ts) =>
        let
          val Ts = map2 (fn NONE => I | SOME sel => fn T =>
            Type (@{type_name var_selector}, [Type ("MRBNF_Recursor." ^ sel, []), T])
          ) sels Ts;
        in fold_map (fn T => fold_map_typ (fn T => fn acc as (params, lthy) => case T of
          orig_T as Type (@{type_name var_selector}, [Type (sel, []), T]) =>
            let val sel = MRBNF_Util.short_type_name sel;
            in if member (op=) vrs sel then
              case find_index (curry (op=) T) (the (Symtab.lookup params "free")) of
                ~1 =>
                  let
                    val (T', lthy) = apfst hd (BNF_Util.mk_TFrees 1 lthy);
                    val rm = remove (op=) T;
                  in (T', (params
                    |> Symtab.map_entry "bound" (cons T')
                    |> Symtab.map_entry "free" (cons T)
                    |> Symtab.map_entry "pfree" rm
                    |> Symtab.map_entry "plive" rm
                  , lthy)) end
                | n => (nth (the (Symtab.lookup params "bound")) n, acc)
            else (orig_T, acc)
          end
          | _ => (T, acc)
        ) T #-> fold_map_typ (fn T => fn acc as (params, lthy) => case T of
          Type (@{type_name var_selector}, [Type (sel, []), T]) =>
            let val sel = MRBNF_Util.short_type_name sel;
            in if member (op=) ts sel then
                case try (member (op=) T_names o fst o dest_Type) T of
                  SOME true => (case the (Symtab.lookup params "brec") of
                    [] =>
                      let val (T', lthy) = apfst hd (BNF_Util.mk_TFrees 1 lthy);
                      in (T', (Symtab.map_entry "brec" (cons T') params, lthy)) end
                    | x::_ => (x, acc))
                  | _ => error "can only bind in recursive subterms"
              else (T, acc)
            end
          | _ => (T, acc)
      )) Ts (params, lthy) end;

    val (Ts, (params, lthy)) = fold_map (fold_map_typ (fn T => fn acc as (params, lthy) =>
      case try (fst o dest_Type) T of
        NONE => (T, acc)
      | SOME name =>
        if member (op=) T_names name
        then case the (Symtab.lookup params "rec") of
          [] => let val (T', lthy) = apfst hd (BNF_Util.mk_TFrees 1 lthy);
                in (T', (Symtab.map_entry "rec" (cons T') params, lthy)) end
          | (x::_) => (x, acc)
        else (T, acc)
    )) Ts (params, lthy);

    val spec = ((Binding.name_of name, mixfix), Ts)
   in (spec, (lthy, params)) end

fun create_binder_spec T_names ((((params, b), mixfix), ctors), (vvsubst_b, tvsubst_b)) lthy =
  let
    fun prepare_type_arg (T, sort) =
      let val TFree (s, _) = Syntax.parse_typ lthy T
      in resort_tfree_or_tvar @{sort type} (TFree (s, Typedecl.read_constraint lthy sort)) end;

    (* This should be just a record, but the lack of record update syntax in ML makes that way too painful *)
    val params' = Symtab.make [("pfree", []), ("pbound", []), ("plive", []), ("dead", []), ("free", []), ("bound", []), ("rec", []), ("brec", [])];
    val Ts = map (map_prod I prepare_type_arg) params;

    val lthy = fold (Variable.declare_typ o snd) Ts lthy;

    val params = fold_rev (fn ((ann, _), T) => Symtab.map_entry (case ann of
      NONE => "plive" | SOME MRBNF_Def.Free_Var => "pfree" | SOME MRBNF_Def.Bound_Var => "plive" | _ => "dead"
    ) (cons T)) Ts params';

    val (ctors, (lthy, params)) = fold_map (create_ctor_spec T_names) ctors (lthy, params);
    fun flat s t = rev (map (rpair t o dest_TFree) (the (Symtab.lookup params s)));

    val brecs = flat "brec" MRBNF_Def.Live_Var
    val recs = flat "rec" MRBNF_Def.Live_Var
    val bounds = flat "bound" MRBNF_Def.Bound_Var;
    val vars =
      flat "free" MRBNF_Def.Free_Var
      @ flat "pfree" MRBNF_Def.Free_Var
      @ flat "plive" MRBNF_Def.Live_Var
      @ flat "pbound" MRBNF_Def.Bound_Var
      @ bounds @ brecs @ recs;

    fun with_def bnd def = if Binding.is_empty bnd then
        Binding.suffix_name ("_" ^ Binding.name_of b) def
      else bnd

    val spec = {
      fp_b = b,
      ctors = ctors,
      vars = vars,
      binding_rel = map (K (0 upto length brecs - 1)) bounds,
      rec_vars = length brecs + length recs,
      map_b = with_def vvsubst_b @{binding vvsubst},
      tvsubst_b = with_def tvsubst_b @{binding tvsubst}
    } : MRBNF_Sugar.spec;
  in (spec, lthy) end

fun create_binder_specs specs lthy =
  let
    fun add_fake_type ((((params, b), mixfix), _), _) =
      Typedecl.basic_typedecl {final = true} (b, length params, Mixfix.reset_pos mixfix)
    val (fake_T_names, fake_lthy) = fold_map add_fake_type specs lthy;

    val (specs, fake_lthy) = fold_map (create_binder_spec fake_T_names) specs fake_lthy;
  in MRBNF_Sugar.create_binder_datatype (hd specs) lthy end;

val _ =
  Outer_Syntax.local_theory @{command_keyword binder_datatype}
    "create a binding-aware datatype"
    (parse_binder_datatype >> create_binder_specs)

end