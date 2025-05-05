signature MRSBNF_COMP = sig

  val mrsbnf_of_typ: bool -> (theory -> BNF_Def.fact_policy)
    -> (binding -> binding) -> (string * sort) list -> ((string * sort) * MRBNF_Def.var_type) list
    -> typ -> ((MRBNF_Comp.comp_cache * MRBNF_Comp.unfold_set) * local_theory)
    -> ((MRSBNF_Def.mrsbnf, MRBNF_Def.mrbnf) MRBNF_Util.either * (typ list * typ list))
        * ((MRBNF_Comp.comp_cache * MRBNF_Comp.unfold_set) * local_theory)

end

structure MRSBNF_Comp : MRSBNF_COMP = struct

open MRBNF_Util

fun mrsbnf_of lthy s = case MRSBNF_Def.mrsbnf_of lthy s of
  SOME mrsbnf => SOME (Inl mrsbnf, lthy)
  | NONE => (case MRBNF_Def.mrbnf_of lthy s of
    SOME mrbnf => SOME (Inr mrbnf, lthy)
    | NONE => Option.map (fn bnf =>
      apfst Inr (MRBNF_Def.register_bnf_as_mrbnf NONE bnf lthy)
    ) (BNF_Def.bnf_of lthy s)
  )

fun is_Inl (Inl _) = true
  | is_Inl _ = false

fun mrsbnf_of_typ _ _ qualify Ds0 var_types (T as TFree T') accum =
  (if member (op =) Ds0 T' then ((Inr MRBNF_Comp.DEADID_mrbnf, ([T], [])), accum) else
      (case map_filter (fn a => if fst a = T' then SOME (snd a) else NONE) var_types of
        [] => ((Inr MRBNF_Comp.ID_mrbnf, ([], [T])), accum)
        | [MRBNF_Def.Dead_Var] => error "var_types may only be Live, Free or Bound, use Ds0 for deads"
        | [var_type] =>
          let
            val qualify' = qualify o Binding.suffix_name ("_" ^ fst T')
            val (ID', accum') = MRBNF_Comp.demote_mrbnf qualify' [var_type] MRBNF_Comp.ID_mrbnf accum
          in ((Inr ID', ([], [T])), accum') end
        | _ => error "Same variable appears twice in var_types"
      )
    )
  | mrsbnf_of_typ _ _ _ _ _ (TVar _) _ = error "unexpected schematic variable"
  | mrsbnf_of_typ optim const_policy qualify' Ds0 var_types (T as Type (n, Ts)) (accum, lthy) = (case mrsbnf_of lthy n of
    NONE => ((Inr MRBNF_Comp.DEADID_mrbnf, ([T], [])), (accum, lthy))
    | SOME (outer, lthy) =>
      if optim andalso forall is_TFree Ts then
        let
          val mrbnf = case outer of
            Inl mrsbnf => hd (MRSBNF_Def.mrbnfs_of_mrsbnf mrsbnf)
            | Inr mrbnf => mrbnf;
          val mrbnf' = MRBNF_Def.morph_mrbnf (MRBNF_Util.subst_typ_morphism (
            snd (dest_Type (MRBNF_Def.T_of_mrbnf mrbnf)) ~~ Ts
          )) mrbnf;
          val deads = MRBNF_Def.deads_of_mrbnf mrbnf';
          val _ = case filter (Option.isSome o AList.lookup (op=) var_types o dest_TFree) deads of
            T'::_ => error ("Variable " ^ Syntax.string_of_typ lthy T' ^ " is forced dead by type " ^ Syntax.string_of_typ lthy T ^ " but was specified as other usage")
            | [] => ()
          val Ts' = subtract (op=) deads Ts;
          val _ = @{print} Ts'
          val var_types = map (AList.lookup (op=) var_types o dest_TFree) Ts';
          val var_types = @{map 3} (fn req => fn var_type => fn T => if member (op=) Ds0 (dest_TFree T) then
            MRBNF_Def.Dead_Var else the_default var_type req
          ) var_types (MRBNF_Def.var_types_of_mrbnf mrbnf) Ts';

          val (mrsbnf, accum) = if MRBNF_Def.var_types_of_mrbnf mrbnf = var_types then
              (outer, (accum, lthy))
            else case outer of
              Inl mrsbnf => error "TODO: Demote MRSBNF"
              | Inr mrbnf => apfst Inr (MRBNF_Comp.demote_mrbnf qualify' var_types mrbnf (accum, lthy));
        in ((mrsbnf, (inter (op=) Ts (deads @ map TFree Ds0), subtract (op=) (map TFree Ds0) Ts')), accum) end
      else
        let
          val name = Long_Name.base_name n;
          fun qualify i =
            let val namei = name ^ nonzero_string_of_int i;
            in qualify' o Binding.qualify true namei end;
          val mrbnf = case outer of
            Inl mrsbnf => hd (MRSBNF_Def.mrbnfs_of_mrsbnf mrsbnf)
            | Inr mrbnf => mrbnf

          val odead = MRBNF_Def.dead_of_mrbnf mrbnf;
          val olive = MRBNF_Def.live_of_mrbnf mrbnf;
          val obound = MRBNF_Def.bound_of_mrbnf mrbnf;
          val ofree = MRBNF_Def.free_of_mrbnf mrbnf;
          val Ds = map (fn i => TFree (string_of_int i, [])) (1 upto odead);
          val Us = snd (Term.dest_Type (MRBNF_Def.mk_T_of_mrbnf Ds (replicate olive dummyT) (replicate obound dummyT) (replicate ofree dummyT) mrbnf));
          val oDs_pos = map (fn x => find_index (fn y => x = y) Us) Ds
            |> filter (fn x => x >= 0);
          val oAs = map (fn (T, var_type) => case var_type of
            MRBNF_Def.Live_Var => NONE | _ => SOME T
          ) (Ts ~~ MRBNF_Def.var_types_of_mrbnf mrbnf)
          val oDs = map (nth Ts) oDs_pos;
          val ofree_bound_pos = map_filter I (map_index (fn (i, x) => case x of
            SOME _ => SOME i | NONE => NONE
          ) oAs)
          val Ts' = map (nth Ts) (subtract (op =) (oDs_pos @ ofree_bound_pos) (0 upto length Ts - 1));

          val ((inners, (Dss, Ass)), (accum, lthy)) =
            apfst (apsnd split_list o split_list) (@{fold_map 2}
              (fn i => mrsbnf_of_typ optim const_policy (qualify i) Ds0 var_types)
              (if length Ts' = 1 then [0] else 1 upto length Ts') Ts' (accum, lthy));

          val _ = @{print} T
          val Xs = rev (Term.add_tfreesT T []);
          val Xs' = map (swap o `(the_default MRBNF_Def.Live_Var o AList.lookup (op=) var_types)) Xs
        in if exists is_Inl inners orelse is_Inl outer then
          let
            val (outer', lthy) = case outer of
              Inl mrsbnf => (mrsbnf, lthy)
              | Inr mrbnf => MRSBNF_Def.mrsbnf_of_mrbnf mrbnf lthy
            val (inners', lthy) = fold_map (fn Inl mrsbnf => (fn lthy => (mrsbnf, lthy))
              | Inr mrbnf => MRSBNF_Def.mrsbnf_of_mrbnf mrbnf
            ) inners lthy;
            val _ = @{print} (outer' :: inners')
            val _ = ()
          in error "TODO: compose mrsbnfs" end
        else
          apfst (apfst Inr) (MRBNF_Comp.compose_mrbnf MRBNF_Def.Smart_Inline qualify (distinct (op=) o flat)
            mrbnf (map (fn Inr x => x | _ => error "impossible") inners) oDs Dss oAs Ass Xs' (accum, lthy)
          )
        end
    );

end