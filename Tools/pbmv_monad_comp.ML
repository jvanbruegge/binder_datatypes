signature PBMV_MONAD_COMP = sig

  val id_bmv_monad: BMV_Monad_Def.bmv_monad
  val mk_id_bmv_monad: string * sort -> BMV_Monad_Def.bmv_monad

  val pbmv_monad_of_typ: bool -> BNF_Def.inline_policy -> (theory -> BNF_Def.fact_policy)
    -> (binding -> binding) -> typ -> (thm list * local_theory)
    -> BMV_Monad_Def.bmv_monad option * (thm list * local_theory)
end

structure PBMV_Monad_Comp : PBMV_MONAD_COMP = struct

open MRBNF_Util

val id_bmv_monad = the (BMV_Monad_Def.pbmv_monad_of @{context} "BMV_Monad.ID");

fun mk_id_bmv_monad free = BMV_Monad_Def.morph_bmv_monad (
  MRBNF_Util.subst_typ_morphism [(hd (BMV_Monad_Def.frees_of_bmv_monad id_bmv_monad), TFree free)]
) id_bmv_monad;

fun pbmv_monad_of_typ _ _ _ _ (TFree x) accum = (SOME (mk_id_bmv_monad x), accum)
  | pbmv_monad_of_typ _ _ _ _ (TVar _) _ = error "unexpected schematic variable"
  | pbmv_monad_of_typ optim const_policy inline_policy qualify' (T as Type (n, Ts)) (accum, lthy) =
    let val (bmv_opt, lthy) = case BMV_Monad_Def.pbmv_monad_of lthy n of
      SOME bmv => (SOME bmv, lthy)
      | NONE => case BNF_Def.bnf_of lthy n of
        SOME bnf =>
          let val (bmv, lthy) = BMV_Monad_Def.pbmv_monad_of_bnf bnf lthy
          in (SOME bmv, BMV_Monad_Def.register_pbmv_monad n bmv lthy) end
        | NONE => (NONE, lthy);
    in case bmv_opt of
      NONE => (NONE, (accum, lthy))
      | SOME bmv => if null (BMV_Monad_Def.lives_of_bmv_monad bmv) then
          let val T = nth (BMV_Monad_Def.ops_of_bmv_monad bmv) (BMV_Monad_Def.leader_of_bmv_monad bmv)
          in (SOME (BMV_Monad_Def.morph_bmv_monad (MRBNF_Util.subst_typ_morphism (
            rev (map TFree (Term.add_tfreesT T []) @ map TVar (Term.add_tvarsT T [])) ~~ Ts
          )) bmv), (accum, lthy)) end
        else let
          val name = Long_Name.base_name n;

          fun qualify i =
              let val namei = name ^ nonzero_string_of_int i;
              in qualify' o Binding.qualify true namei end;

          val leader = BMV_Monad_Def.leader_of_bmv_monad bmv;
          val T = nth (BMV_Monad_Def.ops_of_bmv_monad bmv) leader;
          val bmv = BMV_Monad_Def.morph_bmv_monad (
            MRBNF_Util.subst_typ_morphism (snd (dest_Type T) ~~ Ts)
          ) bmv;
          val bmv = BMV_Monad_Def.morph_bmv_monad (MRBNF_Util.subst_typ_morphism (
             BMV_Monad_Def.lives'_of_bmv_monad bmv ~~ BMV_Monad_Def.lives_of_bmv_monad bmv
          )) bmv;
          val live_Ts = BMV_Monad_Def.lives_of_bmv_monad bmv;

          val qualifies = map qualify (1 upto length live_Ts);
          val (bmv_opts, (accum, lthy)) = @{fold_map 2} (pbmv_monad_of_typ optim const_policy inline_policy) qualifies live_Ts (accum, lthy)
          val bmvs = map2 (fn T => fn NONE => Inr T | SOME bmv => Inl bmv) live_Ts bmv_opts;
        in if exists Option.isSome bmv_opts then
          let val ((bmv, unfold_set), lthy) = BMV_Monad_Def.compose_bmv_monad (qualify 0) bmv bmvs lthy;
          in (SOME bmv, (unfold_set @ accum, lthy)) end
        else
          (NONE, (accum, lthy))
        end
    end;

end