signature MRBNF_RECURSOR =
sig
  type 'a termlike_axioms = {
    map_id0: 'a,
    map_comp0: 'a,
    map_id_on_FVars: 'a list,
    map_inv_FVars: 'a list
  };

  type 'a termlike = {
    T: typ,
    FVars: term list,
    map: term,
    axioms: 'a termlike_axioms
  };
  val map_termlike: ('a -> 'b) -> 'a termlike -> 'b termlike;
  val ap_termlike_axioms: ('a -> 'b) termlike_axioms -> 'a termlike_axioms
    -> 'b termlike_axioms

  val create_binding_recursor: (Proof.context -> tactic) termlike -> local_theory -> local_theory;
end

structure MRBNF_Recursor : MRBNF_RECURSOR =
struct

open BNF_Util
open MRBNF_Util

type 'a termlike_axioms = {
  map_id0: 'a,
  map_comp0: 'a,
  map_id_on_FVars: 'a list,
  map_inv_FVars: 'a list
};

type 'a termlike = {
  T: typ,
  FVars: term list,
  map: term,
  axioms: 'a termlike_axioms
};

fun map_termlike_axioms f x = {
  map_id0 = f (#map_id0 x),
  map_comp0 = f (#map_comp0 x),
  map_id_on_FVars = map f (#map_id_on_FVars x),
  map_inv_FVars = map f (#map_inv_FVars x)
}
fun ap_termlike_axioms fx y = {
  map_id0 = (#map_id0 fx) (#map_id0 y),
  map_comp0 = (#map_comp0 fx) (#map_comp0 y),
  map_id_on_FVars = map2 (curry op|>) (#map_id_on_FVars y) (#map_id_on_FVars fx),
  map_inv_FVars =  map2 (curry op|>) (#map_inv_FVars y) (#map_inv_FVars fx)
};

fun map_termlike f x = {
  T = #T x,
  FVars = #FVars x,
  map = #map x,
  axioms = map_termlike_axioms f (#axioms x)
};

fun mk_bij t = t
  |> fastype_of
  |> dest_funT
  |> apply2 HOLogic.mk_UNIV
  |-> BNF_LFP_Util.mk_bij_betw t;

fun create_binding_recursor D lthy =
  let
    fun mk_goals term_structure =
      let
        val T = #T term_structure;
        val mapx = #map term_structure;
        val vars = snd (dest_Type T);
        val n = length vars;

        val ((((fs, gs), d), xs), lthy') =
          lthy
          |> mk_Frees "f" (map2 (curry op -->) vars vars)
          ||>> mk_Frees "g" (map2 (curry op -->) vars vars)
          ||>> apfst hd o mk_Frees "d" [T]
          ||>> mk_Frees "a" vars;

        fun mk_supp_bound h = HOLogic.mk_Trueprop (mk_ordLess (mk_card_of (mk_supp h)) (
          mk_card_of (HOLogic.mk_UNIV (fst (dest_funT (fastype_of h))))
        ));
        fun interlace [] [] = []
          | interlace (x::xs) (y::ys) = x::y::interlace xs ys

        fun add_f_prems hs = fold_rev (fn a => fn b => Logic.implies $ a $ b) (
          interlace (map (HOLogic.mk_Trueprop o mk_bij) hs) (map mk_supp_bound hs)
        )
      in {
        map_id0 = HOLogic.mk_Trueprop (
          HOLogic.eq_const (T --> T) $
          Term.list_comb (mapx, map HOLogic.id_const vars) $
          HOLogic.id_const T
        ),
        map_comp0 = fold_rev Logic.all (fs @ gs) (add_f_prems (fs @ gs) (HOLogic.mk_Trueprop (
          HOLogic.eq_const (T --> T) $
            (Term.list_comb (mapx, map2 (curry HOLogic.mk_comp) fs gs)) $
            (HOLogic.mk_comp (
              Term.list_comb (mapx, fs),
              Term.list_comb (mapx, gs)
            ))
        ))),
        map_id_on_FVars = map (fn i =>
          let val a = nth xs i in
            fold_rev Logic.all (d::fs) (add_f_prems fs (
              Logic.implies $ (Logic.all a (Logic.implies $
                HOLogic.mk_Trueprop (HOLogic.mk_mem (a, nth (#FVars term_structure) i $ d)) $
                mk_Trueprop_eq (nth fs i $ a, a)
              )) $
              mk_Trueprop_eq (Term.list_comb (mapx, fs) $ d, d)
            ))
          end) (0 upto n - 1),
        map_inv_FVars = map (fn i =>
          let
            val a = nth xs i;
            val FVars = nth (#FVars term_structure) i;
          in
            fold_rev Logic.all (a::d::fs) (add_f_prems fs (mk_Trueprop_eq (
              HOLogic.mk_mem (a, FVars $ (Term.list_comb (mapx, fs) $ d)),
              HOLogic.mk_mem (mk_inv (nth fs i) $ a, FVars $ d)
            )))
          end
        ) (0 upto n - 1)
      }
    end;

    fun prove goal tac = Goal.prove_sorry lthy [] [] goal (fn {context,...} => tac context)

    val D_thms = ap_termlike_axioms (map_termlike_axioms prove (mk_goals D)) (#axioms D)
    val _ = @{print} D_thms
  in
    lthy
  end;

end
