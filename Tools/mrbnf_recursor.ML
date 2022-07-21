signature MRBNF_RECURSOR =
sig
  type 'a parameter_axioms = {
    Pmap_id0: 'a,
    Pmap_comp0: 'a,
    Pmap_cong_ids: 'a list,
    in_PFVars_Pmap: 'a list,
    small_PFVars: 'a list
  };

  type 'a parameter = {
    P: typ,
    PFVars: term list,
    Pmap: term,
    axioms: 'a parameter_axioms
  };

  type 'a model_axioms = {
    Umap_id0: 'a,
    Umap_comp0: 'a,
    Umap_cong_ids: 'a list,
    in_UFVars_Umap: 'a list
  };

  type 'a model = {
    U: typ,
    term_quotient: { qT: typ, qmap: term } option,
    UFVars: term list,
    Umap: term,
    Uctor: term,
    parameters: 'a parameter,
    axioms: 'a model_axioms
  };

  val create_binding_recursor: (Proof.context -> tactic) model -> local_theory -> local_theory;
end

structure MRBNF_Recursor : MRBNF_RECURSOR =
struct

open BNF_Util
open MRBNF_Util

type 'a parameter_axioms = {
  Pmap_id0: 'a,
  Pmap_comp0: 'a,
  Pmap_cong_ids: 'a list,
  in_PFVars_Pmap: 'a list,
  small_PFVars: 'a list
};

type 'a parameter = {
  P: typ,
  PFVars: term list,
  Pmap: term,
  axioms: 'a parameter_axioms
};

type 'a model_axioms = {
  Umap_id0: 'a,
  Umap_comp0: 'a,
  Umap_cong_ids: 'a list,
  in_UFVars_Umap: 'a list
};

type 'a model = {
  U: typ,
  term_quotient: { qT: typ, qmap: term } option,
  UFVars: term list,
  Umap: term,
  Uctor: term,
  parameters: 'a parameter,
  axioms: 'a model_axioms
};

fun mk_bij t = t
  |> fastype_of
  |> dest_funT
  |> apply2 HOLogic.mk_UNIV
  |-> BNF_LFP_Util.mk_bij_betw t;

fun mk_termlike_goals quotient_opt T mapx FVars lthy =
  let
    val maybe_strip_last = if is_some quotient_opt then fst o split_last else I;
    val vars = map (fst o dest_funT) (maybe_strip_last (fst (strip_fun_type (fastype_of mapx))));
    val n = length vars;

    val (((((fs, gs), d), t), xs), lthy') =
      lthy
      |> mk_Frees "f" (map2 (curry op -->) vars vars)
      ||>> mk_Frees "g" (map2 (curry op -->) vars vars)
      ||>> apfst hd o mk_Frees "d" [T]
      ||>> mk_Frees "t" (the_default [] (Option.map (single o #qT) quotient_opt))
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
    map_id0 = fold_rev Logic.all t (HOLogic.mk_Trueprop (
      HOLogic.eq_const (T --> T) $
      Term.list_comb (mapx, map HOLogic.id_const vars @ t) $
      HOLogic.id_const T
    )),
    map_comp0 = fold_rev Logic.all (fs @ gs @ t) (add_f_prems (fs @ gs) (HOLogic.mk_Trueprop (
      HOLogic.eq_const (T --> T) $
        (Term.list_comb (mapx, map2 (curry HOLogic.mk_comp) fs gs @ t)) $
        (HOLogic.mk_comp (
          Term.list_comb (mapx, fs @ t),
          Term.list_comb (mapx, gs @ t)
        ))
    ))),
    map_cong_ids = map (fn i =>
      let val a = nth xs i in
        fold_rev Logic.all (d::t @ fs) (add_f_prems fs (
          Logic.implies $ (Logic.all a (Logic.implies $
            HOLogic.mk_Trueprop (HOLogic.mk_mem (a, Term.list_comb (nth FVars i, t @ [d]))) $
            mk_Trueprop_eq (nth fs i $ a, a)
          )) $
          mk_Trueprop_eq (Term.list_comb (mapx, fs @ t) $ d, d)
        ))
      end) (0 upto n - 1),
    in_FVars_map = map (fn i =>
      let
        val a = nth xs i;
        val FVars = nth FVars i;
      in
        fold_rev Logic.all (a::d::t @ fs) (add_f_prems fs (mk_Trueprop_eq (
          HOLogic.mk_mem (a, Term.list_comb (FVars,
            map (fn t => Term.list_comb (#qmap (the quotient_opt), fs @ [t])) t @ [Term.list_comb (mapx, fs @ t) $ d])),
          HOLogic.mk_mem (mk_inv (nth fs i) $ a, Term.list_comb (FVars, t @ [d]))
        )))
      end
    ) (0 upto n - 1)
  }
end;

fun create_binding_recursor model lthy =
  let
    fun prove goal tac = Goal.prove_sorry lthy [] [] goal (fn {context,...} => tac context);

    val goals = mk_termlike_goals (#term_quotient model) (#U model) (#Umap model) (#UFVars model) lthy;

    val print_lthy = Config.put eta_contract false lthy
    val _ = @{print} (map (Thm.cterm_of print_lthy) (#in_FVars_map goals))
  in
    lthy
  end;

end
