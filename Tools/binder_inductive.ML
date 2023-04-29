signature BINDER_INDUCTIVE = sig
  val binder_inductive_cmd: (string * (int * string list) list) -> Proof.context -> Proof.state
end;

structure Binder_Inductive : BINDER_INDUCTIVE = struct

open BNF_Util
open MRBNF_Util

fun binder_inductive_cmd (ind, rules) lthy =
  let
    val info = Inductive.the_inductive lthy (Syntax.read_term lthy ind);
    val rules = map (apsnd (map (dest_Free o Syntax.read_term lthy))) rules;
    
    val induct = #induct (snd info);

    val (xs, P) = split_last (rev (Term.add_vars (Thm.prop_of induct) []));
    val vars = rev (Term.add_tvars (Thm.prop_of induct) []);
    val ((As, C), names_lthy) = lthy
      |> mk_TFrees' (map snd vars)
      ||>> apfst hd o mk_TFrees 1;
    val replace = Term.typ_subst_atomic (map TVar vars ~~ As);

    val ((xs, P), names_lthy) = names_lthy
      |> mk_Frees "x" (map (replace o snd) xs)
      ||>> apfst hd o BNF_Util.mk_Frees "P" [replace (snd P)];

    val induct = infer_instantiate' lthy (map (SOME o Thm.cterm_of lthy) (xs @ [P])) induct;
    val (ind_prem::prems) = Thm.prems_of induct

    val to_avoid = maps (fn (i, ys) => filter (fn (n, _) => member (fn (a, b) => a = fst b) ys n) (
      Term.strip_all_vars (nth prems (i - 1))
    )) rules;
    val ((Ks, rho), _) = names_lthy
      |> mk_Frees "K" (map (fn (_, A) => C --> HOLogic.mk_setT A) to_avoid)
      ||>> apfst hd o mk_Frees "\<rho>" [C];

    val bound_prems = map (fn K => HOLogic.mk_Trueprop (HOLogic.mk_all ("\<rho>", C, mk_ordLess
      (mk_card_of (K $ Bound 0)) (mk_card_of (HOLogic.mk_UNIV (HOLogic.dest_setT (range_type (fastype_of K)))))
    ))) Ks;

    fun mk_all (a, b) c = HOLogic.mk_all (a, b, c)    
    val prems' = map_index (fn (i, prem) =>
      let
        val vars = Term.strip_all_vars prem
        val body = Term.strip_all_body prem
        val prems = Logic.strip_assums_hyp body
        val ((Pn, PT), ts) = apfst dest_Free (Term.strip_comb (Term.incr_boundvars 1 (
          HOLogic.dest_Trueprop (Logic.strip_assums_concl body)
        )));
        val prems' = map (Term.incr_boundvars 1) prems;
        val P' = Free (Pn, fold_rev (curry (op-->)) (Term.binder_types PT @ [C]) @{typ bool});
        val concl = HOLogic.mk_Trueprop (Term.list_comb (P', ts @ [Bound 0]));

        val prems' = map (fn prem => case Term.strip_comb (HOLogic.dest_Trueprop prem) of
          (Free (a, _), ts) => if a = Pn then HOLogic.mk_Trueprop (mk_all (dest_Free rho) (
            Term.list_comb (P', map (Term.incr_boundvars 1) ts @ [Bound 0])
          )) else prem
          | _ => prem
        ) prems';

        val prems' = case filter (fn (j, _) => i + 1 = j) rules of
          [] => prems'
          | (_, ys)::_ =>
          let
            val ys' = map Free (filter (member (fn (a, b) => a = fst b) ys o fst) vars);
            val disjoint_prems = map (fn y => HOLogic.mk_Trueprop (case try HOLogic.dest_setT (fastype_of y) of
              SOME _ => MRBNF_Recursor.mk_int_empty (y, hd (filter (fn K => range_type (fastype_of K) = fastype_of y) Ks) $ Bound 0)
              | _ => HOLogic.mk_not (HOLogic.mk_mem (y, hd (filter (fn K => HOLogic.dest_setT (range_type (fastype_of K)) = fastype_of y) Ks) $ Bound 0))
            )) ys';
          in disjoint_prems @ prems' end;

        val goal = fold_rev (Logic.all o Free) (vars @ [dest_Free rho]) (Logic.list_implies (prems', concl));
      in goal end
    ) prems;

    val ((Pn, PT), ts) = apfst dest_Free (Term.strip_comb (HOLogic.dest_Trueprop (Thm.concl_of induct)));
    val P' = Free (Pn, fold_rev (curry (op-->)) (Term.binder_types PT @ [C]) @{typ bool});
    val concl' = HOLogic.mk_Trueprop (mk_all (dest_Free rho) (Term.list_comb (P', ts @ [rho])));
    
    val strong_induct = Logic.list_implies ([ind_prem] @ bound_prems @ prems', concl');
    fun after_qed thms ctxt =
      let
        val (_, ctxt') = Local_Theory.note (
          (Binding.qualify true (short_type_name (hd (#names (fst info)))) (Binding.name "strong_induct"), []),
          flat thms
        ) ctxt
      in ctxt' end
  in Proof.theorem NONE after_qed [[(strong_induct, [])]] lthy end;

val _ = Outer_Syntax.local_theory_to_proof @{command_keyword binder_inductive}
  "strengthen the induction theorem so bound variables avoid a set of variables"
  ((Parse.term --| @{keyword where} -- (Scan.repeat1 (
    Parse.nat --| @{keyword :} -- Scan.repeat1 Parse.term
  ))) >> binder_inductive_cmd);

end