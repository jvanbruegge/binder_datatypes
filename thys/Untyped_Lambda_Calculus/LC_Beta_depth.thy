(*Beta reduction for the (untyped) lambda-calculus with applicative redex-depth counted *)
theory LC_Beta_depth 
imports LC "Binders.Generic_Barendregt_Enhanced_Rule_Induction" "Prelim.Curry_LFP" "Prelim.More_Stream" LC_Head_Reduction
begin

(* INSTANTIATING THE ABSTRACT SETTING: *)

(* *)

abbreviation Tsupp :: "nat \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> var set" where 
"Tsupp d e1 e2 \<equiv> FFVars_term e1 \<union> FFVars_term e2"

lemma fresh: "\<exists>xx. xx \<notin> Tsupp d e1 e2"
by (metis Lam_avoid term.card_of_FFVars_bounds term.set(2))

inductive stepD :: "nat \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> bool" where
  Beta: "stepD 0 (App (Lam x e1) e2) (tvsubst (Var(x:=e2)) e1)"
| AppL: "stepD d e1 e1' \<Longrightarrow> stepD (Suc d) (App e1 e2) (App e1' e2)"
| AppR: "stepD d e2 e2' \<Longrightarrow> stepD (Suc d) (App e1 e2) (App e1 e2')"
| Xi: "stepD d e e' \<Longrightarrow> stepD d (Lam x e) (Lam x e')"
ML \<open>
local
  open BNF_Util
in

fun refreshability_tac B Tsupp G_thm small_thms instss simp_thms intro_thms ctxt =
  let
    val fresh = infer_instantiate' ctxt
      [SOME (Thm.cterm_of ctxt B), SOME (Thm.cterm_of ctxt Tsupp),
       SOME (Thm.cterm_of ctxt (HOLogic.mk_binop \<^const_name>\<open>minus\<close> (Tsupp, B)))]
      @{thm eextend_fresh};
    val small_ctxt = ctxt addsimps small_thms;
    fun case_tac NONE _ prems ctxt = SOLVE (auto_tac (ctxt addsimps prems))
      | case_tac (SOME insts) params prems ctxt =
        let
          val f = hd params |> snd |> Thm.term_of;
          val ex_f = infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt f)] exI;
          val args = tl params |> map (snd #> Thm.term_of);
          val xs = @{map 2} (fn i => fn a => Thm.cterm_of ctxt (i $ f $ a)) insts args;
          val id_onI = nth prems 3 RS @{thm id_on_antimono};
        in
          HEADGOAL (EVERY' (map (fn x => rtac ctxt (infer_instantiate' ctxt [NONE, SOME x] exI)) xs)) THEN
print_tac ctxt "foo" THEN
          SOLVE (HEADGOAL (SELECT_GOAL (mk_auto_tac (ctxt
            addsimps (simp_thms @ prems)
            addSIs (ex_f :: id_onI :: intro_thms)) 0 4) THEN_ALL_NEW
            SELECT_GOAL (print_tac ctxt "auto failed")))
        end;
  in
    HEADGOAL (rtac ctxt (fresh RS exE) THEN'
      rtac ctxt (G_thm RSN (2, cut_rl)) THEN' SELECT_GOAL (auto_tac small_ctxt) THEN'
      REPEAT_DETERM_N 4 o simp_tac small_ctxt THEN'
      REPEAT_DETERM o etac ctxt conjE THEN'
      EVERY' [rtac ctxt exI, rtac ctxt conjI, assume_tac ctxt] THEN'
K (print_tac ctxt "bar") THEN'
      rtac ctxt (G_thm RSN (2, cut_rl)) THEN'
      REPEAT_ALL_NEW (eresolve_tac ctxt @{thms exE conjE disj_forward}) THEN'
      EVERY' (map (fn insts => Subgoal.FOCUS (fn focus =>
        case_tac insts (#params focus) (#prems focus) (#context focus)) ctxt) instss))
  end;

end;
\<close>
binder_inductive stepD where
  Beta binds x
| Xi binds x
for perms: "\<lambda>_. id" rrename rrename and supps: "\<lambda>_. {}" FFVars_term FFVars_term
  apply (auto simp: o_def split_beta term.rrename_comps fun_eq_iff isPerm_def
    small_def term.card_of_FFVars_bounds term.Un_bound emp_bound infinite_UNIV) [16]
  subgoal for R B \<sigma> x1 x2 x3
    by (elim disj_forward exE case_prodE)
      (auto simp: isPerm_def term.rrename_comps rrename_tvsubst_comp
        | ((rule exI[of _ "\<sigma> _"] exI)+, (rule conjI)?, rule refl)
        | ((rule exI[of _ "\<sigma> _"])+; auto))+
  subgoal premises prems for R B d t1 t2
    apply (tactic \<open>refreshability_tac @{term B} @{term "Tsupp d t1 t2"}
      @{thm prems(3)} @{thms emp_bound singl_bound term.Un_bound term.card_of_FFVars_bounds infinite}
      [SOME [@{term "(\<lambda>f x. f x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"},
             @{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"},
             @{term "(\<lambda>f e. e) :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"}],
       NONE,
       NONE,
       SOME [@{term "(\<lambda>f d. id d) :: (var \<Rightarrow> var) \<Rightarrow> nat \<Rightarrow> nat"},
             @{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"},
             @{term "rrename :: (var \<Rightarrow> var) \<Rightarrow> trm \<Rightarrow> trm"},
             @{term "(\<lambda>f x. f x) :: (var \<Rightarrow> var) \<Rightarrow> var \<Rightarrow> var"}]]
      @{thms Lam_inject}
      @{thms prems(2) Lam_eq_tvsubst term.rrename_cong_ids[symmetric]}
      @{context}\<close>)
    done
  done

thm stepD.strong_induct
thm stepD.equiv

(* Other properties: *)

lemma red_stepD: "red e ee \<Longrightarrow> stepD 0 e ee"
by (metis red_def stepD.Beta)

lemma red_stepD2: "stream_all2 red es ees \<Longrightarrow> stream_all2 (stepD 0) es ees"
unfolding stream_all2_iff_snth using red_stepD by auto


end