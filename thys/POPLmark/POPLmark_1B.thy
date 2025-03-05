theory POPLmark_1B
imports SystemFSub
begin

(********************* Actual formalization ************************)

lemma ty_refl: "\<lbrakk> \<turnstile> \<Gamma> ok ; T closed_in \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> T <: T"
proof (binder_induction T arbitrary: \<Gamma> avoiding: "dom \<Gamma>" rule: typ.strong_induct)
  case (TyVar x \<Gamma>)
  then show ?case by blast
next
  case (Rec x \<Gamma>)
  then show ?case using SA_Rec by (force intro: lfin_values)
qed (auto simp: Diff_single_insert SA_All wf_Cons)

lemma ty_permute: "\<lbrakk> \<Gamma> \<turnstile> S <: T ; \<turnstile> \<Delta> ok ; set \<Gamma> = set \<Delta> \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> S <: T"
proof (binder_induction \<Gamma> S T arbitrary: \<Delta> avoiding: "dom \<Delta>" rule: ty.strong_induct)
  case (SA_Refl_TVar \<Gamma> x \<Delta>)
  then show ?case by blast
next
  case (SA_All \<Gamma> T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2 \<Delta>)
  then have "set (\<Gamma> \<^bold>, x <: T\<^sub>1) = set (\<Delta>\<^bold>, x <: T\<^sub>1)" by auto
  then show ?case by (meson SA_All ty.SA_All well_scoped(1) wf_Cons)
next
  case (SA_Rec \<Gamma>' X Y \<Delta>)
  then show ?case by (metis ty.SA_Rec)
qed auto

lemma wf_concat: "\<lbrakk> \<turnstile> \<Delta> ok ; \<turnstile> \<Gamma> ok ; \<Gamma> \<bottom> \<Delta> \<rbrakk> \<Longrightarrow> \<turnstile> \<Gamma> \<^bold>, \<Delta> ok"
proof (induction \<Delta> rule: wf_ty.induct)
  case (wf_Cons x \<Delta> T)
  then have 1: "(\<Gamma> \<^bold>, (\<Delta> \<^bold>, x <: T)) = ((\<Gamma> \<^bold>, \<Delta>)\<^bold>, x <: T)" by simp
  show ?case unfolding 1
    apply (rule wf_ty.wf_Cons)
    using wf_Cons by auto
qed auto

lemma weaken_closed: "\<lbrakk> S closed_in \<Gamma> ; \<Gamma> \<bottom> \<Delta> \<rbrakk> \<Longrightarrow> S closed_in \<Gamma> \<^bold>, \<Delta>"
  by auto

lemma wf_concat_disjoint: "\<turnstile> \<Gamma> \<^bold>, \<Delta> ok \<Longrightarrow> \<Gamma> \<bottom> \<Delta>"
proof (induction \<Delta>)
  case (Cons a \<Delta>)
  then show ?case
    by (smt (verit, del_insts) Un_iff append_Cons disjoint_iff fst_conv image_iff inf.idem insertE list.inject list.simps(15) set_append set_empty2 wf_ty.cases)
qed simp

lemma wf_insert: "\<lbrakk> \<turnstile> \<Gamma> \<^bold>, \<Delta> ok ; x \<notin> dom \<Gamma> ; x \<notin> dom \<Delta> ; T closed_in \<Gamma> \<rbrakk> \<Longrightarrow> \<turnstile> \<Gamma> \<^bold>,x<:T\<^bold>, \<Delta> ok"
  by (induction \<Delta>) auto

lemma ty_weakening:
  assumes "\<Gamma> \<turnstile> S <: T" "\<turnstile> \<Gamma> \<^bold>, \<Delta> ok"
shows "\<Gamma> \<^bold>, \<Delta> \<turnstile> S <: T"
using assms proof (binder_induction \<Gamma> S T avoiding: "dom \<Delta>" \<Gamma> S T rule: ty.strong_induct)
  case (SA_Top \<Gamma> S)
  then show ?case using ty.SA_Top weaken_closed wf_concat_disjoint by meson
next
  case (SA_Refl_TVar \<Gamma> x)
  then show ?case using ty.SA_Refl_TVar weaken_closed wf_concat_disjoint by meson
next
  case (SA_All \<Gamma> T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2)
  have 1: "\<turnstile> \<Gamma> \<^bold>, x <: T\<^sub>1 \<^bold>, \<Delta> ok"
    by (meson wf_insert SA_All.fresh(1,5) SA_All.hyps(1,3) UnCI well_scoped(1))
  have 2: "\<turnstile> \<Gamma> \<^bold>, \<Delta> \<^bold>, x <: T\<^sub>1 ok"
    by (metis SA_All.fresh(1,5) SA_All.IH(1) SA_All.hyps(3) UnE image_Un set_append well_scoped(1) wf_Cons)
  show ?case using ty_permute[OF _ 2] 1 SA_All by auto
next
  case (SA_Rec \<Gamma>' X Y)
  then show ?case by (metis ty.SA_Rec weaken_closed wf_concat_disjoint)
qed auto

corollary ty_weakening_extend: "\<lbrakk> \<Gamma> \<turnstile> S <: T ; X \<notin> dom \<Gamma> ; Q closed_in \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<^bold>,X<:Q \<turnstile> S <: T"
  using ty_weakening[of _ _ _ "[(X, Q)]"] by (metis append_Cons append_Nil wf_Cons wf_context)

lemma wf_concatD: "\<turnstile> \<Gamma> \<^bold>, \<Delta> ok \<Longrightarrow> \<turnstile> \<Gamma> ok"
  by (induction \<Delta>) auto

lemma context_determ: "\<lbrakk> X <: U \<in> (\<Gamma> \<^bold>, X <: U'\<^bold>, \<Delta>) ;  \<turnstile> \<Gamma> \<^bold>, X <: U'\<^bold>, \<Delta> ok \<rbrakk> \<Longrightarrow> U = U'"
proof (induction \<Delta>)
  case Nil
  then show ?case
    by (metis Pair_inject append_Nil fst_conv image_eqI set_ConsD wf_ConsE)
qed auto

lemma narrow_wf: "\<lbrakk> \<turnstile> (\<Gamma> \<^bold>, X <: Q)\<^bold>, \<Delta> ok ; R closed_in \<Gamma> \<rbrakk> \<Longrightarrow> \<turnstile> (\<Gamma> \<^bold>, X <: R)\<^bold>, \<Delta> ok"
proof (induction \<Delta>)
  case (Cons a \<Delta>)
  then have "\<turnstile> \<Gamma> \<^bold>, X <: R\<^bold>, \<Delta> ok" by auto
  obtain b c where 2: "a = (b, c)" by fastforce
  then have 1: "\<And>R. \<Gamma> \<^bold>, X <: R\<^bold>, (a # \<Delta>) = (b, c) # (\<Gamma> \<^bold>, X <: R\<^bold>, \<Delta>)" by simp
  have "b \<notin> dom (\<Gamma> \<^bold>, X <: R\<^bold>, \<Delta>)" using Cons(2)[unfolded 1] by auto
  then show ?case unfolding 1 using Cons 2 by auto
qed auto

(* todo for A: look at this and the next *)
(* TODO: Automatically derive these from strong induction *)
lemma SA_AllE1[consumes 2, case_names SA_Trans_TVar SA_All]:
  assumes "\<Gamma> \<turnstile> \<forall>X<:S\<^sub>1. S\<^sub>2 <: T" "X \<notin> dom \<Gamma>"
    and Top: "\<And>\<Gamma>. \<lbrakk> \<turnstile> \<Gamma> ok ; \<forall>X<:S\<^sub>1. S\<^sub>2 closed_in \<Gamma> \<rbrakk> \<Longrightarrow> R \<Gamma> (\<forall>X<:S\<^sub>1. S\<^sub>2) Top"
    and Forall: "\<And>\<Gamma> T\<^sub>1 T\<^sub>2. \<lbrakk> \<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 ; \<Gamma> \<^bold>, X<:T\<^sub>1 \<turnstile> S\<^sub>2 <: T\<^sub>2 \<rbrakk> \<Longrightarrow> R \<Gamma> (\<forall>X<:S\<^sub>1. S\<^sub>2) (\<forall>X<:T\<^sub>1 . T\<^sub>2)"
  shows "R \<Gamma> (\<forall>X<:S\<^sub>1. S\<^sub>2) T"
using assms(1,2) proof (binder_induction \<Gamma> "\<forall>X<:S\<^sub>1. S\<^sub>2" T avoiding: \<Gamma> "\<forall>X<:S\<^sub>1. S\<^sub>2" T rule: ty.strong_induct)
  case (SA_All \<Gamma> T\<^sub>1 R\<^sub>1 Y R\<^sub>2 T\<^sub>2)
  have 1: "\<forall>Y<:T\<^sub>1 . T\<^sub>2 = \<forall>X<:T\<^sub>1. permute_typ (id(Y:=X,X:=Y)) T\<^sub>2"
    apply (rule Forall_swap)
    using SA_All(7,10) well_scoped(2) by fastforce
  have fresh: "X \<notin> FVars_typ T\<^sub>1"
    by (meson SA_All(5,10) in_mono well_scoped(1))
  have same: "R\<^sub>1 = S\<^sub>1" using SA_All(9) typ_inject by blast
  have x: "\<forall>Y<:S\<^sub>1. R\<^sub>2 = \<forall>X<:S\<^sub>1. permute_typ (id(Y:=X,X:=Y)) R\<^sub>2"
    apply (rule Forall_swap)
    by (metis (no_types, lifting) SA_All(9) assms(1,2) in_mono sup.bounded_iff typ.set(4) well_scoped(1))
  show ?case unfolding 1
    apply (rule Forall)
    using same SA_All(5) apply simp
    apply (rule iffD2[OF arg_cong3[OF _ _ refl, of _ _ _ _ ty], rotated -1])
      apply (rule ty.equiv)
       apply (rule bij_swap supp_swap_bound infinite_UNIV)+
        apply (rule SA_All(7))
        apply (unfold map_context_def[symmetric])
     apply (subst extend_eqvt)
       apply (rule bij_swap supp_swap_bound infinite_UNIV)+
     apply (rule arg_cong3[of _ _ _ _ _ _ extend])
    using SA_All(1,10) apply (metis bij_swap SA_All(5) Un_iff context_map_cong_id fun_upd_apply id_apply infinite_UNIV supp_swap_bound wf_FFVars wf_context)
      apply simp
    using fresh SA_All(4) apply simp
    using x SA_All(9) unfolding same by simp
qed (auto simp: Top)

lemma SA_AllE2[consumes 2, case_names SA_Trans_TVar SA_All]:
  assumes "\<Gamma> \<turnstile> S <: \<forall>X<:T\<^sub>1. T\<^sub>2" "X \<notin> dom \<Gamma>"
    and TyVar: "\<And>\<Gamma> x U. \<lbrakk> x<:U \<in> \<Gamma> ; \<Gamma> \<turnstile> U <: \<forall> X <: T\<^sub>1 . T\<^sub>2 ; R \<Gamma> U (\<forall>X<:T\<^sub>1. T\<^sub>2) \<rbrakk> \<Longrightarrow> R \<Gamma> (TyVar x) (\<forall> X <: T\<^sub>1 . T\<^sub>2)"
    and Forall: "\<And>\<Gamma> S\<^sub>1 S\<^sub>2. \<lbrakk> \<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 ; \<Gamma> \<^bold>, X<:T\<^sub>1 \<turnstile> S\<^sub>2 <: T\<^sub>2 \<rbrakk> \<Longrightarrow> R \<Gamma> (\<forall>X<:S\<^sub>1. S\<^sub>2) (\<forall> X <: T\<^sub>1 . T\<^sub>2)"
  shows "R \<Gamma> S (\<forall>X<:T\<^sub>1. T\<^sub>2)"
using assms(1,2) proof (binder_induction \<Gamma> S "\<forall>X<:T\<^sub>1. T\<^sub>2" avoiding: \<Gamma> S "\<forall>X<:T\<^sub>1. T\<^sub>2" rule: ty.strong_induct)
  case (SA_All \<Gamma> R\<^sub>1 S\<^sub>1 Y S\<^sub>2 R\<^sub>2)
  have 1: "\<forall>Y<:S\<^sub>1. S\<^sub>2 = \<forall>X<:S\<^sub>1. permute_typ (id(Y:=X,X:=Y)) S\<^sub>2"
    apply (rule Forall_swap)
    using SA_All(7,10) well_scoped(1) by fastforce
  have fresh: "X \<notin> dom \<Gamma>" "Y \<notin> dom \<Gamma>"
    using SA_All(10) apply blast
    by (metis SA_All(7) fst_conv wf_ConsE wf_context)
  have fresh2: "X \<notin> FVars_typ T\<^sub>1" "Y \<notin> FVars_typ T\<^sub>1"
     apply (metis SA_All(5,9) in_mono fresh(1) typ_inject well_scoped(1))
    by (metis SA_All(5,9) in_mono fresh(2) typ_inject well_scoped(1))
  have same: "R\<^sub>1 = T\<^sub>1" using SA_All(9) typ_inject by blast
  have x: "\<forall>Y<:T\<^sub>1 . R\<^sub>2 = \<forall>X<:T\<^sub>1. permute_typ (id(Y:=X,X:=Y)) R\<^sub>2"
    apply (rule Forall_swap)
    by (metis SA_All(9) Un_iff assms(1,2) in_mono typ.set(4) well_scoped(2))
  show ?case unfolding 1
    apply (rule Forall)
     apply (metis SA_All(5,9) typ_inject)
    apply (rule iffD2[OF arg_cong3[OF _ refl, of _ _ _ _ ty], rotated -1])
      apply (rule ty.equiv)
       apply (rule bij_swap supp_swap_bound infinite_UNIV)+
        apply (rule SA_All(7))
        apply (unfold map_context_def[symmetric])
     apply (subst extend_eqvt)
       apply (rule bij_swap supp_swap_bound infinite_UNIV)+
     apply (rule arg_cong3[of _ _ _ _ _ _ extend])
    using fresh apply (metis bij_swap SA_All(5) Un_iff context_map_cong_id fun_upd_apply id_apply infinite_UNIV supp_swap_bound wf_FFVars wf_context)
      apply simp
    using fresh2 unfolding same apply (metis bij_swap fun_upd_apply id_apply infinite_UNIV supp_swap_bound typ.permute_cong_id)
    using SA_All(9) x unfolding same by simp
qed (auto simp: TyVar)

lemma ty_transitivity : "\<lbrakk> \<Gamma> \<turnstile> S <: Q ; \<Gamma> \<turnstile> Q <: T \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> S <: T"
  and ty_narrowing : "\<lbrakk> \<Gamma> \<^bold>, X <: Q\<^bold>, \<Delta> \<turnstile> M <: N ; \<Gamma> \<turnstile> R <: Q \<rbrakk> \<Longrightarrow> \<Gamma> \<^bold>, X <: R\<^bold>, \<Delta> \<turnstile> M <: N"
proof -
  have
    ty_trans: "\<lbrakk> \<Gamma> \<turnstile> S <: Q ; \<Gamma> \<turnstile> Q <: T \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> S <: T"
  and ty_narrow: "\<lbrakk> (\<Gamma> \<^bold>, X <: Q)\<^bold>, \<Delta> \<turnstile> M <: N ; \<Gamma> \<turnstile> R <: Q ; \<turnstile> \<Gamma> \<^bold>, X <: R\<^bold>, \<Delta> ok ; M closed_in (\<Gamma> \<^bold>, X <: R\<^bold>, \<Delta>) ; N closed_in (\<Gamma> \<^bold>, X <: R\<^bold>, \<Delta>) \<rbrakk> \<Longrightarrow> (\<Gamma> \<^bold>, X <: R)\<^bold>, \<Delta> \<turnstile> M <: N"
  proof (binder_induction Q arbitrary: \<Gamma> \<Delta> S T M N X R avoiding: X "dom \<Gamma>" "dom \<Delta>" rule: typ.strong_induct)
    case (TyVar Y \<Gamma> \<Delta> S T M N X R)
    {
      fix \<Gamma> S T
      show ty_trans: "\<Gamma> \<turnstile> S <: TyVar Y \<Longrightarrow> \<Gamma> \<turnstile> TyVar Y <: T \<Longrightarrow> \<Gamma> \<turnstile> S <: T"
        by (induction \<Gamma> S "TyVar Y" rule: ty.induct) auto
    } note ty_trans = this
    {
      case 2
      then show ?case
      proof (binder_induction "\<Gamma> \<^bold>, X <: TyVar Y\<^bold>, \<Delta>" M N arbitrary: \<Delta> avoiding: X "dom \<Gamma>" "dom \<Delta>" rule: ty.strong_induct)
        case (SA_Trans_TVar Z U T \<Delta>')
        show ?case
        proof (cases "X = Z")
          case True
          then have u: "U = TyVar Y" using SA_Trans_TVar(1,2) context_determ wf_context by blast
          have "TyVar Y closed_in \<Gamma> \<^bold>, Z <: R\<^bold>, \<Delta>'" using SA_Trans_TVar(2) True u well_scoped(1) by fastforce
          then have "\<Gamma> \<^bold>, Z <: R \<^bold>, \<Delta>' \<turnstile> TyVar Y <: T" using SA_Trans_TVar True u by auto
          moreover have "\<Gamma> \<^bold>, Z <: R\<^bold>, \<Delta>' \<turnstile> R <: TyVar Y" using ty_weakening[OF ty_weakening_extend[OF SA_Trans_TVar(4)]]
            by (metis SA_Trans_TVar(5) True wf_ConsE wf_concatD)
          ultimately have "\<Gamma> \<^bold>, Z <: R \<^bold>, \<Delta>' \<turnstile> R <: T" using ty_trans by blast
          then show ?thesis unfolding True u using ty.SA_Trans_TVar by auto
        next
          case False
          have x: "U closed_in (\<Gamma> \<^bold>, X <: R \<^bold>, \<Delta>')" using SA_Trans_TVar(2) well_scoped(1) by fastforce
          show ?thesis
            apply (rule ty.SA_Trans_TVar)
            using SA_Trans_TVar False x by auto
        qed
      next
        case (SA_Arrow T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2 \<Delta>')
        then show ?case by auto
      next
        case (SA_All T\<^sub>1 S\<^sub>1 Z S\<^sub>2 T\<^sub>2 \<Delta>')
        have 1: "\<turnstile> \<Gamma> \<^bold>, X <: R\<^bold>, \<Delta>'\<^bold>, Z <: T\<^sub>1 ok"
          apply (rule wf_Cons)
          using SA_All UnI1 image_iff by auto
        have "\<Gamma> \<^bold>, X <: R\<^bold>, (\<Delta>'\<^bold>, Z <: T\<^sub>1) \<turnstile> S\<^sub>2 <: T\<^sub>2"
          by (smt (verit, del_insts) "1" SA_All.hyps(6-8) append_Cons fst_conv image_Un image_insert list.simps(15) set_append well_scoped(1) well_scoped(2))
        then show ?case using SA_All by auto
      next
        case (SA_Rec X Y \<Delta>')
        then show ?case
          by (smt (verit, del_insts) SA_RecER ty.SA_Rec ty_refl typ.distinct(4) well_scoped(2))
      qed (rule context_set_bd_UNIV | blast)+
    }
  next
    case (Top \<Gamma> \<Delta> S T M N X R)
    show ty_trans: "\<Gamma> \<turnstile> S <: Top \<Longrightarrow> \<Gamma> \<turnstile> Top <: T \<Longrightarrow> \<Gamma> \<turnstile> S <: T" by auto
    {
      case 2
      then show ?case
      proof (binder_induction "\<Gamma> \<^bold>, X <: Top\<^bold>, \<Delta>" M N arbitrary: \<Delta> avoiding: X "dom \<Gamma>" "dom \<Delta>" rule: ty.strong_induct)
        case (SA_Trans_TVar Z U T \<Delta>')
        then show ?case
        proof (cases "X = Z")
          case True
          then have u: "U = Top" using SA_Trans_TVar(1,2) context_determ wf_context by blast
          have "\<Gamma> \<^bold>, Z <: R \<^bold>, \<Delta>' \<turnstile> Top <: T" using SA_Trans_TVar True u by auto
          then have "\<Gamma> \<^bold>, Z <: R \<^bold>, \<Delta>' \<turnstile> R <: T"
            by (metis SA_TopE SA_Trans_TVar(4) ty_weakening ty_weakening_extend wf_ConsE wf_concatD)
          then show ?thesis unfolding True u using ty.SA_Trans_TVar by auto
        next
          case False
          have x: "U closed_in \<Gamma> \<^bold>, X <: R \<^bold>, \<Delta>'" using SA_Trans_TVar(2) well_scoped(1) by fastforce
          show ?thesis
            apply (rule ty.SA_Trans_TVar)
            using SA_Trans_TVar False x by auto
        qed
      next
        case (SA_Arrow T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2 \<Delta>')
        then show ?case by auto
      next
        case (SA_All T\<^sub>1 S\<^sub>1 Z S\<^sub>2 T\<^sub>2 \<Delta>')
        have 1: "\<turnstile> \<Gamma> \<^bold>, X <: R \<^bold>, \<Delta>' \<^bold>, Z <: T\<^sub>1 ok"
          apply (rule wf_Cons)
          using SA_All UnI1 image_iff by auto
        have "\<Gamma> \<^bold>, X <: R \<^bold>, (\<Delta>' \<^bold>, Z <: T\<^sub>1) \<turnstile> S\<^sub>2 <: T\<^sub>2"
          by (smt (verit, del_insts) "1" SA_All.hyps(6-8) append_Cons fst_conv image_Un image_insert list.simps(15) set_append well_scoped(1) well_scoped(2))
        then show ?case using SA_All by auto
      next
        case (SA_Rec X Y \<Delta>')
        then show ?case
          by (smt (verit) SA_RecER ty.SA_Rec ty_refl typ.distinct(17) well_scoped(2))
      qed (rule context_set_bd_UNIV | blast)+
    }
  next
    case (Fun Q\<^sub>1 Q\<^sub>2 \<Gamma> \<Delta> S T M N X R)
    {
      fix \<Gamma> S T
      assume "\<Gamma> \<turnstile> S <: Q\<^sub>1 \<rightarrow> Q\<^sub>2" "\<Gamma> \<turnstile> Q\<^sub>1 \<rightarrow> Q\<^sub>2 <: T"
      then show "\<Gamma> \<turnstile> S <: T"
      proof (induction \<Gamma> S "Q\<^sub>1 \<rightarrow> Q\<^sub>2" rule: ty.induct)
        case left: (SA_Arrow \<Gamma> T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2)
        from left(6,1-5) show ?case
        proof cases
          case SA_Top
          then show ?thesis by (meson left(1,3) ty.SA_Arrow ty.SA_Top well_scoped(1))
        next
          case right: (SA_Arrow U\<^sub>1 R\<^sub>1 R\<^sub>2 U\<^sub>2)
          then show ?thesis using left by (metis Fun(1,3) SA_Arrow typ.inject)
        qed auto
      qed auto
    } note ty_trans = this
    {
      case 2
      then show ?case
      proof (binder_induction "\<Gamma> \<^bold>, X <: (Q\<^sub>1 \<rightarrow> Q\<^sub>2) \<^bold>, \<Delta>" M N arbitrary: \<Delta> avoiding: X "dom \<Gamma>" "dom \<Delta>" rule: ty.strong_induct)
        case (SA_Trans_TVar Z U T \<Delta>')
        then show ?case
        proof (cases "X = Z")
          case True
          then have u: "U = (Q\<^sub>1 \<rightarrow> Q\<^sub>2)" using SA_Trans_TVar(1,2) context_determ wf_context by blast
          have "(Q\<^sub>1 \<rightarrow> Q\<^sub>2) closed_in \<Gamma> \<^bold>, Z <: R \<^bold>, \<Delta>'" using SA_Trans_TVar(2) True u well_scoped(1) by fastforce
          then have "\<Gamma> \<^bold>, Z <: R \<^bold>, \<Delta>' \<turnstile> (Q\<^sub>1 \<rightarrow> Q\<^sub>2) <: T" using SA_Trans_TVar True u by auto
          moreover have "\<Gamma> \<^bold>, Z <: R \<^bold>, \<Delta>' \<turnstile> R <: (Q\<^sub>1 \<rightarrow> Q\<^sub>2)" using ty_weakening[OF ty_weakening_extend[OF SA_Trans_TVar(4)]]
            by (metis SA_Trans_TVar(5) True wf_ConsE wf_concatD)
          ultimately have "\<Gamma> \<^bold>, Z <: R \<^bold>, \<Delta>' \<turnstile> R <: T" using ty_trans by blast
          then show ?thesis unfolding True u using ty.SA_Trans_TVar by auto
        next
          case False
          have x: "U closed_in \<Gamma> \<^bold>, X <: R \<^bold>, \<Delta>'" using SA_Trans_TVar(2) well_scoped(1) by fastforce
          show ?thesis
            apply (rule ty.SA_Trans_TVar)
            using SA_Trans_TVar False x by auto
        qed
      next
        case (SA_Arrow T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2 \<Delta>')
        then show ?case by auto
      next
        case (SA_All T\<^sub>1 S\<^sub>1 Z S\<^sub>2 T\<^sub>2 \<Delta>')
        have 1: "\<turnstile> \<Gamma> \<^bold>, X <: R \<^bold>, \<Delta>' \<^bold>, Z <: T\<^sub>1 ok"
          apply (rule wf_Cons)
          using SA_All UnI1 image_iff by auto
        have "\<Gamma> \<^bold>, X <: R \<^bold>, (\<Delta>' \<^bold>, Z <: T\<^sub>1) \<turnstile> S\<^sub>2 <: T\<^sub>2"
          by (smt (verit, del_insts) "1" SA_All.hyps(6-8) append_Cons fst_conv image_Un image_insert list.simps(15) set_append well_scoped(1) well_scoped(2))
        then show ?case using SA_All by auto
      next
        case (SA_Rec X Y \<Delta>')
        then show ?case
          by (smt (verit, ccfv_threshold) SA_RecER ty.SA_Rec ty_refl typ.distinct(17) well_scoped(2))
      qed (rule context_set_bd_UNIV | blast)+
    }
  next
    case (Forall X Q\<^sub>1 Q\<^sub>2 \<Gamma> \<Delta> S T M N Y R)
    have ty_trans: "\<And>\<Gamma> S T. X \<notin> dom \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> S <: \<forall>X<:Q\<^sub>1. Q\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> \<forall>X<:Q\<^sub>1. Q\<^sub>2 <: T \<Longrightarrow> \<Gamma> \<turnstile> S <: T"
    proof -
      fix \<Gamma> S T
      assume a: "X \<notin> dom \<Gamma>" "\<Gamma> \<turnstile> S <: \<forall>X<:Q\<^sub>1. Q\<^sub>2" "\<Gamma> \<turnstile> \<forall>X<:Q\<^sub>1. Q\<^sub>2 <: T"
      from a(2,1,3) a(1) show "\<Gamma> \<turnstile> S <: T"
      proof (induction rule: SA_AllE2)
        case (SA_All \<Gamma> S\<^sub>1 S\<^sub>2)
        from SA_All(3,4,1,2) show ?case
        proof (induction rule: SA_AllE1)
          case (SA_Trans_TVar \<Gamma>)
          then show ?case by (meson SA_Top ty.SA_All well_scoped(1))
        next
          case (SA_All \<Gamma> T\<^sub>1 T\<^sub>2)
          have 1: "\<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1" by (rule Forall(4)[OF SA_All(1,3)])
          have "\<Gamma> \<^bold>, X <: T\<^sub>1 \<turnstile> S\<^sub>2 <: Q\<^sub>2" using Forall(5)[of \<emptyset> X \<Gamma> S\<^sub>2 Q\<^sub>2, OF _ SA_All(1)] SA_All(4)
            by (metis (mono_tags, lifting) SA_All(2) append.left_neutral fst_conv image_insert list.simps(15) well_scoped(1) wf_context)
          then have "\<Gamma> \<^bold>, X <: T\<^sub>1 \<turnstile> S\<^sub>2 <: T\<^sub>2" by (rule Forall(6)[OF _ SA_All(2)])
          then show ?case using 1 by blast
        qed
      qed auto
    qed
    {
      case 1
      then show ?case using ty_trans Forall(2) by blast
    next
      case 2
      then show ?case using Forall(1-3)
      proof (binder_induction "\<Gamma> \<^bold>, Y <: (\<forall>X<:Q\<^sub>1. Q\<^sub>2) \<^bold>, \<Delta>" M N arbitrary: \<Delta> avoiding: X Y "dom \<Gamma>" "dom \<Delta>" rule: ty.strong_induct)
        case (SA_Trans_TVar Z U T \<Delta>')
        then show ?case
        proof (cases "Y = Z")
          case True
          then have u: "U = \<forall> X <: Q\<^sub>1 . Q\<^sub>2" using SA_Trans_TVar(1,2) context_determ wf_context by blast
          have "\<forall> X <: Q\<^sub>1 . Q\<^sub>2 closed_in \<Gamma> \<^bold>, Z <: R \<^bold>, \<Delta>'" using SA_Trans_TVar(2) True u well_scoped(1) by fastforce
          then have "\<Gamma> \<^bold>, Z <: R \<^bold>, \<Delta>' \<turnstile> \<forall> X <: Q\<^sub>1 . Q\<^sub>2 <: T" using SA_Trans_TVar True u by auto
          moreover have "\<Gamma> \<^bold>, Z <: R \<^bold>, \<Delta>' \<turnstile> R <: \<forall> X <: Q\<^sub>1 . Q\<^sub>2" using ty_weakening[OF ty_weakening_extend[OF SA_Trans_TVar(4)]]
            by (metis SA_Trans_TVar(5) True wf_ConsE wf_concatD)
          moreover have "X \<notin> dom (\<Gamma> \<^bold>, Z <: R \<^bold>, \<Delta>')" using SA_Trans_TVar(8-10) True by auto
          ultimately have "\<Gamma> \<^bold>, Z <: R \<^bold>, \<Delta>' \<turnstile> R <: T" using ty_trans by blast
          then show ?thesis unfolding True u using ty.SA_Trans_TVar by auto
        next
          case False
          have x: "U closed_in \<Gamma> \<^bold>, Y <: R \<^bold>, \<Delta>'" using SA_Trans_TVar(2) well_scoped(1) by fastforce
          show ?thesis
            apply (rule ty.SA_Trans_TVar)
            using SA_Trans_TVar False x by auto
        qed
      next
        case (SA_Arrow T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2 \<Delta>')
        then show ?case by auto
      next
        case (SA_All T\<^sub>1 S\<^sub>1 Z S\<^sub>2 T\<^sub>2 \<Delta>')
        have 1: "\<turnstile> \<Gamma> \<^bold>, Y <: R \<^bold>, \<Delta>' \<^bold>, Z <: T\<^sub>1 ok"
          apply (rule wf_Cons)
          using SA_All UnI1 image_iff by auto
        have "\<Gamma> \<^bold>, Y <: R \<^bold>, (\<Delta>' \<^bold>, Z <: T\<^sub>1) \<turnstile> S\<^sub>2 <: T\<^sub>2"
          apply (rule SA_All(8))
                 apply (simp add: SA_All 1)+
          using SA_All.hyps(7) well_scoped(1) apply fastforce
             apply (simp add: SA_All 1)
          using SA_All.hyps(7) well_scoped(2) apply fastforce
          using SA_All by (auto simp: 1)
        then show ?case using SA_All by auto
      next
        case (SA_Rec X Y \<Delta>')
        then show ?case
          by (smt (verit) SA_RecER ty.SA_Rec ty_refl typ.distinct(17) well_scoped(2))
      qed (rule context_set_bd_UNIV | blast)+
    }
  next
    case (Rec Y \<Gamma> \<Delta> S T M N X R)
    {
      fix \<Gamma> S T assume "\<Gamma> \<turnstile> S <: Rec Y" "\<Gamma> \<turnstile> Rec Y <: T"
      then have "\<Gamma> \<turnstile> S <: T"
        apply (induct \<Gamma> S "Rec Y")
             apply (auto elim!: SA_RecEL[of _ Y T])
         apply (meson SA_Rec SA_Top well_scoped(1))
        apply (meson Rec.IH SA_Rec lfin_values subset_trans)
        done
    } note * = this
    {
      case 1
      then show ?case by (rule *)
    next
      case 2
      then show ?case
      proof (induction "(\<Gamma> \<^bold>, X <: Rec Y)\<^bold>, \<Delta>" M N arbitrary: \<Delta> rule: ty.induct)
        case (SA_Trans_TVar XX U T)
        show ?case
        proof (cases "X = XX")
          case True
          then have "\<Gamma> \<^bold>, X <: R \<^bold>, \<Delta> \<turnstile> U <: T" using SA_Trans_TVar well_scoped(1)[where \<Gamma> = "\<Gamma> \<^bold>, X <: Rec Y \<^bold>, \<Delta>"]
            by auto
          moreover have "\<Gamma> \<^bold>, X <: R \<^bold>, \<Delta> \<turnstile> R <: U" using True SA_Trans_TVar
            by (metis context_determ ty_weakening ty_weakening_extend wf_ConsE wf_concatD wf_context)
          ultimately have "\<Gamma> \<^bold>, X <: R \<^bold>, \<Delta> \<turnstile> R <: T"
            using 2(2) *[of "\<Gamma> \<^bold>, X <: R \<^bold>, \<Delta>" R T] True
            using SA_Trans_TVar.hyps(1,2) context_determ wf_context by blast
          then show ?thesis
            using True by auto
        next
          case False
          then show ?thesis
            using SA_Trans_TVar well_scoped(1)[where \<Gamma> = "\<Gamma> \<^bold>, X <: Rec Y \<^bold>, \<Delta>"] by auto
        qed
      next
        case (SA_Arrow T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2)
        then show ?case by force
      next
        case (SA_All T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2)
        then show ?case
          by clarsimp (smt (verit, del_insts) Diff_single_insert append_Cons insert_commute narrow_wf ty.SA_All well_scoped(1) wf_context)
      next
        case (SA_Rec X Y)
        then show ?case
          by (smt (verit, ccfv_threshold) SA_RecER ty.SA_Rec ty_refl typ.distinct(17) well_scoped(2))
      qed blast+
    }
  qed simp_all

  show "\<lbrakk> \<Gamma> \<turnstile> S <: Q ; \<Gamma> \<turnstile> Q <: T \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> S <: T" using ty_trans by blast
  show "\<lbrakk> (\<Gamma> \<^bold>, X <: Q)\<^bold>, \<Delta> \<turnstile> M <: N ; \<Gamma> \<turnstile> R <: Q \<rbrakk> \<Longrightarrow> (\<Gamma> \<^bold>, X <: R)\<^bold>, \<Delta> \<turnstile> M <: N"
    apply (rule ty_narrow)
        apply assumption+
    using narrow_wf well_scoped wf_context apply metis
    using well_scoped by fastforce+
qed

lemma ty_narrowing_aux:
  assumes ty_trans: "\<And>\<Gamma> S T. \<lbrakk> \<Gamma> \<turnstile> S <: Q ; \<Gamma> \<turnstile> Q <: T \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> S <: T"
  and "(\<Gamma> \<^bold>, X <: Q)\<^bold>, \<Delta> \<turnstile> M <: N" "\<Gamma> \<turnstile> R <: Q"
shows "(\<Gamma> \<^bold>, X <: R)\<^bold>, \<Delta> \<turnstile> M <: N"
proof -
  have 1: "\<turnstile> \<Gamma> \<^bold>, X <: R\<^bold>, \<Delta> ok" using assms(2-3) narrow_wf well_scoped(1) wf_context by blast
  show ?thesis using assms(2-3) 1
  proof (induction "(\<Gamma> \<^bold>, X <: Q)\<^bold>, \<Delta>" M N arbitrary: \<Delta> rule: ty.induct)
    case (SA_Trans_TVar Y U T \<Delta>)
    show ?case
    proof (cases "X = Y")
      case True
      then have "\<Gamma> \<^bold>, X <: R \<^bold>, \<Delta> \<turnstile> U <: T" using SA_Trans_TVar by auto
      then show ?thesis
        by (metis SA_Trans_TVar(1,2,4) True context_determ list.set_intros(1) ty.SA_Trans_TVar ty_trans ty_weakening ty_weakening_extend wf_ConsE wf_concatD wf_context)
    next
      case False
      then show ?thesis using SA_Trans_TVar by auto
    qed
  next
    case (SA_All T\<^sub>1 S\<^sub>1 x S\<^sub>2 T\<^sub>2 \<Delta>)
    then show ?case by (metis Cons_eq_appendI narrow_wf ty.SA_All well_scoped(1) wf_context)
  next
    case (SA_Rec X Y)
    then show ?case by (meson ty.SA_Rec ty_narrowing)
  qed (auto simp: ty.intros)
qed

theorem ty_transitivity2: "\<lbrakk> \<Gamma> \<turnstile> S <: Q ; \<Gamma> \<turnstile> Q <: T \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> S <: T"
proof (binder_induction Q arbitrary: \<Gamma> S T avoiding: "dom \<Gamma>" rule: typ.strong_induct)
  case (TyVar x \<Gamma> S T)
  then show ?case
    by (induction \<Gamma> S "TyVar x") auto
next
  case (Fun x1 x2 \<Gamma> S T)
  from Fun(4,3) show ?case
  proof (induction \<Gamma> "x1 \<rightarrow> x2" T)
    case (SA_Top \<Gamma>)
    then show ?case using well_scoped by blast
  next
    case outer: (SA_Arrow \<Gamma> T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2)
    from outer(6,1,3,5) show ?case
    proof (induction \<Gamma> S "x1 \<rightarrow> x2")
      case (SA_Arrow \<Gamma> U\<^sub>1 R\<^sub>1 R\<^sub>2 U\<^sub>2)
      show ?case
        apply (rule ty.SA_Arrow)
         apply (metis Fun(1) SA_Arrow(1,5,6,8) typ.inject(2))
        by (metis Fun(2) SA_Arrow(3,5,7,8) typ.inject(2))
    qed auto
  qed auto
next
  case (Forall X Q\<^sub>1 Q\<^sub>2 \<Gamma> S T)
  from Forall(4,1,5,1) show ?case
  proof (induction rule: SA_AllE2)
    case outer: (SA_All \<Gamma> S\<^sub>1 S\<^sub>2)
    from outer(3,4,1,2,4) show ?case
    proof (induction rule: SA_AllE1)
      case (SA_Trans_TVar \<Gamma>)
      then show ?case by (meson SA_All SA_Top well_scoped(1))
    next
      case (SA_All \<Gamma> T\<^sub>1 T\<^sub>2)
      then have "\<Gamma> \<^bold>, X <: T\<^sub>1 \<turnstile> S\<^sub>2 <: Q\<^sub>2"
        using ty_narrowing_aux[where \<Delta>="[]", unfolded append.simps] Forall(2) by blast
      then have "\<Gamma> \<^bold>, X <: T\<^sub>1 \<turnstile> S\<^sub>2 <: T\<^sub>2" using Forall(3) SA_All(2) by blast
      moreover have "\<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1" by (rule Forall(2)[OF SA_All(1,3)])
      ultimately show ?case by blast
    qed
  qed blast
next
  case (Rec Y \<Gamma> S T)
  from Rec(2,3) show ?case
    apply (induct \<Gamma> S "Rec Y")
         apply (auto elim!: SA_RecEL[of _ Y T])
     apply (meson SA_Rec SA_Top well_scoped(1))
    apply (meson Rec.IH SA_Rec lfin_values subset_trans)
    done
qed auto

corollary ty_narrowing2: "\<lbrakk> \<Gamma> \<^bold>, X <: Q\<^bold>, \<Delta> \<turnstile> M <: N ; \<Gamma> \<turnstile> R <: Q \<rbrakk> \<Longrightarrow> \<Gamma> \<^bold>, X <: R\<^bold>, \<Delta> \<turnstile> M <: N"
  using ty_narrowing_aux ty_transitivity2 by blast

end
