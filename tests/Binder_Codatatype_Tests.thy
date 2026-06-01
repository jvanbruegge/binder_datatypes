theory Binder_Codatatype_Tests
  imports "Binders.MRBNF_Recursor"
begin

declare [[mrbnf_internals]]

binder_codatatype 'a "term" =
    Var 'a
  | App "'a term" "'a term"
  | Lam x::'a t::"'a term" binds x in t

lemmas case_sum_if =
  if_distrib[of "case_sum f g" _ "Inl x" "Inr y", unfolded sum.case] for f g x y

locale HL_COREC_term =
  fixes is_Udvar    :: "'u \<Rightarrow> bool"
    and Udvar       :: "'u \<Rightarrow> 'a :: covar"
    and is_Udapp    :: "'u \<Rightarrow> bool"
    and Udapp_stop1 :: "'u \<Rightarrow> bool"
    and Udapp_end1  :: "'u \<Rightarrow> 'a term"
    and Udapp_cont1 :: "'u \<Rightarrow> 'u"
    and Udapp_stop2 :: "'u \<Rightarrow> bool"
    and Udapp_end2  :: "'u \<Rightarrow> 'a term"
    and Udapp_cont2 :: "'u \<Rightarrow> 'u"
    and is_Udlam    :: "'u \<Rightarrow> bool"
    and Udlam_stop  :: "'u \<Rightarrow> bool"
    and Udlam_end   :: "'u \<Rightarrow> ('a \<times> 'a term) set"
    and Udlam_cont  :: "'u \<Rightarrow> ('a \<times> 'u) set"
    and Umap        :: "('a \<Rightarrow> 'a) \<Rightarrow> 'u \<Rightarrow> 'u"
    and UFVars      :: "'u \<Rightarrow> 'a set"
    and validU      :: "'u \<Rightarrow> bool"
  assumes
    ctor_partition: "\<And>d. validU d \<Longrightarrow>
        (is_Udvar d \<and> \<not> is_Udapp d \<and> \<not> is_Udlam d) \<or>
        (\<not> is_Udvar d \<and> is_Udapp d \<and> \<not> is_Udlam d) \<or>
        (\<not> is_Udvar d \<and> \<not> is_Udapp d \<and> is_Udlam d)"
    and Udlam_end_ne:
      "\<And>d. validU d \<Longrightarrow> is_Udlam d \<Longrightarrow> Udlam_stop d \<Longrightarrow> Udlam_end d \<noteq> {}"
    and Udlam_cont_ne:
      "\<And>d. validU d \<Longrightarrow> is_Udlam d \<Longrightarrow> \<not> Udlam_stop d \<Longrightarrow> Udlam_cont d \<noteq> {}"
    and Udlam_end_alpha:
      "\<And>d x t x' t'. validU d \<Longrightarrow> is_Udlam d \<Longrightarrow> Udlam_stop d \<Longrightarrow>
       (x, t) \<in> Udlam_end d \<Longrightarrow> (x', t') \<in> Udlam_end d \<Longrightarrow>
       \<exists>f. bij f \<and> |supp f| <o |UNIV :: 'a set| \<and>
           id_on (set_term t - {x}) f \<and> f x = x' \<and> permute_term f t = t'"
    and Udlam_cont_alpha:
      "\<And>d x u x' u'. validU d \<Longrightarrow> is_Udlam d \<Longrightarrow> \<not> Udlam_stop d \<Longrightarrow>
       (x, u) \<in> Udlam_cont d \<Longrightarrow> (x', u') \<in> Udlam_cont d \<Longrightarrow>
       \<exists>f. bij f \<and> |supp f| <o |UNIV :: 'a set| \<and>
           id_on (UFVars u - {x}) f \<and> f x = x' \<and> Umap f u = u'"
    and UFVars_Udvar:
      "\<And>d. validU d \<Longrightarrow> is_Udvar d \<Longrightarrow> Udvar d \<in> UFVars d"
    and UFVars_Udapp_end1:
      "\<And>d. validU d \<Longrightarrow> is_Udapp d \<Longrightarrow> Udapp_stop1 d \<Longrightarrow>
       set_term (Udapp_end1 d) \<subseteq> UFVars d"
    and UFVars_Udapp_cont1:
      "\<And>d. validU d \<Longrightarrow> is_Udapp d \<Longrightarrow> \<not> Udapp_stop1 d \<Longrightarrow>
       UFVars (Udapp_cont1 d) \<subseteq> UFVars d"
    and UFVars_Udapp_end2:
      "\<And>d. validU d \<Longrightarrow> is_Udapp d \<Longrightarrow> Udapp_stop2 d \<Longrightarrow>
       set_term (Udapp_end2 d) \<subseteq> UFVars d"
    and UFVars_Udapp_cont2:
      "\<And>d. validU d \<Longrightarrow> is_Udapp d \<Longrightarrow> \<not> Udapp_stop2 d \<Longrightarrow>
       UFVars (Udapp_cont2 d) \<subseteq> UFVars d"
    and UFVars_Udlam_end:
      "\<And>d x t. validU d \<Longrightarrow> is_Udlam d \<Longrightarrow> Udlam_stop d \<Longrightarrow>
       (x, t) \<in> Udlam_end d \<Longrightarrow> set_term t - {x} \<subseteq> UFVars d"
    and UFVars_Udlam_cont:
      "\<And>d x u. validU d \<Longrightarrow> is_Udlam d \<Longrightarrow> \<not> Udlam_stop d \<Longrightarrow>
       (x, u) \<in> Udlam_cont d \<Longrightarrow> UFVars u - {x} \<subseteq> UFVars d"
    and Umap_is_Udvar:
      "\<And>d f. validU d \<Longrightarrow> bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow>
       is_Udvar (Umap f d) \<longleftrightarrow> is_Udvar d"
    and Umap_is_Udapp:
      "\<And>d f. validU d \<Longrightarrow> bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow>
       is_Udapp (Umap f d) \<longleftrightarrow> is_Udapp d"
    and Umap_is_Udlam:
      "\<And>d f. validU d \<Longrightarrow> bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow>
       is_Udlam (Umap f d) \<longleftrightarrow> is_Udlam d"
    and Umap_Udapp_stop1:
      "\<And>d f. validU d \<Longrightarrow> bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow>
       is_Udapp d \<Longrightarrow> Udapp_stop1 (Umap f d) \<longleftrightarrow> Udapp_stop1 d"
    and Umap_Udapp_stop2:
      "\<And>d f. validU d \<Longrightarrow> bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow>
       is_Udapp d \<Longrightarrow> Udapp_stop2 (Umap f d) \<longleftrightarrow> Udapp_stop2 d"
    and Umap_Udlam_stop:
      "\<And>d f. validU d \<Longrightarrow> bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow>
       is_Udlam d \<Longrightarrow> Udlam_stop (Umap f d) \<longleftrightarrow> Udlam_stop d"
    and Umap_Udvar:
      "\<And>d f. validU d \<Longrightarrow> bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow>
       is_Udvar d \<Longrightarrow> Udvar (Umap f d) = f (Udvar d)"
    and Umap_Udapp_end1:
      "\<And>d f. validU d \<Longrightarrow> bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow>
       is_Udapp d \<Longrightarrow> Udapp_stop1 d \<Longrightarrow>
       Udapp_end1 (Umap f d) = permute_term f (Udapp_end1 d)"
    and Umap_Udapp_cont1:
      "\<And>d f. validU d \<Longrightarrow> bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow>
       is_Udapp d \<Longrightarrow> \<not> Udapp_stop1 d \<Longrightarrow>
       Udapp_cont1 (Umap f d) = Umap f (Udapp_cont1 d)"
    and Umap_Udapp_end2:
      "\<And>d f. validU d \<Longrightarrow> bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow>
       is_Udapp d \<Longrightarrow> Udapp_stop2 d \<Longrightarrow>
       Udapp_end2 (Umap f d) = permute_term f (Udapp_end2 d)"
    and Umap_Udapp_cont2:
      "\<And>d f. validU d \<Longrightarrow> bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow>
       is_Udapp d \<Longrightarrow> \<not> Udapp_stop2 d \<Longrightarrow>
       Udapp_cont2 (Umap f d) = Umap f (Udapp_cont2 d)"
    and Umap_Udlam_end:
      "\<And>d f. validU d \<Longrightarrow> bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow>
       is_Udlam d \<Longrightarrow> Udlam_stop d \<Longrightarrow>
       Udlam_end (Umap f d) = (\<lambda>(x, t). (f x, permute_term f t)) ` Udlam_end d"
    and Umap_Udlam_cont:
      "\<And>d f. validU d \<Longrightarrow> bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow>
       is_Udlam d \<Longrightarrow> \<not> Udlam_stop d \<Longrightarrow>
       Udlam_cont (Umap f d) = (\<lambda>(x, u). (f x, Umap f u)) ` Udlam_cont d"
    and validU_Udapp_cont1:
      "\<And>d. validU d \<Longrightarrow> is_Udapp d \<Longrightarrow> \<not> Udapp_stop1 d \<Longrightarrow>
       validU (Udapp_cont1 d)"
    and validU_Udapp_cont2:
      "\<And>d. validU d \<Longrightarrow> is_Udapp d \<Longrightarrow> \<not> Udapp_stop2 d \<Longrightarrow>
       validU (Udapp_cont2 d)"
    and validU_Udlam_cont:
      "\<And>d x u. validU d \<Longrightarrow> is_Udlam d \<Longrightarrow> \<not> Udlam_stop d \<Longrightarrow>
       (x, u) \<in> Udlam_cont d \<Longrightarrow> validU u"
    and Umap_comp:
      "\<And>d f g. validU d \<Longrightarrow>
       bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow>
       bij g \<Longrightarrow> |supp g| <o |UNIV :: 'a set| \<Longrightarrow>
       Umap f (Umap g d) = Umap (f \<circ> g) d"
    and Umap_cong_id:
      "\<And>d f. validU d \<Longrightarrow>
       bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow>
       (\<And>a. a \<in> UFVars d \<Longrightarrow> f a = a) \<Longrightarrow> Umap f d = d"
    and validU_Umap:
      "\<And>d f. validU d \<Longrightarrow>
       bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow>
       validU (Umap f d)"
begin

definition Udtor :: "'u \<Rightarrow> ('a, 'a, 'a term + 'u, 'a term + 'u) term_pre set" where
  "Udtor d =
    (if is_Udvar d then {Abs_term_pre (Inl (Udvar d))}
     else if is_Udapp d then
       {Abs_term_pre (Inr (Inl
         ((if Udapp_stop1 d then Inl (Udapp_end1 d) else Inr (Udapp_cont1 d)),
          (if Udapp_stop2 d then Inl (Udapp_end2 d) else Inr (Udapp_cont2 d)))))}
     else if is_Udlam d \<and> Udlam_stop d then
       (\<lambda>(x, t). Abs_term_pre (Inr (Inr (x, Inl t)))) ` Udlam_end d
     else if is_Udlam d \<and> \<not> Udlam_stop d then
       (\<lambda>(x, u). Abs_term_pre (Inr (Inr (x, Inr u)))) ` Udlam_cont d
     else {})"

(* Consequences of the constructor partition *)

lemma is_Udapp_not_Udvar: "validU d \<Longrightarrow> is_Udapp d \<Longrightarrow> \<not> is_Udvar d"
  apply (drule ctor_partition)
  apply (elim disjE conjE)
    apply ((erule notE, assumption) | assumption)+
  done

lemma is_Udlam_not_Udvar: "validU d \<Longrightarrow> is_Udlam d \<Longrightarrow> \<not> is_Udvar d"
  apply (drule ctor_partition)
  apply (elim disjE conjE)
    apply ((erule notE, assumption) | assumption)+
  done

lemma is_Udlam_not_Udapp: "validU d \<Longrightarrow> is_Udlam d \<Longrightarrow> \<not> is_Udapp d"
  apply (drule ctor_partition)
  apply (elim disjE conjE)
    apply ((erule notE, assumption) | assumption)+
  done

(* Case characterisations of Udtor *)

lemma Udtor_Udvar:
  "validU d \<Longrightarrow> is_Udvar d \<Longrightarrow>
   Udtor d = {Abs_term_pre (Inl (Udvar d))}"
  unfolding Udtor_def
  apply (rule if_P, assumption)
  done

lemma Udtor_Udapp:
  "validU d \<Longrightarrow> is_Udapp d \<Longrightarrow>
   Udtor d = {Abs_term_pre (Inr (Inl
     ((if Udapp_stop1 d then Inl (Udapp_end1 d) else Inr (Udapp_cont1 d)),
      (if Udapp_stop2 d then Inl (Udapp_end2 d) else Inr (Udapp_cont2 d)))))}"
  unfolding Udtor_def
  apply (rule trans[OF if_not_P])
   apply (rule is_Udapp_not_Udvar, assumption+)
  apply (rule if_P, assumption)
  done

lemma Udtor_Udlam_stop:
  "validU d \<Longrightarrow> is_Udlam d \<Longrightarrow> Udlam_stop d \<Longrightarrow>
   Udtor d = (\<lambda>(x, t). Abs_term_pre (Inr (Inr (x, Inl t)))) ` Udlam_end d"
  unfolding Udtor_def
  apply (rule trans[OF if_not_P])
   apply (rule is_Udlam_not_Udvar, assumption+)
  apply (rule trans[OF if_not_P])
   apply (rule is_Udlam_not_Udapp, assumption+)
  apply (rule if_P, rule conjI, assumption+)
  done

lemma Udtor_Udlam_cont:
  "validU d \<Longrightarrow> is_Udlam d \<Longrightarrow> \<not> Udlam_stop d \<Longrightarrow>
   Udtor d = (\<lambda>(x, u). Abs_term_pre (Inr (Inr (x, Inr u)))) ` Udlam_cont d"
  unfolding Udtor_def
  apply (rule trans[OF if_not_P])
   apply (rule is_Udlam_not_Udvar, assumption+)
  apply (rule trans[OF if_not_P])
   apply (rule is_Udlam_not_Udapp, assumption+)
  apply (rule trans[OF if_not_P])
   apply (rule contrapos_nn[of "Udlam_stop d"], assumption, erule conjunct2)
  apply (rule if_P, rule conjI, assumption+)
  done

(* Properties of the App argument summands *)

lemma UFVars_Udapp_if1:
  "validU d \<Longrightarrow> is_Udapp d \<Longrightarrow>
   case_sum set_term UFVars
     (if Udapp_stop1 d then Inl (Udapp_end1 d) else Inr (Udapp_cont1 d)) \<subseteq> UFVars d"
  apply (cases "Udapp_stop1 d")
   apply (subst if_P, assumption)
   apply (unfold sum.case)
   apply (rule UFVars_Udapp_end1, assumption+)
  apply (subst if_not_P, assumption)
  apply (unfold sum.case)
  apply (rule UFVars_Udapp_cont1, assumption+)
  done

lemma UFVars_Udapp_if2:
  "validU d \<Longrightarrow> is_Udapp d \<Longrightarrow>
   case_sum set_term UFVars
     (if Udapp_stop2 d then Inl (Udapp_end2 d) else Inr (Udapp_cont2 d)) \<subseteq> UFVars d"
  apply (cases "Udapp_stop2 d")
   apply (subst if_P, assumption)
   apply (unfold sum.case)
   apply (rule UFVars_Udapp_end2, assumption+)
  apply (subst if_not_P, assumption)
  apply (unfold sum.case)
  apply (rule UFVars_Udapp_cont2, assumption+)
  done

lemma validU_Udapp_if1:
  "validU d \<Longrightarrow> is_Udapp d \<Longrightarrow>
   pred_sum (\<lambda>_. True) validU
     (if Udapp_stop1 d then Inl (Udapp_end1 d) else Inr (Udapp_cont1 d))"
  apply (cases "Udapp_stop1 d")
   apply (subst if_P, assumption)
   apply (unfold pred_sum_inject)
   apply (rule TrueI)
  apply (subst if_not_P, assumption)
  apply (unfold pred_sum_inject)
  apply (rule validU_Udapp_cont1, assumption+)
  done

lemma validU_Udapp_if2:
  "validU d \<Longrightarrow> is_Udapp d \<Longrightarrow>
   pred_sum (\<lambda>_. True) validU
     (if Udapp_stop2 d then Inl (Udapp_end2 d) else Inr (Udapp_cont2 d))"
  apply (cases "Udapp_stop2 d")
   apply (subst if_P, assumption)
   apply (unfold pred_sum_inject)
   apply (rule TrueI)
  apply (subst if_not_P, assumption)
  apply (unfold pred_sum_inject)
  apply (rule validU_Udapp_cont2, assumption+)
  done

lemma Umap_Udapp_if1:
  "validU d \<Longrightarrow> bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow> is_Udapp d \<Longrightarrow>
   (if Udapp_stop1 (Umap f d) then Inl (Udapp_end1 (Umap f d))
    else Inr (Udapp_cont1 (Umap f d))) =
   map_sum (permute_term f) (Umap f)
     (if Udapp_stop1 d then Inl (Udapp_end1 d) else Inr (Udapp_cont1 d))"
  apply (cases "Udapp_stop1 d")
   apply (subst if_P)
    apply (rule Umap_Udapp_stop1[THEN iffD2], assumption+)
   apply (subst if_P, assumption)
   apply (unfold map_sum.simps)
   apply (rule arg_cong[of _ _ Inl])
   apply (rule Umap_Udapp_end1, assumption+)
  apply (subst if_not_P)
   apply (rule contrapos_nn[of "Udapp_stop1 d"], assumption)
   apply (rule Umap_Udapp_stop1[THEN iffD1], assumption+)
  apply (subst if_not_P, assumption)
  apply (unfold map_sum.simps)
  apply (rule arg_cong[of _ _ Inr])
  apply (rule Umap_Udapp_cont1, assumption+)
  done

lemma Umap_Udapp_if2:
  "validU d \<Longrightarrow> bij f \<Longrightarrow> |supp f| <o |UNIV :: 'a set| \<Longrightarrow> is_Udapp d \<Longrightarrow>
   (if Udapp_stop2 (Umap f d) then Inl (Udapp_end2 (Umap f d))
    else Inr (Udapp_cont2 (Umap f d))) =
   map_sum (permute_term f) (Umap f)
     (if Udapp_stop2 d then Inl (Udapp_end2 d) else Inr (Udapp_cont2 d))"
  apply (cases "Udapp_stop2 d")
   apply (subst if_P)
    apply (rule Umap_Udapp_stop2[THEN iffD2], assumption+)
   apply (subst if_P, assumption)
   apply (unfold map_sum.simps)
   apply (rule arg_cong[of _ _ Inl])
   apply (rule Umap_Udapp_end2, assumption+)
  apply (subst if_not_P)
   apply (rule contrapos_nn[of "Udapp_stop2 d"], assumption)
   apply (rule Umap_Udapp_stop2[THEN iffD1], assumption+)
  apply (subst if_not_P, assumption)
  apply (unfold map_sum.simps)
  apply (rule arg_cong[of _ _ Inr])
  apply (rule Umap_Udapp_cont2, assumption+)
  done

(* Factored unfold blocks *)

lemmas term_pre_map_simps =
  map_term_pre_def comp_def Abs_term_pre_inverse[OF UNIV_I]
  map_sum.simps map_prod_simp sum.case prod.case
  fst_conv snd_conv id_apply

lemmas term_pre_set_simps =
  set1_term_pre_def set2_term_pre_def set3_term_pre_def set4_term_pre_def
  comp_def Abs_term_pre_inverse[OF UNIV_I]
  map_sum.simps map_prod_simp sum_set_simps prod_set_simps sum.case
  image_insert image_empty image_Un
  Union_insert Union_empty Union_Un_distrib
  Un_empty_left Un_empty_right
  empty_Diff Diff_empty

lemmas ball_unfolds = ball_Un ball_simps simp_thms

interpretation HL_to_LL: COREC_term Udtor Umap UFVars validU
  apply unfold_locales

  (* Udtor_ne *)
  subgoal for d
    apply (frule ctor_partition)
    apply (elim disjE conjE)
      apply (subst Udtor_Udvar, assumption+)
      apply (rule insert_not_empty)
     apply (subst Udtor_Udapp, assumption+)
     apply (rule insert_not_empty)
    apply (cases "Udlam_stop d")
     apply (subst Udtor_Udlam_stop, assumption+)
     apply (unfold image_is_empty)
     apply (rule Udlam_end_ne, assumption+)
    apply (subst Udtor_Udlam_cont, assumption+)
    apply (unfold image_is_empty)
    apply (rule Udlam_cont_ne, assumption+)
    done

  (* alpha_Udtor *)
  subgoal for X X' d
    apply (frule ctor_partition)
    apply (elim disjE conjE)
      subgoal
        apply (subst (asm) Udtor_Udvar, assumption+)
        apply (unfold insert_subset singleton_iff)
        apply ((erule conjE)+)?
        apply hypsubst_thin
        apply (rule exI[where x=id])
        apply (rule conjI bij_id supp_id_bound id_on_id)+
        apply (unfold term_pre_map_simps)
        apply (rule refl)
        done
     subgoal
       apply (subst (asm) Udtor_Udapp, assumption+)
       apply (unfold insert_subset singleton_iff)
       apply ((erule conjE)+)?
       apply hypsubst_thin
       apply (rule exI[where x=id])
       apply (rule conjI bij_id supp_id_bound id_on_id)+
       apply (unfold term_pre_map_simps)
       apply (rule refl)
       done
    apply (cases "Udlam_stop d")
     subgoal
       apply (subst (asm) Udtor_Udlam_stop, assumption+)
       apply (unfold insert_subset)
       apply ((erule conjE)+)?
       apply (erule imageE)+
       apply hypsubst_thin
       subgoal for p p'
         apply (cases p)
         apply (cases p')
         apply hypsubst_thin
         apply (unfold prod.case)
         subgoal for x t x' t'
           apply (unfold term_pre_set_simps)
           apply (frule Udlam_end_alpha[of _ x t x' t'], assumption+)
           apply (erule exE)
           apply ((erule conjE)+)?
           apply hypsubst_thin
           apply (rule exI)
           apply ((rule conjI, assumption)+)
           apply (unfold term_pre_map_simps)
           apply (rule refl)
           done
         done
       done
    subgoal
      apply (subst (asm) Udtor_Udlam_cont, assumption+)
      apply (unfold insert_subset)
      apply ((erule conjE)+)?
      apply (erule imageE)+
      apply hypsubst_thin
      subgoal for p p'
        apply (cases p)
        apply (cases p')
        apply hypsubst_thin
        apply (unfold prod.case)
        subgoal for x u x' u'
          apply (unfold term_pre_set_simps)
          apply (frule Udlam_cont_alpha[of _ x u x' u'], assumption+)
          apply (erule exE)
          apply ((erule conjE)+)?
          apply hypsubst_thin
          apply (rule exI)
          apply ((rule conjI, assumption)+)
          apply (unfold term_pre_map_simps)
          apply (rule refl)
          done
        done
      done
    done

  (* UFVars_Udtor *)
  subgoal for d X
    apply (frule ctor_partition)
    apply (elim disjE conjE)
      subgoal
        apply (subst (asm) Udtor_Udvar, assumption+)
        apply (drule singletonD)
        apply hypsubst_thin
        apply (unfold term_pre_set_simps insert_subset)
        apply (rule conjI)
         apply (rule UFVars_Udvar, assumption+)
        apply (rule empty_subsetI)
        done
     subgoal
       apply (subst (asm) Udtor_Udapp, assumption+)
       apply (drule singletonD)
       apply hypsubst_thin
       apply (unfold term_pre_set_simps)
       apply (rule Un_least)
        apply (rule UFVars_Udapp_if1, assumption+)
       apply (rule UFVars_Udapp_if2, assumption+)
       done
    apply (cases "Udlam_stop d")
     subgoal
       apply (subst (asm) Udtor_Udlam_stop, assumption+)
       apply (erule imageE)
       apply hypsubst_thin
       subgoal for p
         apply (cases p)
         apply hypsubst_thin
         apply (unfold prod.case term_pre_set_simps)
         apply (rule UFVars_Udlam_end, assumption+)
         done
       done
    subgoal
      apply (subst (asm) Udtor_Udlam_cont, assumption+)
      apply (erule imageE)
      apply hypsubst_thin
      subgoal for p
        apply (cases p)
        apply hypsubst_thin
        apply (unfold prod.case term_pre_set_simps)
        apply (rule UFVars_Udlam_cont, assumption+)
        done
      done
    done

  (* Umap_Udtor *)
  subgoal for f d
    apply (frule ctor_partition)
    apply (elim disjE conjE)
      subgoal
        apply (subst Udtor_Udvar)
          apply (rule validU_Umap, assumption+)
         apply (rule Umap_is_Udvar[THEN iffD2], assumption+)
        apply (subst Udtor_Udvar, assumption+)
        apply (subst Umap_Udvar, assumption+)
        apply (unfold image_insert image_empty term_pre_map_simps)
        apply (rule subset_refl)
        done
     subgoal
       apply (subst Udtor_Udapp)
         apply (rule validU_Umap, assumption+)
        apply (rule Umap_is_Udapp[THEN iffD2], assumption+)
       apply (subst Udtor_Udapp, assumption+)
       apply (subst Umap_Udapp_if1, assumption+)
       apply (subst Umap_Udapp_if2, assumption+)
       apply (unfold image_insert image_empty term_pre_map_simps)
       apply (rule subset_refl)
       done
    apply (cases "Udlam_stop d")
     subgoal
       apply (subst Udtor_Udlam_stop)
          apply (rule validU_Umap, assumption+)
         apply (rule Umap_is_Udlam[THEN iffD2], assumption+)
        apply (rule Umap_Udlam_stop[THEN iffD2], assumption+)
       apply (subst Udtor_Udlam_stop, assumption+)
       apply (subst Umap_Udlam_end, assumption+)
       apply (unfold image_image split_beta term_pre_map_simps)
       apply (rule subset_refl)
       done
    subgoal
      apply (subst Udtor_Udlam_cont)
         apply (rule validU_Umap, assumption+)
        apply (rule Umap_is_Udlam[THEN iffD2], assumption+)
       apply (rule contrapos_nn[of "Udlam_stop d"], assumption)
       apply (rule Umap_Udlam_stop[THEN iffD1], assumption+)
      apply (subst Udtor_Udlam_cont, assumption+)
      apply (subst Umap_Udlam_cont, assumption+)
      apply (unfold image_image split_beta term_pre_map_simps)
      apply (rule subset_refl)
      done
    done

  apply (rule Umap_comp; assumption)
   apply (rule Umap_cong_id; assumption)
  apply (rule validU_Umap; assumption)

  (* valid_Udtor *)
  subgoal for d X
    apply (frule ctor_partition)
    apply (elim disjE conjE)
      subgoal
        apply (subst (asm) Udtor_Udvar, assumption+)
        apply (drule singletonD)
        apply hypsubst_thin
        apply (unfold term_pre.pred_set term_pre_set_simps ball_unfolds)
        apply (rule TrueI)
        done
     subgoal
       apply (subst (asm) Udtor_Udapp, assumption+)
       apply (drule singletonD)
       apply hypsubst_thin
       apply (unfold term_pre.pred_set term_pre_set_simps ball_unfolds)
       apply (rule conjI)
        apply (rule validU_Udapp_if1, assumption+)
       apply (rule validU_Udapp_if2, assumption+)
       done
    apply (cases "Udlam_stop d")
     subgoal
       apply (subst (asm) Udtor_Udlam_stop, assumption+)
       apply (erule imageE)
       apply hypsubst_thin
       subgoal for p
         apply (cases p)
         apply hypsubst_thin
         apply (unfold prod.case term_pre.pred_set term_pre_set_simps ball_unfolds
                  pred_sum_inject)
         apply (rule TrueI)
         done
       done
    subgoal
      apply (subst (asm) Udtor_Udlam_cont, assumption+)
      apply (erule imageE)
      apply hypsubst_thin
      subgoal for p
        apply (cases p)
        apply hypsubst_thin
        apply (unfold prod.case term_pre.pred_set term_pre_set_simps ball_unfolds
                 pred_sum_inject)
        apply (rule validU_Udlam_cont, assumption+)
        done
      done
    done
  done

definition HL_COREC_term :: "'u \<Rightarrow> 'a term" where
  "HL_COREC_term = HL_to_LL.COREC_term"

lemma HL_COREC_term_Var:
  "validU u \<Longrightarrow> is_Udvar u \<Longrightarrow> HL_COREC_term u = Var (Udvar u)"
  unfolding HL_COREC_term_def Var_def
  apply (subst HL_to_LL.COREC_dtor[of "Abs_term_pre (Inl (Udvar u))"])
    apply (subst Udtor_Udvar, assumption+)
    apply (rule insertI1)
   apply assumption
  apply (unfold term_pre_map_simps)
  apply (rule refl)
  done

lemma HL_COREC_term_App:
  "validU u \<Longrightarrow> is_Udapp u \<Longrightarrow>
   HL_COREC_term u =
     App (if Udapp_stop1 u then Udapp_end1 u else HL_COREC_term (Udapp_cont1 u))
         (if Udapp_stop2 u then Udapp_end2 u else HL_COREC_term (Udapp_cont2 u))"
  unfolding HL_COREC_term_def App_def
  apply (subst HL_to_LL.COREC_dtor[of
    "Abs_term_pre (Inr (Inl
       ((if Udapp_stop1 u then Inl (Udapp_end1 u) else Inr (Udapp_cont1 u)),
        (if Udapp_stop2 u then Inl (Udapp_end2 u) else Inr (Udapp_cont2 u)))))"])
    apply (subst Udtor_Udapp, assumption+)
    apply (rule insertI1)
   apply assumption
  apply (unfold term_pre_map_simps case_sum_if)
  apply (rule refl)
  done

lemma HL_COREC_term_Lam_stop:
  "validU u \<Longrightarrow> is_Udlam u \<Longrightarrow> Udlam_stop u \<Longrightarrow> (x, t) \<in> Udlam_end u \<Longrightarrow>
   HL_COREC_term u = Lam x t"
  unfolding HL_COREC_term_def Lam_def
  apply (subst HL_to_LL.COREC_dtor[of "Abs_term_pre (Inr (Inr (x, Inl t)))"])
    apply (subst Udtor_Udlam_stop, assumption+)
    apply (rule image_eqI[of _ _ "(x, t)"])
     apply (unfold prod.case)
     apply (rule refl)
    apply assumption+
  apply (unfold term_pre_map_simps)
  apply (rule refl)
  done

lemma HL_COREC_term_Lam_cont:
  "validU u \<Longrightarrow> is_Udlam u \<Longrightarrow> \<not> Udlam_stop u \<Longrightarrow> (x, u') \<in> Udlam_cont u \<Longrightarrow>
   HL_COREC_term u = Lam x (HL_COREC_term u')"
  unfolding HL_COREC_term_def Lam_def
  apply (subst HL_to_LL.COREC_dtor[of "Abs_term_pre (Inr (Inr (x, Inr u')))"])
    apply (subst Udtor_Udlam_cont, assumption+)
    apply (rule image_eqI[of _ _ "(x, u')"])
     apply (unfold prod.case)
     apply (rule refl)
    apply assumption+
  apply (unfold term_pre_map_simps)
  apply (rule refl)
  done

lemmas HL_COREC_term_swap   = HL_to_LL.COREC_swap[folded HL_COREC_term_def]
lemmas HL_COREC_term_UFVars = HL_to_LL.COREC_FVars[folded HL_COREC_term_def]
lemmas HL_COREC_term_dtor   = HL_to_LL.COREC_dtor[folded HL_COREC_term_def]

end

interpretation const_HL: HL_COREC_term
  where
        Umap        = "image :: ('a :: covar \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> 'a set"
    and UFVars      = "id :: 'a :: covar set \<Rightarrow> 'a set"
    and validU      = "finite :: 'a :: covar set \<Rightarrow> bool"
    and is_Udvar    = "\<lambda>_. False"
    and Udvar       = "\<lambda>_. undefined"
    and is_Udapp    = "\<lambda>_. False"
    and Udapp_stop1 = "\<lambda>_. undefined"
    and Udapp_end1  = "\<lambda>_. undefined"
    and Udapp_cont1 = "\<lambda>_. undefined"
    and Udapp_stop2 = "\<lambda>_. undefined"
    and Udapp_end2  = "\<lambda>_. undefined"
    and Udapp_cont2 = "\<lambda>_. undefined"
    and is_Udlam    = "\<lambda>_. True"
    and Udlam_stop  = "\<lambda>_. False"
    and Udlam_end   = "\<lambda>_. {}"
    and Udlam_cont  = "\<lambda>A. {(z, insert z A) | z. z \<notin> A}"
  apply unfold_locales
                      apply (simp_all add: arb_element image_image)
  subgoal for A x x'
    apply (rule exI[where x="swap x x'"])
    apply (auto simp: id_on_def)
      apply (metis swap_simps(3))
     apply (metis swap_simps(3))
    apply (metis image_iff swap_simps(3))
    done
  subgoal for A f
    apply (rule set_eqI, auto simp: image_iff bij_inv_eq_iff)
     subgoal for z by (rule exI[where x="inv f z"]) (auto simp: bij_inv_eq_iff)
    by (metis bij_betw_imp_inj_on inj_eq)
  done

lemma "finite A \<Longrightarrow> z \<notin> A \<Longrightarrow>
  const_HL.HL_COREC_term A = Lam z (const_HL.HL_COREC_term (insert z A))"
  by (subst const_HL.HL_COREC_term_Lam_cont[where x=z and u'="insert z A"]) auto

end
