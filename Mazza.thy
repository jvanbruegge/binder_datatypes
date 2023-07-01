theory Mazza
  imports
    "thys/MRBNF_Recursor"
    "HOL-Library.Linear_Temporal_Logic_on_Streams"
    "HOL-Library.Prefix_Order"
    "HOL-Library.Countable_Set_Type"
    "HOL-Library.Extended_Nat"
    "HOL-Cardinals.Cardinals"
    "HOL-Library.Disjoint_Sets"
    "HOL-Library.BNF_Corec"
begin

(*untyped lambda calculus*)
(* binder_datatype 'a lam =
  Var 'a
| App "'a lam" "'a lam"
| Abs x::'a t::"'a lam" binds x in t
*)

ML \<open>
val ctors = [
  (("Var", (NONE : mixfix option)), [@{typ 'var}]),
  (("App", NONE), [@{typ 'rec}, @{typ "'rec"}]),
  (("Abs", NONE), [@{typ "'bvar"}, @{typ 'brec}])
]

val spec = {
  fp_b = @{binding "lam"},
  vars = [
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[0]],
  rec_vars = 2,
  ctors = ctors,
  map_b = @{binding vvsubst},
  tvsubst_b = @{binding tvsubst}
}
\<close>

declare [[mrbnf_internals]]
local_setup \<open> MRBNF_Sugar.create_binder_datatype spec \<close>
print_mrbnfs

abbreviation "fv \<equiv> FFVars_lam"

class infinite_regular =
  assumes large: "|Field (card_suc natLeq)| \<le>o |UNIV::'a set|" and regular: "regularCard |UNIV::'a set|"

lemma infinite_natLeq: "natLeq \<le>o |A| \<Longrightarrow> infinite A"
  using infinite_iff_natLeq_ordLeq by blast

lemma infinite: "infinite (UNIV :: 'a ::infinite_regular set)"
  using ordLeq_transitive[OF ordLess_imp_ordLeq[OF card_suc_greater_set[OF natLeq_card_order ordLeq_refl[OF natLeq_Card_order]]]
      ordIso_ordLeq_trans[OF ordIso_symmetric[OF card_of_Field_ordIso[OF Card_order_card_suc[OF natLeq_card_order]]] large]]
  by (rule infinite_natLeq)

lemma infinite_ex_inj: "\<exists>f :: nat \<Rightarrow> 'a :: infinite_regular. inj f"
  by (rule infinite_countable_subset[OF infinite, simplified])

(*countably infinite set*)
typedef 'a :: infinite_regular cinfset = "{X :: 'a set. infinite X \<and> countable X}"
  morphisms set_cinfset Abs_cinfset
  using infinite_countable_subset'[OF infinite] by auto

abbreviation in_cinfset  ("(_/ \<in>\<in> _)" [51, 51] 50) where
  "x \<in>\<in> X \<equiv> x \<in> set_cinfset X"

setup_lifting type_definition_cinfset

lift_definition image_cinfset :: "('a :: infinite_regular \<Rightarrow> 'a) \<Rightarrow> 'a cinfset \<Rightarrow> 'a cinfset" is
  "\<lambda>f X. if inj_on f X then f ` X else X"
  by (auto simp: finite_image_iff)

mrbnf "'a ::infinite_regular cinfset"
  map: image_cinfset
  sets: bound: set_cinfset
  bd: "card_suc natLeq"
  var_class: infinite_regular
  subgoal by (rule ext, transfer) simp
  subgoal by (rule ext, transfer) (simp add: image_comp bij_is_inj inj_on_subset[OF _ subset_UNIV])
  subgoal by transfer (simp add: image_comp bij_is_inj inj_on_subset[OF _ subset_UNIV])
  subgoal by (rule ext, transfer) (simp add: image_comp bij_is_inj inj_on_subset[OF _ subset_UNIV])
  subgoal by (rule infinite_regular_card_order_card_suc[OF natLeq_card_order natLeq_Cinfinite])
  subgoal
    apply (rule card_suc_greater_set[OF natLeq_card_order])
    apply transfer
    apply (simp flip: countable_card_le_natLeq)
    done
  subgoal by blast
  subgoal by (clarsimp, transfer) auto
  done

lift_definition get_cinfset :: "'a :: infinite_regular cinfset \<Rightarrow> nat \<Rightarrow> 'a" is "from_nat_into" .

lemma bij_betw_get_cinfset: "bij_betw (get_cinfset S) UNIV (set_cinfset S)"
  by transfer (simp add: bij_betw_from_nat_into)

lemma inj_get_cinfset: "inj (get_cinfset S)"
  by (metis bij_betw_def bij_betw_get_cinfset)

lemma get_cinfset_in: "get_cinfset S n \<in>\<in> S"
  by (metis bij_betw_def bij_betw_get_cinfset rangeI)

(*countably infinite multiset*)
typedef 'a cinfmset = "{f :: 'a \<Rightarrow> enat. countable {x. f x \<noteq> 0} \<and>
  (infinite {x. f x \<noteq> 0} \<or> (\<exists>x. f x = \<infinity>))}"
  morphisms count_cinfmset Abs_cinfmset
  by (rule exI[of _ "\<lambda>x. if x = undefined then \<infinity> else 0"]) auto

setup_lifting type_definition_cinfmset

lemma sum_infinite_enat: "finite X \<Longrightarrow> sum g X = (\<infinity> :: enat) \<longleftrightarrow> (\<exists>x \<in> X. g x = \<infinity>)"
  by (induct X rule: finite_induct) auto

lemma sum_infinite_enat': "finite X \<Longrightarrow>  (\<infinity> :: enat) = sum g X \<longleftrightarrow> (\<exists>x \<in> X. g x = \<infinity>)"
  by (metis sum_infinite_enat)

lift_definition set_cinfmset :: "'a cinfmset \<Rightarrow> 'a set" is
  "\<lambda>g. {x. g x \<noteq> 0}" .

abbreviation in_cinfmset  ("(_/ \<in>#\<in> _)" [51, 51] 50) where
  "x \<in>#\<in> X \<equiv> x \<in> set_cinfmset X"

function count_stream :: "'a stream \<Rightarrow> 'a \<Rightarrow> enat" where
  "count_stream s x = (if x \<notin> sset s then 0
     else if (\<forall>n. x \<in> sset (sdrop n s)) then \<infinity>
     else (if x = shd s then eSuc else id) (count_stream (stl s) x))"
  by auto
termination
  apply (relation "measure (\<lambda>(s, x). LEAST n. x \<notin> sset (sdrop n s))")
   apply (simp_all add: sset_range image_iff flip: snth.simps(2))
  apply safe
  apply (subst (2) Least_Suc)
    apply auto
  done
declare count_stream.simps[simp del]

lemma count_stream_zero_iff:  "count_stream s x = 0 \<longleftrightarrow> x \<notin> sset s"
  apply (induct s x rule: count_stream.induct)
  apply (auto simp: count_stream.simps split: if_splits)
  by (metis stream.sel(1) stream.sel(2) stream.set_cases)

lemma count_stream_infinity_iff: "count_stream s x = \<infinity> \<longleftrightarrow> alw (ev (HLD {x})) s"
  apply (induct s x rule: count_stream.induct)
  apply (subst count_stream.simps)
  apply (auto simp: shd_sset alw_iff_sdrop ev_holds_sset simp flip: holds_eq1 dest: spec[of _ 0])
   apply (metis (mono_tags, lifting) eSuc_infinity eSuc_inject ev_iff_sdrop sdrop_simps(1) sdrop_stl snth_sset stl_sset)
  apply (metis (mono_tags, lifting) ev_iff_sdrop sdrop_simps(1) sdrop_stl snth_sset stl_sset)
  done

lemma count_stream_infinity_iff': "\<infinity> = count_stream s x  \<longleftrightarrow> alw (ev (HLD {x})) s"
  by (metis count_stream_infinity_iff)

lemma exists_infinite_count: "finite (sset s) \<Longrightarrow> \<exists>x \<in> sset s. count_stream s x = \<infinity>"
  by (erule pigeonhole_stream[of "sset s" s, folded count_stream_infinity_iff, rotated])
    (auto simp: alw_iff_sdrop HLD_def)

lift_definition cinfmset :: "'a stream \<Rightarrow> 'a cinfmset" is count_stream
  apply safe
   apply (simp add: sset_range count_stream_zero_iff)
  apply (auto simp: count_stream_zero_iff dest!: exists_infinite_count)
  apply (metis enat.distinct(2))
  done

lemma set_cinfmset_cinfmset[simp]: "set_cinfmset (cinfmset s) = sset s"
  by transfer (auto simp: count_stream_zero_iff)

definition rel_cinfmset where
  "rel_cinfmset R X Y \<longleftrightarrow> (\<exists>s s'. cinfmset s = X \<and> cinfmset s' = Y \<and> stream_all2 R s s')"

lemma disjE1': "P \<or> Q \<Longrightarrow> (P \<Longrightarrow> \<not> Q \<Longrightarrow> R) \<Longrightarrow> (Q \<Longrightarrow> R) \<Longrightarrow> R"
  by auto
lemma disjE2': "P \<or> Q \<Longrightarrow> (P \<Longrightarrow> R) \<Longrightarrow> (Q \<Longrightarrow> \<not> P \<Longrightarrow> R) \<Longrightarrow> R"
  by auto

lift_definition image_cinfmset :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a cinfmset \<Rightarrow> 'b cinfmset" is
  "\<lambda>f g y. let X = f -` {y} \<inter> {x. g x \<noteq> 0} in if infinite X then \<infinity> else sum g X"
  subgoal for f g
    apply (erule conj_mono[rule_format, rotated -1])
     apply (auto simp: Let_def) []
     apply (drule countable_image[of _ f])
     apply (erule countable_subset[rotated])
     apply auto []
     apply (smt (verit, best) disjoint_iff_not_equal finite.simps image_iff vimage_singleton_eq)
    apply (erule disjE1')
     apply (auto simp: Let_def sum_infinite_enat)
     apply (erule contrapos_np)
     apply simp
     apply (rule finite_subset[rotated])
      apply (rule finite_UN[THEN iffD2])
       apply assumption
      apply (rule ballI)
      apply (erule spec)
     apply auto
    apply fastforce
    done
  done

lemma count_image_cinfmset:
  \<open>count_cinfmset (image_cinfmset f A) x =
   (if infinite (f -` {x} \<inter> set_cinfmset A) then \<infinity>
   else (\<Sum>y\<in>f -` {x} \<inter> set_cinfmset A. count_cinfmset A y))\<close>
  by transfer auto

lemma cinfmset_eqI: "(\<forall>x. count_cinfmset A x = count_cinfmset B x) \<Longrightarrow> A = B"
  by transfer auto

lemma cinfmset_set_map: "set_cinfmset (image_cinfmset f A) = f ` set_cinfmset A"
  apply transfer
  apply (auto simp: Let_def image_iff)
   apply (metis (mono_tags, lifting) disjoint_iff_not_equal finite.emptyI mem_Collect_eq vimage_singleton_eq)
  apply (metis (mono_tags, lifting) disjoint_iff_not_equal finite.emptyI mem_Collect_eq vimage_singleton_eq)
  done

lemma cinfmset_map_comp: "image_cinfmset f (image_cinfmset g A) = image_cinfmset (f o g) A"
  apply (rule cinfmset_eqI)
  apply (auto simp: count_image_cinfmset sum_infinite_enat sum_infinite_enat' cinfmset_set_map
      simp flip: vimage_comp)
    apply (drule finite_imageI[of _ g])
    apply (erule notE)
    apply (erule finite_subset[rotated])
    apply auto []
   apply (erule contrapos_np)
   apply auto []
   apply (rule finite_subset[rotated])
    apply (rule finite_UN[THEN iffD2])
     apply assumption
    apply (rule ballI)
    apply (drule bspec)
     apply assumption
    apply (erule conjunct1)
   apply auto []
  apply (subst sum.If_cases)
   apply assumption
  apply (auto simp: of_nat_eq_enat sum_infinite_enat sum_infinite_enat')
  subgoal
    apply (rule trans[OF _ sum.group[where g=g]])
       apply (rule sum.cong[OF refl])
       apply (rule sum.cong[OF _ refl])
       apply auto []
      apply assumption
     apply blast
    apply blast
    done
  apply (smt (verit, del_insts) Int_assoc Int_insert_right_if1 Int_left_commute finite_Int inf_bot_right insertI1 vimageI2 vimage_Int)
  done

lemma eSuc_infinity_iff: "eSuc x = \<infinity> \<longleftrightarrow> x = \<infinity>"
  by (cases x) (auto simp: eSuc_enat)

lemma pigeonhole_stream_strong:
  assumes "alw (ev (HLD s)) \<omega>"
  assumes "finite s"
  shows "\<exists>x\<in>s. alw (ev (HLD {x})) \<omega>"
proof -
  obtain S where "infinite S" "\<forall>i \<in> S. \<exists>x\<in>s. \<omega> !! i = x"
    using \<open>alw (ev (HLD s)) \<omega>\<close>
    apply atomize_elim
    apply (auto simp add: alw_iff_sdrop ev_iff_sdrop HLD_iff le_iff_add choice_iff)
    by (metis infinite_nat_iff_unbounded_le le_add1 sdrop_snth vimage_eq)
  from pigeonhole_infinite_rel[OF this(1) \<open>finite s\<close> this(2)]
  show ?thesis
    by (auto simp add: HLD_iff simp flip: infinite_iff_alw_ev)
qed

lemma exist_infinite_preimage:
  "finite (f -` {x} \<inter> sset s) \<Longrightarrow> \<forall>n. \<exists>y\<in>sset (sdrop n s). x = f y \<Longrightarrow>
  \<exists>y. x = f y \<and> alw (ev (HLD {y})) s"
  using pigeonhole_stream_strong[of "f -` {x} \<inter> sset s" s]
  apply (auto simp: alw_iff_sdrop ev_iff_sdrop HLD_iff sset_range sdrop_snth)
  apply (metis IntD1 vimage_singleton_eq)
  done

lemma count_stream_smap: "finite (f -` {x} \<inter> sset s) \<Longrightarrow>
  count_stream (smap f s) x = sum (count_stream s) (f -` {x} \<inter> sset s)"
  apply (induct "smap f s" x arbitrary: s rule: count_stream.induct)
  apply (subst (1 2) count_stream.simps[abs_def])
  apply (auto simp: stream.set_map image_iff shd_sset sum_infinite_enat' intro: sum.neutral)
  subgoal for s x
    apply (drule (1) exist_infinite_preimage)
    apply (auto)
    by (metis (no_types, opaque_lifting) IntI alw_ev_stl count_stream.elims count_stream_infinity_iff eSuc_infinity i0_ne_infinity vimage_singleton_eq)
  subgoal premises prems for s n x
    using prems(2-)
    apply (subst prems(1))
        apply (auto elim!: finite_subset[rotated] stream.set_sel(2))
    apply (subst (2) sum.remove[of _ "shd s"])
      apply (auto simp: shd_sset sum.If_cases)
     apply metis
    apply (subst card_0_eq[THEN iffD2])
      apply (auto elim!: finite_subset[rotated] stream.set_sel(2))
     apply metis
    apply (subst (3) Int_absorb2)
     apply auto
     apply metis
    apply (cases "shd s \<in> sset (stl s)")
     apply (subst sum.remove[of _ "shd s"])
       apply (auto simp: iadd_Suc elim!: finite_subset[rotated] stream.set_sel(2)
        intro!: sum.cong)
     apply (metis stream.sel(1) stream.sel(2) stream.set_cases)
    apply (subst count_stream_zero_iff[THEN iffD2, of "shd s"])
     apply assumption
    apply (auto intro!: sum.cong elim!: stream.set_sel(2))
    apply (metis stream.sel(1) stream.sel(2) stream.set_cases)
    done
  subgoal for s x
    apply (drule (1) exist_infinite_preimage)
    apply (auto)
    by (metis (no_types, opaque_lifting) IntI alw_ev_stl count_stream.elims count_stream_infinity_iff i0_ne_infinity vimage_singleton_eq)
  subgoal premises prems for s n x
    using prems(2-)
    apply (subst prems(1))
        apply (auto elim!: finite_subset[rotated] stream.set_sel(2))
    apply (auto simp: shd_sset sum.If_cases)
    apply (subst card_0_eq[THEN iffD2])
      apply (auto elim!: finite_subset[rotated] stream.set_sel(2))
     apply metis
    apply (subst (3) Int_absorb2)
     apply auto
     apply metis
    apply (rule sum.cong)
     apply auto
     apply (auto intro!: sum.cong elim!: stream.set_sel(2))
    apply (metis stream.sel(1) stream.sel(2) stream.set_cases)
    done
  done

lemma image_cinfmset_cinfmset[simp]: "image_cinfmset f (cinfmset s) = cinfmset (smap f s)"
  by transfer
    (auto simp: fun_eq_iff Let_def count_stream_infinity_iff' count_stream_zero_iff sset_range
      infinite_iff_alw_ev[symmetric] count_stream_smap simp flip: holds_eq1 intro: finite_surj[of _ _ "snth _"])

lift_definition NATS_cinfmset :: "nat cinfmset" is "\<lambda>x::nat. 1"
  by auto

definition "spermute \<pi> s = smap (\<lambda>i. snth s (\<pi> i)) nats"

lemma sset_spermute: "bij \<pi> \<Longrightarrow> sset (spermute \<pi> s) = sset s"
  apply (auto simp: spermute_def stream.set_map sset_range image_iff)
  apply (metis bij_pointE)
  done

lemma count_stream_fromN: "count_stream (fromN n) x = (if x < n then 0 else 1)"
  apply (induct "fromN n" x arbitrary: n rule: count_stream.induct)
  apply (subst count_stream.simps)
  apply (auto simp: count_stream_zero_iff one_eSuc not_less)
  using add_leD1 linorder_not_le apply blast
  done

lemma count_stream_alt: "count_stream s x = (let I = (!!) s -` {x} in if infinite I then \<infinity> else card I)"
  apply (cases "count_stream s x = \<infinity>")
   apply (auto simp: count_stream_infinity_iff Let_def alw_iff_sdrop ev_iff_sdrop HLD_iff
      infinite_nat_iff_unbounded_le)
    apply (metis le_add1)
   apply (metis le_iff_add)
  apply (subst stream_smap_nats)
  apply (subst count_stream_smap)
   apply (auto simp: Let_def count_stream_fromN of_nat_eq_enat)
  apply (meson infinite_nat_iff_unbounded_le vimage_singleton_eq)
  done

lemma count_stream_spermute:
  "bij \<pi> \<Longrightarrow> count_stream (spermute \<pi> s) x = count_stream s x"
  unfolding spermute_def
  apply (cases "count_stream s x = \<infinity>")
   apply simp
   apply (auto simp: count_stream_infinity_iff alw_iff_sdrop ev_iff_sdrop HLD_iff) []
  subgoal for m
    apply (rule ccontr)
    apply simp
    apply (cases m)
     apply simp
     apply (metis bij_pointE)
    apply (subgoal_tac "finite {i. s !! i = x}")
     apply (metis (mono_tags, lifting) infinite_nat_iff_unbounded_le le_add1 mem_Collect_eq)
    apply (subgoal_tac "finite {i. s !! \<pi> i = x}")
     apply (erule finite_surj[of _ _ "\<pi>"])
     apply (auto simp: image_iff) []
     apply (metis bij_pointE)
    apply (rule finite_subset[of _ "{0 ..< m}"])
     apply auto
    apply (metis add.commute less_natE not_less_eq)
    done
  apply (auto simp: count_stream_infinity_iff alw_iff_sdrop ev_iff_sdrop HLD_iff) []
  subgoal for m
    apply (subst count_stream_smap)
     apply auto
     apply (rule finite_subset[of _ "{0 ..< Suc (Max (\<pi> -` {0 ..< m}))}"])
      apply (auto simp: less_Suc_eq_le count_stream_fromN)
     apply (metis Max.coboundedI atLeastLessThan_iff finite_atLeastLessThan finite_vimage_iff le_iff_add less_eq_nat.simps(1) linorder_not_less vimageI2)
    subgoal
      apply (subst count_stream_alt)
      apply (auto simp: Let_def of_nat_eq_enat)
       apply (metis infinite_nat_iff_unbounded_le less_eqE vimage_singleton_eq)
      apply (subgoal_tac "card ((\<lambda>i. s !! \<pi> i) -` {x}) = card ((\<lambda>i. s !! i) -` {x})")
       prefer 2
       apply (rule card_bij[of \<pi> _ _ "inv \<pi>"])
            apply (auto simp: inj_on_def)
      apply (rule finite_subset[of _ "{0 ..< Suc (Max (\<pi> -` {0 ..< m}))}"])
       apply (auto simp: less_Suc_eq_le)
      apply (metis Max.coboundedI atLeastLessThan_iff finite_atLeastLessThan finite_vimage_iff le_iff_add less_eq_nat.simps(1) linorder_not_less vimageI2)
      done
    done
  done

coinductive counts_stream where
  "x \<notin> sset s \<Longrightarrow> counts_stream s x 0"
| "counts_stream s x n \<Longrightarrow> counts_stream (x ## s) x (eSuc n)"
| "x \<in> sset s \<Longrightarrow> counts_stream s x n \<Longrightarrow> x \<noteq> y \<Longrightarrow> counts_stream (y ## s) x n"

lemma enat_coinduct:
  assumes "R n n'"
    "(\<And>n n'. R n n' \<Longrightarrow> (n = 0 \<longleftrightarrow> n' = 0) \<and> (\<forall>m m'. n = eSuc m \<longrightarrow> n' = eSuc m' \<longrightarrow> R m m'))"
  shows "n = n'"
proof ((cases n; cases n'), goal_cases enat_enat enat_inf inf_enat inf_inf)
  case (enat_enat m m')
  with assms(1) show ?case
    apply hypsubst_thin
  proof (induct m arbitrary: m')
    case 0
    then show ?case
      by (induct m') (auto simp: enat_0 dest: assms(2))
  next
    case (Suc m)
    then show ?case
      by (induct m') (auto simp: enat_0 simp flip: eSuc_enat dest!: assms(2))
  qed
next
  case (enat_inf m)
  with assms(1) show ?case
    by (hypsubst_thin) (induct m, auto simp: enat_0 eSuc_enat dest: assms(2))
next
  case (inf_enat m')
  with assms(1) show ?case
    by (hypsubst_thin) (induct m', auto simp: enat_0 eSuc_enat dest: assms(2))
next
  case inf_inf
  then show ?case
    by simp
qed

lemma in_sset_counts_stream: "x \<in> sset s \<Longrightarrow> counts_stream s x 0 \<Longrightarrow> False"
  by (induct x s rule: stream.set_induct; erule counts_stream.cases) auto

lemma counts_stream_inject: "counts_stream s x m \<Longrightarrow> counts_stream s x n \<Longrightarrow> m = n"
  apply (coinduction arbitrary: s m n rule: enat_coinduct)
  apply (erule counts_stream.cases; erule counts_stream.cases)
          apply (auto dest: in_sset_counts_stream)
  subgoal for s y m m'
    apply (induct x s rule: stream.set_induct; erule counts_stream.cases; erule counts_stream.cases)
                     apply auto
    done
  done

lemma counts_stream_count_stream: "counts_stream s x (count_stream s x)"
  apply (coinduction arbitrary: s x)
  subgoal for s x
    apply (auto simp: count_stream_zero_iff)
    apply (subst count_stream.simps)
    apply (subst (asm) (1 3) count_stream.simps)
    apply (cases s)
    apply (auto simp: Let_def split: if_splits)
         apply (metis sdrop.simps(1) sdrop_simps(2) sdrop_stl stream.sel(2))
        apply (metis count_stream.elims sdrop.simps(1) sdrop_add sdrop_simps(2) stream.sel(2))
       apply (rule exI[of _ \<infinity>])
       apply (auto simp: count_stream_infinity_iff' alw_iff_sdrop ev_iff_sdrop HLD_iff
        dest: spec[of _ "Suc 0"]) []
       apply (metis rangeE sdrop_simps(2) sdrop_snth sdrop_stl sset_range stream.sel(2))
      apply (metis count_stream.elims sdrop.simps(1) sdrop_add sdrop_simps(2) stream.sel(2))
     apply (metis count_stream.elims sdrop.simps(1) sdrop_add sdrop_simps(2) stream.sel(2))
    apply (metis count_stream.elims eSuc_infinity_iff sdrop_simps(2) sdrop_stl stream.sel(2))
    done
  done

lemma counts_stream_flat: "\<forall>xs \<in> sset s. xs \<noteq> [] \<Longrightarrow>
  counts_stream (flat s) x (if infinite {i. x \<in> set (s !! i)} then \<infinity> else (\<Sum>i | x \<in> set (s !! i). count_list (s !! i) x))"
  apply (coinduction arbitrary: s)
  subgoal for s
    apply (cases "{i. x \<in> set (s !! i)} = {}")
     apply (rule disjI1)
     apply (auto simp: enat_0_iff dest: not_finite_existsD) []
     apply (metis imageE sset_range)
    apply (cases "infinite {i. x \<in> set (s !! i)}")
     apply (cases "x = hd (shd s)")
      apply (rule disjI2)
      apply (rule disjI1)
      apply (subst flat.code)
      apply auto []
       apply (rule exI[of _ \<infinity>])
       apply simp
       apply (rule disjI1)
       apply (rule exI[of _ "stl s"])
       apply simp []
       apply (rule conjI)
        apply (metis stl_sset)
       apply (erule contrapos_nn)
       apply (rule finite_subset[rotated])
        apply (rule finite_insert[THEN iffD2, of _ "0"])
        apply (erule finite_imageI[of _ Suc])
       apply (auto simp: image_iff) []
       apply (metis nat.exhaust snth.simps(2))
      apply (rule exI[of _ \<infinity>])
      apply simp
      apply (rule disjI1)
      apply (rule exI[of _ "tl (shd s) ## stl s"])
      apply simp []
      apply (rule conjI)
       apply (metis stl_sset)
      apply (erule contrapos_nn)
      apply (rule finite_subset[rotated])
       apply (erule finite_insert[THEN iffD2, of _ "0"])
      apply (auto simp: image_iff) []
      apply (metis Suc_pred snth.simps(2) stream.sel(2))
     apply (rule disjI2)
     apply (rule disjI2)
     apply (subst flat.code)
     apply auto []
        apply (smt (verit, ccfv_SIG) UN_I flat.code insertE snth_sset sset_flat stream.set)
       apply (rule exI[of _ "stl s"])
       apply simp
       apply (rule conjI)
        apply (metis stl_sset)
       apply (erule contrapos_nn)
       apply (rule finite_subset[rotated])
        apply (rule finite_insert[THEN iffD2, of _ "0"])
        apply (erule finite_imageI[of _ Suc])
       apply (auto simp: image_iff) []
       apply (metis nat.exhaust snth.simps(2))
      apply (metis (no_types, opaque_lifting) UN_I list.exhaust_sel list_decode.cases set_ConsD snth.simps(1) snth.simps(2) snth_sset sset_flat stl_sset)
     apply (rule exI[of _ "tl (shd s) ## stl s"])
     apply simp
     apply (rule conjI)
      apply (metis stl_sset)
     apply (erule contrapos_nn)
     apply (rule finite_subset[rotated])
      apply (erule finite_insert[THEN iffD2, of _ "0"])
     apply (auto simp: image_iff) []
     apply (metis Suc_pred snth.simps(2) stream.sel(2))

    apply (cases "x = hd (shd s)")
     apply (rule disjI2)
     apply (rule disjI1)
     apply (subst flat.code)
     apply (auto simp: enat_eSuc_iff) []
      apply (cases "\<Sum>i | x \<in> set (s !! i). count_list (s !! i) x")
       apply (simp add: count_list_0_iff)
    subgoal for xs m
      apply (rule exI[of _ "enat m"])
      apply (rule conjI)
       apply (rule exI[of _ "m"])
       apply (rule conjI[rotated])
        apply (rule refl)
       apply simp
      apply (rule disjI1)
      apply (rule exI[of _ "stl s"])
      apply simp
      apply (rule conjI)
       apply (erule finite_surj[of _ _ "\<lambda>x. x - 1"])
       apply (auto simp: image_iff) []
       apply (metis One_nat_def diff_Suc_1 snth.simps(2))
      apply (rule impI conjI[rotated])+
       apply (metis stl_sset)
      apply (subst (asm) sum.remove[of _ "0"])
        apply (auto simp: shd_sset)
      apply (cases "shd s")
       apply (auto simp: shd_sset image_iff simp flip: snth.simps
          intro!: sum.reindex_bij_betw[of Suc, symmetric])
      using not0_implies_Suc apply blast
      done
     apply (cases "\<Sum>i | x \<in> set (s !! i). count_list (s !! i) x")
      apply (simp add: count_list_0_iff)
    subgoal for xs m
      apply (rule exI[of _ "enat m"])
      apply (rule conjI)
       apply (rule exI[of _ "m"])
       apply (rule conjI[rotated])
        apply (rule refl)
       apply simp
      apply (rule disjI1)
      apply (rule exI[of _ "tl (shd s) ## stl s"])
      apply simp
      apply (rule conjI)
       apply (erule finite_subset[rotated])
       apply (auto simp: image_iff) []
       apply (metis hd_in_set list.sel(2) not0_implies_Suc snth.simps(1) snth.simps(2) snth_Stream)
      apply (rule impI conjI[rotated])+
       apply (metis stl_sset)
      apply (rule Suc_inject)
      apply (erule trans[OF sym])
      apply (cases "hd (shd s) \<in> set (tl (shd s))")
       apply (subst (1 2) sum.remove[of _ 0])
           apply auto [5]
        apply (metis list.sel(2) list.set_sel(1))
       apply (cases "shd s")
        apply (auto simp: shd_sset gr0_conv_Suc intro!: sum.cong) [2]
      using not0_implies_Suc apply fastforce
      apply (subst (1) sum.remove[of _ 0])
        apply auto [3]
       apply (metis list.sel(2) list.set_sel(1))
      apply (cases "shd s")
       apply (auto simp: shd_sset gr0_conv_Suc intro!: sum.cong) [2]
       apply (metis nat.exhaust snth.simps(1) snth.simps(2) stream.sel(1) stream.sel(2))
      apply (metis gr0_conv_Suc neq0_conv snth.simps(1) snth.simps(2) snth_Stream stream.sel(1))
      done
    apply (rule disjI2)
    apply (rule disjI2)
    apply (subst flat.code)
    apply (auto simp: enat_eSuc_iff) []
       apply (smt (verit, ccfv_threshold) UN_I flat.code insert_iff snth_sset sset_flat stream.set)
      apply (rule exI[of _ "stl s"])
      apply simp
      apply (rule conjI)
       apply (rule finite_subset[rotated])
        apply (erule finite_imageI[of _ "\<lambda>x. x - 1"])
       apply (auto simp: image_iff) []
       apply (metis diff_Suc_Suc minus_nat.diff_0 snth.simps(2))
      apply (intro impI conjI)
       apply (auto simp: shd_sset image_iff dest: stl_sset simp flip: snth.simps
        intro!: sum.reindex_bij_betw[of Suc, symmetric])
      apply (metis empty_iff list.sel(1) list.set(1) list_decode.cases set_ConsD tl_Nil)
     apply (metis (no_types, opaque_lifting) UN_I gr0_implies_Suc less_nat_zero_code list.exhaust_sel not_less_iff_gr_or_eq set_ConsD snth.simps(2) snth_sset sset_flat stl_sset)
      apply (rule exI[of _ "tl (shd s) ## stl s"])
      apply simp
      apply (rule conjI)
       apply (erule finite_subset[rotated])
     apply (auto simp: image_iff) []
    apply (metis gr0_conv_Suc list.set_sel(2) neq0_conv snth.simps(1) snth.simps(2) snth_Stream stream.sel(1) tl_Nil)
      apply (intro impI conjI)
       apply (auto simp: shd_sset image_iff dest: stl_sset simp flip: snth.simps(2)
        intro!: sum.cong)
    apply (metis empty_iff list.exhaust_sel list.set(1) nat.exhaust set_ConsD snth.simps(1) snth.simps(2) snth_Stream stream.sel(1))
     apply (metis list.sel(2) list.set_sel(2) not0_implies_Suc snth.simps(1) snth.simps(2) snth_Stream stream.sel(1))
    subgoal for _ i
      apply (cases s; cases "shd s"; cases i)
         apply simp_all
      done
    done
  done

lemma count_stream_flat:
  "\<forall>xs \<in> sset s. xs \<noteq> [] \<Longrightarrow>
  count_stream (flat s) x = (if infinite {i. x \<in> set (s !! i)} then \<infinity> else (\<Sum>i | x \<in> set (s !! i). count_list (s !! i) x))"
  by (erule counts_stream_inject[OF counts_stream_count_stream counts_stream_flat])

lemma count_list_replicate: "count_list (replicate n x) x = n"
  by (induct n) auto

lemma count_stream_flat_unique: "\<exists>!i. x \<in> set (s !! i) \<Longrightarrow>
   \<forall>xs \<in> sset s. \<exists>z. \<exists>n > 0. xs = replicate n z \<Longrightarrow>
   count_stream (flat s) x = length (s !! (THE i. x \<in> set (s !! i)))"
  apply (rule the1I2)
  apply assumption
  apply (subst count_stream_flat)
   apply (auto simp: finite_nat_set_iff_bounded)
  subgoal for i j m
    apply (subst sum.remove[of _ i])
      apply (auto simp: finite_nat_set_iff_bounded)
    apply (subst sum.neutral)
     apply (auto simp: count_list_replicate dest!: bspec[of _ _ "s !! i"])
    done
  done

lemma ex_cinfmset: "\<exists>xs. cinfmset xs = X"
  apply transfer
  subgoal for f
    apply (elim conjE exE disjE1')
    apply (frule (1) bij_betw_from_nat_into)
    subgoal
      apply (rule exI[of _ "flat (smap (\<lambda>i.
         let x = from_nat_into {x. f x \<noteq> 0} i in replicate (the_enat (f x)) x) nats)"])
      apply (rule ext)
      subgoal for z
        apply (cases "f z = 0")
        apply (auto simp: count_stream_zero_iff)
        apply (subst (asm) sset_flat)
        apply (auto simp: stream.set_map Let_def zero_enat_def) [2]
        apply (smt (verit) bij_betw_def mem_Collect_eq neq0_conv rangeI the_enat.simps)
        apply (subst count_stream_flat_unique)
        apply (auto simp: stream.set_map Let_def)
        apply (metis (mono_tags, lifting) enat_0_iff(2) from_nat_into_surj mem_Collect_eq the_enat.simps zero_less_iff_neq_zero)
        apply (metis (mono_tags, lifting) Collect_empty_eq enat_0_iff(2) from_nat_into mem_Collect_eq the_enat.simps zero_less_iff_neq_zero)
        apply (rule the1I2)
        apply (auto simp: stream.set_map Let_def)
        apply (metis (mono_tags, lifting) enat_0_iff(2) from_nat_into_surj mem_Collect_eq the_enat.simps zero_less_iff_neq_zero)
        apply (metis (mono_tags, lifting) the_enat.simps)
        done
      done
    sorry
  done

lemma cinfmset_eq_iff_spermute: "cinfmset xs' = cinfmset xs \<longleftrightarrow> (\<exists>\<pi>. bij \<pi> \<and> spermute \<pi> xs = xs')"
  apply transfer
  apply (auto simp: count_stream_spermute fun_eq_iff)
  apply (auto simp: count_stream_alt Let_def split: if_splits)
  sorry

lemma szip_smap_same: "szip (smap f s) (smap g s) = smap (\<lambda>x. (f x, g x)) s"
  by (coinduction arbitrary: s) auto

lemma spermute_szip: "spermute \<pi> (szip xs ys) = szip (spermute \<pi> xs) (spermute \<pi> ys)"
  by (auto simp: spermute_def szip_smap_same)

lemma ex_cinfmset_zip_left:
  assumes "cinfmset xs' = cinfmset xs"
  shows "\<exists>ys'. cinfmset (szip xs' ys') = cinfmset (szip xs ys)"
  using assms unfolding cinfmset_eq_iff_spermute
  apply (elim exE conjE)
  subgoal for \<pi>
    by (auto simp: spermute_szip intro!: exI[of _ "spermute \<pi> ys"] exI[of _ \<pi>])
  done

lemma stream_all2_szipI: "(\<forall>(x, y) \<in> sset (szip xs ys). P x y) \<Longrightarrow> stream_all2 P xs ys"
  apply (coinduction arbitrary: xs ys)
  apply auto
  apply (metis shd_sset szip.simps(1))
  apply (metis stl_sset szip.simps(2))
  done

lemma stream_all2_szipD: "xy \<in> sset (szip xs ys) \<Longrightarrow> stream_all2 P xs ys \<Longrightarrow> P (fst xy) (snd xy)"
  apply (induct xy "szip xs ys" arbitrary: xs ys rule: stream.set_induct)
  subgoal for h t xs ys
    by (metis fst_conv snd_conv stream.rel_sel stream.sel(1) szip.simps(1))
  subgoal for h t xy xs ys
    by (metis stream.rel_sel stream.sel(2) szip.simps(2))
  done

lemma stream_all2_iff: "stream_all2 P xs ys \<longleftrightarrow> (\<forall>(x, y) \<in> sset (szip xs ys). P x y)"
  by (metis split_beta stream_all2_szipD stream_all2_szipI)

lemma stream_all2_reorder_left_invariance:
  assumes rel: "stream_all2 R xs ys" and ms_x: "cinfmset xs' = cinfmset xs"
  shows "\<exists>ys'. stream_all2 R xs' ys' \<and> cinfmset ys' = cinfmset ys"
proof -
  from ms_x obtain ys' where
    ms_xy: "cinfmset (szip xs' ys') = cinfmset (szip xs ys)"
    by (metis ex_cinfmset_zip_left)
  have "stream_all2 R xs' ys'"
    using assms(1) ms_xy unfolding stream_all2_iff
    by (auto dest!: arg_cong[of _ _ set_cinfmset])
  moreover have "cinfmset ys' = cinfmset ys"
    using ms_xy
    apply (subst smap_szip_snd[of "\<lambda>x. x" xs' ys', unfolded stream.map_ident, symmetric])
    apply (subst smap_szip_snd[of "\<lambda>x. x" xs ys, unfolded stream.map_ident, symmetric])
    apply (auto simp flip: image_cinfmset_cinfmset)
    done
  ultimately show ?thesis
    by blast
qed

bnf "'a cinfmset"
  map: image_cinfmset
  sets: set_cinfmset
  bd: "card_suc natLeq"
  rel: rel_cinfmset
  subgoal by (rule ext, transfer) (auto simp: fun_eq_iff Int_insert_left)
  subgoal by (simp add: cinfmset_map_comp fun_eq_iff)
  subgoal
    apply transfer
    apply (auto simp: fun_eq_iff Let_def sum_infinite_enat sum_infinite_enat' intro!: sum.cong)
    apply (metis (mono_tags, lifting) mem_Collect_eq vimage_inter_cong)
    apply (metis (mono_tags, lifting) mem_Collect_eq vimage_inter_cong)
    apply (metis (mono_tags, lifting) mem_Collect_eq vimage_inter_cong)
    apply (metis (mono_tags, lifting) mem_Collect_eq vimage_inter_cong)
    done
  subgoal by (simp add: cinfmset_set_map fun_eq_iff)
  subgoal
    using cinfset.bd_card_order by blast
  subgoal
    using cinfset.bd_cinfinite by blast
  subgoal
    using cinfset.bd_regularCard by blast
  subgoal
    apply (rule card_suc_greater_set[OF natLeq_card_order])
    apply transfer
    apply (simp flip: countable_card_le_natLeq)
    done
  subgoal for R S
    apply (rule predicate2I)
    apply (unfold rel_cinfmset_def)
    apply safe
    apply (drule stream_all2_reorder_left_invariance[rotated])
    apply assumption
    apply (auto simp add: stream.rel_compp relcompp_apply)
    done
  subgoal for R
    unfolding rel_cinfmset_def fun_eq_iff  stream.in_rel
    apply safe
    subgoal for x y s s' z
      by (auto intro!: exI[of _ "cinfmset z"])
    subgoal for x y z
      apply (rule exE[OF ex_cinfmset[of z]])
      apply force
      done
    done
  done

(*infinitary untyped lambda calculus*)
(* binder_datatype 'a ilam =
  Bot
| Var 'a
| App "'a ilam" "'a ilam cinfmset"
| Abs "X::'a cinfset" "t::'a ilam" binds X in t
*)

ML \<open>
val ctors = [
  (("iVar", (NONE : mixfix option)), [@{typ 'var}]),
  (("iApp", NONE), [@{typ 'rec}, @{typ "'rec cinfmset"}]),
  (("iAbs", NONE), [@{typ "'bvar cinfset"}, @{typ 'brec}])
]

val spec = {
  fp_b = @{binding "ilam"},
  vars = [
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[0]],
  rec_vars = 2,
  ctors = ctors,
  map_b = @{binding ivvsubst},
  tvsubst_b = @{binding itvsubst}
}
\<close>

declare [[mrbnf_internals]]
local_setup \<open> MRBNF_Sugar.create_binder_datatype spec \<close>
print_mrbnfs

lemma ex_inj_infinite_regular_var_ilam_pre:
  "\<exists>f :: 'a :: countable \<Rightarrow> 'b :: var_ilam_pre. inj f"
  unfolding card_of_ordLeq[of UNIV UNIV, simplified]
  apply (rule ordLeq_transitive[OF _ large])
  apply (rule ordLeq_transitive[OF countable_card_le_natLeq[THEN iffD1]])
  apply simp
  apply (rule natLeq_ordLeq_cinfinite)
  apply (rule ilam_pre.bd_Cinfinite)
  done

definition embed :: "'a :: countable \<Rightarrow> 'b :: var_ilam_pre"
  ("{{_}}" [999] 1000)  where
  "embed = (SOME f. inj f)"

lemma inj_embed: "inj embed"
  unfolding embed_def
  by (rule someI_ex[OF ex_inj_infinite_regular_var_ilam_pre[where 'a='a]])

abbreviation "ifv \<equiv> FFVars_ilam"

consts lam_ilam :: "'a :: {countable, var_lam_pre} lam \<Rightarrow> nat list \<Rightarrow> 'b :: var_ilam_pre ilam"  ("\<lbrakk>_\<rbrakk>_" [999, 1000] 1000)
consts ilam_lam :: "'b :: var_ilam_pre ilam \<Rightarrow> 'a :: {countable, var_lam_pre} lam"  ("\<lparr>_\<rparr>" [999] 1000)

lemma iso_partition_into_countable: "|UNIV :: 'a :: var_ilam_pre set| *c natLeq =o |UNIV :: 'a :: var_ilam_pre set|"
  by (rule cprod_infinite1'[OF _ Cinfinite_Cnotzero[OF natLeq_Cinfinite]])
    (simp_all add: var_ilam_pre_class.cinfinite var_sum_class.large)


definition iso_partition where
  "iso_partition = (SOME f:: 'a :: var_ilam_pre \<Rightarrow> nat \<Rightarrow> 'a. bij_betw (case_prod f) UNIV UNIV)"

lemma bij_iso_partition: "bij (case_prod iso_partition :: 'a::var_ilam_pre \<times> nat \<Rightarrow> 'a)"
  unfolding iso_partition_def using iso_partition_into_countable[where 'a='a]
  unfolding cprod_def Field_card_of Field_natLeq card_of_ordIso[symmetric] UNIV_prod[symmetric]
  by (elim exE someI[where P = "\<lambda>f. bij (case_prod f)" and x="\<lambda>x y. _ (x, y)", simplified])

definition var_partition where
  "var_partition = range (\<lambda>v :: 'a :: var_ilam_pre. range (iso_partition v))"

lemma partition_var_partition: "partition_on UNIV var_partition"
  unfolding partition_on_def disjoint_def var_partition_def
  using bij_iso_partition unfolding bij_def surj_def inj_on_def
  by (auto 5 5)

lemma inj_iso_partition: "inj (iso_partition X)"
  using bij_iso_partition unfolding bij_def inj_on_def
  by auto

lemma var_partition_cinf: "X \<in> var_partition \<Longrightarrow> countable X \<and> infinite X"
  unfolding var_partition_def
  by (auto intro!: range_inj_infinite[OF inj_iso_partition])

lemma ex1_var_partition: "\<exists>!X. X \<in> var_partition \<and> x \<in> X"
  using partition_var_partition unfolding partition_on_def disjoint_def by auto

lift_definition super :: "'a ::var_ilam_pre \<Rightarrow> 'a cinfset" ("\<lbrace>_\<rbrace>" [999] 1000) is
  "\<lambda>x. THE X. X \<in> var_partition \<and> x \<in> X"
  by (rule the1I2[OF ex1_var_partition]) (auto simp: var_partition_cinf)

lemma in_super: "x \<in>\<in> \<lbrace>x\<rbrace>"
  by transfer (rule the1I2[OF ex1_var_partition, THEN conjunct2])

lemma super_in: "set_cinfset \<lbrace>x\<rbrace> \<in> var_partition"
  by transfer (rule the1I2[OF ex1_var_partition, THEN conjunct1])

lemma disjoint_super: "\<lbrace>x\<rbrace> \<noteq> \<lbrace>y\<rbrace> \<Longrightarrow> set_cinfset \<lbrace>x\<rbrace> \<inter> set_cinfset \<lbrace>y\<rbrace> = {}"
  by (metis Int_emptyI ex1_var_partition set_cinfset_inject super_in)

inductive affine where
  "affine (iVar x)"
| "affine t \<Longrightarrow> affine (iAbs \<lbrace>x\<rbrace> t)"
| "affine t \<Longrightarrow>
   \<forall>u. u \<in>#\<in> uu \<longrightarrow> affine u \<and> ifv t \<inter> ifv u = {} \<Longrightarrow>
   \<forall>u u'. u \<in>#\<in> uu \<longrightarrow> u' \<in>#\<in> uu \<longrightarrow> u \<noteq> u' \<longrightarrow> ifv u \<inter> ifv u' = {} \<Longrightarrow>
   affine (iApp t uu)"

lemma lam_ilam_simps[simp]:
  "\<lbrakk>Var x\<rbrakk>a = iVar (get_cinfset \<lbrace>{{x}}\<rbrace> (list_encode a))"
  "\<lbrakk>Abs x M\<rbrakk>a = iAbs \<lbrace>{{x}}\<rbrace> (\<lbrakk>M\<rbrakk>a)"
  "\<lbrakk>App M N\<rbrakk>a = iApp \<lbrakk>M\<rbrakk>(0#a) (image_cinfmset (\<lambda>i. \<lbrakk>N\<rbrakk>((i + 1) # a)) NATS_cinfmset)"
  sorry

lemma ifv_lam_ilam_disjoint:
  fixes M N :: "'a :: {countable, infinite_regular, var_lam_pre} lam"
  assumes "\<not>a \<le> a'" "\<not>a' \<le> a"
  shows "ifv (\<lbrakk>M\<rbrakk>a :: 'b :: var_ilam_pre ilam) \<inter> ifv (\<lbrakk>N\<rbrakk>a' :: 'b ilam) = {}"
  sorry

lemma
  fixes M :: "'a :: {countable, infinite_regular, var_lam_pre} lam"
  shows "affine (\<lbrakk>M\<rbrakk>a :: 'b :: var_ilam_pre ilam)"
  by (induct M arbitrary: a)
    (auto simp: cinfmset.set_map intro!: affine.intros
      elim: ifv_lam_ilam_disjoint[unfolded disjoint_iff, rule_format, THEN notE, of _ _ _ _ _ False, rotated 2])+

end


























typedef 'a dlist = "{xs :: 'a list. distinct xs}"
  by auto

setup_lifting type_definition_dlist

lift_definition map_dlist :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist" is
  "\<lambda>f xs. if bij f then map f xs else xs"
  by (auto simp: distinct_map bij_def elim: inj_on_subset)

lift_definition set_dlist :: "'a dlist \<Rightarrow> 'a set" is "set" .

lift_definition dNil :: "'a dlist" is "[]" by simp

mrbnf "'a dlist"
  map: map_dlist
  sets: bound: set_dlist
  bd: natLeq
  wits: dNil
  subgoal by (rule ext, transfer) simp
  subgoal by (rule ext, transfer) simp
  subgoal by transfer simp
  subgoal by (rule ext, transfer) simp
  subgoal by (rule infinite_regular_card_order_natLeq)
  subgoal by transfer (simp flip: finite_iff_ordLess_natLeq)
  subgoal by blast
  subgoal by (clarsimp, transfer) auto
  done

typedef 'a dllist = "{xs :: 'a llist. ldistinct xs}"
  by (auto intro!: exI[of _ "LNil"])

setup_lifting type_definition_dllist

lift_definition map_dllist :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a dllist \<Rightarrow> 'a dllist" is
  "\<lambda>f xs. if bij f then lmap f xs else xs"
  by (auto simp: bij_def  elim: inj_on_subset)

lift_definition set_dllist :: "'a dllist \<Rightarrow> 'a set" is "lset" .

lift_definition dLNil :: "'a dllist" is "LNil" by simp

mrbnf "'a dllist"
  map: map_dllist
  sets: bound: set_dllist
  bd: "card_suc natLeq"
  wits: dLNil
  subgoal by (rule ext, transfer) simp
  subgoal by (rule ext, transfer) (simp add: llist.map_comp)
  subgoal by transfer simp
  subgoal by (rule ext, transfer) simp
  subgoal by (simp add: infinite_regular_card_order_card_suc natLeq_Card_order natLeq_card_order natLeq_cinfinite)
  subgoal apply (rule card_suc_greater_set[OF natLeq_card_order])
    apply transfer
    subgoal for xs
      unfolding countable_card_le_natLeq[symmetric] countable_def inj_on_def
      thm bchoice_iff
      apply (auto simp: inj_on_def)
      find_theorems "Least _ = Least _"
      find_theorems "countable _ \<longleftrightarrow> _"
      find_consts "_ llist \<Rightarrow> _"
      subgoal by blast
      subgoal by (clarsimp, transfer) auto
      done

(*
coinductive sdistinct where
  "x \<notin> sset s \<Longrightarrow> sdistinct s \<Longrightarrow> sdistinct (x ## s)"

lemma sdistinct_stl: "sdistinct s \<Longrightarrow> sdistinct (stl s)"
  by (erule sdistinct.cases) simp

lemma sdistinct_fromN[simp]: "sdistinct (fromN n)"
  by (coinduction arbitrary: n) (subst siterate.code,  auto)

lemma sdistinct_smap: "inj_on f (sset s) \<Longrightarrow> sdistinct s \<Longrightarrow> sdistinct (smap f s)"
  by (coinduction arbitrary: s)
    (auto simp: smap_ctr stream.set_map inj_on_def stream.set_sel sdistinct_stl elim: sdistinct.cases)

class infinite = assumes infinite: "infinite (UNIV :: 'a set)"

lemma infinite_ex_inj: "\<exists>f :: nat \<Rightarrow> 'a :: infinite. inj f"
  by (rule infinite_countable_subset[OF infinite, simplified])

typedef 'a dstream = "{xs :: 'a :: infinite stream. sdistinct xs}"
  by (auto intro!: exI[of _ "smap (SOME f :: nat \<Rightarrow> 'a. inj f) nats"] sdistinct_smap
    someI_ex[OF infinite_ex_inj])

setup_lifting type_definition_dstream

lift_definition map_dstream :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a dstream \<Rightarrow> 'a :: infinite dstream" is
  "\<lambda>f xs. if bij f then smap f xs else xs"
  by (auto simp: bij_def intro!: sdistinct_smap elim: inj_on_subset)

lift_definition set_dstream :: "'a :: infinite dstream \<Rightarrow> 'a set" is "sset" .

mrbnf "'a ::infinite dstream"
  map: map_dstream
  sets: bound: set_dstream
  bd: natLeq
  subgoal apply (rule ext, transfer)
    using [[show_consts]]
    apply simp
(*
  subgoal by (rule ext, transfer) simp
  subgoal by transfer simp
  subgoal by (rule ext, transfer) simp
  subgoal by (rule infinite_regular_card_order_natLeq)
  subgoal by transfer (simp flip: finite_iff_ordLess_natLeq)
  subgoal by blast
  subgoal by (clarsimp, transfer) auto
  done
*)
*)



setup_lifting type_definition_dlist

lift_definition map_dlist :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist" is
  "\<lambda>f xs. if bij f then map f xs else xs"
  by (auto simp: distinct_map bij_def elim: inj_on_subset)

lift_definition set_dlist :: "'a dlist \<Rightarrow> 'a set" is "set" .

coinductive sdistinct where
  "x \<notin> sset s \<Longrightarrow> sdistinct s \<Longrightarrow> sdistinct (x ## s)"

lemma sdistinct_stl: "sdistinct s \<Longrightarrow> sdistinct (stl s)"
  by (erule sdistinct.cases) simp

lemma sdistinct_fromN[simp]: "sdistinct (fromN n)"
  by (coinduction arbitrary: n) (subst siterate.code,  auto)

lemma sdistinct_smap: "inj_on f (sset s) \<Longrightarrow> sdistinct s \<Longrightarrow> sdistinct (smap f s)"
  by (coinduction arbitrary: s)
    (auto simp: smap_ctr stream.set_map inj_on_def stream.set_sel sdistinct_stl elim: sdistinct.cases)

typedef 'a dstream = "{xs :: 'a :: infinite_regular stream. sdistinct xs}"
  by (auto intro!: exI[of _ "smap (SOME f :: nat \<Rightarrow> 'a. inj f) nats"] sdistinct_smap
      someI_ex[OF infinite_ex_inj])

setup_lifting type_definition_dstream

lift_definition dsmap :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a dstream \<Rightarrow> 'a :: infinite_regular dstream" is
  "\<lambda>f xs. if bij f then smap f xs else xs"
  by (auto simp: bij_def intro!: sdistinct_smap elim: inj_on_subset)

lift_definition dsset :: "'a :: infinite_regular dstream \<Rightarrow> 'a set" is "sset" .

lift_definition dsnth :: "'a :: infinite_regular dstream \<Rightarrow> nat \<Rightarrow> 'a" (infixl \<open>!#!\<close> 100) is "snth" .

lemma countable_sset:
  fixes s
  notes * = LeastI[where P="\<lambda>i. s !! i = s !! _", OF refl]
  shows "countable (sset s)"
  unfolding sset_range
  by (intro countableI[where f="\<lambda>x. LEAST i. snth s i = x"] inj_onI, elim imageE, hypsubst_thin)
    (rule box_equals[OF _ * *], simp)

(*polyadic untyped lambda calculus*)
(* binder_datatype 'a polylc =
  Bot
| Var 'a
| App "'a polylc" "'a polylc list"
| Abs xs::'a dlist t::"'a terms" binds xs in t
*)

ML \<open>
val ctors = [
  (("Var", (NONE : mixfix option)), [@{typ 'var}]),
  (("App", NONE), [@{typ 'rec}, @{typ "'rec llist"}]),
  (("Abs", NONE), [@{typ "('bvar \<times> \<tau>) llist"}, @{typ 'brec}])
]

val spec = {
  fp_b = @{binding "terms"},
  vars = [
    (dest_TFree @{typ 'var}, MRBNF_Def.Free_Var),
    (dest_TFree @{typ 'bvar}, MRBNF_Def.Bound_Var),
    (dest_TFree @{typ 'brec}, MRBNF_Def.Live_Var),
    (dest_TFree @{typ 'rec}, MRBNF_Def.Live_Var)
  ],
  binding_rel = [[0]],
  rec_vars = 2,
  ctors = ctors,
  map_b = @{binding vvsubst},
  tvsubst_b = @{binding tvsubst}
}
\<close>

declare [[mrbnf_internals]]
local_setup \<open>fn lthy =>
let
  val lthy' = MRBNF_Sugar.create_binder_datatype spec lthy
in lthy' end\<close>
print_mrbnfs

(*infinitary untyped lambda calculus*)
(* binder_datatype 'a inflc =
  Bot
| Var 'a
| App "'a inflc" "'a inflc stream"
| Abs xs::'a dstream t::"'a inflc" binds xs in t
*)

end
