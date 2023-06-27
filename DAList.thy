theory DAList
  imports "thys/MRBNF_Recursor"
begin

(* The HOL-Library.DAList entry does not close the context *)
typedef ('k, 'v) dalist = "{ (xs::('k \<times> 'v) list). distinct (map fst xs) }"
  by (rule exI[of _ "[]"]) auto

setup_lifting type_definition_dalist

lift_definition map_dalist :: "('k \<Rightarrow> 'k) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('k, 'a) dalist \<Rightarrow> ('k, 'b) dalist"
  is "\<lambda>f g x. if inj_on f (fst ` set x) then map (map_prod f g) x else []"
  by (auto split: if_splits)[1] (simp add: comp_inj_on distinct_map)

lift_definition keys_dalist :: "('k, 'v) dalist \<Rightarrow> 'k set" is "\<lambda>x. fst ` set x" .
lift_definition vals_dalist :: "('k, 'v) dalist \<Rightarrow> 'v set" is "\<lambda>x. snd ` set x" .
lift_definition pairs_dalist :: "('k, 'v) dalist \<Rightarrow> ('k \<times> 'v) set" is "set" .

lift_definition dalist_all2 :: "('v \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('k, 'v) dalist \<Rightarrow> ('k, 'b) dalist \<Rightarrow> bool"
  is "\<lambda>R. list_all2 (rel_prod (=) R)" .

mrbnf "('k, 'v) dalist"
map: map_dalist
sets:
  bound: keys_dalist
  live: vals_dalist
bd: natLeq
rel: dalist_all2
  subgoal
    apply (rule ext)
    apply transfer
    apply auto
    done
  subgoal
    apply (rule ext)
    apply transfer
    apply (auto simp: image_image comp_inj_on_iff[symmetric] dest: inj_on_imageI2)
    done
  subgoal
    apply transfer
    apply (force simp: inj_on_def intro!: list.map_cong)
    done
  subgoal
    apply (rule ext)
    apply transfer
    apply (force simp: list.set_map inj_on_def)
    done
  subgoal
    apply (rule ext)
    apply transfer
    apply (force simp: list.set_map inj_on_def)
    done
      apply (rule infinite_regular_card_order_natLeq)
  subgoal
    apply transfer
    using finite_iff_ordLess_natLeq by blast
  subgoal
    apply transfer
    using finite_iff_ordLess_natLeq by blast
  subgoal
    apply (rule predicate2I)
    apply transfer
    apply safe
    apply (subst OO_eq[symmetric, of "(=)"])
    apply (unfold prod.rel_compp list.rel_compp)
    apply auto
    done
  subgoal for f R
    apply (transfer fixing: f R)
    subgoal for xs ys
      apply (simp only: bij_is_inj[THEN inj_on_subset[OF _ subset_UNIV]] if_True inj_on_id list.in_rel)
      apply safe
      subgoal for zs
        apply (drule arg_cong[where f="map (map_prod (inv f) id)"])
        apply (force intro!: exI[of _ "map (\<lambda>((a,b),(c,d)). (inv f a,b,d)) zs"] list.map_cong
          simp: list.map_comp list.map_ident list.set_map prod.map_comp o_def split_beta)
        done
      subgoal for zs
        apply (rule exI[of _ "map (\<lambda>(a,b,c). ((f a,b),(f a,c))) zs"])
        apply (auto simp: list.map_comp list.set_map prod.map_comp o_def split_beta intro: list.map_cong)
        done
      done
    done
  done

lift_definition insert_dalist :: "'k \<Rightarrow> 'v \<Rightarrow> ('k, 'v) dalist \<Rightarrow> ('k, 'v) dalist" is
  "\<lambda>k v x. if k \<in> fst ` set x then x else (k, v) # x"
  by (auto split: if_splits)

lemma pairs_insert_fresh[simp]: "k \<notin> keys_dalist xs \<Longrightarrow> pairs_dalist (insert_dalist k v xs) = insert (k, v) (pairs_dalist xs)"
  by transfer auto
lemma pairs_insert_same[simp]: "k \<in> keys_dalist xs \<Longrightarrow> pairs_dalist (insert_dalist k v xs) = pairs_dalist xs"
  by transfer auto
lemma fst_pairs_dalist: "keys_dalist xs = fst ` pairs_dalist xs"
  by transfer (rule refl)

lift_definition concat_dalist :: "('k, 'v) dalist \<Rightarrow> ('k, 'v) dalist \<Rightarrow> ('k, 'v) dalist"
  is "\<lambda>xs ys. if fst ` set xs \<inter> fst ` set ys = {} then xs @ ys else []"
  by auto

end