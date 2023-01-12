theory DALList
imports "thys/MRBNF_Recursor"
begin

declare [[bnf_internals]] \<comment> \<open>to get access to the bd theorems\<close>

(*copied from "Coinductive.Coinductive_List"*)
codatatype (lset: 'a) llist =
    lnull: LNil
  | LCons (lhd: 'a) (ltl: "'a llist")
for
  map: lmap
  rel: llist_all2
where
  "lhd LNil = undefined"
| "ltl LNil = LNil"

(*copied from "Coinductive.Coinductive_List"*)
coinductive ldistinct :: "'a llist \<Rightarrow> bool"
where
  LNil [simp]: "ldistinct LNil"
| LCons: "\<lbrakk> x \<notin> lset xs; ldistinct xs \<rbrakk> \<Longrightarrow> ldistinct (LCons x xs)"

section \<open>Distinct Associative Lazy Lists\<close>

typedef ('k, 'v) dallist = "{xs :: ('k \<times> 'v) llist. ldistinct (lmap fst xs)}"
  by (rule exI[of _ LNil]) auto

setup_lifting type_definition_dallist

lemma ldistinct_lmap: "ldistinct xs \<Longrightarrow> inj_on f (lset xs) \<Longrightarrow> ldistinct (lmap f xs)"
proof (coinduction arbitrary: xs)
  case ldistinct
  then show ?case
    by (cases xs) (auto simp: llist.set_map elim: ldistinct.cases)
qed

lift_definition map_dallist :: "('k \<Rightarrow> 'k) \<Rightarrow> ('v \<Rightarrow> 'v') \<Rightarrow> ('k, 'v) dallist \<Rightarrow> ('k, 'v') dallist"
  is "\<lambda>f g xs. if inj_on f (fst ` lset xs) then lmap (map_prod f g) xs else LNil"
  subgoal for f g xs
    apply (split if_splits)
    apply safe
     apply (drule ldistinct_lmap[of _ f])
      apply (auto simp: llist.map_comp llist.set_map)
    done
  done
lift_definition keys_dallist :: "('k, 'v) dallist \<Rightarrow> 'k set" is "\<lambda>xs. fst ` lset xs" .
lift_definition vals_dallist :: "('k, 'v) dallist \<Rightarrow> 'v set" is "\<lambda>xs. snd ` lset xs" .

lift_definition rel_dallist :: "('v \<Rightarrow> 'v' \<Rightarrow> bool) \<Rightarrow> ('k, 'v) dallist \<Rightarrow> ('k, 'v') dallist \<Rightarrow> bool" is
  "\<lambda>R xs ys. llist_all2 (rel_prod (=) R) xs ys" .

mrbnf "('k, 'v) dallist"
  map: "map_dallist :: ('k \<Rightarrow> 'k) \<Rightarrow> ('v \<Rightarrow> 'v') \<Rightarrow> ('k, 'v) dallist \<Rightarrow> ('k, 'v') dallist"
  sets:
    bound: "keys_dallist :: ('k, 'v) dallist \<Rightarrow> 'k set"
    live: "vals_dallist :: ('k, 'v) dallist \<Rightarrow> 'v set"
  bd: bd_llist
  rel: rel_dallist
  subgoal
    apply (rule ext)
    apply transfer
    apply (auto simp: llist.map_id)
    done
  subgoal for f1 f2 g1 g2
    apply (rule ext)
    apply transfer
    apply (auto simp: llist.set_map llist.map_comp0 map_prod_compose image_image
      comp_inj_on_iff[symmetric] dest: inj_on_imageI2)
    done
  subgoal for x f1 f2 g1 g2
    apply transfer
    apply (force simp: inj_on_def intro!: llist.map_cong)
    done
  subgoal for f1 f2
    apply (rule ext)
    apply transfer
    apply (force simp: llist.set_map inj_on_def)
    done
  subgoal for f1 f2
    apply (rule ext)
    apply transfer
    apply (force simp: llist.set_map inj_on_def)
    done
  subgoal
    apply unfold_locales
    apply (rule llist.bd_card_order)
    apply (rule llist.bd_cinfinite)
    apply (rule llist.bd_regularCard)
    done
  subgoal for x
    apply transfer
    apply (metis llist.set_bd llist.set_map)
    done
  subgoal for x
    apply transfer
    apply (metis llist.set_bd llist.set_map)
    done
  subgoal for R S
    apply (rule predicate2I)
    apply transfer
    apply safe
    apply (subst OO_eq[symmetric, of "(=)"])
    apply (unfold prod.rel_compp llist.rel_compp)
    apply auto
    done
  subgoal for f R
    apply (transfer fixing: f R)
    subgoal for xs ys
      apply (simp only: bij_is_inj[THEN inj_on_subset[OF _ subset_UNIV]] if_True inj_on_id
        llist.in_rel)
      apply safe
      subgoal for zs
        apply (drule arg_cong[where f="lmap (map_prod (inv f) id)"])
        apply (force intro!: exI[of _ "lmap (\<lambda>((a,b),(c,d)). (inv f a,b,d)) zs"] llist.map_cong
          simp: llist.map_comp llist.map_ident llist.set_map prod.map_comp o_def split_beta)
        done
      subgoal for zs
        apply (rule exI[of _ "lmap (\<lambda>(a,b,c). ((f a,b),(f a,c))) zs"])
        apply (auto simp: llist.map_comp llist.set_map prod.map_comp o_def split_beta intro: llist.map_cong)
        done
      done
    done
  done

end