theory DAList_MRBNF
  imports "Binders.MRBNF_Recursor"
    "HOL-Library.DAList"
begin

lift_definition map_alist :: "('k \<Rightarrow> 'k) \<Rightarrow> ('v \<Rightarrow> 'w) \<Rightarrow> ('k, 'v) alist \<Rightarrow> ('k, 'w) alist" is
  "\<lambda>f g xs. if bij f then map (map_prod f g) xs else []"
  by (fastforce simp: distinct_map inj_on_def dest!: bij_is_inj)

lift_definition keys :: "('k, 'v) alist \<Rightarrow> 'k set" is
  "\<lambda>xs. fst ` set xs" .

mrbnf "('k, 'v) alist"
  map: map_alist
  sets:
    bound: "keys" 
    live: "alist.set"
  bd: "natLeq"
  rel: "alist.rel"
  subgoal
    by (rule ext, transfer, simp)
  subgoal
    by (rule ext, transfer, auto)
  subgoal for x f1 f2 g1 g2
    by (transfer, fastforce)
  subgoal
    by (rule ext, transfer, force)
  subgoal
    by (rule ext, transfer, force)
  subgoal
    by (rule infinite_regular_card_order_natLeq)
  subgoal
    by (transfer, metis list.set_bd list.set_map)
  subgoal
    by (rule alist.set_bd)
  subgoal
    by (simp add: alist.rel_compp)
  subgoal
    unfolding alist.in_rel
    apply transfer
    apply (simp only: if_P bij_id)
    apply safe
    subgoal for f R x y z
      apply (rule bexI[where x = "map (map_prod (inv f) id) z"])
       apply (auto simp: o_def prod.map_comp distinct_map intro!: inj_on_imageI dest!: arg_cong[where f="map (map_prod (inv f) id)" and x="map (map_prod id fst) z"])
        apply fastforce
      apply (meson bij_betw_imp_inj_on bij_betw_inv_into inj_on_id prod.inj_map subset_UNIV
          subset_inj_on)
      apply (meson bij_betw_inv_into inj_on_def neq_equiv)
      done
    subgoal for f R x y z
      apply (rule bexI[where x = "map (map_prod f id) z"])
       apply fastforce+
      done
    done
  done

end
   