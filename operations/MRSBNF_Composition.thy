theory MRSBNF_Composition
  imports BMV_Composition
  keywords "mrsbnf" :: thy_goal
begin

consts map_T1 :: "('a \<Rightarrow> 'a') \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'd') \<Rightarrow> ('e \<Rightarrow> 'e') \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g) T1 \<Rightarrow> ('a', 'b, 'c, 'd', 'e', 'f, 'g) T1"
consts rel_T1 :: "('a \<Rightarrow> 'a' \<Rightarrow> bool) \<Rightarrow> ('d \<Rightarrow> 'd' \<Rightarrow> bool) \<Rightarrow> ('e \<Rightarrow> 'e' \<Rightarrow> bool) \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g) T1 \<Rightarrow> ('a', 'b, 'c, 'd', 'e', 'f, 'g) T1 \<Rightarrow> bool"

consts map_T2 :: "('a \<Rightarrow> 'a) \<Rightarrow> ('b => 'b) => ('d \<Rightarrow> 'd) \<Rightarrow> ('a, 'b, 'c, 'd) T2 \<Rightarrow> ('a, 'b, 'c, 'd) T2"
consts set_1_T2 :: "('a, 'b, 'c, 'd) T2 \<Rightarrow> 'a set"

consts map_T3 :: "('a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'd') \<Rightarrow> ('f \<Rightarrow> 'f') \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) T3 \<Rightarrow> ('a, 'b, 'c, 'd', 'e, 'f') T3"
consts set_a_T3 :: "('a, 'b, 'c, 'd, 'e, 'f) T3 \<Rightarrow> 'a set"
consts rel_T3 :: "('d \<Rightarrow> 'd' \<Rightarrow> bool) \<Rightarrow> ('f \<Rightarrow> 'f' \<Rightarrow> bool) \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) T3 \<Rightarrow> ('a, 'b, 'c, 'd', 'e, 'f') T3 \<Rightarrow> bool"

consts map_T4 :: "('a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) T4 \<Rightarrow> ('a, 'b) T4"

declare [[mrbnf_internals]]
mrbnf "('a, 'b, 'c, 'd, 'e, 'f, 'g) T1"
map: map_T1
sets:
  live: set_1_T1
  free: Vrs_1_T1
  free: Vrs_2_T1
  live: set_2_T1
  live: set_3_T1
  free: Vrs_3_T1
bd: natLeq
rel: rel_T1
                   apply (tactic \<open>Skip_Proof.cheat_tac @{context} 1\<close>)+
  done

mrbnf "('a, 'b, 'c, 'd) T2"
  map: map_T2
  sets:
    bound: set_1_T2
    free: Vrs_2_T2
    free: Vrs_1_T2
  bd: natLeq
                   apply (tactic \<open>Skip_Proof.cheat_tac @{context} 1\<close>)+
  done

mrbnf "('a, 'b, 'c, 'd, 'e, 'f) T3"
  map: map_T3
  sets:
    free: set_a_T3
    free: Vrs_3_T3
    free: Vrs_4_T3
    live: set_1_T3
    live: set_2_T3
  bd: natLeq
  rel: rel_T3
                   apply (tactic \<open>Skip_Proof.cheat_tac @{context} 1\<close>)+
  done

local_setup \<open>fn lthy =>
let
  open MRBNF_Def
  val (mrbnf, (_, lthy)) = MRBNF_Comp.demote_mrbnf I
    [Free_Var, Bound_Var, Free_Var, Free_Var, Live_Var]
    (the (MRBNF_Def.mrbnf_of lthy @{type_name T3}))
    ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy)
  val lthy = MRBNF_Def.register_mrbnf_raw "MRSBNF_Composition.T3'" mrbnf lthy
  val (_, lthy) = MRBNF_Def.note_mrbnf_thms (MRBNF_Def.Note_All) I @{binding T3'} mrbnf lthy
in lthy end\<close>
  
mrbnf "('a, 'b) T4"
  map: map_T4
  sets:
    free: Vrs_1_T4
    free: Vrs_2_T4
  bd: natLeq
                   apply (tactic \<open>Skip_Proof.cheat_tac @{context} 1\<close>)+
  done     

ML_file \<open>../Tools/mrsbnf_def.ML\<close>

mrsbnf "('a, 'b, 'c, 'd, 'e, 'f, 'g) T1"
      apply (tactic \<open>Skip_Proof.cheat_tac @{context} 1\<close>)+
  done

mrsbnf "('a, 'b, 'c, 'd) T2"
  apply (tactic \<open>Skip_Proof.cheat_tac @{context} 1\<close>)+
  done

mrsbnf T3': "('a, 'b, 'c, 'd, 'e, 'f) T3" and "('a, 'c) T4"
       apply (tactic \<open>Skip_Proof.cheat_tac @{context} 1\<close>)+
  done

local_setup \<open>fn lthy =>
let
  val ((mrbnf, tys), ((_, unfolds), lthy)) = MRBNF_Comp.compose_mrbnf MRBNF_Def.Do_Inline (Binding.prefix_name o string_of_int) (distinct (op=) o flat)
    (the (MRBNF_Def.mrbnf_of lthy @{type_name T1})) [
      the (MRBNF_Def.mrbnf_of lthy @{type_name T2}),
      MRBNF_Comp.DEADID_mrbnf,
      the (MRBNF_Def.mrbnf_of lthy "MRSBNF_Composition.T3'")
    ] [@{typ 'f}] [
      [@{typ 'e}],
      [@{typ 'g}],
      [@{typ 'e}]
    ] [NONE, SOME @{typ "'b"}, SOME @{typ "'c"}, NONE, NONE, SOME @{typ "'g"}] [
      [@{typ 'a}, @{typ 'b}, @{typ 'd}],
      [],
      [@{typ 'b}, @{typ 'a}, @{typ 'c}, @{typ 'd}, @{typ 'h}]
    ] [] ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy)

  val defs = [("comp_defs", #map_unfolds unfolds, [])]
    |> map (fn (thmN, thms, attrs) => (((Binding.name thmN, attrs), [(thms, [])])));
  val (_, lthy) = Local_Theory.notes defs lthy

  val lthy = MRBNF_Def.register_mrbnf_raw "MRSBNF_Composition.T" mrbnf lthy;
in lthy end
\<close>

mrsbnf T: "('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h) T" and "('a, 'b, 'e, 'd) T2" and T3': "('b, 'a, 'c, 'd, 'e, 'h) T3" and "('a, 'c) T4"
  apply (unfold comp_defs)
             apply (rule trans)
              apply (rule T1.map_is_Sb)
                apply (assumption | rule supp_id_bound)+
             apply (unfold id_o o_id)
             apply (rule sym)
             apply (rule trans[OF comp_assoc])
             apply (rule arg_cong2[OF refl, of _ _ "(\<circ>)"])
             apply (rule trans)
              apply (rule T1.Map_comp)
             apply (unfold id_o o_id)
             apply (rule ext)
             apply (rule sym)
             apply (rule T1.Map_cong)
               apply (rule T2.map_is_Sb[THEN fun_cong]; assumption)
              apply (rule refl)
             apply (rule T3'.map_is_Sb[THEN fun_cong]; assumption)


         apply (rule trans)
          apply (rule trans[OF comp_assoc[symmetric]])
          apply (rule trans)
          apply (rule arg_cong2[OF _ refl, of _ _ "(\<circ>)"])
          apply (rule T1.map_Sb)
            apply (assumption | rule SSupp_Inj_bound)+
          apply (rule trans[OF comp_assoc])
          apply (rule arg_cong2[OF refl, of _ _ "(\<circ>)"])
          apply (unfold T1.Map_map)[1]
          apply (rule T1.map_comp0[symmetric])
               apply (rule supp_id_bound)+
         apply (unfold id_o o_id)
         apply (rule sym)
         apply (rule trans)
            apply (rule trans[OF comp_assoc])
          apply (rule arg_cong2[OF refl, of _ _ "(\<circ>)"])
          apply (unfold T1.Map_map)[1]
          apply (rule T1.map_comp0[symmetric])
               apply (rule supp_id_bound)+
         apply (unfold id_o o_id)
         apply (rule arg_cong2[of _ _ _ _ "(\<circ>)"])
          apply (unfold T1.Map_map[symmetric] T1.Map_Inj)[1]
          apply (rule refl)
  apply (rule sym)
  apply (rule ext)
         apply (rule T1.map_cong0)
                    apply (rule supp_id_bound)+
                      apply (rule T2.map_Sb[THEN fun_cong])
                      apply assumption+
                      apply (rule refl)+
          apply (rule T3'.map_Sb[THEN fun_cong])
             apply assumption+
                   apply (rule refl)

                  apply (unfold T1.Map_map[symmetric])[1]
                  apply (rule T1.Map_Inj)

  subgoal for x
    apply (subst T1.set_map, (rule supp_id_bound)+)+
    apply (unfold UN_empty2 Un_empty_left Un_empty_right Un_assoc[symmetric]
      T3'.set_Vrs(1) (* need to filter reflexive theorems *) Un_Union_image
    )
    apply (rule refl)
    done
  subgoal for x
    apply (subst T1.set_map, (rule supp_id_bound)+)+
    apply (unfold UN_empty2 Un_empty_left Un_empty_right Un_assoc[symmetric]
      T3'.set_Vrs(1) Un_Union_image
    )
    apply (rule refl)
    done
  subgoal for x
    apply (subst T1.set_map, (rule supp_id_bound)+)+
    apply (unfold UN_empty2 Un_empty_left Un_empty_right Un_assoc[symmetric]
      T3'.set_Vrs(1) Un_Union_image
    )
    apply (rule refl)
    done

  subgoal
    supply outer_set_maps = T1.set_map[where v="_::(('d, 'a, 'i, 'c) T2, 'a, 'b, 'h set, ('a, 'd, 'b, 'c, 'i, 'e) T3, 'g, 'h) T1"]
    supply comp_apply' = comp_apply[of "_::(('d, 'a, 'i, 'c) T2, 'a, 'b, 'h set,
          ('a, 'd, 'b, 'c, 'i, 'e) T3, 'g, 'h) T1 \<Rightarrow> (('d, 'a, 'i, 'c) T2, 'a, 'b, 'h set,
          ('a, 'd, 'b, 'c, 'i, 'e) T3, 'g, 'h) T1"]
    apply (subst outer_set_maps, (rule supp_id_bound bij_id)+)+
    apply (unfold comp_apply' UN_empty2 Un_empty_right Un_empty_left image_id)
    apply (subst T1.set_Sb, (assumption | rule SSupp_Inj_bound)+)+
    apply (unfold T1.Vrs_Map)
    apply (unfold T1.Map_map)
    apply (subst outer_set_maps, (rule supp_id_bound bij_id)+)+
    apply (unfold image_comp[unfolded comp_def] image_Un)
    apply (subst T2.set_Sb T3'.set_Sb, (assumption | rule SSupp_Inj_bound)+)+
    apply (unfold Un_Union_image Union_Un_distrib UN_UN_flatten)
    apply (unfold (* T1.set_Inj *) T1.Supp_Inj UN_empty UN_empty2 Un_empty_left Un_empty_right)
    apply (rule set_eqI)
    apply (rule iffI)
     apply (rotate_tac -1)
     apply (erule contrapos_pp)
     apply (unfold Un_iff de_Morgan_disj)[1]
     apply (erule conjE)+
     apply ((rule conjI)+, assumption+)+
     apply (rotate_tac -1)
     apply (erule contrapos_pp)
     apply (unfold Un_iff de_Morgan_disj)[1]
     apply (erule conjE)+
    apply ((rule conjI)+, assumption+)+
    done


  subgoal
    supply outer_set_maps = T1.set_map[where v="_::(('d, 'a, 'i, 'c) T2, 'a, 'b, 'h set, ('a, 'd, 'b, 'c, 'i, 'e) T3, 'g, 'h) T1"]
    supply comp_apply' = comp_apply[of "_::(('d, 'a, 'i, 'c) T2, 'a, 'b, 'h set,
          ('a, 'd, 'b, 'c, 'i, 'e) T3, 'g, 'h) T1 \<Rightarrow> (('d, 'a, 'i, 'c) T2, 'a, 'b, 'h set,
          ('a, 'd, 'b, 'c, 'i, 'e) T3, 'g, 'h) T1"]
    apply (subst outer_set_maps, (rule supp_id_bound bij_id)+)+
    apply (unfold comp_apply' UN_empty2 Un_empty_right Un_empty_left image_id)
    apply (subst T1.set_Sb, (assumption | rule SSupp_Inj_bound)+)+
    apply (unfold T1.Vrs_Map)
    apply (unfold T1.Map_map)
    apply (subst outer_set_maps, (rule supp_id_bound bij_id)+)+
    apply (unfold image_comp[unfolded comp_def] image_Un)
    apply (subst T2.set_Sb T3'.set_Sb, (assumption | rule SSupp_Inj_bound)+)+
    apply (unfold Un_Union_image Union_Un_distrib UN_UN_flatten)
    apply (unfold (* T1.set_Inj *) T1.Supp_Inj UN_empty UN_empty2 Un_empty_left Un_empty_right)
    apply (rule set_eqI)
    apply (rule iffI)
     apply (rotate_tac -1)
     apply (erule contrapos_pp)
     apply (unfold Un_iff de_Morgan_disj)[1]
     apply (erule conjE)+
     apply ((rule conjI)+, assumption+)+
     apply (rotate_tac -1)
     apply (erule contrapos_pp)
     apply (unfold Un_iff de_Morgan_disj)[1]
     apply (erule conjE)+
    apply ((rule conjI)+, assumption+)+
    done

            apply (rule T2.map_is_Sb; assumption)
           apply (rule T2.map_Sb; assumption)
          apply (rule ext)
          apply (rule trans[OF comp_apply])
          apply (rule trans)
           apply (rule T2.map_Inj)
              apply (assumption | rule supp_id_bound bij_id)+
          apply (rule arg_cong[OF id_apply])
         apply (rule T2.set_Sb; assumption)

        apply (rule T3'.map_is_Sb; assumption)
       apply (rule T3'.map_Sb; assumption)
          apply (rule ext)
          apply (rule trans[OF comp_apply])
          apply (rule trans)
           apply (rule T3'.map_Inj)
              apply (assumption | rule supp_id_bound bij_id)+
          apply (rule arg_cong[OF id_apply])
     apply (rule T3'.set_Vrs)
   apply (rule T3'.set_Sb; assumption)+
  apply (rule T3'.map_is_Sb; assumption)
  done
print_theorems

ML_file \<open>../Tools/mrsbnf_comp.ML\<close>
local_setup \<open>fn lthy =>
let
  val (deadid, lthy) = MRSBNF_Def.mrsbnf_of_mrbnf MRBNF_Comp.DEADID_mrbnf lthy
  val ((mrsbnf, _), (_, lthy)) = MRSBNF_Comp.compose_mrsbnfs BNF_Def.Do_Inline (K BNF_Def.Note_Some)
    (Binding.suffix_name o string_of_int) (the (MRSBNF_Def.mrsbnf_of lthy @{type_name T1}))
    [
      the (MRSBNF_Def.mrsbnf_of lthy @{type_name T2}),
      deadid,
      the (MRSBNF_Def.mrsbnf_of lthy "MRSBNF_Composition.T3'")
    ] [@{typ 'f}] [
      [@{typ 'e}],
      [@{typ 'g}],
      [@{typ 'e}]
    ] [NONE, SOME @{typ "'b"}, SOME @{typ "'c"}, NONE, NONE, SOME @{typ "'g"}] [
      [@{typ "'a"}, @{typ 'b}, @{typ 'd}],
      [],
      [@{typ 'b}, @{typ 'a}, @{typ 'c}, @{typ 'd}, @{typ 'h}]
    ] [] (([], (MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds)), lthy)
in lthy end\<close>

end