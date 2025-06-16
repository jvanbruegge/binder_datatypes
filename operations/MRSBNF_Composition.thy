theory MRSBNF_Composition
  imports BMV_Composition
  keywords "mrsbnf" :: thy_goal
begin

consts map_T1 :: "('a \<Rightarrow> 'a') \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'd') \<Rightarrow> ('e \<Rightarrow> 'e') \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g) T1 \<Rightarrow> ('a', 'b, 'c, 'd', 'e', 'f, 'g) T1"
consts rel_T1 :: "('a \<Rightarrow> 'a' \<Rightarrow> bool) \<Rightarrow> ('d \<Rightarrow> 'd' \<Rightarrow> bool) \<Rightarrow> ('e \<Rightarrow> 'e' \<Rightarrow> bool) \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g) T1 \<Rightarrow> ('a', 'b, 'c, 'd', 'e', 'f, 'g) T1 \<Rightarrow> bool"

consts map_T2 :: "('b => 'b) => ('d \<Rightarrow> 'd) \<Rightarrow> ('a, 'b, 'c, 'd) T2 \<Rightarrow> ('a, 'b, 'c, 'd) T2"

consts map_T3 :: "('a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'd') \<Rightarrow> ('f \<Rightarrow> 'f') \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) T3 \<Rightarrow> ('a, 'b, 'c, 'd', 'e, 'f') T3"
consts set_a_T3 :: "('a, 'b, 'c, 'd, 'e, 'f) T3 \<Rightarrow> 'a set"
consts rel_T3 :: "('d \<Rightarrow> 'd' \<Rightarrow> bool) \<Rightarrow> ('f \<Rightarrow> 'f' \<Rightarrow> bool) \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f) T3 \<Rightarrow> ('a, 'b, 'c, 'd', 'e, 'f') T3 \<Rightarrow> bool"

consts map_T4 :: "('a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) T4 \<Rightarrow> ('a, 'b) T4"

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
    [Free_Var, Dead_Var, Free_Var, Free_Var, Live_Var]
    (the (MRBNF_Def.mrbnf_of lthy @{type_name T3}))
    ((MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds), lthy)
  val lthy = MRBNF_Def.register_mrbnf_raw "MRSBNF_Composition.T3'" mrbnf lthy
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
  apply (tactic \<open>Skip_Proof.cheat_tac @{context} 1\<close>)
  done

mrsbnf T3': "('a, 'b, 'c, 'd, 'e, 'f) T3" and "('a, 'c) T4"
       apply (tactic \<open>Skip_Proof.cheat_tac @{context} 1\<close>)+
  done

end