theory BMV_Composition
  imports "Binders.MRBNF_Recursor"
  keywords "print_pbmv_monads" :: diag and
   "pbmv_monad" :: thy_goal
begin

lemma image_const_empty: "x \<noteq> y \<Longrightarrow> (\<lambda>_. x) ` A = (\<lambda>_. y) ` B \<Longrightarrow> A = {} \<and> B = {}"
  by fast

ML_file \<open>../Tools/bmv_monad_def.ML\<close>

(* live, free, free, live, live, dead, free *)
typedecl ('a, 'b, 'c, 'd, 'e, 'f, 'g) T1
(* dead, free, dead, free *)
typedecl ('a, 'b, 'c, 'd) T2
(* free, free, free, live, dead, live *)
typedecl ('a, 'b, 'c, 'd, 'e, 'f) T3
(* free, live *)
typedecl ('a, 'b) T4

consts Sb_T1 :: "('b::var \<Rightarrow> 'b) \<Rightarrow> ('c::var \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g) T1) \<Rightarrow> ('g::var \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g) T1) \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g) T1 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g) T1"
consts Map_T1 :: "('a \<Rightarrow> 'a') \<Rightarrow> ('d \<Rightarrow> 'd') \<Rightarrow> ('e \<Rightarrow> 'e') \<Rightarrow> ('a, 'b::var, 'c::var, 'd, 'e, 'f, 'g::var) T1 \<Rightarrow> ('a', 'b, 'c, 'd', 'e', 'f, 'g) T1"
consts set_1_T1 :: "('a, 'b::var, 'c::var, 'd, 'e, 'f, 'g::var) T1 \<Rightarrow> 'a set"
consts set_2_T1 :: "('a, 'b::var, 'c::var, 'd, 'e, 'f, 'g::var) T1 \<Rightarrow> 'd set"
consts set_3_T1 :: "('a, 'b::var, 'c::var, 'd, 'e, 'f, 'g::var) T1 \<Rightarrow> 'e set"
consts Vrs_1_T1 :: "('a, 'b::var, 'c::var, 'd, 'e, 'f, 'g::var) T1 \<Rightarrow> 'b set"
consts Vrs_2_T1 :: "('a, 'b::var, 'c::var, 'd, 'e, 'f, 'g::var) T1 \<Rightarrow> 'c set"
consts Vrs_3_T1 :: "('a, 'b::var, 'c::var, 'd, 'e, 'f, 'g::var) T1 \<Rightarrow> 'g set"
consts Inj_1_T1 :: "'c \<Rightarrow> ('a, 'b::var, 'c::var, 'd, 'e, 'f, 'g::var) T1"
consts Inj_2_T1 :: "'g \<Rightarrow> ('a, 'b::var, 'c::var, 'd, 'e, 'f, 'g::var) T1"

consts Sb_T2 :: "('d::var \<Rightarrow> 'd) \<Rightarrow> ('b::var \<Rightarrow> ('a, 'b, 'c, 'd) T2) \<Rightarrow> ('a, 'b, 'c, 'd) T2 \<Rightarrow> ('a, 'b, 'c, 'd) T2"
consts Vrs_1_T2 :: "('a, 'b::var, 'c, 'd::var) T2 \<Rightarrow> 'd set"
consts Vrs_2_T2 :: "('a, 'b::var, 'c, 'd::var) T2 \<Rightarrow> 'b set"
consts Inj_T2 :: "'b \<Rightarrow> ('a, 'b::var, 'c, 'd::var) T2"

consts Sb_T3 :: "('a::var \<Rightarrow> ('a::var, 'b, 'c::var, 'd, 'e, 'f) T3) \<Rightarrow> ('a::var \<Rightarrow> ('a::var, 'c::var) T4) \<Rightarrow> ('b::var \<Rightarrow> ('a::var, 'b, 'c::var, 'd, 'e, 'f) T3) \<Rightarrow> ('c::var \<Rightarrow> ('a, 'c) T4) \<Rightarrow> ('a::var, 'b, 'c::var, 'd, 'e, 'f) T3 \<Rightarrow> ('a::var, 'b, 'c::var, 'd, 'e, 'f) T3"
consts Map_T3 :: "('d \<Rightarrow> 'd') \<Rightarrow> ('f \<Rightarrow> 'f') \<Rightarrow> ('a::var, 'b, 'c::var, 'd, 'e, 'f) T3 \<Rightarrow> ('a, 'b, 'c, 'd', 'e, 'f') T3"
consts set_1_T3 :: "('a::var, 'b, 'c::var, 'd, 'e, 'f) T3 \<Rightarrow> 'd set"
consts set_2_T3 :: "('a::var, 'b, 'c::var, 'd, 'e, 'f) T3 \<Rightarrow> 'f set"
consts Vrs_1_T3 :: "('a::var, 'b, 'c::var, 'd, 'e, 'f) T3 \<Rightarrow> 'a set"
consts Vrs_2_T3 :: "('a::var, 'b, 'c::var, 'd, 'e, 'f) T3 \<Rightarrow> 'a set"
consts Vrs_3_T3 :: "('a::var, 'b, 'c::var, 'd, 'e, 'f) T3 \<Rightarrow> 'b set"
consts Vrs_4_T3 :: "('a::var, 'b, 'c::var, 'd, 'e, 'f) T3 \<Rightarrow> 'c set"
consts Inj_1_T3 :: "'a \<Rightarrow> ('a::var, 'b, 'c::var, 'd, 'e, 'f) T3"
consts Inj_2_T3 :: "'b \<Rightarrow> ('a::var, 'b, 'c::var, 'd, 'e, 'f) T3"

consts Sb_T4 :: "('a::var \<Rightarrow> ('a, 'b) T4) \<Rightarrow> ('b::var \<Rightarrow> ('a, 'b) T4) \<Rightarrow> ('a, 'b) T4 \<Rightarrow> ('a, 'b) T4"
consts Vrs_1_T4 :: "('a::var, 'b::var) T4 \<Rightarrow> 'a set"
consts Vrs_2_T4 :: "('a::var, 'b::var) T4 \<Rightarrow> 'b set"
consts Inj_1_T4 :: "'a \<Rightarrow> ('a::var, 'b::var) T4"
consts Inj_2_T4 :: "'b \<Rightarrow> ('a::var, 'b::var) T4"

ML \<open>
Multithreading.parallel_proofs := 0
\<close>
declare [[goals_limit=1000]]
pbmv_monad "('a, 'b, 'c, 'd, 'e, 'f, 'g) T1"
  Sbs: Sb_T1
  RVrs: Vrs_1_T1
  Injs: Inj_1_T1 Inj_2_T1
  Vrs: Vrs_2_T1 Vrs_3_T1
  Maps: Map_T1
  Supps: set_1_T1 set_2_T1 set_3_T1
  bd: natLeq
                      apply (tactic \<open>Skip_Proof.cheat_tac @{context} 1\<close>)+
  done
print_theorems

pbmv_monad "('a, 'b, 'c, 'd) T2"
  Sbs: Sb_T2
  RVrs: Vrs_1_T2
  Injs: Inj_T2
  Vrs: Vrs_2_T2
  bd: natLeq
                      apply (tactic \<open>Skip_Proof.cheat_tac @{context} 1\<close>)+
  done

pbmv_monad "('a, 'b, 'c, 'd, 'e, 'f) T3" and "('a, 'c) T4"
  Sbs: Sb_T3 and Sb_T4
  Injs: Inj_1_T3 Inj_1_T4 Inj_2_T3 Inj_2_T4 and Inj_1_T4 Inj_2_T4
  Vrs: Vrs_1_T3 Vrs_2_T3 Vrs_3_T3 Vrs_4_T3 and Vrs_1_T4 Vrs_2_T4
  Maps: Map_T3
  Supps: set_1_T3 set_2_T3
  bd: natLeq
                      apply (tactic \<open>Skip_Proof.cheat_tac @{context} 1\<close>)+
  done
print_theorems
print_pbmv_monads

type_synonym ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h) T =
  "(('a, 'b, 'e, 'd) T2, 'b, 'c, 'g set, ('b, 'a, 'c, 'd, 'e, 'h) T3, 'f, 'g) T1"

(*
deads: 'a, 'e, 'f, 'g
frees: 'b, 'c, 'd
lives: 'h
*)

lemma cong': "f x = g x \<Longrightarrow> x = y \<Longrightarrow> f x = g y"
  by simp

(* Demoting T3 *)
pbmv_monad T3': "('a, 'b, 'c, 'd, 'e, 'f) T3" and "('a::var, 'c::var) T4"
  Sbs: "\<lambda>f1 \<rho>1 \<rho>2 \<rho>4. Sb_T3 \<rho>1 \<rho>2 Inj_2_T3 \<rho>4 \<circ> Map_T3 f1 id" and Sb_T4
  RVrs: set_1_T3
  Injs: Inj_1_T3 Inj_1_T4 Inj_2_T4 and Inj_1_T4 Inj_2_T4
  Vrs: Vrs_1_T3 Vrs_2_T3 Vrs_4_T3 and Vrs_1_T4 Vrs_2_T4
  Maps: "Map_T3 id"
  Supps: set_2_T3
  bd: natLeq
                      apply (rule infinite_regular_card_order_natLeq)
                      apply (unfold T3.Sb_Inj T3.Map_id id_o)
                      apply (rule refl)
                      apply (unfold comp_assoc T3.Map_Inj)
                      apply (rule T3.Sb_comp_Inj; (assumption | rule SSupp_Inj_bound))+
                      apply (rule trans)
                      apply (rule arg_cong2[OF refl, of _ _ "(\<circ>)"])
                      apply (rule trans[OF comp_assoc[symmetric]])
                      apply (rule arg_cong2[OF _ refl, of _ _ "(\<circ>)"])
                      apply (rule T3.Map_Sb)
                      apply (assumption | rule SSupp_Inj_bound)+
                      apply (rule trans)
                      apply (unfold comp_assoc)[1]
                      apply (rule trans[OF comp_assoc[symmetric]])
                      apply (rule arg_cong2[of _ _ _ _ "(\<circ>)"])
                      apply (rule T3.Sb_comp)
                      apply (assumption | rule T3.SSupp_Map_bound SSupp_Inj_bound)+
                      apply (rule T3.Map_comp)
                      apply (unfold id_o T3.Map_Inj)
                      apply (subst T3.Sb_comp_Inj, (assumption | rule SSupp_Inj_bound)+)+
                      apply (rule refl)

                      apply (rule T3.Supp_bd T3.Vrs_bd T3.Vrs_Inj)+

  subgoal for f \<rho>1 \<rho>2 \<rho>3 x
    apply (unfold comp_def)
    apply (subst T3.Supp_Sb)
    apply (assumption | rule SSupp_Inj_bound)+
    apply (rule T3.Supp_Map)
    done
  subgoal for f \<rho>1 \<rho>2 \<rho>3 x
    apply (unfold comp_def)
    apply (rule trans)
     apply (rule T3.Vrs_Sb)
        apply (assumption | rule SSupp_Inj_bound)+
    apply (unfold T3.Vrs_Map T3.Vrs_Inj UN_empty2 Un_empty_right Un_empty_left)
    apply (rule refl)
    done

  subgoal for f \<rho>1 \<rho>2 \<rho>3 x
    apply (unfold comp_def)
    apply (rule trans)
     apply (rule T3.Vrs_Sb)
        apply (assumption | rule SSupp_Inj_bound)+
    apply (unfold T3.Vrs_Map T3.Vrs_Inj UN_empty2 Un_empty_right Un_empty_left)
    apply (rule refl)
    done

  subgoal for f \<rho>1 \<rho>2 \<rho>3 x
    apply (unfold comp_def)
    apply (rule trans)
     apply (rule T3.Vrs_Sb)
        apply (assumption | rule SSupp_Inj_bound)+
    apply (unfold T3.Vrs_Map T3.Vrs_Inj UN_empty2 Un_empty_right Un_empty_left)
    apply (rule refl)
    done

  subgoal for f \<rho>1 \<rho>2 \<rho>3 g \<rho>'1 \<rho>'2 \<rho>'3 x
    apply (rule comp_apply_eq)
    apply (rule cong'[OF _ T3.Map_cong, rotated])
      apply (assumption | rule refl)+
    apply (rule T3.Sb_cong)
    apply (unfold T3.Vrs_Map)
               apply (assumption | rule SSupp_Inj_bound refl)+
    done
                      apply (rule refl)
                      apply (rule trans)
                      apply (rule T3.Map_comp)
                      apply (unfold id_o)
                      apply (rule refl)
                      apply (rule T3.Supp_Map)
                      apply (rule T3.Supp_bd)
                      apply (rule T3.Map_cong)
                      apply (rule refl)
                      apply assumption

  subgoal for f fa \<rho>1 \<rho>2 \<rho>3
    apply (rule trans)
     apply (rule trans[OF comp_assoc[symmetric]])
     apply (rule arg_cong2[OF _ refl, of _ _ "(\<circ>)"])
     apply (rule T3.Map_Sb)
        apply (assumption | rule SSupp_Inj_bound)+
    apply (unfold T3.Map_Inj comp_assoc)
    apply (rule arg_cong2[OF refl, of _ _ "(\<circ>)"])
    apply (rule trans)
     apply (rule T3.Map_comp)
    apply (rule sym)
    apply (rule trans)
     apply (rule T3.Map_comp)
    apply (unfold id_o o_id)
    apply (rule refl)
    done

                    apply (unfold comp_def)[1]
                    apply (subst T3.Supp_Sb, (assumption | rule SSupp_Inj_bound)+)
                    apply (rule trans)
                     apply (rule T3.Supp_Map)
                    apply (rule image_id)
  apply (rule trans)
                     apply (rule T3.Supp_Map)
                   apply (rule image_id)
                  apply (unfold T3.Vrs_Map)
                  apply (rule refl)+
             apply (rule T3.Sb_comp_Inj; assumption)+
           apply (rule T3.Sb_comp; assumption)
          apply (rule T3.Vrs_bd T3.Vrs_Inj)+
    apply (rule T3.Vrs_Sb; assumption)+
  apply (rule T3.Sb_cong; assumption)
  done
print_theorems

abbreviation "Vrs_1_T \<equiv> Vrs_2_T1"
abbreviation "Vrs_2_T \<equiv> \<lambda>x. \<Union> (Vrs_2_T2 ` set_1_T1 x)"
abbreviation "Vrs_3_T \<equiv> \<lambda>x. \<Union> (Vrs_1_T3 ` set_3_T1 x)"

declare [[ML_print_depth=1000]]
pbmv_monad T: "('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h) T" and "('a, 'b, 'e, 'd) T2" and T3': "('b, 'a, 'c, 'd, 'e, 'h) T3"
  Sbs: "\<lambda>h1 h2 \<rho>1 \<rho>2 \<rho>3 \<rho>4 \<rho>5. Sb_T1 h1 \<rho>1 Inj_2_T1 \<circ> Map_T1 (Sb_T2 h2 \<rho>2) id (Sb_T3 \<rho>3 \<rho>4 Inj_2_T3 \<rho>5 \<circ> Map_T3 h2 id)"
  RVrs: Vrs_1_T1 "\<lambda>x. \<Union> (Vrs_1_T2 ` set_1_T1 x) \<union> \<Union> (set_1_T3 ` set_3_T1 x)"
  Injs: Inj_1_T1 Inj_T2 Inj_1_T3 Inj_1_T4 Inj_2_T4
  Vrs: Vrs_2_T1 "\<lambda>x. \<Union> (Vrs_2_T2 ` set_1_T1 x)" "\<lambda>x. \<Union> (Vrs_1_T3 ` set_3_T1 x)" "\<lambda>x. \<Union> (Vrs_2_T3 ` set_3_T1 x)" "\<lambda>x. \<Union> (Vrs_4_T3 ` set_3_T1 x)"
  Maps: "\<lambda>f. Map_T1 id id (Map_T3 id f)"
  Supps: "\<lambda>x. \<Union> (set_2_T3 ` set_3_T1 x)"
  bd: natLeq
                      apply (rule infinite_regular_card_order_natLeq)
  subgoal
    apply (unfold id_o T1.Sb_Inj T1.Map_id T2.Sb_Inj T3.Sb_Inj T3.Map_id)
    apply (rule refl)
    done
  subgoal for f1 f2 \<rho>1 \<rho>2 \<rho>3 \<rho>4 \<rho>5
    apply (rule trans)
     apply (rule trans[OF comp_assoc])
     apply (rule arg_cong2[OF refl, of _ _ "(\<circ>)"])
    apply (rule T1.Map_Inj)
     apply (rule T1.Sb_comp_Inj)
       apply (assumption | rule T1.SSupp_Map_bound SSupp_Inj_bound)+
    done

  subgoal for g1 g2 \<rho>'1 \<rho>'2 \<rho>'3 \<rho>'4 \<rho>'5 f1 f2 \<rho>1 \<rho>2 \<rho>3 \<rho>4 \<rho>5
    apply (rule trans)
     apply (rule trans[OF comp_assoc])
    apply (rule trans)
     apply (rule arg_cong2[OF refl, of _ _ "(\<circ>)"])
     apply (rule trans[OF comp_assoc[symmetric]])
    apply (rule trans)
     apply (rule arg_cong2[OF _ refl, of _ _ "(\<circ>)"])
     apply (rule T1.Map_Sb)
        apply (assumption | rule SSupp_Inj_bound)+
     apply (rule trans[OF comp_assoc])
     apply (rule arg_cong2[OF refl, of _ _ "(\<circ>)"])
    apply (rule T1.Map_comp)
     apply (rule comp_assoc[symmetric])
    apply (subst T1.Sb_comp)
          apply (assumption | rule T1.SSupp_Map_bound SSupp_Inj_bound)+
    apply (rule arg_cong2[of _ _ _ _ "(\<circ>)"])
     apply (rule ext)
     apply (rule T1.Sb_cong)
    apply (unfold comp_assoc T1.Map_Inj id_o o_id)
             apply (assumption | rule supp_comp_bound infinite_UNIV T1.SSupp_Sb_bound SSupp_Inj_bound T1.SSupp_Map_bound refl
              T1.Sb_comp_Inj[THEN fun_cong]
            )+
    apply (rule ext)
    apply (rule T1.Map_cong)
      (* REPEAT for inner *)
      apply (rule T2.Sb_comp[THEN fun_cong], assumption+)
     apply (rule refl)
    (* repeated *)
    apply (rule trans)
     apply (rule arg_cong2[OF refl, of _ _ "(\<circ>)", THEN fun_cong])
    apply (rule trans)
     apply (rule trans[OF comp_assoc[symmetric]])
     apply (rule arg_cong2[OF _ refl, of _ _ "(\<circ>)"])
     apply (rule T3.Map_Sb)
        apply (assumption | rule SSupp_Inj_bound)+
     apply (unfold T3.Map_Inj)
     apply (rule trans[OF comp_assoc])
     apply (rule arg_cong2[OF refl, of _ _ "(\<circ>)"])
     apply (rule T3.Map_comp)
    apply (unfold id_o o_id comp_assoc[symmetric])
    apply (rule arg_cong2[OF _ refl, of _ _ "(\<circ>)", THEN fun_cong])
    apply (rule trans)
     apply (rule T3.Sb_comp)
            apply (assumption | rule T3.SSupp_Map_bound SSupp_Inj_bound)+
    apply (subst T3.Sb_comp_Inj, (assumption | rule SSupp_Inj_bound)+)+
    apply (unfold comp_assoc[symmetric])
    apply (rule refl)
    done

  apply (unfold T1.Supp_Inj UN_empty)
  apply (rule refl T1.Vrs_bd T2.Vrs_bd T3.Vrs_bd T1.Vrs_Inj T3'.Vrs_bd infinite_regular_card_order_Un infinite_regular_card_order_UN infinite_regular_card_order_natLeq T1.Supp_bd)+

                      apply (unfold0 comp_apply)[1]
                      apply (rule trans)
                      apply (rule T1.Vrs_Sb)
                      apply (assumption | rule SSupp_Inj_bound)+
                      apply (unfold T1.Vrs_Map)[1]
                      apply (rule refl)

                      apply (unfold0 comp_apply)[1]
                      apply (subst T1.Supp_Sb, (assumption | rule SSupp_Inj_bound)+)+
                      apply (unfold T1.Supp_Map image_comp[unfolded comp_def] T2.Vrs_Sb image_UN)[1]
                      apply (subst T3'.Vrs_Sb, (assumption | rule SSupp_Inj_bound)+)+
                      apply (unfold image_Un image_UN)[1]
                      apply (rule refl)

  subgoal for f1 f2 \<rho>1 \<rho>2 \<rho>3 \<rho>4 \<rho>5 x
    apply (unfold0 comp_apply)
    apply (subst T1.Vrs_Sb)
       apply (assumption | rule SSupp_Inj_bound)+
    apply (unfold T1.Vrs_Map T1.Vrs_Inj UN_empty2 Un_empty_right)
    apply (rule refl)
    done

  subgoal for f1 f2 \<rho>1 \<rho>2 \<rho>3 \<rho>4 \<rho>5 x
    apply (unfold0 comp_apply)
    apply (subst T1.Vrs_Sb T1.Supp_Sb, (assumption | rule SSupp_Inj_bound)+)+
    apply (unfold T1.Vrs_Map T1.Vrs_Inj T1.Supp_Map image_comp[unfolded comp_def] UN_empty2 Un_empty_right)
    apply (subst T2.Vrs_Sb T1.Supp_Sb, (assumption | rule SSupp_Inj_bound)+)+
    apply (unfold UN_UN_flatten)
    apply (rule refl)
    done

  subgoal for f1 f2 \<rho>1 \<rho>2 \<rho>3 \<rho>4 \<rho>5 x
    apply (unfold0 comp_apply)
    apply (subst T1.Vrs_Sb T1.Supp_Sb, (assumption | rule SSupp_Inj_bound)+)+
    apply (unfold T1.Vrs_Map T1.Vrs_Inj comp_apply T1.Supp_Map image_comp[unfolded comp_def] UN_empty2 Un_empty_right)
    apply (subst T3.Vrs_Sb T1.Supp_Sb, (assumption | rule SSupp_Inj_bound)+)+
    apply (unfold UN_UN_flatten T3.Vrs_Map T3.Vrs_Inj UN_empty2 Un_empty_right)
    apply (rule refl)
    done

  subgoal for f1 f2 \<rho>1 \<rho>2 \<rho>3 \<rho>4 \<rho>5 x
    apply (unfold0 comp_apply)
    apply (subst T1.Vrs_Sb T1.Supp_Sb, (assumption | rule SSupp_Inj_bound)+)+
    apply (unfold T1.Vrs_Map T1.Vrs_Inj comp_apply T1.Supp_Map image_comp[unfolded comp_def] UN_empty2 Un_empty_right)
    apply (subst T3.Vrs_Sb T1.Supp_Sb, (assumption | rule SSupp_Inj_bound)+)+
    apply (unfold UN_UN_flatten T3.Vrs_Map T3.Vrs_Inj UN_empty2 Un_empty_right UN_Un_distrib)
    apply (rule refl)
    done

  subgoal for f1 f2 \<rho>1 \<rho>2 \<rho>3 \<rho>4 \<rho>5 x
    apply (unfold0 comp_apply)
    apply (subst T1.Vrs_Sb T1.Supp_Sb, (assumption | rule SSupp_Inj_bound)+)+
    apply (unfold T1.Vrs_Map T1.Vrs_Inj comp_apply T1.Supp_Map image_comp[unfolded comp_def] UN_empty2 Un_empty_right)
    apply (subst T3.Vrs_Sb T1.Supp_Sb, (assumption | rule SSupp_Inj_bound)+)+
    apply (unfold UN_UN_flatten T3.Vrs_Map T3.Vrs_Inj UN_empty2 Un_empty_right UN_Un_distrib)
    apply (rule refl)
    done

  subgoal premises prems for f1 f2 \<rho>1 \<rho>2 \<rho>3 \<rho>4 \<rho>5 g1 g2 \<rho>'1 \<rho>'2 \<rho>'3 \<rho>'4 \<rho>'5 x
    apply (rule comp_apply_eq)
    apply (rule cong'[OF _ T1.Map_cong, rotated])
    (* REPEAT for inners *)
       apply (rule T2.Sb_cong)
            apply (rule prems)+
  (* REPEAT_DETERM *)
        apply (drule UN_I)
         apply assumption
        apply (assumption | erule UnI1 UnI2 | rule UnI2)+
    (* repeated *)
    apply (rule prems)
        apply (drule UN_I)
         apply assumption
        apply (assumption | erule UnI1 UnI2 | rule UnI2)+
    (* END REPEAT_DETERM *)
  (* second inner *)
      apply (rule refl)
  (* third inner *)
     apply (rule T3'.Sb_cong)
    apply (rule prems)+
  (* REPEAT_DETERM *)
        apply (drule UN_I)
         apply assumption
        apply (assumption | erule UnI1 UnI2 | rule UnI2)+
    (* repeated *)
    apply (rule prems)
        apply (drule UN_I)
         apply assumption
        apply (assumption | erule UnI1 UnI2 | rule UnI2)+
    (* repeated *)
    apply (rule prems)
        apply (drule UN_I)
         apply assumption
        apply (assumption | erule UnI1 UnI2 | rule UnI2)+
    (* repeated *)
    apply (rule prems)
        apply (drule UN_I)
         apply assumption
     apply (assumption | erule UnI1 UnI2 | rule UnI2)+
  (* END REPEAT_DETERM *)
    apply (rule T1.Sb_cong)
    apply (unfold T1.Vrs_Map)
            apply (rule prems SSupp_Inj_bound refl | assumption| erule UnI1 UnI2 | rule UnI2)+
    done

                apply (unfold T3'.Map_id T1.Map_id)[1]
                apply (rule refl)

               apply (unfold T1.Map_comp id_o o_id T3'.Map_comp)[1]
               apply (rule refl)

              apply (unfold T1.Supp_Map image_comp[unfolded comp_def] T3'.Supp_Map image_UN)[1]
              apply (rule refl)

             apply (rule infinite_regular_card_order_UN infinite_regular_card_order_natLeq T1.Supp_bd T3'.Supp_bd)+

  subgoal premises prems for f g x
    apply (rule T1.Map_cong)
      apply (rule refl)+
    apply (rule T3'.Map_cong)
    apply (rule prems)
    apply (erule UN_I)
    apply assumption
    done

  subgoal for f f1 f2 \<rho>1 \<rho>2 \<rho>3 \<rho>4 \<rho>5
    apply (unfold comp_assoc[symmetric])
    apply (rule trans)
     apply (rule arg_cong2[OF T1.Map_Sb refl])
       apply (assumption | rule SSupp_Inj_bound)+
    apply (unfold T1.Map_Inj comp_assoc T1.Map_comp id_o o_id T3'.Map_Sb)
    apply (rule refl)
    done

  apply (unfold0 comp_apply)[1]
          apply (subst T1.Supp_Sb, (assumption | rule SSupp_Inj_bound)+)+
          apply (unfold T1.Supp_Map image_comp[unfolded comp_def] T3'.Supp_Sb)[1]
          apply (rule refl)

         apply (unfold T1.Vrs_Map T1.Supp_Map image_id image_comp[unfolded comp_def] T3'.Vrs_Map T1.Map_Inj)
         apply (rule refl)+
  done
print_theorems

ML \<open>
val T1 = the (BMV_Monad_Def.pbmv_monad_of @{context} @{type_name T1});
val T2 = the (BMV_Monad_Def.pbmv_monad_of @{context} @{type_name T2});
val T3 = the (BMV_Monad_Def.pbmv_monad_of @{context} "BMV_Composition.T3'");
\<close>

local_setup \<open>fn lthy =>
let
  open MRBNF_Util
  val ((bmv, unfold_set), lthy) = BMV_Monad_Def.compose_bmv_monad I T1 [Inl T2, Inr @{typ "'g set"}, Inl T3]
    { frees = [@{typ 'b}, @{typ 'c}, @{typ 'g}], deads = [@{typ 'f}] }
    [ SOME { frees = [@{typ 'd}, @{typ 'b}], lives = [], deads = [@{typ 'a}, @{typ 'e}] },
      NONE,
      SOME { frees = [@{typ 'b}, @{typ 'a}, @{typ 'c}], lives = [@{typ 'd}, @{typ 'h}], deads = [@{typ 'e}] }
    ] lthy
in lthy end
\<close>


end