theory BMV_Fixpoint
  imports BMV_Monad
begin

type_synonym ('tv, 'v, 'btv, 'bv, 'c, 'd) FTerm_pre' =
  "'v                    \<comment>\<open>Var 'v\<close>
  + 'd * 'd              \<comment>\<open>App \<open>('tv, 'v) FTerm\<close> \<open>('tv, 'v) FTerm\<close>\<close>
  + 'd * 'tv FType       \<comment>\<open>TyApp \<open>('tv, 'v) FTerm\<close> \<open>'tv FType\<close>\<close>
  + 'bv * 'tv FType * 'c \<comment>\<open>Lam x::'v \<open>'tv FType\<close> t::\<open>('tv, 'v) FTerm\<close> binds x in t\<close>
  + 'btv * 'c            \<comment>\<open>TyLam a::'tv t::\<open>('tv, 'v) FTerm\<close> binds a in t\<close>"

local_setup \<open>fn lthy =>
  let
    val Xs = map dest_TFree []
    val resBs = map dest_TFree [@{typ 'tv}, @{typ 'v}, @{typ 'btv}, @{typ 'bv}, @{typ 'c}, @{typ 'd}]

    fun flatten_tyargs Ass = subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;
    val qualify = Binding.prefix_name "FTerm_pre_"
    val accum = (MRBNF_Comp.empty_comp_cache, MRBNF_Comp.empty_unfolds)

    (* Step 1: Create pre-MRBNF *)
    val ((mrbnf, tys), (accum, lthy)) = MRBNF_Comp.mrbnf_of_typ true MRBNF_Def.Smart_Inline qualify flatten_tyargs Xs []
      [(dest_TFree @{typ 'tv}, MRBNF_Def.Free_Var), (dest_TFree @{typ 'v}, MRBNF_Def.Free_Var),
       (dest_TFree @{typ 'btv}, MRBNF_Def.Bound_Var), (dest_TFree @{typ 'bv}, MRBNF_Def.Bound_Var)
      ] @{typ "('tv, 'v, 'btv, 'bv, 'c, 'd) FTerm_pre'"} (accum, lthy)

    (* Step 2: Seal the pre-MRBNF with a typedef *)
    val ((mrbnf, (Ds, info)), lthy) = MRBNF_Comp.seal_mrbnf I (snd accum) (Binding.name "FTerm_pre") true (fst tys) [] mrbnf lthy

    (* Step 3: Register the pre-MRBNF as a BNF in its live variables *)
    val (bnf, lthy) = MRBNF_Def.register_mrbnf_as_bnf mrbnf lthy

    (* Step 4: Construct the binder fixpoint *)
    val (fp_res, lthy) = MRBNF_FP.construct_binder_fp BNF_Util.Least_FP
    [{
      FVars = [SOME "FTVars", SOME "FVars"],
      T_name = "FTerm",
      nrecs = 2,
      permute = NONE,
      pre_mrbnf = mrbnf
    }] [[([], [0])], [([], [0])]] lthy

    (* Step 5: Prove BMV structure of pre-MRBNF by composition *)
    val (bmv, (thms, lthy)) = apfst the (PBMV_Monad_Comp.pbmv_monad_of_typ true BNF_Def.Smart_Inline (K BNF_Def.Note_Some)
      (map dest_TFree [@{typ 'btv}, @{typ 'bv}, @{typ 'c}, @{typ 'd}])
      I @{typ "('tv, 'v, 'btv, 'bv, 'c, 'd) FTerm_pre'"} ([], lthy))

    (* Register bmv to access theorems later *)
    val lthy = BMV_Monad_Def.register_pbmv_monad "BMV_Fixpoint.FTerm_pre'" bmv lthy;

    val notes = [
      ("bmv_defs", thms)
    ] |> (map (fn (thmN, thms) =>
      ((Binding.name thmN, []), [(thms, [])])
    ));

    val (noted, lthy) = Local_Theory.notes notes lthy

    val _ = @{print} bmv
  in lthy end\<close>

ML \<open>
val bmv = the (BMV_Monad_Def.pbmv_monad_of @{context} "BMV_Fixpoint.FTerm_pre'")
val axioms = BMV_Monad_Def.axioms_of_bmv_monad bmv;
val laxioms = nth axioms (BMV_Monad_Def.leader_of_bmv_monad bmv)
\<close>

lemma comp_assoc_middle: "(\<And>x. f2 (f1 x) = x) \<Longrightarrow> f1 \<circ> g1 \<circ> f2 \<circ> (f1 \<circ> g2 \<circ> f2) = f1 \<circ> (g1 \<circ> g2) \<circ> f2"
  by auto
lemma typedef_Rep_comp: "type_definition Rep Abs UNIV \<Longrightarrow> Rep ((Abs \<circ> f \<circ> Rep) x) = f (Rep x)"
  unfolding comp_def type_definition.Abs_inverse[OF _ UNIV_I] ..

definition "Sb_FTerm_pre \<equiv> \<lambda>(f1::'v::var \<Rightarrow> 'v) (f2::'tv::var \<Rightarrow> 'tv FType). (Abs_FTerm_pre :: _ \<Rightarrow> ('tv, 'v, 'btv::var, 'bv::var, 'c, 'd) FTerm_pre) \<circ> (map_sum (id f1) (map_sum id (BMV_Fixpoint.sum2.sum2.sum.Sb_0 f2) \<circ> id) \<circ> id) \<circ> Rep_FTerm_pre"
definition "Vrs1_FTerm_pre \<equiv> \<lambda>x. \<Union>x\<in>Basic_BNFs.setl (Rep_FTerm_pre x). {x}"
definition "Vrs2_FTerm_pre \<equiv> \<lambda>x. \<Union>x\<in>Basic_BNFs.setr (Rep_FTerm_pre x). \<Union> (BMV_Fixpoint.sum2.sum2.sum.Vrs_0_0_0 ` Basic_BNFs.setr x)"

(* Transfer pbmv structure of pre-datatype to sealed version *)
pbmv_monad "('tv::var, 'v::var, 'btv::var, 'bv::var, 'c, 'd) FTerm_pre" and "'v::var" and "'tv::var FType"
  Sbs: "Sb_FTerm_pre :: _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('tv::var, 'v::var, 'btv::var, 'bv::var, 'c, 'd) FTerm_pre" and "id :: ('v \<Rightarrow> 'v) \<Rightarrow> 'v \<Rightarrow> 'v" and "tvsubst_FType :: ('tv::var \<Rightarrow> 'tv FType) \<Rightarrow> 'tv FType \<Rightarrow> 'tv FType"
  Injs: "id :: 'v::var \<Rightarrow> 'v" "TyVar :: 'tv::var \<Rightarrow> 'tv FType" and "id :: 'v::var \<Rightarrow> 'v" and "TyVar :: 'tv::var \<Rightarrow> 'tv FType"
  Vrs: "Vrs1_FTerm_pre :: ('tv::var, 'v::var, 'btv::var, 'bv::var, 'c, 'd) FTerm_pre \<Rightarrow> _", "Vrs2_FTerm_pre :: ('tv::var, 'v::var, 'btv::var, 'bv::var, 'c, 'd) FTerm_pre \<Rightarrow> _" and "\<lambda>(x::'v). {x}" and "Vrs_FType_1 :: _ \<Rightarrow> 'tv::var set"
  Map: "\<lambda>(f1::'c \<Rightarrow> 'c') (f2::'d \<Rightarrow> 'd'). map_FTerm_pre id id id id f1 f2"
  Supps: "set5_FTerm_pre :: _ \<Rightarrow> 'c set" "set6_FTerm_pre :: _ \<Rightarrow> 'd set"
  bd: natLeq
  apply (unfold Sb_FTerm_pre_def Vrs1_FTerm_pre_def Vrs2_FTerm_pre_def)
  subgoal
    apply (tactic \<open>resolve_tac @{context} [BMV_Monad_Def.bd_infinite_regular_card_order_of_bmv_monad bmv] 1\<close>)
    done
  subgoal
    apply (tactic \<open>Local_Defs.unfold0_tac @{context} [#Sb_Inj laxioms]\<close>)
    apply (unfold o_id)
    apply (rule ext)
    apply (rule trans[OF comp_apply])
    apply (rule trans[OF Rep_FTerm_pre_inverse])
    apply (rule id_apply[symmetric])
    done
  subgoal
    apply (rule trans[OF comp_assoc_middle])
     apply (rule Abs_FTerm_pre_inverse[OF UNIV_I])
    apply (rule arg_cong[of _ _ "\<lambda>x. _ \<circ> x \<circ> _"])
    apply (tactic \<open>resolve_tac @{context} [#Sb_comp laxioms] 1\<close>; assumption)
    done
  subgoal
    apply (tactic \<open>resolve_tac @{context} (maps (map_filter I) (#Vrs_bds laxioms)) 1\<close>)
    done
  subgoal
    apply (tactic \<open>resolve_tac @{context} (maps (map_filter I) (#Vrs_bds laxioms)) 1\<close>)
    done
  subgoal
    apply (unfold typedef_Rep_comp[OF type_definition_FTerm_pre])
    apply (tactic \<open>resolve_tac @{context} (maps (map_filter I) (#Vrs_Sbs laxioms)) 1\<close>)
     apply assumption+
    done
  subgoal
    apply (unfold typedef_Rep_comp[OF type_definition_FTerm_pre])
    apply (tactic \<open>resolve_tac @{context} (maps (map_filter I) (#Vrs_Sbs laxioms)) 1\<close>)
     apply assumption+
    done
  subgoal
    apply (rule trans[OF comp_apply])+
    apply (rule trans[OF _ comp_apply[symmetric]])+
    apply (rule arg_cong[of _ _ Abs_FTerm_pre])
    apply (tactic \<open>resolve_tac @{context} [#Sb_cong laxioms] 1\<close>)
         apply assumption+
    done
  subgoal
    apply (rule FTerm_pre.map_id0)
    done
  subgoal
    apply (rule trans)
     apply (rule FTerm_pre.map_comp0[symmetric])
                apply (rule supp_id_bound bij_id)+
    apply (unfold id_o)
    apply (rule refl)
    done
  subgoal
    apply (rule FTerm_pre.set_map)
         apply (rule supp_id_bound bij_id)+
    done
  subgoal
    apply (rule FTerm_pre.set_map)
         apply (rule supp_id_bound bij_id)+
    done
  subgoal
    apply (rule FTerm_pre.set_bd)
    done
  subgoal
    apply (rule FTerm_pre.set_bd)
    done
  subgoal
    apply (rule FTerm_pre.map_cong0)
                     apply (rule bij_id supp_id_bound)+
         apply (rule refl | assumption)+
    done
  subgoal
    apply (rule ext)
    apply (tactic \<open>Local_Defs.unfold0_tac @{context} (@{thms map_FTerm_pre_def bmv_defs
      comp_def Abs_FTerm_pre_inverse[OF UNIV_I] sum.map_comp prod.map_comp id_apply
      FType.map_id0
    })\<close>)
    apply (rule refl)
    done
  subgoal
    apply (tactic \<open>Local_Defs.unfold0_tac @{context} (@{thms set5_FTerm_pre_def set6_FTerm_pre_def bmv_defs
      comp_def Abs_FTerm_pre_inverse[OF UNIV_I] sum.map_comp prod.map_comp id_apply
      FType.map_id0 id_def[symmetric]
    })\<close>)
    apply (rule refl)
    done
  subgoal
    apply (tactic \<open>Local_Defs.unfold0_tac @{context} (@{thms set5_FTerm_pre_def set6_FTerm_pre_def bmv_defs
      comp_def Abs_FTerm_pre_inverse[OF UNIV_I] sum.map_comp prod.map_comp id_apply
      FType.map_id0 id_def[symmetric]
    })\<close>)
    apply (rule refl)
    done
  subgoal
    apply (tactic \<open>Local_Defs.unfold0_tac @{context} (@{thms map_FTerm_pre_def bmv_defs
      comp_def Abs_FTerm_pre_inverse[OF UNIV_I] sum.map_comp prod.map_comp id_apply
      FType.map_id0 sum.set_map prod.set_map image_id UN_simps(10)
    })\<close>)
    apply (rule refl)
    done
  subgoal
    apply (tactic \<open>Local_Defs.unfold0_tac @{context} (@{thms map_FTerm_pre_def bmv_defs
      comp_def Abs_FTerm_pre_inverse[OF UNIV_I] sum.map_comp prod.map_comp id_apply
      FType.map_id0 sum.set_map prod.set_map image_id UN_simps(10)
    })\<close>)
    apply (rule refl)
    done
      (********************* BMV Structure of minions, no transfer needed *)
               apply (tactic \<open>resolve_tac @{context} (map #Sb_Inj axioms) 1\<close>)
              apply (tactic \<open>resolve_tac @{context} (maps #Sb_comp_Injs axioms) 1\<close>; assumption)
             apply (tactic \<open>resolve_tac @{context} (map #Sb_comp axioms) 1\<close>; assumption)
            apply (tactic \<open>resolve_tac @{context} (maps (maps (map_filter I) o #Vrs_bds) axioms) 1\<close>; assumption)
           apply (tactic \<open>resolve_tac @{context} (maps (maps (map_filter I) o #Vrs_Injs) axioms) 1\<close>; assumption)
          apply (tactic \<open>resolve_tac @{context} (maps (maps (map_filter I) o #Vrs_Sbs) axioms) 1\<close>; assumption)
         apply (tactic \<open>resolve_tac @{context} (map #Sb_cong axioms) 1\<close>; assumption)
    (* also for FType *)
        apply (tactic \<open>resolve_tac @{context} (map #Sb_Inj axioms) 1\<close>)
       apply (tactic \<open>resolve_tac @{context} (maps #Sb_comp_Injs axioms) 1\<close>; assumption)
      apply (tactic \<open>resolve_tac @{context} (map #Sb_comp axioms) 1\<close>; assumption)
     apply (tactic \<open>resolve_tac @{context} (maps (maps (map_filter I) o #Vrs_bds) axioms) 1\<close>; assumption)
    apply (tactic \<open>resolve_tac @{context} (maps (maps (map_filter I) o #Vrs_Injs) axioms) 1\<close>; assumption)
   apply (tactic \<open>resolve_tac @{context} (maps (maps (map_filter I) o #Vrs_Sbs) axioms) 1\<close>; assumption)
  apply (tactic \<open>resolve_tac @{context} (map #Sb_cong axioms) 1\<close>; assumption)
  done
print_pbmv_monads

lemma set1_Vrs: "set1_FTerm_pre x = Vrs2_FTerm_pre x"
  apply (unfold set1_FTerm_pre_def Vrs2_FTerm_pre_def sum.set_map UN_empty2 Un_empty_left
    prod.set_map Un_empty_right comp_def bmv_defs
  )
  apply (rule refl)
  done
lemma set2_Vrs: "set2_FTerm_pre x = Vrs1_FTerm_pre x"
  apply (unfold set2_FTerm_pre_def Vrs1_FTerm_pre_def sum.set_map UN_empty2 Un_empty_left
    prod.set_map Un_empty_right comp_def bmv_defs
  )
  apply (rule refl)
  done
lemma set3_Sb: "set3_FTerm_pre (Sb_FTerm_pre f1 f2 x) = set3_FTerm_pre x"
  apply (unfold Sb_FTerm_pre_def bmv_defs comp_def id_apply set3_FTerm_pre_def
    prod.set_map sum.set_map UN_empty2 Un_empty_left Un_empty_right
    Abs_FTerm_pre_inverse[OF UNIV_I] UN_simps(10)
  )
  apply (rule refl)
  done
lemma set4_Sb: "set4_FTerm_pre (Sb_FTerm_pre f1 f2 x) = set4_FTerm_pre x"
  apply (unfold Sb_FTerm_pre_def bmv_defs comp_def id_apply set4_FTerm_pre_def
    prod.set_map sum.set_map UN_empty2 Un_empty_left Un_empty_right
    Abs_FTerm_pre_inverse[OF UNIV_I] UN_simps(10)
  )
  apply (rule refl)
  done

lemma permute_Sb_FType:
  fixes f::"'tv::var \<Rightarrow> 'tv"
  assumes "bij f" "|supp f| <o |UNIV::'tv set|" "|SSupp_FType g| <o |UNIV::'tv set|"
  shows "Sb_FType (permute_FType f \<circ> g \<circ> inv f) = permute_FType f \<circ> Sb_FType g \<circ> permute_FType (inv f)"
  apply (rule ext)
  apply (rule trans[OF _ comp_apply[symmetric]])
  subgoal for x
    apply (subgoal_tac "|SSupp_FType (permute_FType f \<circ> g \<circ> inv f)| <o |UNIV|")
     prefer 2
     apply (subst FType.SSupp_natural)
    apply (rule assms ordLeq_ordLess_trans[OF card_of_image])+
    apply (binder_induction x avoiding: "IImsupp_FType (permute_FType f \<circ> g \<circ> inv f)" rule: FType.strong_induct)
       apply (unfold IImsupp_FType_def)[1]
       apply (rule FType.Un_bound)
        apply (subst FType.SSupp_natural)
          apply (rule assms)+
        apply (rule ordLeq_ordLess_trans[OF card_of_image])
        apply (rule assms)
    apply (rule FType.UN_bound)
        apply (subst FType.SSupp_natural)
          apply (rule assms)+
        apply (rule ordLeq_ordLess_trans[OF card_of_image])
        apply (rule assms)
       apply (unfold comp_def)[1]
       apply (rule FType.set_bd_UNIV)

    apply (rule trans)
       apply (rule FType.subst)
       apply assumption
      apply (unfold comp_def)[1]
      apply (rule arg_cong[of _ _ "permute_FType _"])
      apply (rule sym)
      apply (rule trans)
       apply (subst FType.permute)
    apply (rule assms bij_imp_bij_inv supp_inv_bound)+
       apply (rule FType.subst)
       apply (rule assms)
      apply (rule refl)

     apply (rule trans)
      apply (rule FType.subst)
      apply assumption
     apply (subst FType.permute)
       apply (rule assms bij_imp_bij_inv supp_inv_bound)+
    apply (unfold comp_def)[1]
     apply (subst FType.subst)
      apply (rule assms)
     apply (subst FType.permute)
       apply (rule assms)+
     apply (rule arg_cong2[of _ _ _ _ TyApp])
      apply assumption+

     apply (rule trans)
     apply (rule FType.subst)
      apply assumption+
    apply (subst FType.permute)
       apply (rule assms bij_imp_bij_inv supp_inv_bound)+
    apply (rule trans[OF _ comp_apply[symmetric]])
    apply (subst FType.subst)
      apply (rule assms)
     apply (subst (asm) FType.IImsupp_natural)
       apply (rule assms)+
     apply (subst (asm) image_in_bij_eq)
      apply (rule assms)
     apply assumption
    apply (subst FType.permute)
      apply (rule assms)+
    apply (subst inv_simp2[of f])
     apply (rule assms)
    apply (rule arg_cong2[of _ _ _ _ TyAll])
     apply (rule refl)
    apply (unfold comp_def)
    apply assumption
    done
  done

lemma Map_Sb':
  fixes f1::"'x1::var \<Rightarrow> 'x1" and f2::"'x2::var \<Rightarrow> 'x2" and f3::"'x3::var \<Rightarrow> 'x3" and f4::"'x4::var \<Rightarrow> 'x4"
  assumes "bij f1" "|supp f1| <o |UNIV::'x1 set|" "bij f2" "|supp f2| <o |UNIV::'x2 set|" "|{a. g2 a \<noteq> Inj_FType_1 a}| <o |UNIV::'x1 set|"
  shows "map_FTerm_pre f1 f2 f3 f4 f5 f6 \<circ> Sb_FTerm_pre g1 g2 = Sb_FTerm_pre (f2 \<circ> g1 \<circ> inv f2) (permute_FType f1 \<circ> g2 \<circ> inv f1) \<circ> map_FTerm_pre f1 f2 f3 f4 f5 f6"
  apply (rule ext)
  apply (subgoal_tac "|SSupp_FType g2| <o |UNIV::'x1 set|")
   prefer 2
   apply (unfold SSupp_FType_def tvVVr_tvsubst_FType_def tv\<eta>_FType_tvsubst_FType_def comp_def TyVar_def[symmetric])[1]
  apply (rule assms)
  apply (tactic \<open>Local_Defs.unfold0_tac @{context} @{thms
    comp_apply map_FTerm_pre_def bmv_defs Sb_FTerm_pre_def Abs_FTerm_pre_inverse[OF UNIV_I] o_id id_apply
    sum.map_comp prod.map_comp
  }\<close>)
  apply (subst permute_Sb_FType, (rule assms | assumption)+)+
  apply (unfold comp_def)
  apply (unfold sum.map_comp id_apply prod.map_comp comp_def)
  apply (subst inv_simp1, rule assms)+
  apply (subst FType.vvsubst_permute FType.permute_comp inv_o_simp1, (rule assms bij_imp_bij_inv supp_inv_bound)+)+
  apply (unfold FType.permute_id)
  apply (rule refl)
  done

ML \<open>
val bmv = the (BMV_Monad_Def.pbmv_monad_of @{context} "BMV_Fixpoint.FTerm_pre")
val axioms = BMV_Monad_Def.axioms_of_bmv_monad bmv
val laxioms = hd axioms
val param = the (hd (BMV_Monad_Def.params_of_bmv_monad bmv))
\<close>

(* Substitution axioms *)
abbreviation \<eta> :: "'v::var \<Rightarrow> ('tv::var, 'v::var, 'a::var, 'b::var, 'c, 'd) FTerm_pre" where
  "\<eta> a \<equiv> Abs_FTerm_pre (Inl a)"

lemma eta_free: "set2_FTerm_pre (\<eta> a) = {a}"
  apply (unfold set2_FTerm_pre_def sum.set_map UN_empty2 Un_empty_left Un_empty_right prod.set_map comp_def
    Abs_FTerm_pre_inverse[OF UNIV_I] sum_set_simps UN_empty UN_single
  )
  apply (rule refl)
  done
lemma eta_inj: "\<eta> a = \<eta> b \<Longrightarrow> a = b"
  apply (unfold Abs_FTerm_pre_inject[OF UNIV_I UNIV_I] sum.inject)
  apply assumption
  done
lemma eta_natural:
  fixes f1::"'x1::var \<Rightarrow> 'x1" and f2::"'x2::var \<Rightarrow> 'x2" and f3::"'x3::var \<Rightarrow> 'x3" and f4::"'x4::var \<Rightarrow> 'x4"
  assumes "|supp f1| <o |UNIV::'x1 set|" "|supp f2| <o |UNIV::'x2 set|"
    "bij f3" "|supp f3| <o |UNIV::'x3 set|" "bij f4" "|supp f4| <o |UNIV::'x4 set|"
  shows "map_FTerm_pre f1 f2 f3 f4 f5 f6 \<circ> \<eta> = \<eta> \<circ> f2"
  apply (rule ext)
  apply (unfold comp_def map_FTerm_pre_def Abs_FTerm_pre_inverse[OF UNIV_I] map_sum.simps)
  apply (rule refl)
  done

(* Construction of substitution *)
type_synonym ('tv, 'v) P = "('v \<Rightarrow> ('tv, 'v) FTerm) \<times> ('tv \<Rightarrow> 'tv FType)"

definition VVr :: "'v::var \<Rightarrow> ('tv::var, 'v) FTerm" where
  "VVr \<equiv> FTerm_ctor \<circ> \<eta>"
definition isVVr :: "('tv::var, 'v::var) FTerm \<Rightarrow> bool" where
  "isVVr x \<equiv> \<exists>a. x = VVr a"
definition asVVr :: "('tv::var, 'v::var) FTerm \<Rightarrow> 'v" where
  "asVVr x \<equiv> (if isVVr x then SOME a. x = VVr a else undefined)"

definition SSupp_FTerm :: "('v \<Rightarrow> ('tv::var, 'v::var) FTerm) \<Rightarrow> 'v set" where
  "SSupp_FTerm f \<equiv> { a. f a \<noteq> VVr a }"
definition IImsupp_FTerm1 :: "('v \<Rightarrow> ('tv::var, 'v::var) FTerm) \<Rightarrow> 'tv set" where
  "IImsupp_FTerm1 f \<equiv> \<Union>(FTVars ` f ` SSupp_FTerm f)"
definition IImsupp_FTerm2 :: "('v \<Rightarrow> ('tv::var, 'v::var) FTerm) \<Rightarrow> 'v set" where
  "IImsupp_FTerm2 f \<equiv> SSupp_FTerm f \<union> \<Union>(FVars ` f ` SSupp_FTerm f)"

definition Uctor :: "('tv::var, 'v::var, 'tv, 'v, ('tv, 'v) FTerm \<times> (('tv, 'v) P \<Rightarrow> ('tv, 'v) FTerm), ('tv, 'v) FTerm \<times> (('tv, 'v) P \<Rightarrow> ('tv, 'v) FTerm)) FTerm_pre
  \<Rightarrow> ('tv, 'v) P \<Rightarrow> ('tv, 'v) FTerm" where
  "Uctor y p \<equiv> case p of (f1, f2) \<Rightarrow> if isVVr (FTerm_ctor (map_FTerm_pre id id id id fst fst y)) then
    f1 (asVVr (FTerm_ctor (map_FTerm_pre id id id id fst fst y)))
  else
    FTerm_ctor (Sb_FTerm_pre id f2 (map_FTerm_pre id id id id ((\<lambda>R. R (f1, f2)) \<circ> snd) ((\<lambda>R. R (f1, f2)) \<circ> snd) y))"

definition PFVars_1 :: "('tv::var, 'v::var) P \<Rightarrow> 'tv set" where
  "PFVars_1 p \<equiv> case p of (f1, f2) \<Rightarrow> IImsupp_FTerm1 f1 \<union> IImsupp_FType f2"
definition PFVars_2 :: "('tv::var, 'v::var) P \<Rightarrow> 'v set" where
  "PFVars_2 p \<equiv> case p of (f1, _) \<Rightarrow> IImsupp_FTerm2 f1"

definition compSS_FType :: "('tv \<Rightarrow> 'tv) \<Rightarrow> ('tv \<Rightarrow> 'tv::var FType) \<Rightarrow> 'tv \<Rightarrow> 'tv FType" where
  "compSS_FType g f \<equiv> permute_FType g \<circ> f \<circ> inv g"
definition compSS_FTerm :: "('tv \<Rightarrow> 'tv) \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('v \<Rightarrow> ('tv::var, 'v::var) FTerm) \<Rightarrow> 'v \<Rightarrow> ('tv, 'v) FTerm" where
  "compSS_FTerm g1 g2 f \<equiv> permute_FTerm g1 g2 \<circ> f \<circ> inv g2"
definition Pmap :: "('tv \<Rightarrow> 'tv) \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('tv::var, 'v::var) P \<Rightarrow> ('tv, 'v) P" where
  "Pmap g1 g2 p \<equiv> case p of (f1, f2) \<Rightarrow> (compSS_FTerm g1 g2 f1, compSS_FType g1 f2)"
lemmas compSS_defs = compSS_FType_def compSS_FTerm_def

definition valid_P :: "('tv::var, 'v::var) P \<Rightarrow> bool" where
  "valid_P p \<equiv> case p of (f1, f2) \<Rightarrow>
    |SSupp_FTerm f1| <o cmin |UNIV::'tv set| |UNIV::'v set|
  \<and> |SSupp_FType f2| <o cmin |UNIV::'tv set| |UNIV::'v set|"

lemma asVVr_VVr: "asVVr (VVr a) = a"
  apply (unfold asVVr_def isVVr_def)
  apply (subst if_P)
   apply (rule exI)
   apply (rule refl)
  apply (rule someI2)
   apply (rule refl)
  apply (unfold VVr_def comp_def)
  apply (unfold FTerm.TT_inject0)
  apply (erule exE conjE)+
  apply (unfold map_FTerm_pre_def comp_def Abs_FTerm_pre_inverse[OF UNIV_I]
    map_sum.simps Abs_FTerm_pre_inject[OF UNIV_I UNIV_I] id_apply
    sum.inject
  )
  apply (erule sym)
  done

ML \<open>
val Map_Sb' = Local_Defs.unfold0 @{context} @{thms comp_apply} (#Map_Sb param RS fun_cong) RS sym
val Vrs_Sb = maps (map_filter I) (#Vrs_Sbs laxioms);
val Vrs_Injs = maps (maps (map_filter I) o #Vrs_Injs) axioms;
\<close>

lemma permute_VVr:
  fixes f1::"'var::var \<Rightarrow> 'var" and f2::"'tyvar::var \<Rightarrow> 'tyvar"
  assumes f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "permute_FTerm f1 f2 (VVr a) = VVr (f2 a)"
  apply (unfold VVr_def comp_def)
  apply (rule trans)
   apply (rule FTerm.permute_ctor[OF assms])
  apply (subst fun_cong[OF eta_natural, unfolded comp_def])
      apply (rule assms)+
  apply (rule refl)
  done

lemma isVVr_permute:
  fixes f1::"'var::var \<Rightarrow> 'var" and f2::"'tyvar::var \<Rightarrow> 'tyvar"
  assumes f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "isVVr (permute_FTerm f1 f2 x) = isVVr x"
  apply (unfold isVVr_def)
  apply (rule iffI)
   apply (erule exE)
   apply (drule arg_cong[of _ _ "permute_FTerm (inv f1) (inv f2)"])
   apply (subst (asm) FTerm.permute_comp)
           apply (rule assms bij_imp_bij_inv supp_inv_bound)+
   apply (subst (asm) inv_o_simp1, rule assms)+
   apply (unfold FTerm.permute_id)
   apply hypsubst_thin
   apply (subst permute_VVr)
       apply (rule assms bij_imp_bij_inv supp_inv_bound)+
   apply (rule exI)
   apply (rule refl)
  apply (erule exE)
  apply hypsubst_thin
  apply (subst permute_VVr)
      apply (rule assms bij_imp_bij_inv supp_inv_bound)+
  apply (rule exI)
  apply (rule refl)
  done

lemma compSS_id0s:
  "compSS_FType id = id"
  "compSS_FTerm id id = id"
  apply (unfold compSS_FType_def compSS_FTerm_def FTerm.permute_id0 FType.permute_id0 id_o o_id inv_id)
  apply (unfold id_def)
  apply (rule refl)+
  done

lemma compSS_comp0_FTerm:
  fixes f1 g1::"'tyvar::var \<Rightarrow> 'tyvar" and f2 g2::"'var::var \<Rightarrow> 'var"
  assumes g_prems: "bij g1" "|supp g1| <o cmin |UNIV::'tyvar set| |UNIV::'var set|" "bij g2" "|supp g2| <o cmin |UNIV::'tyvar set| |UNIV::'var set|"
    and f_prems: "bij f1" "|supp f1| <o cmin |UNIV::'tyvar set| |UNIV::'var set|" "bij f2" "|supp f2| <o cmin |UNIV::'tyvar set| |UNIV::'var set|"
  shows
    "compSS_FTerm f1 f2 \<circ> compSS_FTerm g1 g2 = compSS_FTerm (f1 \<circ> g1) (f2 \<circ> g2)"
  apply (unfold compSS_FTerm_def)
  apply (subst o_inv_distrib FTerm.permute_comp0[symmetric], (rule supp_id_bound bij_id assms ordLess_ordLeq_trans cmin2 cmin1 card_of_Card_order)+)+
  apply (rule ext)
  apply (rule trans[OF comp_apply])
  apply (unfold comp_assoc)
  apply (rule refl)
  done
lemmas compSS_comp0s = FType.compSS_comp0[unfolded tvcompSS_tvsubst_FType_def compSS_FType_def[symmetric]] compSS_comp0_FTerm

lemma IImsupp_VVrs: "f2 a \<noteq> a \<Longrightarrow> imsupp f2 \<inter> IImsupp_FTerm2 y = {} \<Longrightarrow> y a = VVr a"
  apply (unfold imsupp_def supp_def IImsupp_FTerm2_def SSupp_FTerm_def)
  apply (drule iffD1[OF disjoint_iff])
  apply (erule allE)
  apply (erule impE)
   apply (rule UnI1)
   apply (erule iffD2[OF mem_Collect_eq])
  apply (unfold Un_iff de_Morgan_disj mem_Collect_eq not_not)
  apply (erule conjE)
  apply assumption
  done

lemma IImsupp_permute_commute:
  fixes f1::"'var::var \<Rightarrow> 'var" and f2::"'tyvar::var \<Rightarrow> 'tyvar"
  assumes f_prems: "bij f1" "|supp f1| <o |UNIV::'var set|" "bij f2" "|supp f2| <o |UNIV::'tyvar set|"
  shows "imsupp f1 \<inter> IImsupp_FTerm1 y = {} \<Longrightarrow> imsupp f2 \<inter> IImsupp_FTerm2 y = {} \<Longrightarrow> permute_FTerm f1 f2 \<circ> y = y \<circ> f2"
  apply (rule ext)
  apply (unfold comp_def)
  subgoal for a
    apply (rule case_split[of "f2 a = a"])
     apply (rule case_split[of "y a = VVr a"])
      apply (rule trans)
       apply (rule arg_cong[of _ _ "permute_FTerm f1 f2"])
       apply assumption
      apply (rule trans)
       apply (rule permute_VVr)
          apply (rule assms)+
      apply (rule trans)
       apply (rule arg_cong[of _ _ VVr])
       apply assumption
      apply (rule sym)
      apply (rotate_tac -2)
      apply (erule subst[OF sym])
      apply assumption

     apply (rule trans)
      apply (rule FTerm.permute_cong_id)
           apply (rule assms)+
      (* REPEAT_DETERM *)
       apply (erule id_onD[rotated])
       apply (rule imsupp_id_on)
       apply (erule Int_subset_empty2)
       apply (unfold IImsupp_FTerm1_def SSupp_FTerm_def)[1]
       apply (rule subsetI)
       apply (rule UnI2)?
       apply (rule UN_I[rotated])
        apply assumption
       apply (rule imageI)
       apply (rule CollectI)
       apply assumption
      (* repeated *)
      (* REPEAT_DETERM *)
      apply (erule id_onD[rotated])
      apply (rule imsupp_id_on)
      apply (erule Int_subset_empty2)
      apply (unfold IImsupp_FTerm2_def SSupp_FTerm_def)[1]
      apply (rule subsetI)
      apply (rule UnI2)?
      apply (rule UN_I[rotated])
       apply assumption
      apply (rule imageI)
      apply (rule CollectI)
      apply assumption
      (* END REPEAT_DETERM *)
     apply (rotate_tac -2)
     apply (erule subst[OF sym])
     apply (rule refl)

    apply (rule trans)
     apply (rule arg_cong[of _ _ "permute_FTerm f1 f2"])
     defer
     apply (rule trans)
      prefer 3
      apply (erule IImsupp_VVrs)
      apply assumption
     apply (rule permute_VVr)
        apply (rule f_prems)+
    apply (rule sym)
    apply (rule IImsupp_VVrs)
     apply (erule bij_not_eq_twice[rotated])
     apply (rule f_prems)
    apply assumption
    done
  done

lemma compSS_cong_id_FTerm:
  fixes f1 g1::"'tyvar::var \<Rightarrow> 'tyvar" and f2 g2::"'var::var \<Rightarrow> 'var"
  assumes g_prems: "bij g1" "|supp g1| <o cmin |UNIV::'tyvar set| |UNIV::'var set|" "bij g2" "|supp g2| <o cmin |UNIV::'tyvar set| |UNIV::'var set|"
    and f_prems: "bij f1" "|supp f1| <o cmin |UNIV::'tyvar set| |UNIV::'var set|" "bij f2" "|supp f2| <o cmin |UNIV::'tyvar set| |UNIV::'var set|"
  shows
    "(\<And>a. a \<in> IImsupp_FTerm1 h \<Longrightarrow> f1 a = a) \<Longrightarrow> (\<And>a. a \<in> IImsupp_FTerm2 h \<Longrightarrow> f2 a = a) \<Longrightarrow> compSS_FTerm f1 f2 h = h"
  apply (unfold compSS_FTerm_def)
  subgoal premises prems
    apply (subst IImsupp_permute_commute)
          apply (rule assms cmin1 cmin2 card_of_Card_order ordLess_ordLeq_trans)+
    (* REPEAT_DETERM *)
      apply (rule trans[OF Int_commute])
      apply (rule disjointI)
      apply (drule prems)
      apply (erule bij_id_imsupp[rotated])
      apply (rule assms)
    (* repeated *)
      apply (rule trans[OF Int_commute])
      apply (rule disjointI)
      apply (drule prems)
      apply (erule bij_id_imsupp[rotated])
      apply (rule assms)
    (* END REPEAT_DETERM *)
    apply (unfold comp_assoc)
    apply (subst inv_o_simp2)
     apply (rule assms)
    apply (rule o_id)
    done
  done
lemmas compSS_cong_ids = FType.compSS_cong_id[unfolded tvcompSS_tvsubst_FType_def compSS_FType_def[symmetric]] compSS_cong_id_FTerm

lemma SSupp_natural_FTerm:
  fixes f1::"'tyvar::var \<Rightarrow> 'tyvar" and f2::"'var::var \<Rightarrow> 'var"
  assumes f_prems: "bij f1" "|supp f1| <o |UNIV::'tyvar set|" "bij f2" "|supp f2| <o |UNIV::'var set|"
  shows
    "SSupp_FTerm (permute_FTerm f1 f2 \<circ> y \<circ> inv f2) = f2 ` SSupp_FTerm y"
  apply (unfold SSupp_FTerm_def)
  apply (rule set_eqI)
  apply (rule iffI)
   apply (unfold mem_Collect_eq comp_def VVr_def image_Collect)
   apply (erule contrapos_np)
   apply (drule Meson.not_exD)
   apply (erule allE)
   apply (drule iffD1[OF de_Morgan_conj])
   apply (erule disjE)
    apply (subst (asm) inv_simp2[of f2])
     apply (rule assms)
    apply (erule notE)
    apply (rule refl)
   apply (drule notnotD)
   apply (drule sym)
   apply (erule subst)
   apply (rule trans)
    apply (rule FTerm.permute_ctor)
       apply (rule assms)+
   apply (subst fun_cong[OF eta_natural, unfolded comp_def])
       apply (rule assms)+
   apply (subst inv_simp2[of f2])
    apply (rule f_prems)
   apply (rule refl)
  apply (erule exE)
  apply (erule conjE)
  apply hypsubst
  apply (subst inv_simp1)
   apply (rule f_prems)
  apply (erule contrapos_nn)
  apply (drule arg_cong[of _ _ "permute_FTerm (inv f1) (inv f2)"])
  apply (subst (asm) FTerm.permute_comp)
          apply (rule assms supp_inv_bound bij_imp_bij_inv)+
  apply (subst (asm) inv_o_simp1, rule assms)+
  apply (unfold FTerm.permute_id)
  apply (erule trans)
  apply (rule trans)
   apply (rule FTerm.permute_ctor)
      apply (rule assms supp_inv_bound bij_imp_bij_inv)+
  apply (subst fun_cong[OF eta_natural, unfolded comp_def])
      apply (rule assms supp_inv_bound bij_imp_bij_inv)+
  apply (subst inv_simp1)
   apply (rule assms)
  apply (rule refl)
  done
lemmas SSupp_naturals = FType.SSupp_natural SSupp_natural_FTerm

lemma IImsupp_natural_FTerm:
  fixes f1::"'tyvar::var \<Rightarrow> 'tyvar" and f2::"'var::var \<Rightarrow> 'var"
  assumes f_prems: "bij f1" "|supp f1| <o |UNIV::'tyvar set|" "bij f2" "|supp f2| <o |UNIV::'var set|"
  shows
    "IImsupp_FTerm1 (permute_FTerm f1 f2 \<circ> y \<circ> inv f2) = f1 ` IImsupp_FTerm1 y"
    "IImsupp_FTerm2 (permute_FTerm f1 f2 \<circ> y \<circ> inv f2) = f2 ` IImsupp_FTerm2 y"
   apply (unfold IImsupp_FTerm1_def IImsupp_FTerm2_def image_UN image_Un)
   apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])?
   apply (subst SSupp_naturals)
       apply (rule assms)+
   apply (unfold image_comp comp_assoc)[1]
   apply (subst inv_o_simp1, rule assms)
   apply (unfold o_id)
   apply (unfold comp_def)[1]
   apply (subst FTerm.FVars_permute, (rule assms)+)
   apply (rule refl)
    (* repeated *)
  apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])?
   apply (subst SSupp_naturals)
       apply (rule assms)+
   apply (rule refl)
    (* repeated *)
  apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])?
  apply (subst SSupp_naturals)
      apply (rule assms)+
  apply (unfold image_comp comp_assoc)[1]
  apply (subst inv_o_simp1, rule assms)
  apply (unfold o_id)
  apply (unfold comp_def)[1]
  apply (subst FTerm.FVars_permute, (rule assms)+)
  apply (rule refl)
  done
lemmas IImsupp_naturals = FType.IImsupp_natural IImsupp_natural_FTerm

(* Recursor axioms *)
lemma Pmap_id0: "Pmap id id = id"
  apply (rule ext)
  apply (unfold Pmap_def case_prod_beta compSS_id0s)
  apply (unfold id_def prod.collapse)
  apply (rule refl)
  done

lemma Pmap_comp0:
  fixes f1 g1::"'tyvar::var \<Rightarrow> 'tyvar" and f2 g2::"'var::var \<Rightarrow> 'var"
  assumes g_prems: "bij g1" "|supp g1| <o cmin |UNIV::'tyvar set| |UNIV::'var set|" "bij g2" "|supp g2| <o cmin |UNIV::'tyvar set| |UNIV::'var set|"
    and f_prems: "bij f1" "|supp f1| <o cmin |UNIV::'tyvar set| |UNIV::'var set|" "bij f2" "|supp f2| <o cmin |UNIV::'tyvar set| |UNIV::'var set|"
  shows
    "Pmap f1 f2 \<circ> Pmap g1 g2 = Pmap (f1 \<circ> g1) (f2 \<circ> g2)"
  apply (rule ext)
  apply (unfold Pmap_def case_prod_beta)
  apply (rule trans[OF comp_apply])
  apply (unfold prod.inject fst_conv snd_conv)
  apply (rule conjI bij_id supp_id_bound assms ordLess_ordLeq_trans cmin1 card_of_Card_order
      trans[OF comp_apply[symmetric] fun_cong[OF compSS_comp0s(1)]]
      trans[OF comp_apply[symmetric] fun_cong[OF compSS_comp0s(2)]]
      )+
  done

lemma valid_Pmap:
  fixes f1::"'tyvar::var \<Rightarrow> 'tyvar" and f2::"'var::var \<Rightarrow> 'var"
  assumes f_prems: "bij f1" "|supp f1| <o cmin |UNIV::'tyvar set| |UNIV::'var set|" "bij f2" "|supp f2| <o cmin |UNIV::'tyvar set| |UNIV::'var set|"
  shows "valid_P p \<Longrightarrow> valid_P (Pmap f1 f2 p)"
  apply (unfold valid_P_def Pmap_def case_prod_beta compSS_defs fst_conv snd_conv)
  apply (erule conj_forward)+
   apply (subst SSupp_naturals; (assumption | rule assms cmin1 cmin2 card_of_Card_order ordLeq_ordLess_trans[OF card_of_image] ordLess_ordLeq_trans)+)+
  done

lemma PFVars_Pmaps:
  fixes f1::"'tyvar::var \<Rightarrow> 'tyvar" and f2::"'var::var \<Rightarrow> 'var"
  assumes f_prems: "bij f1" "|supp f1| <o cmin |UNIV::'tyvar set| |UNIV::'var set|" "bij f2" "|supp f2| <o cmin |UNIV::'tyvar set| |UNIV::'var set|"
  shows "PFVars_1 (Pmap f1 f2 p) = f1 ` PFVars_1 p"
    "PFVars_2 (Pmap f1 f2 p) = f2 ` PFVars_2 p"
  subgoal
    apply (unfold PFVars_1_def Pmap_def case_prod_beta fst_conv snd_conv compSS_defs)
    apply (subst IImsupp_naturals, (rule assms cmin1 cmin2 card_of_Card_order ordLess_ordLeq_trans)+)+
    apply (unfold image_Un)?
    apply (rule refl)
    done
  subgoal
    apply (unfold PFVars_2_def Pmap_def case_prod_beta fst_conv snd_conv compSS_defs)
    apply (subst IImsupp_naturals, (rule assms cmin1 cmin2 card_of_Card_order ordLess_ordLeq_trans)+)+
    apply (unfold image_Un)?
    apply (rule refl)
    done
  done

lemma Pmap_cong_id:
  fixes f1::"'tyvar::var \<Rightarrow> 'tyvar" and f2::"'var::var \<Rightarrow> 'var"
  assumes f_prems: "bij f1" "|supp f1| <o cmin |UNIV::'tyvar set| |UNIV::'var set|" "bij f2" "|supp f2| <o cmin |UNIV::'tyvar set| |UNIV::'var set|"
  shows "(\<And>a. a \<in> PFVars_1 p \<Longrightarrow> f1 a = a) \<Longrightarrow> (\<And>a. a \<in> PFVars_2 p \<Longrightarrow> f2 a = a) \<Longrightarrow> Pmap f1 f2 p = p"
  apply (unfold PFVars_1_def PFVars_2_def Pmap_def case_prod_beta)
  subgoal premises prems
    apply (subst compSS_cong_ids, (rule f_prems prems cmin1 cmin2 card_of_Card_order ordLess_ordLeq_trans | erule UnI2 UnI1 | rule UnI1)+)+
    apply assumption
    apply (unfold prod.collapse)
    apply (rule refl)
    done
  done

lemmas Cinfinite_UNIV = conjI[OF FTerm_pre.UNIV_cinfinite card_of_Card_order]
lemmas Cinfinite_card = cmin_Cinfinite[OF Cinfinite_UNIV Cinfinite_UNIV]
lemmas regularCard_card = cmin_regularCard[OF FTerm_pre.var_regular FTerm_pre.var_regular Cinfinite_UNIV Cinfinite_UNIV]
lemmas Un_bound = regularCard_Un[OF conjunct2[OF Cinfinite_card] conjunct1[OF Cinfinite_card] regularCard_card]
lemmas UN_bound = regularCard_UNION[OF conjunct2[OF Cinfinite_card] conjunct1[OF Cinfinite_card] regularCard_card]

lemma small_PFVarss:
  "valid_P p \<Longrightarrow> |PFVars_1 (p::('tyvar::var, 'var::var) P)| <o cmin |UNIV::'tyvar set| |UNIV::'var set|"
  "valid_P p \<Longrightarrow> |PFVars_2 p| <o cmin |UNIV::'tyvar set| |UNIV::'var set|"
  subgoal
    apply (unfold PFVars_1_def case_prod_beta IImsupp_FTerm1_def IImsupp_FTerm2_def IImsupp_FType_def comp_def valid_P_def)
    apply (erule conjE)+
        apply (assumption | rule Un_bound UN_bound ordLeq_ordLess_trans[OF card_of_image] FType.set_bd_UNIV FTerm.FVars_bd_UNIVs cmin_greater card_of_Card_order)+
    done
  (* copied from above *)
  subgoal
    apply (unfold PFVars_2_def case_prod_beta IImsupp_FTerm1_def IImsupp_FTerm2_def IImsupp_FType_def comp_def valid_P_def)
    apply (erule conjE)+
        apply (assumption | rule Un_bound UN_bound ordLeq_ordLess_trans[OF card_of_image] FType.set_bd_UNIV FTerm.FVars_bd_UNIVs cmin_greater card_of_Card_order)+
    done
  done

lemma FTVars_subset: "valid_P p \<Longrightarrow> set3_FTerm_pre y \<inter> PFVars_1 p = {} \<Longrightarrow>
  (\<And>t pu p. valid_P p \<Longrightarrow> (t, pu) \<in> set5_FTerm_pre y \<union> set6_FTerm_pre y \<Longrightarrow> FTVars (pu p) \<subseteq> FTVars t \<union> PFVars_1 p) \<Longrightarrow>
  FTVars (Uctor y p) \<subseteq> FTVars (FTerm_ctor (map_FTerm_pre id id id id fst fst y)) \<union> PFVars_1 p"
  subgoal premises prems
    apply (unfold Uctor_def case_prod_beta)
    apply (rule case_split)
     apply (subst if_P)
      apply assumption
     apply (unfold isVVr_def)[1]
     apply (erule exE)
     apply (drule sym)
    apply (erule subst)
     apply (unfold asVVr_VVr)
     apply (rule case_split[of "_ = _"])
      apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<subseteq>)"]])
       apply (rule arg_cong[of _ _ FTVars])
       apply assumption
      apply (rule Un_upper1)
     apply (rule subsetI)
     apply (rule UnI2)
     apply (unfold PFVars_1_def case_prod_beta IImsupp_FTerm1_def SSupp_FTerm_def image_comp[unfolded comp_def])[1]
     apply (rule UnI1)
     apply (rule UN_I)
      apply (rule CollectI)
      apply assumption
     apply assumption
    apply (unfold if_not_P)
    apply (erule thin_rl)

    apply (subgoal_tac "|{ a. id a \<noteq> id a }| <o |UNIV::'v set|")
     prefer 2
      apply (rule card_of_subset_bound[OF _ emp_bound])
      apply (rule subset_emptyI)
      apply (drule CollectD)
      apply (rotate_tac -1)
      apply (erule contrapos_np)
     apply (rule refl)
    apply (subgoal_tac "|{ a. snd p a \<noteq> TyVar a }| <o |UNIV::'tv set|")
     prefer 2
     apply (insert prems(1))[1]
     apply (unfold valid_P_def case_prod_beta SSupp_FType_def tvVVr_tvsubst_FType_def tv\<eta>_FType_tvsubst_FType_def TyVar_def[symmetric] comp_def)[1]
     apply (erule conjE)
     apply (erule ordLess_ordLeq_trans)
     apply (rule cmin1)
    apply (rule card_of_Card_order)+

     apply (tactic \<open>EqSubst.eqsubst_tac @{context} [0] [Map_Sb'] 1\<close>)
       apply assumption
    apply assumption
    apply (unfold FTerm.FVars_ctor)
    apply (subst FTerm_pre.set_map, (rule bij_id supp_id_bound)+)+
    apply (unfold image_id image_comp comp_def prod.collapse)
    apply (rule Un_mono')+
      apply (unfold set3_Sb set4_Sb set1_Vrs set2_Vrs)
      apply (tactic \<open>EqSubst.eqsubst_tac @{context} [0] Vrs_Sb 1\<close>)
        apply assumption+
      apply (unfold PFVars_1_def case_prod_beta IImsupp_FType_def SSupp_FType_def
        tvVVr_tvsubst_FType_def tv\<eta>_FType_tvsubst_FType_def TyVar_def[symmetric] comp_def
      )[1]
      apply (rule subsetI)
      apply (erule UN_E)
    apply (rule case_split[of "_ = _", rotated])
      apply (rule UnI2)+
       apply (rule UN_I)
        apply (rule CollectI)
        apply assumption
       apply assumption
      apply (rule UnI1)
      apply (rotate_tac -2)
      apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
       apply (erule arg_cong)
      apply (tactic \<open>Local_Defs.unfold0_tac @{context} Vrs_Injs\<close>)
      apply (drule singletonD)
      apply hypsubst
      apply assumption

    apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
      apply (rule Diff_Un_disjunct)
      apply (rule prems)
     apply (rule Diff_mono[OF _ subset_refl])
     apply (unfold UN_extend_simps(2))
    (* REPEAT_DETERM *)
     apply (rule subset_If)
      apply (tactic \<open>Local_Defs.unfold0_tac @{context} (#Supp_Sb param)\<close>)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
      apply (rule prems)
     apply (unfold prod.collapse)
     apply (erule UnI2 UnI1)
    (* repeated *)
     apply (rule subset_If)
      apply (tactic \<open>Local_Defs.unfold0_tac @{context} (#Supp_Sb param)\<close>)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
      apply (rule prems)
     apply (unfold prod.collapse)
     apply (erule UnI2 UnI1)
    (* END REPEAT_DETERM *)
    done
  done

lemma FVars_subset: "valid_P p \<Longrightarrow> set4_FTerm_pre y \<inter> PFVars_2 p = {} \<Longrightarrow>
  (\<And>t pu p. valid_P p \<Longrightarrow> (t, pu) \<in> set5_FTerm_pre y \<union> set6_FTerm_pre y \<Longrightarrow> FVars (pu p) \<subseteq> FVars t \<union> PFVars_2 p) \<Longrightarrow>
  FVars (Uctor y p) \<subseteq> FVars (FTerm_ctor (map_FTerm_pre id id id id fst fst y)) \<union> PFVars_2 p"
  subgoal premises prems
    apply (unfold Uctor_def case_prod_beta)
    apply (rule case_split)
     apply (subst if_P)
      apply assumption
     apply (unfold isVVr_def)[1]
     apply (erule exE)
     apply (drule sym)
    apply (erule subst)
     apply (unfold asVVr_VVr)
     apply (rule case_split[of "_ = _"])
      apply (rule iffD2[OF arg_cong2[OF _ refl, of _ _ "(\<subseteq>)"]])
       apply (rule arg_cong[of _ _ FVars])
       apply assumption
      apply (rule Un_upper1)
     apply (rule subsetI)
     apply (rule UnI2)
     apply (unfold PFVars_2_def case_prod_beta IImsupp_FTerm2_def SSupp_FTerm_def image_comp[unfolded comp_def])[1]
    apply (rule UnI2)
     apply (rule UN_I)
      apply (rule CollectI)
      apply assumption
     apply assumption
    apply (unfold if_not_P)
    apply (erule thin_rl)

    apply (subgoal_tac "|{ a. id a \<noteq> id a }| <o |UNIV::'v set|")
     prefer 2
      apply (rule card_of_subset_bound[OF _ emp_bound])
      apply (rule subset_emptyI)
      apply (drule CollectD)
      apply (rotate_tac -1)
      apply (erule contrapos_np)
     apply (rule refl)
    apply (subgoal_tac "|{ a. snd p a \<noteq> TyVar a }| <o |UNIV::'tv set|")
     prefer 2
     apply (insert prems(1))[1]
     apply (unfold valid_P_def case_prod_beta SSupp_FType_def tvVVr_tvsubst_FType_def tv\<eta>_FType_tvsubst_FType_def TyVar_def[symmetric] comp_def)[1]
     apply (erule conjE)
     apply (erule ordLess_ordLeq_trans)
     apply (rule cmin1)
    apply (rule card_of_Card_order)+

     apply (tactic \<open>EqSubst.eqsubst_tac @{context} [0] [Map_Sb'] 1\<close>)
       apply assumption
    apply assumption
    apply (unfold FTerm.FVars_ctor)
    apply (subst FTerm_pre.set_map, (rule bij_id supp_id_bound)+)+
    apply (unfold image_id image_comp comp_def prod.collapse)
    apply (rule Un_mono')+
      apply (unfold set3_Sb set4_Sb set1_Vrs set2_Vrs)
      apply (tactic \<open>EqSubst.eqsubst_tac @{context} [0] Vrs_Sb 1\<close>)
        apply assumption+
      apply (unfold PFVars_2_def case_prod_beta IImsupp_FTerm2_def SSupp_FType_def
        tvVVr_tvsubst_FType_def tv\<eta>_FType_tvsubst_FType_def TyVar_def[symmetric] comp_def
      )[1]
      apply (rule subsetI)
      apply (erule UN_E)
    apply (rule UnI1)
      apply (tactic \<open>Local_Defs.unfold0_tac @{context} Vrs_Injs\<close>)
      apply (drule singletonD)
      apply hypsubst
      apply assumption

    apply (rule iffD2[OF arg_cong2[OF refl, of _ _ "(\<subseteq>)"]])
      apply (rule Diff_Un_disjunct)
      apply (rule prems)
     apply (rule Diff_mono[OF _ subset_refl])
     apply (unfold UN_extend_simps(2))
    (* REPEAT_DETERM *)
     apply (rule subset_If)
      apply (tactic \<open>Local_Defs.unfold0_tac @{context} (#Supp_Sb param)\<close>)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
      apply (rule prems)
     apply (unfold prod.collapse)
     apply (erule UnI2 UnI1)
    (* repeated *)
     apply (rule subset_If)
      apply (tactic \<open>Local_Defs.unfold0_tac @{context} (#Supp_Sb param)\<close>)
      apply (unfold UN_empty')[1]
      apply (rule empty_subsetI)
     apply (rule UN_mono[OF subset_refl])
     apply (rule prems)
      apply (rule prems)
     apply (unfold prod.collapse)
     apply (erule UnI2 UnI1)
    (* END REPEAT_DETERM *)
    done
  done

lemma permute_Uctor:
  fixes f1::"'tv::var \<Rightarrow> 'tv" and f2::"'v::var \<Rightarrow> 'v"
  shows "valid_P p \<Longrightarrow> bij f1 \<Longrightarrow> |supp f1| <o cmin |UNIV::'tv set| |UNIV::'v set| \<Longrightarrow> bij f2 \<Longrightarrow> |supp f2| <o cmin |UNIV::'tv set| |UNIV::'v set|
  \<Longrightarrow> permute_FTerm f1 f2 (Uctor y p) = Uctor (map_FTerm_pre f1 f2 f1 f2
    (\<lambda>(t, pu). (permute_FTerm f1 f2 t, \<lambda>p. if valid_P p then permute_FTerm f1 f2 (pu (Pmap (inv f1) (inv f2) p)) else undefined))
    (\<lambda>(t, pu). (permute_FTerm f1 f2 t, \<lambda>p. if valid_P p then permute_FTerm f1 f2 (pu (Pmap (inv f1) (inv f2) p)) else undefined))
  y) (Pmap f1 f2 p)"
  apply (unfold Uctor_def)
  apply (subst FTerm_pre.map_comp, (assumption | rule supp_id_bound bij_id ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
  apply (unfold id_o_commute[of f1] id_o_commute[of f2] fst_o_f comp_assoc comp_def[of snd] snd_conv case_prod_beta prod.collapse)
  apply (subst FTerm_pre.map_comp[symmetric], (assumption | rule supp_id_bound bij_id ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
  apply (subst FTerm.permute_ctor[symmetric] isVVr_permute, (assumption | rule ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+

  apply (rule case_split)
   apply (subst if_P)
    apply assumption
   apply (unfold if_P if_not_P)
   apply (unfold isVVr_def)[1]
   apply (erule exE)
   apply (erule subst[OF sym])
   apply (subst permute_VVr)
       apply (assumption | rule ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+
   apply (unfold Pmap_def case_prod_beta fst_conv snd_conv asVVr_VVr compSS_FTerm_def comp_def)[1]
   apply (subst inv_simp1)
    apply assumption
   apply (rule refl)

  apply (rule trans)
   apply (rule FTerm.permute_ctor)
      apply (assumption | rule ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+

  apply (subgoal_tac "|{ a. id a \<noteq> id a }| <o |UNIV::'v set|")
   prefer 2
   apply (rule card_of_subset_bound[OF _ emp_bound])
   apply (rule subset_emptyI)
   apply (drule CollectD)
   apply (rotate_tac -1)
   apply (erule contrapos_np)
   apply (rule refl)
  apply (subgoal_tac "|{ a. snd p a \<noteq> TyVar a }| <o |UNIV::'tv set|")
   prefer 2
   apply (unfold valid_P_def case_prod_beta SSupp_FType_def tvVVr_tvsubst_FType_def tv\<eta>_FType_tvsubst_FType_def TyVar_def[symmetric] comp_def)[1]
   apply (erule conjE)
   apply (erule ordLess_ordLeq_trans)
   apply (rule cmin1)
    apply (rule card_of_Card_order)+

     apply (tactic \<open>EqSubst.eqsubst_tac @{context} [0] [Map_Sb'] 1\<close>)
       apply assumption
   apply assumption

  apply (subst FTerm_pre.map_comp, (assumption | rule supp_id_bound bij_id ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+)+
  apply (unfold id_o o_id)
  apply (unfold comp_def)
  apply (subst if_P inv_o_simp1 trans[OF comp_apply[symmetric] Pmap_comp0[THEN fun_cong]], (rule valid_Pmap bij_imp_bij_inv supp_inv_bound | assumption)+)+
  apply (unfold trans[OF Pmap_id0[THEN fun_cong] id_apply])
  apply (unfold Pmap_def case_prod_beta snd_conv compSS_FType_def)
  apply (subst trans[OF comp_apply[symmetric] Map_Sb'[THEN fun_cong]])
      apply (assumption | rule ordLess_ordLeq_trans cmin1 cmin2 card_of_Card_order)+
  apply (unfold id_o o_id inv_o_simp2)
  apply (unfold comp_def)
  apply (rule refl)
  done

ML \<open>
val nvars: int = 2

val parameters = {
  P = @{typ "('tv::var, 'v::var) P"},
  Pmap = @{term "Pmap :: _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('tv::var, 'v::var) P"},
  PFVarss = [
    @{term "PFVars_1 :: ('tv::var, 'v::var) P \<Rightarrow> _"},
    @{term "PFVars_2 :: ('tv::var, 'v::var) P \<Rightarrow> _"}
  ],
  avoiding_sets = [@{term "{} :: 'tv::var set"}, @{term "{} :: 'v::var set"}],
  min_bound = true,
  validity = SOME {
    pred = @{term "valid_P :: ('tv::var, 'v::var) P \<Rightarrow> _"},
    valid_Pmap = fn ctxt => HEADGOAL (resolve_tac ctxt @{thms valid_Pmap} THEN_ALL_NEW assume_tac ctxt)
  },
  axioms = {
    Pmap_id0 = fn ctxt => EVERY1 [
      resolve_tac ctxt [trans],
      resolve_tac ctxt @{thms fun_cong[OF Pmap_id0]},
      resolve_tac ctxt @{thms id_apply}
    ],
    Pmap_comp0 = fn ctxt => resolve_tac ctxt @{thms fun_cong[OF Pmap_comp0[symmetric]]} 1 THEN REPEAT_DETERM (assume_tac ctxt 1),
    Pmap_cong_id = fn ctxt => resolve_tac ctxt @{thms Pmap_cong_id} 1 THEN REPEAT_DETERM (assume_tac ctxt 1 ORELSE Goal.assume_rule_tac ctxt 1),
    PFVars_Pmaps = replicate nvars (fn ctxt => resolve_tac ctxt @{thms PFVars_Pmaps} 1 THEN REPEAT_DETERM (assume_tac ctxt 1)),
    small_PFVarss = replicate nvars (fn ctxt => resolve_tac ctxt @{thms small_PFVarss} 1 THEN assume_tac ctxt 1),
    small_avoiding_sets = replicate nvars (fn ctxt => HEADGOAL (resolve_tac ctxt @{thms cmin_greater}
      THEN_ALL_NEW resolve_tac ctxt @{thms card_of_Card_order emp_bound}))
  }
} : (Proof.context -> tactic) MRBNF_Recursor.parameter;
\<close>

ML \<open>
val fp_res = the (MRBNF_FP_Def_Sugar.fp_result_of @{context} "BMV_Fixpoint.FTerm")
val quot = hd (#quotient_fps fp_res);
val vars = map TVar (rev (Term.add_tvarsT (#T quot) []));
\<close>

ML \<open>
val model = MRBNF_Recursor.mk_quotient_model quot (vars ~~ [@{typ "'tv::var"}, @{typ "'v::var"}]) {
  binding = @{binding "tvsubst_FTerm"},
  Uctor = @{term "Uctor :: _ \<Rightarrow> ('tv::var, 'v::var) P \<Rightarrow> _"},
  validity = NONE,
  axioms = {
    FVars_subsets = [
      fn ctxt => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms Un_empty_right}),
        resolve_tac ctxt @{thms FTVars_subset},
        REPEAT_DETERM o assume_tac ctxt,
        Goal.assume_rule_tac ctxt
      ],
      fn ctxt => EVERY1 [
        K (Local_Defs.unfold0_tac ctxt @{thms Un_empty_right}),
        resolve_tac ctxt @{thms FVars_subset},
        REPEAT_DETERM o assume_tac ctxt,
        Goal.assume_rule_tac ctxt
      ]
    ],
    permute_Uctor = fn ctxt => HEADGOAL (resolve_tac ctxt @{thms permute_Uctor} THEN_ALL_NEW assume_tac ctxt)
  }
}
\<close>

local_setup \<open>fn lthy =>
let
  val qualify = I
  val (ress, lthy) = MRBNF_Recursor.create_binding_recursor qualify fp_res parameters [model] lthy

  val notes =
    [ ("rec_Uctor", map (Local_Defs.unfold0 lthy @{thms Un_empty_right} o #rec_Uctor) ress)
    ] |> (map (fn (thmN, thms) =>
      ((Binding.qualify true "FTerm" (Binding.name thmN), []), [(thms, [])])
    ));
  val (_, lthy) = Local_Theory.notes notes lthy
  val _ = @{print} ress
in lthy end
\<close>
print_theorems

definition tvsubst_FTerm :: "('v \<Rightarrow> ('tv::var, 'v::var) FTerm) \<Rightarrow> ('tv \<Rightarrow> 'tv FType) \<Rightarrow> ('tv, 'v) FTerm \<Rightarrow> ('tv, 'v) FTerm" where
  "tvsubst_FTerm f1 f2 t \<equiv> ff0_tvsubst_FTerm t (f1, f2)"

type_synonym ('tv, 'v) U1_pre = "('tv, 'v, 'tv, 'v, ('tv, 'v) FTerm, ('tv, 'v) FTerm) FTerm_pre"

lemmas eta_natural' = fun_cong[OF eta_natural, unfolded comp_def]

lemma eta_set_empties:
  fixes a::"'v::var"
  shows
    "set1_FTerm_pre (\<eta> a :: ('tv::var, 'v) U1_pre) = {}"
    "set3_FTerm_pre (\<eta> a :: ('tv::var, 'v) U1_pre) = {}"
    "set4_FTerm_pre (\<eta> a :: ('tv::var, 'v) U1_pre) = {}"
    "set5_FTerm_pre (\<eta> a :: ('tv::var, 'v) U1_pre) = {}"
    "set6_FTerm_pre (\<eta> a :: ('tv::var, 'v) U1_pre) = {}"
      apply -
  subgoal
    apply (rule set_eqI)
    apply (unfold empty_iff)
    apply (rule iffI)
     apply (rule exE[OF exists_fresh, of "set1_FTerm_pre (\<eta> a)"])
      apply (rule FTerm_pre.set_bd_UNIV)
     apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
      apply (rule arg_cong[of _ _ set1_FTerm_pre])
      prefer 2
      apply (subst (asm) FTerm_pre.set_map)
            prefer 7
            apply (erule swap_fresh)
            apply assumption
           apply (rule supp_id_bound bij_id supp_swap_bound bij_swap infinite_UNIV)+
     apply (rule sym)
     apply (rule trans)
      apply (rule fun_cong[OF eta_natural, unfolded comp_def])
           apply (rule supp_id_bound bij_id supp_swap_bound bij_swap infinite_UNIV)+
     apply (unfold id_def)
     apply (rule refl)
    apply (erule FalseE)
    done
  subgoal
    apply (rule set_eqI)
    apply (unfold empty_iff)
    apply (rule iffI)
     apply (rule exE[OF exists_fresh, of "set3_FTerm_pre (\<eta> a)"])
      apply (rule FTerm_pre.set_bd_UNIV)
     apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
      apply (rule arg_cong[of _ _ set3_FTerm_pre])
      prefer 2
      apply (subst (asm) FTerm_pre.set_map)
            prefer 7
            apply (erule swap_fresh)
            apply assumption
           apply (rule supp_id_bound bij_id supp_swap_bound bij_swap infinite_UNIV)+
     apply (rule sym)
     apply (rule trans)
      apply (rule fun_cong[OF eta_natural, unfolded comp_def])
           apply (rule supp_id_bound bij_id supp_swap_bound bij_swap infinite_UNIV)+
     apply (unfold id_def)
     apply (rule refl)
    apply (erule FalseE)
    done
  subgoal
    apply (rule set_eqI)
    apply (unfold empty_iff)
    apply (rule iffI)
     apply (rule exE[OF exists_fresh, of "set4_FTerm_pre (\<eta> a)"])
      apply (rule FTerm_pre.set_bd_UNIV)
     apply (drule iffD1[OF arg_cong2[OF refl, of _ _ "(\<in>)"], rotated])
      apply (rule arg_cong[of _ _ set4_FTerm_pre])
      prefer 2
      apply (subst (asm) FTerm_pre.set_map)
            prefer 7
            apply (erule swap_fresh)
            apply assumption
           apply (rule supp_id_bound bij_id supp_swap_bound bij_swap infinite_UNIV)+
     apply (rule sym)
     apply (rule trans)
      apply (rule eta_natural')
           apply (rule supp_id_bound bij_id supp_swap_bound bij_swap infinite_UNIV)+
     apply (unfold id_def)
     apply (rule refl)
    apply (erule FalseE)
    done
  subgoal
    apply (rule set_eqI)
    apply (unfold empty_iff)
    apply (rule iffI)
     apply (drule image_const)
     apply (drule iffD1[OF all_cong1, rotated])
      apply (rule sym)
      apply (rule arg_cong2[OF refl, of _ _ "(\<in>)"])
      apply (rule FTerm_pre.set_map)
           apply (rule supp_id_bound bij_id)+
     apply (subst (asm) eta_natural')
         apply (rule supp_id_bound bij_id)+
     apply (unfold id_def)
     apply (drule forall_in_eq_UNIV)
     apply (drule trans[symmetric])
      apply (rule conjunct1[OF card_order_on_Card_order, OF FTerm_pre.bd_card_order])
     apply (drule card_of_ordIso_subst)
     apply (drule ordIso_symmetric)
     apply (drule ordIso_transitive)
      apply (rule ordIso_symmetric)
      apply (rule iffD1[OF Card_order_iff_ordIso_card_of])
      apply (rule conjunct2[OF card_order_on_Card_order, OF FTerm_pre.bd_card_order])
     apply (erule ordIso_ordLess_False)
     apply (rule FTerm_pre.set_bd)
    apply (erule FalseE)
    done
  subgoal
    apply (rule set_eqI)
    apply (unfold empty_iff)
    apply (rule iffI)
     apply (drule image_const)
     apply (drule iffD1[OF all_cong1, rotated])
      apply (rule sym)
      apply (rule arg_cong2[OF refl, of _ _ "(\<in>)"])
      apply (rule FTerm_pre.set_map)
           apply (rule supp_id_bound bij_id)+
     apply (subst (asm) eta_natural')
         apply (rule supp_id_bound bij_id)+
     apply (unfold id_def)
     apply (drule forall_in_eq_UNIV)
     apply (drule trans[symmetric])
      apply (rule conjunct1[OF card_order_on_Card_order, OF FTerm_pre.bd_card_order])
     apply (drule card_of_ordIso_subst)
     apply (drule ordIso_symmetric)
     apply (drule ordIso_transitive)
      apply (rule ordIso_symmetric)
      apply (rule iffD1[OF Card_order_iff_ordIso_card_of])
      apply (rule conjunct2[OF card_order_on_Card_order, OF FTerm_pre.bd_card_order])
     apply (erule ordIso_ordLess_False)
     apply (rule FTerm_pre.set_bd)
    apply (erule FalseE)
    done
  done

lemma tvsubst_VVr:
  assumes    
    "|SSupp_FTerm f1| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    "|SSupp_FType f2| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows "tvsubst_FTerm f1 f2 (VVr a :: ('tv::var, 'v::var) FTerm) = f1 a"
  apply (unfold tvsubst_FTerm_def VVr_def comp_def)
  apply (rule trans)
   apply (rule FTerm.rec_Uctor)
      apply (unfold valid_P_def prod.case)
      apply (rule conjI assms)+
     apply (unfold eta_set_empties noclash_FTerm_def Uctor_def Un_empty prod.case)
     apply (rule Int_empty_left conjI)+
  apply (subst FTerm_pre.map_comp, (rule supp_id_bound bij_id)+)+
  apply (unfold id_o o_id comp_def[of fst] fst_conv id_def[symmetric] FTerm_pre.map_id)
  apply (rule trans)
   apply (rule if_P)
   apply (unfold isVVr_def VVr_def comp_def )
   apply (rule exI)
   apply (rule refl)
  apply (unfold meta_eq_to_obj_eq[OF VVr_def, THEN fun_cong, unfolded comp_def, symmetric] asVVr_VVr)
  apply (rule refl)
  done

lemma tvsubst_FTerm_no_is_VVr:
  fixes x::"('tv::var, 'v::var) U1_pre"
  assumes f_prems: "|SSupp_FTerm f1| <o cmin |UNIV::'tv set| |UNIV::'v set|" "|SSupp_FType f2| <o cmin |UNIV::'tv set| |UNIV::'v set|"
    and empty_prems: "set3_FTerm_pre x \<inter> (IImsupp_FTerm1 f1 \<union> IImsupp_FType f2) = {}" "set4_FTerm_pre x \<inter> IImsupp_FTerm2 f1 = {}"
    and noclash: "noclash_FTerm x"
    and VVr_prems: "\<not>isVVr (FTerm_ctor x)"
  shows
    "tvsubst_FTerm f1 f2 (FTerm_ctor x) = FTerm_ctor (Sb_FTerm_pre id f2 (map_FTerm_pre id id id id (tvsubst_FTerm f1 f2) (tvsubst_FTerm f1 f2) x))"
  apply (unfold tvsubst_FTerm_def)
  apply (subgoal_tac "valid_P (f1, f2)")
   prefer 2
   apply (unfold valid_P_def prod.case)[1]
   apply (rule conjI f_prems)+
  apply (rule trans)
   apply (rule FTerm.rec_Uctor)
      apply assumption
     apply (unfold PFVars_1_def PFVars_2_def prod.case)
     apply (rule empty_prems noclash)+
  apply (unfold Uctor_def prod.case)
  apply (subst FTerm_pre.map_comp, (rule supp_id_bound bij_id)+)+
  apply (unfold id_o o_id comp_def[of fst] fst_conv id_def[symmetric] FTerm_pre.map_id)
  apply (subst if_not_P, rule VVr_prems)+
  apply (unfold comp_def snd_conv if_P)
  apply (rule refl)
  done

(* Sugar theorems for substitution *)
definition Var :: "'v \<Rightarrow> ('tv::var, 'v::var) FTerm" where
  "Var a \<equiv> FTerm_ctor (Abs_FTerm_pre (Inl a))"
definition App :: "('tv, 'v) FTerm \<Rightarrow> ('tv, 'v) FTerm \<Rightarrow> ('tv::var, 'v::var) FTerm" where
  "App t1 t2 \<equiv> FTerm_ctor (Abs_FTerm_pre (Inr (Inl (t1, t2))))"
definition TyApp :: "('tv, 'v) FTerm \<Rightarrow> 'tv FType \<Rightarrow> ('tv::var, 'v::var) FTerm" where
  "TyApp t T \<equiv> FTerm_ctor (Abs_FTerm_pre (Inr (Inr (Inl (t, T)))))"
definition Lam :: "'v \<Rightarrow> 'tv FType \<Rightarrow> ('tv, 'v) FTerm \<Rightarrow> ('tv::var, 'v::var) FTerm" where
  "Lam x T t \<equiv> FTerm_ctor (Abs_FTerm_pre (Inr (Inr (Inr (Inl (x, T, t))))))"
definition TyLam :: "'tv \<Rightarrow> ('tv, 'v) FTerm \<Rightarrow> ('tv::var, 'v::var) FTerm" where
  "TyLam a t \<equiv> FTerm_ctor (Abs_FTerm_pre (Inr (Inr (Inr (Inr (a, t))))))"

lemma FTerm_subst:
  fixes f1::"'v \<Rightarrow> ('tv::var, 'v::var) FTerm" and f2::"'tv \<Rightarrow> 'tv FType"
  assumes "|SSupp_FTerm f1| <o cmin |UNIV::'tv set| |UNIV::'v set|" "|SSupp_FType f2| <o cmin |UNIV::'tv set| |UNIV::'v set|"
  shows
    "tvsubst_FTerm f1 f2 (Var x) = f1 x"
    "tvsubst_FTerm f1 f2 (App t1 t2) = App (tvsubst_FTerm f1 f2 t1) (tvsubst_FTerm f1 f2 t2)"
    "tvsubst_FTerm f1 f2 (TyApp t T) = TyApp (tvsubst_FTerm f1 f2 t) (tvsubst_FType f2 T)"
    "x \<notin> IImsupp_FTerm2 f1 \<Longrightarrow> tvsubst_FTerm f1 f2 (Lam x T t) = Lam x (tvsubst_FType f2 T) (tvsubst_FTerm f1 f2 t)"
    "a \<notin> IImsupp_FTerm1 f1 \<union> IImsupp_FType f2 \<Longrightarrow> tvsubst_FTerm f1 f2 (TyLam a t) = TyLam a (tvsubst_FTerm f1 f2 t)"
      apply (unfold Var_def App_def TyApp_def Lam_def TyLam_def)
      apply (unfold meta_eq_to_obj_eq[OF VVr_def, THEN fun_cong, unfolded comp_def, symmetric])
      apply (rule tvsubst_VVr)
       apply (rule assms)+

     apply (rule trans)
      apply (rule tvsubst_FTerm_no_is_VVr)
           apply (rule assms)+
         apply (unfold set3_FTerm_pre_def sum.set_map prod.set_map UN_empty2 Un_empty_left Un_empty_right UN_singleton comp_def
      Abs_FTerm_pre_inverse[OF UNIV_I] sum_set_simps UN_single UN_empty set4_FTerm_pre_def noclash_FTerm_def
      )
         apply (rule Int_empty_left conjI)+
      apply (unfold isVVr_def VVr_def comp_def FTerm.TT_inject0)[1]
      apply (rule notI)
      apply (erule exE conjE)+
      apply (unfold map_FTerm_pre_def comp_def Abs_FTerm_pre_inverse[OF UNIV_I] map_sum.simps prod.map_id
      Abs_FTerm_pre_inject[OF UNIV_I UNIV_I]
      )[1]
      apply (rotate_tac -1)
      apply (erule contrapos_pp)
      apply (rule sum.distinct)
     apply (unfold map_FTerm_pre_def comp_def Abs_FTerm_pre_inverse[OF UNIV_I] map_sum.simps prod.map_id
      Abs_FTerm_pre_inject[OF UNIV_I UNIV_I] Sb_FTerm_pre_def id_def map_prod_simp
      )[1]
     apply (rule refl)

    apply (rule trans)
     apply (rule tvsubst_FTerm_no_is_VVr)
          apply (rule assms)+
        apply (unfold set3_FTerm_pre_def sum.set_map prod.set_map UN_empty2 Un_empty_left Un_empty_right UN_singleton comp_def
      Abs_FTerm_pre_inverse[OF UNIV_I] sum_set_simps UN_single UN_empty set4_FTerm_pre_def noclash_FTerm_def
      )
        apply (rule Int_empty_left conjI)+
     apply (unfold isVVr_def VVr_def comp_def FTerm.TT_inject0)[1]
     apply (rule notI)
     apply (erule exE conjE)+
     apply (unfold map_FTerm_pre_def comp_def Abs_FTerm_pre_inverse[OF UNIV_I] map_sum.simps prod.map_id
      Abs_FTerm_pre_inject[OF UNIV_I UNIV_I]
      )[1]
     apply (rotate_tac -1)
     apply (erule contrapos_pp)
     apply (rule sum.distinct)
    apply (unfold map_FTerm_pre_def comp_def Abs_FTerm_pre_inverse[OF UNIV_I] map_sum.simps prod.map_id
      Abs_FTerm_pre_inject[OF UNIV_I UNIV_I] Sb_FTerm_pre_def id_def map_prod_simp bmv_defs
      )[1]
    apply (unfold id_def[symmetric] FType.map_id)
    apply (rule refl)

   apply (rule trans)
    apply (rule tvsubst_FTerm_no_is_VVr)
         apply (rule assms)+
       apply (unfold set2_FTerm_pre_def set6_FTerm_pre_def set3_FTerm_pre_def sum.set_map prod.set_map UN_empty2 Un_empty_left Un_empty_right UN_singleton comp_def
      Abs_FTerm_pre_inverse[OF UNIV_I] sum_set_simps UN_single UN_empty set4_FTerm_pre_def noclash_FTerm_def prod_set_simps
      )
       apply (rule Int_empty_left Int_empty_right conjI iffD2[OF disjoint_single] | assumption)+
    apply (unfold isVVr_def VVr_def comp_def FTerm.TT_inject0)[1]
    apply (rule notI)
    apply (erule exE conjE)+
    apply (unfold map_FTerm_pre_def comp_def Abs_FTerm_pre_inverse[OF UNIV_I] map_sum.simps prod.map_id
      Abs_FTerm_pre_inject[OF UNIV_I UNIV_I]
      )[1]
    apply (rotate_tac -1)
    apply (erule contrapos_pp)
    apply (rule sum.distinct)
   apply (unfold map_FTerm_pre_def comp_def Abs_FTerm_pre_inverse[OF UNIV_I] map_sum.simps prod.map_id
      Abs_FTerm_pre_inject[OF UNIV_I UNIV_I] Sb_FTerm_pre_def id_def map_prod_simp bmv_defs
      )[1]
   apply (unfold id_def[symmetric] FType.map_id)
   apply (rule refl)

  apply (rule trans)
   apply (rule tvsubst_FTerm_no_is_VVr)
        apply (rule assms)+
      apply (unfold set2_FTerm_pre_def set6_FTerm_pre_def set3_FTerm_pre_def sum.set_map prod.set_map UN_empty2 Un_empty_left Un_empty_right UN_singleton comp_def
      Abs_FTerm_pre_inverse[OF UNIV_I] sum_set_simps UN_single UN_empty set4_FTerm_pre_def noclash_FTerm_def prod_set_simps
      set1_FTerm_pre_def
      )
      apply (rule Int_empty_left Int_empty_right conjI iffD2[OF disjoint_single] | assumption)+
   apply (unfold isVVr_def VVr_def comp_def FTerm.TT_inject0)[1]
   apply (rule notI)
   apply (erule exE conjE)+
   apply (unfold map_FTerm_pre_def comp_def Abs_FTerm_pre_inverse[OF UNIV_I] map_sum.simps prod.map_id
      Abs_FTerm_pre_inject[OF UNIV_I UNIV_I]
      )[1]
   apply (rotate_tac -1)
   apply (erule contrapos_pp)
   apply (rule sum.distinct)
  apply (unfold map_FTerm_pre_def comp_def Abs_FTerm_pre_inverse[OF UNIV_I] map_sum.simps prod.map_id
      Abs_FTerm_pre_inject[OF UNIV_I UNIV_I] Sb_FTerm_pre_def id_def map_prod_simp bmv_defs
      )[1]
  apply (rule refl)
  done


end