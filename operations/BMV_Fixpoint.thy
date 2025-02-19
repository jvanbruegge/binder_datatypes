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
      FVars = replicate 2 NONE,
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
    val lthy = BMV_Monad_Def.register_pbmv_monad "FTerm_pre'" bmv lthy;

    val notes = [
      ("bmv_defs", thms)
    ] |> (map (fn (thmN, thms) =>
      ((Binding.name thmN, []), [(thms, [])])
    ));

    val (noted, lthy) = Local_Theory.notes notes lthy

    val _ = @{print} bmv
  in lthy end\<close>

ML \<open>
val bmv = the (BMV_Monad_Def.pbmv_monad_of @{context} "FTerm_pre'")
val axioms = BMV_Monad_Def.axioms_of_bmv_monad bmv;
val laxioms = nth axioms (BMV_Monad_Def.leader_of_bmv_monad bmv)
\<close>

lemma comp_assoc_middle: "(\<And>x. f2 (f1 x) = x) \<Longrightarrow> f1 \<circ> g1 \<circ> f2 \<circ> (f1 \<circ> g2 \<circ> f2) = f1 \<circ> (g1 \<circ> g2) \<circ> f2"
  by auto
lemma typedef_Rep_comp: "type_definition Rep Abs UNIV \<Longrightarrow> Rep ((Abs \<circ> f \<circ> Rep) x) = f (Rep x)"
  unfolding comp_def type_definition.Abs_inverse[OF _ UNIV_I] ..

(* Transfer pbmv structure of pre-datatype to sealed version *)
pbmv_monad "('tv::var, 'v::var, 'btv::var, 'bv::var, 'c, 'd) FTerm_pre" and "'v::var" and "'tv::var FType"
  Sbs: "\<lambda>(f1::'v::var \<Rightarrow> 'v) (f2::'tv::var \<Rightarrow> 'tv FType). (Abs_FTerm_pre :: _ \<Rightarrow> ('tv, 'v, 'btv::var, 'bv::var, 'c, 'd) FTerm_pre) \<circ> (map_sum (id f1) (map_sum id (BMV_Fixpoint.sum2.sum2.sum.Sb_0 f2) \<circ> id) \<circ> id) \<circ> Rep_FTerm_pre" and "id :: ('v \<Rightarrow> 'v) \<Rightarrow> 'v \<Rightarrow> 'v" and "tvsubst_FType :: ('tv::var \<Rightarrow> 'tv FType) \<Rightarrow> 'tv FType \<Rightarrow> 'tv FType"
  Injs: "id :: 'v::var \<Rightarrow> 'v" "TyVar :: 'tv::var \<Rightarrow> 'tv FType" and "id :: 'v::var \<Rightarrow> 'v" and "TyVar :: 'tv::var \<Rightarrow> 'tv FType"
  Vrs: "\<lambda>x. \<Union>x\<in>Basic_BNFs.setl (Rep_FTerm_pre x). {x}", "\<lambda>x. \<Union>x\<in>Basic_BNFs.setr (Rep_FTerm_pre x). \<Union> (BMV_Fixpoint.sum2.sum2.sum.Vrs_0_0_0 ` Basic_BNFs.setr x)" and "\<lambda>(x::'v). {x}" and "Vrs_FType_1 :: _ \<Rightarrow> 'tv::var set"
  Map: "\<lambda>(f1::'c \<Rightarrow> 'c') (f2::'d \<Rightarrow> 'd'). map_FTerm_pre id id id id f1 f2"
  Supps: "set5_FTerm_pre :: _ \<Rightarrow> 'c set" "set6_FTerm_pre :: _ \<Rightarrow> 'd set"
  bd: natLeq
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

end