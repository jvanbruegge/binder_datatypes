theory Expressions
  imports Underlying_MN_Monad
begin

(**************************)
(* 1. Generalized Nominal Assumptions *)

locale Nominal = 
  fixes Eperm :: "('a :: var \<Rightarrow> 'a) \<Rightarrow> 'e \<Rightarrow> 'e"
  and EVrs :: "'e \<Rightarrow> 'a set"
  and Ebd :: "'bd rel"
  assumes
  Eperm_comp:
  "\<And>\<sigma> \<tau>. bij (\<sigma> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>
   bij (\<tau> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<tau>| <o |UNIV :: 'a set| \<Longrightarrow>
   Eperm \<sigma> o Eperm \<tau> = Eperm (\<sigma> o \<tau>)"
  and Eperm_cong_id:
  "\<And>\<sigma> e. bij (\<sigma> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>
   (\<And>a. a \<in> EVrs e \<Longrightarrow> \<sigma> a = a) \<Longrightarrow> Eperm \<sigma> e = e"
  (* and Eperm_Evrs: 
   "\<And>e \<sigma>. bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> 
   EVrs (Eperm \<sigma> e) = \<sigma> ` EVrs e" *)
  and Ebd_infinite_regular_card_order: "infinite_regular_card_order Ebd"
  and Ebd_le: "Ebd \<le>o |UNIV :: 'a::var set|"
  and EVrs_bd:
  "\<And>e. |EVrs (e :: 'e)| <o Ebd"
begin

lemma Eperm_id: "Eperm id = id"
  apply (rule ext)
  apply (rule trans[OF Eperm_cong_id id_apply[symmetric]])
    apply simp_all
  done

lemma Eperm_comp':
  "bij (\<sigma> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>
   bij (\<tau> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<tau>| <o |UNIV :: 'a set| \<Longrightarrow>
   Eperm (\<sigma> o \<tau>) e = Eperm \<sigma> (Eperm \<tau> e)"
by (metis Eperm_comp comp_apply)


lemma EVrs_bound[simp]: "|EVrs (x :: 'e)| <o |UNIV :: 'a set|"
  by (rule ordLess_ordLeq_trans[OF EVrs_bd Ebd_le])

end

(* Relativized nominal :*)
locale NominalRel = 
  fixes Evalid :: "'e \<Rightarrow> bool"
  and Eperm :: "('a :: var \<Rightarrow> 'a) \<Rightarrow> 'e \<Rightarrow> 'e"
  and EVrs :: "'e \<Rightarrow> 'a set"
  assumes
  Eperm_Evalid: "\<And>\<sigma> e. bij (\<sigma> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> Evalid e \<Longrightarrow> Evalid (Eperm \<sigma> e)"
  and Eperm_comp:
  "\<And>\<sigma> \<tau> e. bij (\<sigma> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>
   bij (\<tau> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<tau>| <o |UNIV :: 'a set| \<Longrightarrow>
   Evalid e \<Longrightarrow>
   Eperm \<sigma> (Eperm \<tau> e) = Eperm (\<sigma> o \<tau>) e"
  and Eperm_cong_id:
  "\<And>\<sigma> e. bij (\<sigma> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> Evalid e \<Longrightarrow>
   (\<And>a. a \<in> EVrs e \<Longrightarrow> \<sigma> a = a) \<Longrightarrow> Eperm \<sigma> e = e" 
  and Eperm_Evrs: 
   "\<And>\<sigma> e. Evalid e \<Longrightarrow> bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> 
   EVrs (Eperm \<sigma> e) = \<sigma> ` EVrs e"
  and EVrs_bd:
  "\<And>e. Evalid e \<Longrightarrow> |EVrs (e :: 'e)| <o |UNIV :: 'a::var set|"

(**************************)
(* 2. Expression-Like Entities *)

(* In addition to the nominal structure, 
expression also have a well-behaved 
(in particular quasi-injective) 
bindeing-aware constructor *)

(* Recall that our G stands G0 in the 
triple (I0,P0,G0), where  
where I0 = {1,2} and P0 = {1,2}*)

(* Below, the assumption is that, in  ('a,'a,'e,'e) G:
-- the first-component-variables (GVrs1) are top-free 
-- the second-conponent variables (GVrs2) are top-bound. 
So in the binding-spec B = (J0,Q0,\<xi>,\<theta>) where:
----- J0 = {1}
----- Q0 = P0 = {1,2} 
----- \<xi> : {1} \<rightarrow> {2}, \<xi>(1) = 2
----- \<theta> \<subseteq> J0 \<times> Q0 = {1} \<times> {1,2}, \<theta> = {(1,1)} 
(the binding happens in the first recursve component).   
*)


locale Expression = Nominal +
  fixes Ector :: "('a :: var, 'a, 'e, 'e) G \<Rightarrow> 'e"
  assumes EVrs_Eperm:
  "\<And>\<sigma> u. bij (\<sigma> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> 
   EVrs (Eperm \<sigma> u) = \<sigma> ` EVrs u"
  and Eperm_Ector:
  "\<And>\<sigma> u. bij (\<sigma> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>
    Eperm \<sigma> (Ector u) = Ector (Gren \<sigma> \<sigma> (Gmap (Eperm \<sigma>) (Eperm \<sigma>) u))"
  and EVrs_Ector:
  "\<And>u. EVrs (Ector u) =
     GVrs1 u \<union> ((\<Union>e \<in> GSupp1 u. EVrs e) - GVrs2 u) \<union> (\<Union>e \<in> GSupp2 u. EVrs e)"
  and Ector_inject: "\<And>x y. Ector x = Ector y \<longleftrightarrow>
   (\<exists>\<sigma> :: 'a :: var \<Rightarrow> 'a. bij \<sigma> \<and> |supp \<sigma>| <o |UNIV :: 'a set| \<and>
     id_on (\<Union> (EVrs ` GSupp1 x) - GVrs2 x) \<sigma> \<and> Gren id \<sigma> (Gmap (Eperm \<sigma>) id x) = y)"
begin

lemma EVrs_Eperm_su:
  "bij (\<sigma> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> 
   EVrs (Eperm \<sigma> u) \<subseteq> \<sigma> ` EVrs u"
using EVrs_Eperm by auto


lemma Eperm_cong: "bij (\<sigma> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow>
         bij (\<tau> :: 'a :: var \<Rightarrow> 'a) \<Longrightarrow> |supp \<tau>| <o |UNIV :: 'a set| \<Longrightarrow>
   (\<And>a. a \<in> EVrs e \<Longrightarrow> \<sigma> a = \<tau> a) \<Longrightarrow> Eperm \<sigma> e = Eperm \<tau> e"
  apply (rule trans[OF _ Eperm_cong_id, of _ "\<sigma> o inv \<tau>"])
     apply (auto simp: Eperm_comp[THEN fun_cong, simplified] supp_comp_bound
      dest: EVrs_Eperm_su[THEN set_mp, rotated -1] simp flip: o_assoc)
  done

lemma Ector_fresh_inject:
  assumes "GVrs2 x \<inter> A = {}" "GVrs2 y \<inter> A = {}" "|A :: 'a::var set| <o |UNIV :: 'a set|"
  shows "(Ector x = Ector y) \<longleftrightarrow> (\<exists>\<sigma>. bij \<sigma> \<and> |supp \<sigma>| <o |UNIV :: 'a set| \<and> imsupp \<sigma> \<inter> A = {}
    \<and> id_on (\<Union> (EVrs ` GSupp1 x) - GVrs2 x) \<sigma> \<and> Gren id \<sigma> (Gmap (Eperm \<sigma>) id x) = y)"
  apply (subst Ector_inject; rule iffI; (elim exE conjE)?)
  subgoal for \<sigma>
    apply (insert ex_avoiding_bij[of \<sigma> "(\<Union> (EVrs ` GSupp1 x) - GVrs2 x)" "GVrs2 x" A])
    apply (drule meta_mp; simp add: UN_bound card_of_minus_bound ordLess_ordLeq_trans[OF G.Supp_bd(1) large'] ordLess_ordLeq_trans[OF G.Vrs_bd(2) large'] assms)+
    apply (elim exE conjE)
    subgoal for \<tau>
      apply (auto simp: G.Vrs_Map Gren_def intro!: exI[of _ \<tau>] trans[OF G.Sb_cong arg_cong[where f="Gsub _ _", OF G.Map_cong]] Eperm_cong)
      using G.Vrs_Map(2) G.Vrs_Sb(2) assms(2) imageI supp_id_bound apply blast
      apply (smt (verit, ccfv_threshold) Diff_iff G.Vrs_Map(2) G.Vrs_Sb(2) UN_I assms(2) disjoint_iff_not_equal id_on_eq imageI supp_id_bound)
      done
    done
  apply blast
  done

end

end