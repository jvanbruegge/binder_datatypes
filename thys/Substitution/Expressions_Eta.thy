theory Expressions_Eta
imports Expressions_Strong Substitution_Factory
begin


context Expression begin
lemma SSupp_Eperm_comp: 
  "bij (\<sigma> :: 'a \<Rightarrow> 'a::var) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> SSupp (Ector \<circ> \<eta>) (Eperm \<sigma> \<circ> \<rho> \<circ> inv \<sigma>) \<subseteq> SSupp (Ector \<circ> \<eta>) \<rho> \<union> supp \<sigma>"
  "bij (\<sigma> :: 'a \<Rightarrow> 'a::var) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> SSupp (Ector \<circ> \<eta>') (Eperm \<sigma> \<circ> \<rho>' \<circ> inv \<sigma>) \<subseteq> SSupp (Ector \<circ> \<eta>') \<rho>' \<union> supp \<sigma>"
   apply (auto simp: SSupp_def imsupp_def image_iff)
   apply (metis Eperm_Ector Gren_def bij_imp_inv eta_natural not_in_supp_alt)
  apply (metis Eperm_Ector Gren_def bij_imp_inv eta'_natural not_in_supp_alt)
  done
end (* context Expression *) 

context Expression_with_Surj_and_Coinduct begin

lemma Ector_eta_inj: "Ector u = Ector (\<eta> a) \<longleftrightarrow> u = \<eta> a"
  by (metis Ector_inject eta_natural supp_id_bound Gren_def)

lemma Ector_eta'_inj: "Ector u = Ector (\<eta>' a) \<longleftrightarrow> u = \<eta>' a"
  unfolding Ector_inject
  apply safe
  subgoal for \<sigma>
    apply (drule arg_cong[where f = "Gsub id (inv \<sigma>) o Gmap (Eperm (inv \<sigma>)) id"])
    apply (auto simp: eta'_natural G.Map_comp[THEN fun_cong, simplified]
        G.Map_Sb[THEN fun_cong, simplified] G.Sb_comp[THEN fun_cong, simplified]
        G.Map_id G.Sb_Inj Eperm_comp Eperm_id Gren_def)
    done
  subgoal
    apply (auto simp: eta'_natural Gren_def) 
    done 
  done

lemma Ector_eta_inj': "Ector (\<eta> a) = Ector x \<longleftrightarrow> x = \<eta> a"
  using Ector_eta_inj by metis

lemma Ector_eta'_inj': "Ector (\<eta>' a) = Ector x \<longleftrightarrow> x = \<eta>' a"
  using Ector_eta'_inj by metis

end (* context Expression_with_Surj_and_Coinduct *)

end