theory Expression_Like_Strong
  imports Expression_Like
begin

locale Expression_with_Surj_and_Coinduct = Expression +
  assumes (* AtoD: I added the "no-clash condition: GVrs2 u \<inter> GVrs1 u = {} *)
  Ector_fresh_surj: "\<And>A e. |A::'a set| <o |UNIV :: 'a::var set| \<Longrightarrow> 
    \<exists>u. GVrs2 u \<inter> A = {} \<and> e = Ector u" and
  E_coinduct: "\<And>P (g :: 'e \<Rightarrow> 'e) h e. (\<And>e. P e \<Longrightarrow> g e = h e \<or>
       (\<exists>u. g e = Ector (Gmap g g u) \<and> h e = Ector (Gmap h h u) \<and>
         (\<forall>e \<in> GSupp1 u. P e) \<and> (\<forall>e \<in> GSupp2 u. P e))) \<Longrightarrow>
         P e \<Longrightarrow> g e = h e"
begin

(* this is generaly true for the top-free variables: *)
lemma Ector_eq_GVrs1: "Ector u = Ector u' \<Longrightarrow> GVrs1 u = GVrs1 u'"
by (metis Ector_inject G.Vrs_Map1 G.Vrs_Sb(1) Gren_def supp_id_bound)

(* Shifting to the version with no-clash, taking advantage 
of the above lemma: *)
lemma Ector_fresh_surj': 
assumes "|A::'a set| <o |UNIV :: 'a::var set|" 
shows "\<exists>u. GVrs2 u \<inter> GVrs1 u = {} \<and> GVrs2 u \<inter> A = {} \<and> e = Ector u" 
proof-
  obtain v where e: "e = Ector v"  
  using Ector_fresh_surj assms by blast
  have 0: "|A \<union> GVrs1 v| <o |UNIV :: 'a::var set|"   
  using assms 
  by (metis EVrs_Ector EVrs_bound card_of_Un1 infinite_class.Un_bound 
           ordLeq_ordLess_trans)
  show ?thesis 
  using Ector_fresh_surj[OF 0, of e]  
  using Ector_eq_GVrs1 e by blast
qed

end (* context Expression_with_Surj_and_Coinduct *)

end