theory Expression_Like_Strong
  imports Expression_Like
begin

locale Expression_Strong = Expression +
  fixes Ebd :: "'bd rel"
  assumes
  Ector_fresh_surj: "\<And>A e. |A::'a set| <o |UNIV :: 'a::var set| \<Longrightarrow> 
    \<exists>u. GVrs2 u \<inter> A = {} \<and> e = Ector u" and
  Ector_eqI: "\<And>x y.
   (\<exists>\<sigma> :: 'a :: var \<Rightarrow> 'a. bij \<sigma> \<and> |supp \<sigma>| <o |UNIV :: 'a set| \<and>
     id_on (\<Union> (EVrs ` GSupp1 x) - GVrs2 x) \<sigma> \<and> Gren id \<sigma> (Gmap (Eperm \<sigma>) id x) = y) \<Longrightarrow> Ector x = Ector y" and
  E_coinduct: "\<And>P (g :: 'e \<Rightarrow> 'e) h e. (\<And>e. P e \<Longrightarrow> g e = h e \<or>
       (\<exists>u. g e = Ector (Gmap g g u) \<and> h e = Ector (Gmap h h u) \<and>
         (\<forall>e \<in> GSupp1 u. P e) \<and> (\<forall>e \<in> GSupp2 u. P e))) \<Longrightarrow>
         P e \<Longrightarrow> g e = h e"
  and Ebd_infinite_regular_card_order: "infinite_regular_card_order Ebd"
  and Ebd_le: "Ebd \<le>o |UNIV :: 'a::var set|"
  and EVrs_bd:
  "\<And>x. |EVrs (x :: 'e)| <o Ebd"
begin

lemma Ector_inject: "\<And>x y. (Ector x = Ector y) =
   (\<exists>\<sigma> :: 'a :: var \<Rightarrow> 'a. bij \<sigma> \<and> |supp \<sigma>| <o |UNIV :: 'a set| \<and>
     id_on (\<Union> (EVrs ` GSupp1 x) - GVrs2 x) \<sigma> \<and> Gren id \<sigma> (Gmap (Eperm \<sigma>) id x) = y)"
  using Ector_eqI Ector_eqD by metis

lemma EVrs_bound[simp]: "|EVrs (x :: 'e)| <o |UNIV :: 'a set|"
  by (rule ordLess_ordLeq_trans[OF EVrs_bd Ebd_le])

lemma GVrs2_bound[simp]: "|GVrs2 (u::('a :: var, 'a, 'e, 'e) G)| <o |UNIV :: 'a set|"
  by (rule ordLess_ordLeq_trans[OF G.Vrs_bd(2) large'])

lemma Ector_fresh_inject:
  assumes "GVrs2 x \<inter> A = {}" "GVrs2 y \<inter> A = {}" "|A :: 'a::var set| <o |UNIV :: 'a set|"
  shows "(Ector x = Ector y) = (\<exists>\<sigma>. bij \<sigma> \<and> |supp \<sigma>| <o |UNIV :: 'a set| \<and> imsupp \<sigma> \<inter> A = {}
    \<and> id_on (\<Union> (EVrs ` GSupp1 x) - GVrs2 x) \<sigma> \<and> Gren id \<sigma> (Gmap (Eperm \<sigma>) id x) = y)"
  using Ector_fresh_eqD[OF assms EVrs_bound]
  by (auto simp: Ector_inject)

end

end