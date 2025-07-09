theory Expression_Like_Strong
  imports Expression_Like
begin

axiomatization where
  Ector_fresh_surj: "\<And>A e. |A::'a set| <o |UNIV :: 'a::var set| \<Longrightarrow> 
    \<exists>u. GVrs2 u \<inter> A = {} \<and> e = Ector u" and
  Ector_eqI: "\<And>x y.
   (\<exists>\<sigma> :: 'a :: var \<Rightarrow> 'a. bij \<sigma> \<and> |supp \<sigma>| <o |UNIV :: 'a set| \<and>
     id_on (\<Union> (EVrs ` GSupp1 x) - GVrs2 x) \<sigma> \<and> Gren id \<sigma> (Gmap (Eperm \<sigma>) id x) = y) \<Longrightarrow> Ector x = Ector y" and
  E_coinduct: "\<And>P (g :: 'a::var E \<Rightarrow> 'a E) h e. (\<And>e. P e \<Longrightarrow> g e = h e \<or>
       (\<exists>u. g e = Ector (Gmap g g u) \<and> h e = Ector (Gmap h h u) \<and>
         (\<forall>e \<in> GSupp1 u. P e) \<and> (\<forall>e \<in> GSupp2 u. P e))) \<Longrightarrow>
         P e \<Longrightarrow> g e = h e" 
  and EVrs_bd:
  "\<And>x. |EVrs (x :: 'a :: var E)| <o Gbd"

lemma Ector_inject: "\<And>x y. (Ector x = Ector y) =
   (\<exists>\<sigma> :: 'a :: var \<Rightarrow> 'a. bij \<sigma> \<and> |supp \<sigma>| <o |UNIV :: 'a set| \<and>
     id_on (\<Union> (EVrs ` GSupp1 x) - GVrs2 x) \<sigma> \<and> Gren id \<sigma> (Gmap (Eperm \<sigma>) id x) = y)"
  using Ector_eqI Ector_eqD by metis

consts \<eta> :: "'a1 :: var \<Rightarrow> ('a1, 'a2 :: var, 'x1, 'x2) G"
consts \<eta>' :: "'a1 :: var \<Rightarrow> ('a1, 'a2 :: var, 'x1, 'x2) G"

axiomatization where
  eta_inversion: "\<And>\<delta>1 \<delta>2 f1 f2 u a. |supp \<delta>1| <o |UNIV::'a1 set| \<Longrightarrow> |supp \<delta>2| <o |UNIV::'a2 set| \<Longrightarrow>
   Gsub \<delta>1 \<delta>2 (Gmap f1 f2 u) = (\<eta> a :: ('a1::var, 'a2 :: var, 'x1, 'x2) G) \<Longrightarrow> \<exists>y. u = \<eta> y"
  and eta_natural: "\<And>\<delta>1 \<delta>2 f1 f2 a. |supp \<delta>1| <o |UNIV::'a1 set| \<Longrightarrow> |supp \<delta>2| <o |UNIV::'a2 set| \<Longrightarrow>
   Gsub \<delta>1 \<delta>2 (Gmap f1 f2 (\<eta> a :: ('a1::var, 'a2 :: var, 'x1, 'x2) G)) = \<eta> (\<delta>1 a)"
  and eta_mem: "\<And>a. a \<in> GVrs1 (\<eta> a :: ('a1::var, 'a2 :: var, 'x1, 'x2) G)"
  and eta'_inversion: "\<And>\<delta>1 \<delta>2 f1 f2 u a. |supp \<delta>1| <o |UNIV::'a1 set| \<Longrightarrow> |supp \<delta>2| <o |UNIV::'a2 set| \<Longrightarrow>
   Gsub \<delta>1 \<delta>2 (Gmap f1 f2 u) = \<eta>' a \<Longrightarrow> \<exists>y. u = \<eta>' y"
  and eta'_natural: "\<And>\<delta>1 \<delta>2 f1 f2 a. |supp \<delta>1| <o |UNIV::'a1 set| \<Longrightarrow> |supp \<delta>2| <o |UNIV::'a2 set| \<Longrightarrow>
   Gsub \<delta>1 \<delta>2 (Gmap f1 f2 (\<eta>' a :: ('a1::var, 'a2 :: var, 'x1, 'x2) G)) = \<eta>' (\<delta>1 a)"
  and eta'_mem: "\<And>a. a \<in> GVrs1 (\<eta>' a :: ('a1::var, 'a2 :: var, 'x1, 'x2) G)"
  and eta_inj: "\<And>a a'. \<eta> a = \<eta> a' \<Longrightarrow> a = a'"
  and eta'_inj: "\<And>a a'. \<eta>' a = \<eta>' a' \<Longrightarrow> a = a'"
  and eta_distinct: "\<And>a a'. \<eta> a \<noteq> \<eta>' a'"

end