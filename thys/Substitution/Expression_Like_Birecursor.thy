theory Expression_Like_Birecursor
  imports Expression_Like_Sub
begin

context Expression begin

(*TODO provide definition and proof *)
interpretation Substitution undefined
  apply standard
  sorry

definition Esub :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a ::var \<Rightarrow> 'a E) \<Rightarrow> ('a ::var \<Rightarrow> 'a E) \<Rightarrow> 'a E \<Rightarrow> 'a E" where
  "Esub \<delta> \<rho> \<rho>' x = undefined"

lemma
  Esub_Ector\<eta>:
  "\<And>\<delta> \<rho> \<rho>' a u.
    |supp (\<delta> :: 'a \<Rightarrow> 'a :: var)| <o |UNIV::'a set| \<Longrightarrow>
    |SSupp (Ector o \<eta>) (\<rho>::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow>
    |SSupp (Ector o \<eta>') (\<rho>'::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow>
    Esub \<delta> \<rho> \<rho>' (Ector (\<eta> a)) = \<rho> a"
  and Esub_Ector\<eta>':
  "\<And>\<delta> \<rho> \<rho>' a u.
    |supp (\<delta> :: 'a \<Rightarrow> 'a :: var)| <o |UNIV::'a set| \<Longrightarrow>
    |SSupp (Ector o \<eta>) (\<rho>::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow>
    |SSupp (Ector o \<eta>') (\<rho>'::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow>
    Esub \<delta> \<rho> \<rho>' (Ector (\<eta>' a)) = \<rho>' a"
  and Esub_Ector:
  "\<And>\<delta> \<rho> \<rho>' a u.
    |supp (\<delta> :: 'a \<Rightarrow> 'a :: var)| <o |UNIV::'a set| \<Longrightarrow>
    |SSupp (Ector o \<eta>) (\<rho>::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow>
    |SSupp (Ector o \<eta>') (\<rho>'::'a::var \<Rightarrow> 'a E)| <o |UNIV::'a set| \<Longrightarrow>
  GVrs2 u \<inter> imsupp \<delta> = {} \<Longrightarrow>
  GVrs2 u \<inter> IImsupp' (Ector o \<eta>) EVrs \<rho> = {} \<Longrightarrow>
  GVrs2 u \<inter> IImsupp' (Ector o \<eta>') EVrs \<rho>' = {} \<Longrightarrow>
  GVrs2 u \<inter> EVrs (Ector u) = {} \<Longrightarrow>
  \<forall>a. u \<noteq> \<eta> a \<Longrightarrow> \<forall>a'. u \<noteq> \<eta>' a' \<Longrightarrow>
  Esub \<delta> \<rho> \<rho>' (Ector u) = Ector (Gsub \<delta> id (Gmap (Esub \<delta> \<rho> \<rho>') (Esub \<delta> \<rho> \<rho>') u))"
  and EVrs_Esub: "\<And>\<delta> \<rho> \<rho>' e. |supp (\<delta> :: 'a \<Rightarrow> 'a :: var)| <o |UNIV::'a set| \<Longrightarrow>
    |SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV::'a set| \<Longrightarrow> |SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV::'a set| \<Longrightarrow>
    EVrs (Esub \<delta> \<rho> \<rho>' e) \<subseteq> EVrs e \<union> (imsupp \<delta> \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>')"
  and Eperm_Esub: "\<And>\<delta> \<rho> \<rho>' \<sigma> e. |supp (\<delta> :: 'a \<Rightarrow> 'a :: var)| <o |UNIV :: 'a set| \<Longrightarrow>
    |SSupp (Ector \<circ> \<eta>) \<rho>| <o |UNIV :: 'a set| \<Longrightarrow> |SSupp (Ector \<circ> \<eta>') \<rho>'| <o |UNIV :: 'a set| \<Longrightarrow>
    bij \<sigma> \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> imsupp \<sigma> \<inter> (imsupp \<delta> \<union> IImsupp' (Ector \<circ> \<eta>) EVrs \<rho> \<union> IImsupp' (Ector \<circ> \<eta>') EVrs \<rho>') = {} \<Longrightarrow>
    Eperm \<sigma> (Esub \<delta> \<rho> \<rho>' e) = Esub \<delta> \<rho> \<rho>' (Eperm \<sigma> e)"
  sorry

end