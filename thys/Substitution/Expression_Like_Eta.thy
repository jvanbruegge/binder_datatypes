theory Expression_Like_Eta
imports Expression_Like_Strong
begin

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

context Expression begin

lemma eta_inject: "\<eta> a = \<eta> a' \<longleftrightarrow> a = a'"
  using eta_inj by metis
lemma eta'_inject: "\<eta>' a = \<eta>' a' \<longleftrightarrow> a = a'"
  using eta'_inj by metis

lemma eta_distinct': "\<eta>' a \<noteq> \<eta> a'"
  using eta_distinct[of a' a] by metis

lemma GVrs_eta[simp]:
  "GVrs1 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = {a}"
  "GVrs2 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = {}"
proof safe
  fix b assume b: "b \<in> GVrs1 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)"
  { assume "a \<noteq> b"
    then have *: "\<eta> a = Gsub (b \<leftrightarrow> c) id (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)" if "c \<notin> {a, b}" for c
      using eta_natural[of "b \<leftrightarrow> c" id id id a, symmetric, simplified] that
      by (auto simp: G.Map_id)
    have "c \<in> GVrs1 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)" if "c \<notin> {a, b}" for c
      using that b
      apply (subst (asm) *)
       apply (simp_all add: G.Vrs_Sb)
      apply (auto simp: swap_def)
      done
    with b have "|UNIV - {a}| \<le>o |GVrs1 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)|"
      by (intro card_of_mono1) auto
    then have "|UNIV::'a1 set| \<le>o |GVrs1 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)|"
      by (meson infinite_UNIV infinite_card_of_diff_singl ordIso_ordLeq_trans ordIso_symmetric)
    then have False
      using G.Vrs_bd(1) large' not_ordLeq_ordLess
        ordLeq_ordLess_trans by blast
  }
  then show "b = a"
    by blast
next
  fix b :: 'a2 assume "b \<in> GVrs2 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)"
  then have "c \<in> GVrs2 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)" for c :: 'a2
    by (subst eta_natural[of id "b \<leftrightarrow> c" id id a, symmetric, simplified])
      (auto simp: G.Vrs_Sb  G.Map_id image_iff intro!: bexI[of _ b])
  then have "GVrs2 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = UNIV"
    by blast
  then show "b \<in> {}"
    by (metis G.Vrs_bd(2) large' exists_fresh exists_univ_eq ordLess_ordLeq_trans)
qed (rule eta_mem)

lemma GVrs_eta'[simp]:
  "GVrs1 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = {a}"
  "GVrs2 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = {}"
proof safe
  fix b assume b: "b \<in> GVrs1 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)"
  { assume "a \<noteq> b"
    then have *: "\<eta>' a = Gsub (b \<leftrightarrow> c) id (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)" if "c \<notin> {a, b}" for c
      using eta'_natural[of "b \<leftrightarrow> c" id id id a, symmetric, simplified] that
      by (auto simp: G.Map_id)
    have "c \<in> GVrs1 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)" if "c \<notin> {a, b}" for c
      using that b
      apply (subst (asm) *)
       apply (simp_all add: G.Vrs_Sb)
      apply (auto simp: swap_def)
      done
    with b have "|UNIV - {a}| \<le>o |GVrs1 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)|"
      by (intro card_of_mono1) auto
    then have "|UNIV::'a1 set| \<le>o |GVrs1 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)|"
      by (meson infinite_UNIV infinite_card_of_diff_singl ordIso_ordLeq_trans ordIso_symmetric)
    then have False
      using G.Vrs_bd(1) large' not_ordLeq_ordLess
        ordLeq_ordLess_trans by blast
  }
  then show "b = a"
    by blast
next
  fix b :: 'a2 assume "b \<in> GVrs2 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)"
  then have "c \<in> GVrs2 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)" for c :: 'a2
    by (subst eta'_natural[of id "b \<leftrightarrow> c" id id a, symmetric, simplified])
      (auto simp: G.Vrs_Sb  G.Map_id image_iff intro!: bexI[of _ b])
  then have "GVrs2 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = UNIV"
    by blast
  then show "b \<in> {}"
    by (metis G.Vrs_bd(2) large' exists_fresh exists_univ_eq ordLess_ordLeq_trans)
qed (rule eta'_mem)

lemma GSupp_eta[simp]:
  "GSupp1 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = {}"
  "GSupp2 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = {}"
proof safe
  fix b :: 'x1 assume "b \<in> GSupp1 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)"
  then have "c \<in> GSupp1 (\<eta> a :: ('a1 ::var, 'a2 :: var, Gbd_type, 'x2) G)" for c :: Gbd_type
    by (subst eta_natural[of id id "\<lambda>x. if x = b then c else (undefined :: Gbd_type)" id a, symmetric, simplified])
      (auto simp: G.Supp_Sb  G.Supp_Map image_iff intro!: bexI[of _ b])
  then have "GSupp1 (\<eta> a :: ('a1 ::var, 'a2 :: var, Gbd_type, 'x2) G) = UNIV"
    by blast
  moreover have "|UNIV :: Gbd_type set| =o Gbd"
    using card_of_unique G.infinite_regular_card_order
      infinite_regular_card_order.card_order ordIso_symmetric by blast
  ultimately show "b \<in> {}"
    by (metis G.Supp_bd(1) not_ordLess_ordIso)
next
  fix b :: 'x2 assume "b \<in> GSupp2 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)"
  then have "c \<in> GSupp2 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, Gbd_type) G)" for c :: Gbd_type
    by (subst eta_natural[of id id id "\<lambda>x. if x = b then c else (undefined :: Gbd_type)" a, symmetric, simplified])
      (auto simp: G.Supp_Sb  G.Supp_Map image_iff intro!: bexI[of _ b])
  then have "GSupp2 (\<eta> a :: ('a1 ::var, 'a2 :: var, 'x1, Gbd_type) G) = UNIV"
    by blast
  moreover have "|UNIV :: Gbd_type set| =o Gbd"
    using card_of_unique G.infinite_regular_card_order
      infinite_regular_card_order.card_order ordIso_symmetric by blast
  ultimately show "b \<in> {}"
    by (metis G.Supp_bd(2) not_ordLess_ordIso)
qed

lemma GSupp_eta'[simp]:
  "GSupp1 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = {}"
  "GSupp2 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G) = {}"
proof safe
  fix b :: 'x1 assume "b \<in> GSupp1 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)"
  then have "c \<in> GSupp1 (\<eta>' a :: ('a1 ::var, 'a2 :: var, Gbd_type, 'x2) G)" for c :: Gbd_type
    by (subst eta'_natural[of id id "\<lambda>x. if x = b then c else (undefined :: Gbd_type)" id a, symmetric, simplified])
      (auto simp: G.Supp_Sb  G.Supp_Map image_iff intro!: bexI[of _ b])
  then have "GSupp1 (\<eta>' a :: ('a1 ::var, 'a2 :: var, Gbd_type, 'x2) G) = UNIV"
    by blast
  moreover have "|UNIV :: Gbd_type set| =o Gbd"
    using card_of_unique G.infinite_regular_card_order
      infinite_regular_card_order.card_order ordIso_symmetric by blast
  ultimately show "b \<in> {}"
    by (metis G.Supp_bd(1) not_ordLess_ordIso)
next
  fix b :: 'x2 assume "b \<in> GSupp2 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, 'x2) G)"
  then have "c \<in> GSupp2 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, Gbd_type) G)" for c :: Gbd_type
    by (subst eta'_natural[of id id id "\<lambda>x. if x = b then c else (undefined :: Gbd_type)" a, symmetric, simplified])
      (auto simp: G.Supp_Sb G.Supp_Map image_iff intro!: bexI[of _ b])
  then have "GSupp2 (\<eta>' a :: ('a1 ::var, 'a2 :: var, 'x1, Gbd_type) G) = UNIV"
    by blast
  moreover have "|UNIV :: Gbd_type set| =o Gbd"
    using card_of_unique G.infinite_regular_card_order
      infinite_regular_card_order.card_order ordIso_symmetric by blast
  ultimately show "b \<in> {}"
    by (metis G.Supp_bd(2) not_ordLess_ordIso)
qed

lemma SSupp_Eperm_comp: 
  "bij (\<sigma> :: 'a \<Rightarrow> 'a::var) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> SSupp (Ector \<circ> \<eta>) (Eperm \<sigma> \<circ> \<rho> \<circ> inv \<sigma>) \<subseteq> SSupp (Ector \<circ> \<eta>) \<rho> \<union> supp \<sigma>"
  "bij (\<sigma> :: 'a \<Rightarrow> 'a::var) \<Longrightarrow> |supp \<sigma>| <o |UNIV :: 'a set| \<Longrightarrow> SSupp (Ector \<circ> \<eta>') (Eperm \<sigma> \<circ> \<rho>' \<circ> inv \<sigma>) \<subseteq> SSupp (Ector \<circ> \<eta>') \<rho>' \<union> supp \<sigma>"
   apply (auto simp: SSupp_def imsupp_def image_iff)
   apply (metis Eperm_Ector Gren_def bij_imp_inv eta_natural not_in_supp_alt)
  apply (metis Eperm_Ector Gren_def bij_imp_inv eta'_natural not_in_supp_alt)
  done

end

context Expression_Strong begin

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

end

end