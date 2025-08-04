theory Comodels
  imports "Expressions"
begin(* *)
 
definition dtorNeC :: "('E' \<Rightarrow> bool) \<Rightarrow> ('E' \<Rightarrow> 'a E + (('a::var,'a,'E','E')G) set) \<Rightarrow> bool" where 
"dtorNeC valid dtor \<equiv> \<forall>e U. valid e \<and> dtor e = Inr U \<longrightarrow> U \<noteq> {}"

definition dtorPermC :: "('E' \<Rightarrow> bool) \<Rightarrow> 
('E' \<Rightarrow> 'a E + ('a::var,'a,'E','E')G set) \<Rightarrow> 
(('a \<Rightarrow> 'a) \<Rightarrow> 'E' \<Rightarrow> 'E') \<Rightarrow> bool" 
where "dtorPermC valid dtor perm \<equiv> 
\<forall>\<sigma> e. valid e \<and> small \<sigma> \<and> bij \<sigma> \<longrightarrow>
  (\<forall>e1. dtor e = Inl e1 \<longrightarrow> dtor (perm \<sigma> e) = Inl (Eperm \<sigma> e1))
  \<and> 
  (\<forall> U. dtor e = Inr U \<longrightarrow> (\<exists>U'. dtor (perm \<sigma> e) = Inr U' \<and> U' \<subseteq> Gren \<sigma> \<sigma> ` (Gmap (perm \<sigma>) (perm \<sigma>) ` U)))"

definition dtorVrsGrenC :: "('E' \<Rightarrow> bool) \<Rightarrow> 
('E' \<Rightarrow> 'a E + ('a::var,'a,'E','E')G set) \<Rightarrow> 
(('a \<Rightarrow> 'a) \<Rightarrow> 'E' \<Rightarrow> 'E') \<Rightarrow> ('E' \<Rightarrow> 'a set) \<Rightarrow> bool" 
where
"dtorVrsGrenC valid dtor perm Vrs \<equiv> 
 (\<forall>e U u1 u2. valid e \<and> dtor e = Inr U \<and> {u1,u2} \<subseteq> U \<longrightarrow> 
   (\<exists>\<sigma>. small \<sigma> \<and> bij \<sigma> \<and> 
        id_on ((\<Union> (Vrs ` GSupp1 u1) - GVrs2 u1)) \<sigma> \<and> 
        Gren id \<sigma> (Gmap (perm \<sigma>) id u1) = u2))"

(* 
Ector_eqA: "\<And>u1 u2. Ector u1 = Ector u2 \<Longrightarrow>
   (\<exists>\<sigma> :: 'a :: var \<Rightarrow> 'a. bij \<sigma> \<and> |supp \<sigma>| <o |UNIV :: 'a set| \<and>
     id_on ((\<Union> (EVrs ` GSupp1 u1)) \<union> (\<Union> (EVrs ` GSupp1 u1) - GVrs2 u1)) \<sigma> \<and> 
     Gren id \<sigma> (Gmap (Eperm \<sigma>) (Eperm \<sigma>) u1) = u2)"
*)

definition dtorVrsC :: "('E' \<Rightarrow> bool) \<Rightarrow> 
('E' \<Rightarrow> 'a E + ('a::var,'a,'E','E')G set) \<Rightarrow> 
('E' \<Rightarrow> 'a set) \<Rightarrow> bool" 
where
"dtorVrsC valid dtor Vrs \<equiv> 
 (\<forall>e. valid e \<longrightarrow>   
  (\<forall>U. dtor e = Inr U \<longrightarrow> 
       (\<forall>u\<in>U. GVrs1 u \<union> 
              (\<Union> {Vrs e - GVrs2 u | e . e \<in> GSupp1 u}) \<union> 
              (\<Union> {Vrs e | e . e \<in> GSupp2 u})
              \<subseteq> 
              Vrs e)) 
  \<and>  
  (\<forall>e1. dtor e = Inl e1 \<longrightarrow> EVrs e1 \<subseteq> Vrs e)
)"

(* destructor preserves validity *)
definition presDV :: "('E' \<Rightarrow> bool) \<Rightarrow> 
  ('E' \<Rightarrow> 'a E + ('a::var,'a,'E','E')G set) \<Rightarrow> bool" 
where "presDV valid dtor \<equiv> 
 \<forall>e. valid e \<longrightarrow>   
     (\<forall>U u e'. dtor e = Inr U \<and> u \<in> U \<and> e' \<in> GSupp1 u \<union> GSupp2 u \<longrightarrow> valid e')"

(* permutation preserves validity *)
definition presPV :: "('E' \<Rightarrow> bool) \<Rightarrow> (('a::var \<Rightarrow> 'a) \<Rightarrow> 'E' \<Rightarrow> 'E') \<Rightarrow> bool" 
where "presPV valid perm \<equiv> 
\<forall>\<sigma> e. valid e \<and> small \<sigma> \<and> bij \<sigma> \<longrightarrow> valid (perm \<sigma> e)"

(* Full-recursion comodel:   *)
locale Comodel =
fixes (* no set V, as we need no Barendregt convention here *)
Evalid' :: "'E' \<Rightarrow> bool" and 
Edtor' :: "'E' \<Rightarrow> 'a E + ('a::var,'a,'E','E')G set" 
and Eperm' :: "('a::var \<Rightarrow> 'a) \<Rightarrow> 'E' \<Rightarrow> 'E'" 
and EVrs' :: "'E' \<Rightarrow> 'a::var set" 
assumes 
presDV_Evalid'_Edtor': "presDV Evalid' Edtor'"
and 
presPV_Evalid'_Edtor': "presPV Evalid' Eperm'"
and
nom: "nom Evalid' Eperm' EVrs'" 
and  
dtorNeC: "dtorNeC Evalid' Edtor'"
and 
dtorPermC: "dtorPermC Evalid' Edtor' Eperm'"
and 
dtorVrsGrenC: "dtorVrsGrenC Evalid' Edtor' Eperm' EVrs'"
and 
dtorVrsC: "dtorVrsC Evalid' Edtor' EVrs'"
begin 


definition corec :: "'E' \<Rightarrow> 'a E" where 
"corec = undefined"

lemma corec_Edtor_Inl:
"Evalid' e \<Longrightarrow> Edtor' e = Inr U \<Longrightarrow> Gmap corec corec ` U  \<subseteq> Edtor (corec e)"
sorry

lemma corec_Edtor_Inr:
"Evalid' e \<Longrightarrow> Edtor' e = Inl e1 \<Longrightarrow> corec e = e1"
sorry

lemma corec_Eperm:
"Evalid' e \<Longrightarrow> small \<sigma> \<Longrightarrow> bij \<sigma> \<Longrightarrow>   
 corec (Eperm' \<sigma> e) = Eperm \<sigma> (corec e)"
sorry


lemma corec_EVrs:
"Evalid' e \<Longrightarrow> EVrs (corec e) \<subseteq> EVrs' e"
sorry

lemma corec_unique: 
assumes "\<And> e U. Evalid' e \<Longrightarrow> Edtor' e = Inr U \<Longrightarrow> Gmap H H ` U  \<subseteq> Edtor (H e)"
and "\<And>e e1. Evalid' e \<Longrightarrow> Edtor' e = Inl e1 \<Longrightarrow> H e = e1"
shows "\<And>e. Evalid' e \<Longrightarrow> H e = corec e"
sorry

end (* locale Comodel *)



end