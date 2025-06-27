theory Comodels
  imports "Expressions"
begin(* *)
 
definition dtorNeC :: "('E' \<Rightarrow> (('E','E')G) set + E) \<Rightarrow> bool" where 
"dtorNeC dtor \<equiv> \<forall>e U. dtor e = Inl U \<longrightarrow> U \<noteq> {}"

definition dtorPermC :: "('E' \<Rightarrow> (('E','E')G) set + E) \<Rightarrow> ((var \<Rightarrow> var) \<Rightarrow> 'E' \<Rightarrow> 'E') \<Rightarrow> bool" 
where "dtorPermC dtor perm \<equiv> 
\<forall>\<sigma> e. small \<sigma> \<and> bij \<sigma> \<longrightarrow> 
  (\<forall> U. dtor e = Inl U \<longrightarrow> (\<exists>U'. dtor (perm \<sigma> e) = Inl U' \<and> U' \<subseteq> Gren \<sigma> \<sigma> ` (Gmap (perm \<sigma>) (perm \<sigma>) ` U)))
  \<and> 
  (\<forall>e1. dtor e = Inr e1 \<longrightarrow> (\<exists>e1'. dtor (perm \<sigma> e) = Inr e1' \<and> e1' =  Eperm \<sigma> e1))"

definition dtorVrsGrenC :: "('E' \<Rightarrow> (('E','E')G) set + E) \<Rightarrow> ('E' \<Rightarrow> var set) \<Rightarrow> bool" 
where
"dtorVrsGrenC dtor Vrs \<equiv> 
 (\<forall>e U u1 u2. dtor e = Inl U \<and> {u1,u2} \<subseteq> U \<longrightarrow> 
   (\<exists>\<sigma>. small \<sigma> \<and> bij \<sigma> \<and> 
        supp \<sigma> \<subseteq> GVrs1 u1 \<union> 
                 (\<Union> {Vrs e | e . e \<in> GSupp1 u1}) \<union> 
                 (\<Union> {Vrs e - GVrs2 u1 | e . e \<in> GSupp1 u1}) \<and> 
        u2 = Gren id \<sigma> u1))"

definition dtorVrsC :: "('E' \<Rightarrow> (('E','E')G) set + E) \<Rightarrow> ('E' \<Rightarrow> var set) \<Rightarrow> bool" 
where
"dtorVrsC dtor Vrs \<equiv> 
 (\<forall>e.  
  (\<forall>U. dtor e = Inl U \<longrightarrow> 
       (\<forall>u\<in>U. GVrs1 u \<union> 
              (\<Union> {Vrs e | e . e \<in> GSupp1 u}) \<union> 
              (\<Union> {Vrs e - GVrs2 u | e . e \<in> GSupp1 u}) 
              \<subseteq> 
              Vrs e)) 
  \<and>  
  (\<forall>e1. dtor e = Inr e1 \<longrightarrow> EVrs e1 \<subseteq> Vrs e)
)"

(* Full-recursion comodel:   *)
locale Comodel =
fixes (* no set V, as we need no Barendregt convention here *)
Edtor' :: "'E' \<Rightarrow> (('E','E')G) set + E" 
and Eperm' :: "(var \<Rightarrow> var) \<Rightarrow> 'E' \<Rightarrow> 'E'" 
and EVrs' :: "'E' \<Rightarrow> var set" 
assumes 
nom: "nom Eperm' EVrs'" 
and  
dtorNeC: "dtorNeC Edtor'"
and 
dtorPermC: "dtorPermC Edtor' Eperm'"
and 
dtorVrsGrenC: "dtorVrsGrenC Edtor' EVrs'"
and 
dtorVrsC: "dtorVrsC Edtor' EVrs'"
begin 


definition corec :: "'E' \<Rightarrow> E" where 
"corec = undefined"

lemma corec_Edtor_Inl:
"Edtor' e = Inl U \<Longrightarrow> Gmap corec corec ` U  \<subseteq> Edtor (corec e)"
sorry

lemma corec_Edtor_Inr:
"Edtor' e = Inr e1 \<Longrightarrow> corec e = e1"
sorry

lemma corec_Eperm:
"small \<sigma> \<Longrightarrow> bij \<sigma> \<Longrightarrow> supp \<sigma> \<inter> V = {} \<Longrightarrow> 
 corec (Eperm' \<sigma> e') = Eperm \<sigma> (corec e')"
sorry

lemma corec_EVrs:
"EVrs (corec e') \<subseteq> EVrs' e'"
sorry

lemma corec_unique: 
assumes "\<And> e U. Edtor' e = Inl U \<Longrightarrow> Gmap H H ` U  \<subseteq> Edtor (corec e)"
and "\<And>e e1. Edtor' e = Inr e1 \<Longrightarrow> H e = e1"
shows "H = corec"
sorry

end (* locale Comodel *)



end