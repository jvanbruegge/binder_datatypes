theory LC_Head_Reduction
imports LC
begin

definition red where 
"red (e::trm) ee \<equiv> \<exists>x e1 e2. e = App (Lam x e1) e2 \<and> ee = tvsubst (Var(x:=e2)) e1"

lemma red_determ: 
"red e e' \<Longrightarrow> red e e'' \<Longrightarrow> e' = e''"
unfolding red_def  
by auto (meson Lam_eq_tvsubst)

end