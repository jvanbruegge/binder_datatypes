theory LC_Head_Reduction
imports LC
begin

definition red where 
"red (e::trm) ee \<equiv> \<exists>x e1 e2. e = Ap (Lm x e1) e2 \<and> ee = tvsubst (Vr(x:=e2)) e1"

lemma red_determ: 
"red e e' \<Longrightarrow> red e e'' \<Longrightarrow> e' = e''"
unfolding red_def  
by auto (meson Lm_eq_tvsubst)

end