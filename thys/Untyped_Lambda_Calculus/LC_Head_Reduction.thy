theory LC_Head_Reduction
imports LC2
begin

definition red where 
"red e ee \<equiv> \<exists>x e1 e2. e = App (Lam x e1) e2 \<and> ee = tvsubst (Var(x:=e2)) e1"

end