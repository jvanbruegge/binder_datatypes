theory Curry_LFP imports Main
begin

(* Currying-uncurrying infrastructure *)

(* 2-ARY *)

definition uncurry2 :: "('a1 \<Rightarrow> 'a2 \<Rightarrow> bool) \<Rightarrow> 'a1 \<times> 'a2 \<Rightarrow> bool" where 
"uncurry2 q \<equiv> \<lambda>(x1,x2). q x1 x2"
definition curry2 :: "('a1 \<times> 'a2 \<Rightarrow> bool) \<Rightarrow> 'a1 \<Rightarrow> 'a2 \<Rightarrow> bool" where 
"curry2 r \<equiv> \<lambda> x1 x2. r (x1,x2)"

lemma curry2_uncurry2[simp]: "curry2 (uncurry2 q) = q"
unfolding uncurry2_def curry2_def by auto

lemma uncurry2_o_curry2[simp]: "uncurry2 o curry2 = id"
unfolding uncurry2_def curry2_def by auto

lemma uncurry2_curry2[simp]: "uncurry2 (curry2 q) = q"
unfolding uncurry2_def curry2_def by auto

lemma uncurry2_mono: "q \<le> q' \<Longrightarrow> uncurry2 q \<le> uncurry2 q'"
unfolding uncurry2_def le_fun_def by auto

lemma curry2_mono: "r \<le> r' \<Longrightarrow> curry2 r \<le> curry2 r'"
unfolding curry2_def le_fun_def by auto

lemma curry2_o_uncurry2[simp]: "curry2 o uncurry2 = id"
unfolding uncurry2_def curry2_def by auto

(* *)

lemma lfp_uncurry2: 
"uncurry2 (lfp (F o uncurry2)) = lfp (uncurry2 o F)"
unfolding lfp_def uncurry2_def unfolding Inf_INT_eq Inf_INT_eq2 
unfolding fun_eq_iff o_def le_fun_def  
by simp (metis case_prod_curry old.prod.case) 

lemma lfp_uncurry2': 
"uncurry2 (lfp F) = lfp (uncurry2 o F o curry2)"
using lfp_uncurry2[of "F o curry2"] unfolding o_assoc[symmetric] curry2_o_uncurry2 by simp

lemma lfp_curry2': 
"lfp F = curry2 (lfp (uncurry2 o F o curry2))"
by (metis curry2_uncurry2 lfp_uncurry2')
 
lemma lfp_curry2: 
"lfp F x1 x2 \<longleftrightarrow> lfp (\<lambda>q (x1,x2). F (\<lambda>x1 x2. q (x1,x2)) x1 x2) (x1,x2)"  
using lfp_curry2' unfolding curry2_def uncurry2_def fun_eq_iff o_def by metis

(*****************)
(* 3-ARY *)

definition uncurry3 :: "('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a3 \<Rightarrow> bool) \<Rightarrow> 'a1 \<times> 'a2 \<times> 'a3 \<Rightarrow> bool" where 
"uncurry3 q \<equiv> \<lambda>(x1,x2,x3). q x1 x2 x3"
definition curry3 :: "('a1 \<times> 'a2 \<times> 'a3 \<Rightarrow> bool) \<Rightarrow> 'a1 \<Rightarrow> 'a2 \<Rightarrow> 'a3 \<Rightarrow> bool" where 
"curry3 r \<equiv> \<lambda> x1 x2 x3. r (x1,x2,x3)"

lemma curry3_uncurry3[simp]: "curry3 (uncurry3 q) = q"
unfolding uncurry3_def curry3_def by auto

lemma uncurry3_o_curry3[simp]: "uncurry3 o curry3 = id"
unfolding uncurry3_def curry3_def by auto

lemma uncurry3_curry3[simp]: "uncurry3 (curry3 q) = q"
unfolding uncurry3_def curry3_def by auto

lemma uncurry3_mono: "q \<le> q' \<Longrightarrow> uncurry3 q \<le> uncurry3 q'"
unfolding uncurry3_def le_fun_def by auto

lemma curry3_mono: "r \<le> r' \<Longrightarrow> curry3 r \<le> curry3 r'"
unfolding curry3_def le_fun_def by auto

lemma curry3_o_uncurry3[simp]: "curry3 o uncurry3 = id"
unfolding uncurry3_def curry3_def by auto

(* *)

lemma lfp_uncurry3: 
"uncurry3 (lfp (F o uncurry3)) = lfp (uncurry3 o F)"
unfolding lfp_def uncurry3_def unfolding Inf_INT_eq Inf_fun_def 
unfolding fun_eq_iff o_def le_fun_def 
by simp (smt (verit, best) curry3_uncurry3 split_conv uncurry3_curry3 uncurry3_def)

lemma lfp_uncurry3': 
"uncurry3 (lfp F) = lfp (uncurry3 o F o curry3)"
using lfp_uncurry3[of "F o curry3"] unfolding o_assoc[symmetric] curry3_o_uncurry3 by simp

lemma lfp_curry3': 
"lfp F = curry3 (lfp (uncurry3 o F o curry3))"
by (metis curry3_uncurry3 lfp_uncurry3')
 
lemma lfp_curry3: 
"lfp F x1 x2 x3 \<longleftrightarrow> lfp (\<lambda>q (x1,x2,x3). F (\<lambda>x1 x2 x3. q (x1,x2,x3)) x1 x2 x3) (x1,x2,x3)"  
using lfp_curry3' unfolding curry3_def uncurry3_def fun_eq_iff o_def by metis


(*****************)
(* 4-ARY *)

definition uncurry4 :: "('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a3 \<Rightarrow> 'a4 \<Rightarrow> bool) \<Rightarrow> 'a1 \<times> 'a2 \<times> 'a3 \<times> 'a4 \<Rightarrow> bool" where 
"uncurry4 q \<equiv> \<lambda>(x1,x2,x3,x4). q x1 x2 x3 x4"
definition curry4 :: "('a1 \<times> 'a2 \<times> 'a3 \<times> 'a4 \<Rightarrow> bool) \<Rightarrow> 'a1 \<Rightarrow> 'a2 \<Rightarrow> 'a3 \<Rightarrow> 'a4 \<Rightarrow> bool" where 
"curry4 r \<equiv> \<lambda> x1 x2 x3 x4. r (x1,x2,x3,x4)"

lemma curry4_uncurry4[simp]: "curry4 (uncurry4 q) = q"
unfolding uncurry4_def curry4_def by auto

lemma uncurry4_o_curry4[simp]: "uncurry4 o curry4 = id"
unfolding uncurry4_def curry4_def by auto

lemma uncurry4_curry4[simp]: "uncurry4 (curry4 q) = q"
unfolding uncurry4_def curry4_def by auto

lemma uncurry4_mono: "q \<le> q' \<Longrightarrow> uncurry4 q \<le> uncurry4 q'"
unfolding uncurry4_def le_fun_def by auto

lemma curry4_mono: "r \<le> r' \<Longrightarrow> curry4 r \<le> curry4 r'"
unfolding curry4_def le_fun_def by auto

lemma curry4_o_uncurry4[simp]: "curry4 o uncurry4 = id"
unfolding uncurry4_def curry4_def by auto

(* *)

lemma lfp_uncurry4: 
"uncurry4 (lfp (F o uncurry4)) = lfp (uncurry4 o F)"
unfolding lfp_def uncurry4_def unfolding Inf_INT_eq Inf_fun_def 
unfolding fun_eq_iff o_def le_fun_def 
by simp (smt (verit) curry4_def curry4_uncurry4 uncurry4_curry4 uncurry4_def) 

lemma lfp_uncurry4': 
"uncurry4 (lfp F) = lfp (uncurry4 o F o curry4)"
using lfp_uncurry4[of "F o curry4"] unfolding o_assoc[symmetric] curry4_o_uncurry4 by simp

lemma lfp_curry4': 
"lfp F = curry4 (lfp (uncurry4 o F o curry4))"
by (metis curry4_uncurry4 lfp_uncurry4')
 
lemma lfp_curry4: 
"lfp F x1 x2 x3 x4 \<longleftrightarrow> lfp (\<lambda>q (x1,x2,x3,x4). F (\<lambda>x1 x2 x3 x4. q (x1,x2,x3,x4)) x1 x2 x3 x4) (x1,x2,x3,x4)"  
using lfp_curry4' unfolding curry4_def uncurry4_def fun_eq_iff o_def by metis

(*****************)
(* 5-ARY *)

definition uncurry5 :: "('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a3 \<Rightarrow> 'a4 \<Rightarrow> 'a5 \<Rightarrow> bool) \<Rightarrow> 'a1 \<times> 'a2 \<times> 'a3 \<times> 'a4 \<times>'a5 \<Rightarrow> bool" where 
"uncurry5 q \<equiv> \<lambda>(x1,x2,x3,x4,x5). q x1 x2 x3 x4 x5"
definition curry5 :: "('a1 \<times> 'a2 \<times> 'a3 \<times> 'a4 \<times> 'a5 \<Rightarrow> bool) \<Rightarrow> 'a1 \<Rightarrow> 'a2 \<Rightarrow> 'a3 \<Rightarrow> 'a4  \<Rightarrow> 'a5 \<Rightarrow> bool" where 
"curry5 r \<equiv> \<lambda> x1 x2 x3 x4 x5. r (x1,x2,x3,x4,x5)"

lemma curry5_uncurry5[simp]: "curry5 (uncurry5 q) = q"
unfolding uncurry5_def curry5_def by auto

lemma uncurry5_o_curry5[simp]: "uncurry5 o curry5 = id"
unfolding uncurry5_def curry5_def by auto

lemma uncurry5_curry5[simp]: "uncurry5 (curry5 q) = q"
unfolding uncurry5_def curry5_def by auto

lemma uncurry5_mono: "q \<le> q' \<Longrightarrow> uncurry5 q \<le> uncurry5 q'"
unfolding uncurry5_def le_fun_def by auto

lemma curry5_mono: "r \<le> r' \<Longrightarrow> curry5 r \<le> curry5 r'"
unfolding curry5_def le_fun_def by auto

lemma curry5_o_uncurry5[simp]: "curry5 o uncurry5 = id"
unfolding uncurry5_def curry5_def by auto

(* *)

lemma lfp_uncurry5: 
"uncurry5 (lfp (F o uncurry5)) = lfp (uncurry5 o F)"
unfolding lfp_def uncurry5_def unfolding Inf_INT_eq Inf_fun_def 
unfolding fun_eq_iff o_def le_fun_def 
by simp (smt (verit) curry5_def curry5_uncurry5 uncurry5_curry5 uncurry5_def) 

lemma lfp_uncurry5': 
"uncurry5 (lfp F) = lfp (uncurry5 o F o curry5)"
using lfp_uncurry5[of "F o curry5"] unfolding o_assoc[symmetric] curry5_o_uncurry5 by simp

lemma lfp_curry5': 
"lfp F = curry5 (lfp (uncurry5 o F o curry5))"
by (metis curry5_uncurry5 lfp_uncurry5')
 
lemma lfp_curry5: 
"lfp F x1 x2 x3 x4 x5 \<longleftrightarrow> lfp (\<lambda>q (x1,x2,x3,x4,x5). F (\<lambda>x1 x2 x3 x4 x5. q (x1,x2,x3,x4,x5)) x1 x2 x3 x4 x5) (x1,x2,x3,x4,x5)"  
using lfp_curry5' unfolding curry5_def uncurry5_def fun_eq_iff o_def by metis


(* *)
(* *)

lemmas disjI3_1 = disjI1[OF disjI1, simplified]
lemmas disjI3_2 = disjI1[OF disjI2, simplified]
lemmas disjI3_3 = disjI2[OF disjI2, simplified]

(* *)

lemmas disjI4_1 = disjI1[OF disjI1, OF disjI1, simplified]
lemmas disjI4_2 = disjI1[OF disjI2, OF disjI1, simplified]
lemmas disjI4_3 = disjI2[OF disjI2, OF disjI1, simplified]
lemmas disjI4_4 = disjI2[OF disjI2, OF disjI2, simplified]

(* *)

lemmas disjI5_1 = disjI1[OF disjI1, OF disjI1, OF disjI1, simplified]
lemmas disjI5_2 = disjI1[OF disjI2, OF disjI1, OF disjI1, simplified]
lemmas disjI5_3 = disjI2[OF disjI2, OF disjI1, OF disjI1, simplified]
lemmas disjI5_4 = disjI2[OF disjI2, OF disjI2, OF disjI1, simplified]
lemmas disjI5_5 = disjI2[OF disjI2, OF disjI2, OF disjI2, simplified]

(* *)

lemmas disjI6_1 = disjI1[OF disjI1, OF disjI1, OF disjI1, OF disjI1, simplified]
lemmas disjI6_2 = disjI1[OF disjI2, OF disjI1, OF disjI1, OF disjI1, simplified]
lemmas disjI6_3 = disjI2[OF disjI2, OF disjI1, OF disjI1, OF disjI1, simplified]
lemmas disjI6_4 = disjI2[OF disjI2, OF disjI2, OF disjI1, OF disjI1, simplified]
lemmas disjI6_5 = disjI2[OF disjI2, OF disjI2, OF disjI2, OF disjI1, simplified]
lemmas disjI6_6 = disjI2[OF disjI2, OF disjI2, OF disjI2, OF disjI2, simplified]

(* *)

lemmas disjI7_1 = disjI1[OF disjI1, OF disjI1, OF disjI1, OF disjI1, OF disjI1, simplified]
lemmas disjI7_2 = disjI1[OF disjI2, OF disjI1, OF disjI1, OF disjI1, OF disjI1, simplified]
lemmas disjI7_3 = disjI2[OF disjI2, OF disjI1, OF disjI1, OF disjI1, OF disjI1, simplified]
lemmas disjI7_4 = disjI2[OF disjI2, OF disjI2, OF disjI1, OF disjI1, OF disjI1, simplified]
lemmas disjI7_5 = disjI2[OF disjI2, OF disjI2, OF disjI2, OF disjI1, OF disjI1, simplified]
lemmas disjI7_6 = disjI2[OF disjI2, OF disjI2, OF disjI2, OF disjI2, OF disjI1, simplified]
lemmas disjI7_7 = disjI2[OF disjI2, OF disjI2, OF disjI2, OF disjI2, OF disjI2, simplified]


end