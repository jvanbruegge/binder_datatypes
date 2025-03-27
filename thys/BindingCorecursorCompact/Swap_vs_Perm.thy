theory Swap_vs_Perm 
  imports Infinitary_Lambda_Terms Swapping 
begin 

definition permut :: "('c \<Rightarrow> (var \<Rightarrow> var) \<Rightarrow> 'c) \<Rightarrow> bool" where
"permut perm \<equiv> 
  (\<forall> c. perm c id = c) \<and> 
  (\<forall> c \<sigma> \<tau>. bij \<sigma> \<and> fsupp \<sigma> \<and> bij \<tau> \<and> fsupp \<tau> \<longrightarrow> perm (perm c \<sigma>) \<tau> = perm c (\<tau> o \<sigma>))"

lemma permut_id[simp]: "permut perm \<Longrightarrow> perm c id = c"
unfolding permut_def by auto

lemma permut_comp: "permut perm \<Longrightarrow> bij \<sigma> \<Longrightarrow> fsupp \<sigma> \<Longrightarrow> bij \<tau> \<Longrightarrow> fsupp \<tau> \<Longrightarrow> 
 perm (perm c \<sigma>) \<tau> = perm c (\<tau> o \<sigma>)"
unfolding permut_def by auto

lemma fsupp_inv[simp]: "bij \<sigma> \<Longrightarrow> fsupp \<sigma> \<Longrightarrow> fsupp (inv \<sigma>)"
by (smt (verit, del_insts) Collect_cong bij_inv_eq_iff fsupp_def)

lemma permut_inv1: 
assumes p: "permut perm" and \<sigma>: "bij \<sigma>" "fsupp \<sigma>" and d: "d = perm c \<sigma>"
shows "c = perm d (inv \<sigma>)"
unfolding d by (simp add: \<sigma> bij_imp_bij_inv bijection.intro bijection.inv_comp_left p permut_comp)

lemma permut_inv: 
assumes "permut perm" and \<sigma>: "bij \<sigma>" "fsupp \<sigma>"
shows "d = perm c \<sigma> \<longleftrightarrow> c = perm d (inv \<sigma>)"
by (metis assms(1) assms(2) assms(3) bij_imp_bij_inv fsupp_inv inv_inv_eq permut_inv1)


(* One direction: *)

definition toSwp :: "('c \<Rightarrow> (var \<Rightarrow> var) \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'c)" where 
"toSwp perm c x y = perm c (id(x:=y,y:=x))"

theorem nswapping_toSwp: 
assumes "permut perm"
shows "nswapping (toSwp perm)"
proof-
  have [simp]: "\<And>c \<sigma> \<tau>. bij \<sigma> \<Longrightarrow> fsupp \<sigma> \<Longrightarrow> bij \<tau> \<Longrightarrow> fsupp \<tau>  \<Longrightarrow> perm (perm c \<sigma>) \<tau> = perm c (\<tau> \<circ> \<sigma>) " 
   using assms unfolding permut_def by auto
  show ?thesis using assms unfolding nswapping_def permut_def toSwp_def 
  by (auto simp add: id_swapTwice id_swapTwice2)  
qed   

(* The other direction: *)

(* Composition of a list of transpositions:   *)  
fun cmpTrans :: "(var \<times> var) list \<Rightarrow> (var \<Rightarrow> var)" where 
 "cmpTrans [] = id"
|"cmpTrans ((z1,z2) # z1z2s) = (id(z1:=z2,z2:=z1)) o cmpTrans z1z2s"

lemma cmpTrans_append: "cmpTrans (z1z2s @ z1z2s') c = cmpTrans z1z2s (cmpTrans z1z2s' c)"
by(induct z1z2s) auto

(* Action of a list of transpositions: *)
fun actTrans :: "('c \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'c) \<Rightarrow> (var \<times> var) list \<Rightarrow> 'c \<Rightarrow> 'c" where 
 "actTrans swp [] c = c"
|"actTrans swp ((z1,z2) # z1z2s) c = swp (actTrans swp z1z2s c) z1 z2"

lemma actTransTrans_append: "actTrans swp (z1z2s @ z1z2s') c = actTrans swp z1z2s (actTrans swp z1z2s' c)"
by(induct z1z2s) auto


(*Preliminary lemmas about swapping algebras*)
lemma cmpTrans_hd_sym:"cmpTrans ((x,y) # z1z2s) = cmpTrans ((y,x) # z1z2s)"
  unfolding cmpTrans.simps(2) by auto

lemma actTransTrans_hd_sym: assumes "nswapping swp"
  shows "actTrans swp ((x,y) # z1z2s) c = actTrans swp ((y,x) # z1z2s) c"
  unfolding actTrans.simps(2) using nswapping_sym1[OF assms] by presburger

lemma cmpTrans_disj_supp_commutes: assumes"{x1,x2} \<inter> {y1,y2} = {}"
  shows "cmpTrans ((x1,x2) # (y1,y2) # z1z2s) = cmpTrans ((y1,y2) # (x1,x2) # z1z2s)"
  unfolding cmpTrans.simps(2) o_assoc using assms fun_upd_twist by auto

lemma actTransTrans_disj_supp_commutes: assumes "nswapping swp" "{x1,x2} \<inter> {y1,y2} = {}"
  shows "actTrans swp ((x1,x2) # (y1,y2) # z1z2s) c = actTrans swp ((y1,y2) # (x1,x2) # z1z2s) c"
  unfolding actTrans.simps(2) sw_def 
    assms(1)[unfolded nswapping_def, THEN conjunct2, THEN conjunct2, rule_format, of _ y1 y2 x1 x2]
  using assms(2) by fastforce

lemma bij_cmpTrans[simp,intro!]: "bij (cmpTrans x1x2s)"
apply(induct x1x2s, safe) subgoal unfolding cmpTrans.simps by blast
subgoal for a b x1x2s unfolding cmpTrans.simps by (simp add: bij_o) 
done

lemma cmpTrans_diff_implies_diff_im: "cmpTrans x1x2s x \<noteq> x 
  \<Longrightarrow> cmpTrans x1x2s (cmpTrans x1x2s x) \<noteq> cmpTrans x1x2s x"
  using bij_cmpTrans bij_is_inj by (metis injD)

lemma cmpTrans_support0:assumes "\<forall> p. p \<in> set x1x2s \<longrightarrow> x \<noteq> fst p \<and> x \<noteq> snd p"
  shows "cmpTrans x1x2s x = x"
  using assms
proof(induct x1x2s, simp)
  fix a x1x2s 
  assume ih':"\<forall>p. p \<in> set x1x2s \<longrightarrow> x \<noteq> fst p \<and> x \<noteq> snd p \<Longrightarrow> cmpTrans x1x2s x = x" 
    and h':"\<forall>p. p \<in> set (a # x1x2s) \<longrightarrow> x \<noteq> fst p \<and> x \<noteq> snd p"
  obtain a1 a2 where a:"a = (a1,a2)" by fastforce
  have h:"\<forall>p. p \<in> set x1x2s \<longrightarrow> x \<noteq> fst p \<and> x \<noteq> snd p" "x \<noteq> a1" "x \<noteq> a2"
    apply (simp add: h') using a h' apply auto .
  have ih:"cmpTrans x1x2s x = x" by(rule ih'[OF h(1)])
  show "cmpTrans (a # x1x2s) x = x"
    unfolding a cmpTrans.simps by(simp add: h ih)
qed


lemma cmpTrans_support:"cmpTrans x1x2s x \<noteq> x \<Longrightarrow> (\<exists> p. p \<in> set x1x2s \<and> (x = fst p \<or> x = snd p))"
  using cmpTrans_support0 by blast

lemma cmpTrans_support_im:"cmpTrans x1x2s x \<noteq> x \<Longrightarrow> 
  (\<exists> p. p \<in> set x1x2s \<and> (cmpTrans x1x2s x = fst p \<or> cmpTrans x1x2s x = snd p))"
  using cmpTrans_support0 cmpTrans_diff_implies_diff_im by blast

lemma cmpTrans_leftmost_eq: assumes notem:"x1x2s \<noteq> []" 
  and tail:"\<forall> p. p \<in> set (tl x1x2s) \<longrightarrow> x2 \<noteq> fst p \<and> x2 \<noteq> snd p"
  and neq:"x1 \<noteq> x2"
shows "(cmpTrans x1x2s x2 = x1) = (hd x1x2s = (x1,x2) \<or> hd x1x2s = (x2,x1))"
proof(cases x1x2s, simp add: notem, safe)
  fix a b list
  assume hp:"x1x2s = (a, b) # list" "x1 = cmpTrans ((a, b) # list) x2" 
    "hd ((a, b) # list) \<noteq> (x2, cmpTrans ((a, b) # list) x2)"
  have eq:"list = tl x1x2s" using hp(1) by simp
  show "hd ((a, b) # list) = (cmpTrans ((a, b) # list) x2, x2)"
    using hp(2) neq unfolding cmpTrans.simps o_apply eq cmpTrans_support0[OF tail] 
    by (metis fun_upd_apply hp(2) hp(3) id_apply list.sel(1))
next
  fix a b list
  assume hp:"x1x2s = (a, b) # list" "hd ((a, b) # list) = (x1, x2)"
  have eq:"list = tl x1x2s" "(a,b) = (x1,x2)" using hp by simp_all
  show "cmpTrans ((a, b) # list) x2 = x1"
    unfolding eq cmpTrans.simps o_apply cmpTrans_support0[OF tail] by simp
next
  fix a b list
  assume hp:"x1x2s = (a, b) # list" "hd ((a, b) # list) = (x2, x1)"
  have eq:"list = tl x1x2s" "(a,b) = (x2,x1)" using hp by simp_all
  show "cmpTrans ((a, b) # list) x2 = x1"
    unfolding eq cmpTrans.simps o_apply cmpTrans_support0[OF tail] by simp
qed

lemma cmpTrans_head_same:"cmpTrans ((x,x)#x1x2s) x = cmpTrans x1x2s x"
  unfolding cmpTrans.simps by simp

lemma cmpTrans_leftmost1: assumes notem:"x1x2s \<noteq> []" 
  and tail:"\<forall> p. p \<in> set (tl x1x2s) \<longrightarrow> x2 \<noteq> fst p \<and> x2 \<noteq> snd p"
  and head:"hd x1x2s = (x1,x2)"
shows "cmpTrans x1x2s x2 = x1"
  apply (cases "x1 = x2") 
  subgoal using cmpTrans_head_same assms by (metis cmpTrans_support0 list.exhaust_sel)
  subgoal using cmpTrans_leftmost_eq[OF notem tail] head by simp
  done

lemma cmpTrans_leftmost2: assumes notem:"x1x2s \<noteq> []" 
  and tail:"\<forall> p. p \<in> set (tl x1x2s) \<longrightarrow> x2 \<noteq> fst p \<and> x2 \<noteq> snd p"
  and head:"hd x1x2s = (x2,x1)"
shows "cmpTrans x1x2s x2 = x1"
  apply (cases "x1 = x2") 
  subgoal using cmpTrans_head_same assms by (metis cmpTrans_support0 list.exhaust_sel)
  subgoal using cmpTrans_leftmost_eq[OF notem tail] head by simp
  done

lemma cmpTrans_pair_fix:"cmpTrans [(x,y)] z = z \<Longrightarrow> x \<noteq> y \<Longrightarrow> (x \<noteq> z \<and> y \<noteq> z)"
  unfolding cmpTrans.simps by auto


lemma cmpTrans_pair_push_left: assumes "cmpTrans [(a,b),(x0, x2)] x2 = x1" 
  shows "\<exists> a0 b0.
          cmpTrans [(a,b),(x0, x2)] = cmpTrans [(x1,x2),(a0,b0)] \<and> x2 \<notin> {a0,b0}"
proof(cases "x0 = x1")
  case True
  show ?thesis unfolding True 
  proof(cases "a = b")
    assume ab:"a = b"
    obtain xx where xx:"xx \<noteq> x1" "xx \<noteq> x2"
       using exists_var[of "{x1,x2}"] by blast
    show "\<exists> a0 b0. cmpTrans [(a,b),(x1, x2)] = cmpTrans [(x1,x2),(a0,b0)] \<and> x2 \<notin> {a0,b0}"  
       unfolding ab cmpTrans.simps apply(rule exI[of _ xx], rule exI[of _ xx])
       using xx by simp
  next
    assume ab:"a \<noteq> b"
    have  abfix:"cmpTrans [(a,b)] x1 = x1"
        using assms unfolding True cmpTrans.simps by simp
    have ab_x1:"a \<noteq> x1" "b \<noteq> x1"
        by(auto simp add: cmpTrans_pair_fix[OF abfix ab]) 
    show "\<exists> a0 b0. cmpTrans [(a,b),(x1, x2)] = cmpTrans [(x1,x2),(a0,b0)] \<and> x2 \<notin> {a0,b0}" 
      apply (cases "a = x2")
      subgoal apply(rule exI[of _ x1], rule exI[of _ b])
      unfolding cmpTrans.simps using ab ab_x1 
          by (simp add: fun_upd_comp fun_upd_twist)
      subgoal apply(cases "b = x2")
        subgoal apply(rule exI[of _ x1], rule exI[of _ a])
            unfolding cmpTrans.simps using ab ab_x1 fun_upd_twist by auto
        subgoal apply(rule exI[of _ a], rule exI[of _ b])
            unfolding cmpTrans.simps using ab_x1 fun_upd_twist by auto
        done
      done
  qed
next
  case False
  have step2:"cmpTrans [(a,b)] x0 = x1"
      using assms by simp
  have ab:"{x1,x0}={a,b}"
      using cmpTrans_support[OF False[symmetric, unfolded step2[symmetric]]]
        cmpTrans_support_im[OF False[symmetric, unfolded step2[symmetric]]] 
      unfolding step2 using False by auto
  show ?thesis
  proof (cases "x0 = x2")
    assume comx2:"x0 = x2"
    obtain x00 where x00:"x00 \<notin> {x1,x2}" 
        using exists_var 
        by (meson countable_empty countable_insert_eq)
    show ?thesis unfolding comx2 apply(rule exI[of _ x00], rule exI[of _ x00], simp, safe)
      subgoal using ab unfolding comx2 by fastforce
      subgoal using x00 by blast done
  next
    assume comx2:"x0 \<noteq> x2"
    show ?thesis
      apply(cases "x1 = x2") 
        subgoal apply(rule exI[of _ "x0"],
            rule exI[of _ "x0"], safe, simp_all add: comx2[symmetric])
          using ab comx2 unfolding cmpTrans.simps
          by (metis doubleton_eq_iff fun_upd_twist id_swapTwice)
        subgoal apply(rule exI[of _ x1], rule exI[of _ "x0"], safe, 
            simp_all add: comx2[symmetric]) using comx2 ab 
          by (smt comp_id doubleton_eq_iff fun_upd_comp 
                    fun_upd_other fun_upd_same fun_upd_twist fun_upd_upd id_apply)
        done
  qed
qed


lemma cmpTrans_push_left: assumes notem:"x1x2s \<noteq> []" 
  and inset:"\<exists> p. p \<in> set x1x2s \<and> (x2 = fst p \<or> x2 = snd p)"
  and image:"cmpTrans x1x2s x2 = x1"
shows "\<exists> x1x2s'. length x1x2s' = length x1x2s 
  \<and> cmpTrans x1x2s' = cmpTrans x1x2s \<and> hd x1x2s' = (x1,x2)
  \<and> (\<forall> p. p \<in> set (tl x1x2s') \<longrightarrow> x2 \<noteq> fst p \<and> x2 \<noteq> snd p)"
  using assms
proof(induct x1x2s arbitrary: x1 x2 rule: length_induct, simp)
  fix x1x2s x1 x2
  assume ih: "\<forall>ys. length ys < length x1x2s \<longrightarrow>
            ys \<noteq> [] \<longrightarrow>
            (\<forall>x. (\<exists>a b. (a, b) \<in> set ys \<and> (x = a \<or> x = b)) \<longrightarrow>
                 (\<exists>x1x2s'.
                     length x1x2s' = length ys \<and>
                     cmpTrans x1x2s' = cmpTrans ys \<and>
                     hd x1x2s' = (cmpTrans ys x, x) \<and>
                     (\<forall>a b. (a, b) \<in> set (tl x1x2s') \<longrightarrow> x \<noteq> a \<and> x \<noteq> b)))"
    and neq:"x1x2s \<noteq> []"
    and inset:"\<exists> a b. (a,b) \<in> set x1x2s \<and> (x2 = a \<or> x2 = b)"
    and comp:"cmpTrans x1x2s x2 = x1"  
  show "\<exists>x1x2s'.
          length x1x2s' = length x1x2s \<and>
          cmpTrans x1x2s' = cmpTrans x1x2s \<and> hd x1x2s' = (x1, x2)
         \<and> (\<forall>a b. (a, b) \<in> set (tl x1x2s') \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b)"
    apply(cases x1x2s, simp add:neq)
  proof safe
    fix a b y1y2s
    assume x1x2s:"x1x2s = (a,b) # y1y2s"
    show "\<exists>x1x2s'.
     length x1x2s' = length ((a,b) # y1y2s) \<and>
     cmpTrans x1x2s' = cmpTrans ((a,b) # y1y2s) \<and> hd x1x2s' = (x1, x2)
     \<and> (\<forall> a b. (a,b) \<in> set (tl x1x2s') \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b)"
      apply (cases y1y2s) 
      subgoal proof(intro exI[of _ "[(x1,x2)]"])
        assume empty:"y1y2s = []"
        show "length [(x1, x2)] = length ((a, b) # y1y2s) \<and>
          cmpTrans [(x1, x2)] = cmpTrans ((a, b) # y1y2s) \<and>
          hd [(x1, x2)] = (x1, x2) \<and> (\<forall>a b. (a, b) \<in> set (tl [(x1, x2)]) \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b)"
          using comp inset unfolding x1x2s empty cmpTrans.simps by force
      qed
      subgoal for aa list proof(cases "\<forall>a b. (a, b) \<in> set (y1y2s) \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b")
        assume ny:"y1y2s = aa # list"
          and casen:"\<forall>a b. (a, b) \<in> set y1y2s \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b"
        have fromcasen:"cmpTrans y1y2s x2 = x2"
          using cmpTrans_support0 casen by force
        have fromcasen2:"cmpTrans [(a,b)] x2 = x1"
          unfolding comp[symmetric] x1x2s cmpTrans.simps o_apply fromcasen by simp
        have seteq:"x1 \<noteq> x2 \<Longrightarrow> {a,b}={x1,x2}"
          using fromcasen2 unfolding cmpTrans.simps
          using casen doubleton_eq_iff inset x1x2s by fastforce
        have eqeq:"x1 = x2 \<Longrightarrow> a = b" using fromcasen2 unfolding cmpTrans.simps
          by (metis Pair_inject casen cmpTrans_pair_fix fromcasen2 inset set_ConsD x1x2s)
        show ?thesis apply(rule exI[of _ "(x1,x2) # y1y2s"], simp add: casen, cases "x1 = x2")
          subgoal using eqeq by simp
          subgoal using seteq cmpTrans_hd_sym fromcasen2 by auto
          done
      next
        assume ny:"y1y2s = aa # list"
          and casey:" \<not> (\<forall>a b. (a, b) \<in> set y1y2s \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b)"
        have expair:"\<exists> a b. (a, b) \<in> set y1y2s \<and> (x2 = a \<or> x2 = b)" using casey by blast
        obtain z1z2s where z1z2s:"length z1z2s = length y1y2s"
          "cmpTrans z1z2s = cmpTrans y1y2s" "hd z1z2s = (cmpTrans y1y2s x2, x2)"
          "\<forall>a b. (a, b) \<in> set (tl z1z2s) \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b"
          using ih[rule_format, of y1y2s x2, OF _ _ expair] using ny x1x2s by auto
        have step:"cmpTrans ((a, b) # y1y2s) = cmpTrans ((a,b)#(cmpTrans y1y2s x2, x2)# tl z1z2s)"
          unfolding cmpTrans.simps(2)[of a b] z1z2s(2)[symmetric] using z1z2s(3)
          by (metis length_0_conv list.exhaust_sel list.simps(3) ny z1z2s(1) z1z2s(2))
        have step0:"cmpTrans ((a, b) # y1y2s) x2  = cmpTrans [(a,b),(cmpTrans y1y2s x2, x2)] x2"
          unfolding step unfolding cmpTrans.simps
          using z1z2s(4) cmpTrans_support0 by fastforce
        have step1:"cmpTrans [(a,b),(cmpTrans y1y2s x2, x2)] x2 = x1"
          using step0 comp x1x2s by auto
        obtain a0 b0 where final:
          "cmpTrans [(a,b),(cmpTrans y1y2s x2, x2)] = cmpTrans [(x1,x2),(a0,b0)]" "x2 \<notin> {a0,b0}"
          using cmpTrans_pair_push_left[OF step1] by blast
        show ?thesis
          apply(rule exI[of _ "(x1,x2) # (a0,b0) # tl z1z2s"], safe)
          subgoal by (simp add: ny z1z2s(1))
          subgoal using final unfolding step unfolding cmpTrans.simps by (simp add: o_assoc)
          subgoal by simp
          subgoal using final z1z2s(4) by auto
          subgoal using final z1z2s(4) by auto
          done
      qed
      done
  qed
qed

lemma cmpTrans_push_left_last: assumes notem:"x1x2s \<noteq> []" 
  and last:"last x1x2s = (x0,x2)"
  and image:"cmpTrans x1x2s x2 = x1"
shows "\<exists> x1x2s'. length x1x2s' = length x1x2s 
  \<and> cmpTrans x1x2s' = cmpTrans x1x2s \<and> hd x1x2s' = (x1,x2)
  \<and> (\<forall> p. p \<in> set (tl x1x2s') \<longrightarrow> x2 \<noteq> fst p \<and> x2 \<noteq> snd p)"
  apply(intro cmpTrans_push_left[OF notem _ image])
  using last last_in_set notem by fastforce



lemma actTransTrans_cmpTrans_pair_push_left: assumes comp:"cmpTrans [(a,b),(y, x2)] x2 = x1"
  and swp:"nswapping swp"
  shows "\<exists> a0 b0. cmpTrans [(a,b),(y, x2)] = cmpTrans [(x1,x2),(a0,b0)] \<and>
          actTrans swp [(a,b),(y, x2)] = actTrans swp [(x1,x2),(a0,b0)] \<and> x2 \<notin> {a0,b0}"
proof(cases "y = x1")
  case True
  show ?thesis unfolding True 
  proof(cases "a = b")
    assume ab:"a = b"
    obtain xx where xx:"xx \<noteq> x1" "xx \<noteq> x2"
       using exists_var[of "{x1,x2}"] by blast
     show "\<exists> a0 b0. cmpTrans [(a, b), (x1, x2)] = cmpTrans [(x1, x2), (a0, b0)] \<and>
            actTrans swp [(a,b),(x1, x2)] = actTrans swp [(x1,x2),(a0,b0)] \<and> x2 \<notin> {a0,b0}"  
       unfolding ab actTrans.simps cmpTrans.simps apply(rule exI[of _ xx], rule exI[of _ xx],
           safe, simp_all add: xx[symmetric])
       unfolding swp[unfolded nswapping_def, THEN conjunct1, rule_format] using xx by fast
  next
    assume ab:"a \<noteq> b"
    have  abfix:"cmpTrans [(a,b)] x1 = x1"
        using assms unfolding True cmpTrans.simps by simp
    have ab_x1:"a \<noteq> x1" "b \<noteq> x1"
        by(auto simp add: cmpTrans_pair_fix[OF abfix ab]) 
      show "\<exists> a0 b0. cmpTrans [(a, b), (x1, x2)] = cmpTrans [(x1, x2), (a0, b0)] \<and> 
            actTrans swp [(a,b),(x1, x2)] = actTrans swp [(x1,x2),(a0,b0)] \<and> x2 \<notin> {a0,b0}" 
      apply (cases "a = x2")
      subgoal apply(rule exI[of _ x1], rule exI[of _ b])
        unfolding actTrans.simps cmpTrans.simps
        swp[unfolded nswapping_def, THEN conjunct2, THEN conjunct2, rule_format, of _ x1 b]
        using ab ab_x1 by force
      subgoal apply(cases "b = x2")
        subgoal apply(rule exI[of _ x1], rule exI[of _ a])
          unfolding actTrans.simps cmpTrans.simps
          swp[unfolded nswapping_def, THEN conjunct2, THEN conjunct2, rule_format, of _ x1 a]
          using ab ab_x1 apply safe subgoal by (simp add: fun_upd_comp fun_upd_twist)
          subgoal by (simp add: nswapping_sym1[OF swp]) done
        subgoal apply(rule exI[of _ a], rule exI[of _ b])
          using ab_x1 apply simp
          using  actTransTrans_disj_supp_commutes[OF swp, of a b x1 x2 "[]"] by force
        done
      done
  qed
next
  case False
  have step2:"cmpTrans [(a,b)] y = x1"
      using assms by simp
  have ab:"{x1,y}={a,b}"
      using cmpTrans_support[OF False[symmetric, unfolded step2[symmetric]]]
        cmpTrans_support_im[OF False[symmetric, unfolded step2[symmetric]]] 
      unfolding step2 using False by auto
  show ?thesis
  proof (cases "y = x2")
    assume comx2:"y = x2"
    obtain x0 where x0:"x0 \<notin> {x1,x2}" 
    using exists_var by (meson countable_empty countable_insert) 
    show ?thesis unfolding comx2 apply(rule exI[of _ x0], rule exI[of _ x0], simp, safe)
      subgoal using ab unfolding comx2 by fastforce
      subgoal using ab unfolding comx2 actTrans.simps 
        unfolding swp[unfolded nswapping_def, THEN conjunct1, rule_format] 
        by (metis doubleton_eq_iff nswapping_sym1 swp)        
      subgoal using x0 by blast done
  next
    assume comx2:"y \<noteq> x2"
    show ?thesis
      apply(cases "x1 = x2") 
        subgoal apply(rule exI[of _ "y"],
            rule exI[of _ "y"], simp_all add: comx2[symmetric])
          using ab comx2 unfolding actTrans.simps 
          unfolding swp[unfolded nswapping_def, THEN conjunct1, rule_format] 
          apply(cases "x2=a", simp) using doubleton_eq_iff 
          subgoal apply safe subgoal by (simp add: doubleton_eq_iff fun_upd_twist id_swapTwice)
            subgoal using nswapping_sym0[OF swp, of _ y x2] by auto done
          subgoal apply safe subgoal by (simp add: doubleton_eq_iff id_swapTwice) subgoal
            using 
              swp[unfolded nswapping_def, THEN conjunct2, THEN conjunct1, rule_format, of _ y x2]
            by auto done
          done
        subgoal apply(rule exI[of _ x1], rule exI[of _ "y"], 
            simp_all add: comx2[symmetric]) proof(cases "a = x1")
          assume neq:"x1 \<noteq> x2" and ttr:"a = x1"
          have byy:"b = y" using ab ttr doubleton_eq_iff by fastforce
          show "id(a := b, b := a) \<circ> id(y := x2, x2 := y) 
              = id(x1 := x2, x2 := x1) \<circ> id(x1 := y, y := x1)
              \<and> 
              actTrans swp [(a, b), (y, x2)] = actTrans swp [(x1, x2), (x1, y)]"
            apply safe
            subgoal unfolding ttr byy using comx2 neq by auto
            subgoal unfolding ttr byy actTrans.simps
            swp[unfolded nswapping_def, THEN conjunct2, THEN conjunct2, rule_format, of _ y x2]
            unfolding sw_eqR sw_diff[OF neq[symmetric] comx2[symmetric]] by simp done
        next
          assume neq:"x1 \<noteq> x2" and fls:"a \<noteq> x1"
          have bx1:"b = x1" and ay:"a = y" using ab fls doubleton_eq_iff[of x1 y a b] by auto 
          show "id(a := b, b := a) \<circ> id(y := x2, x2 := y) 
              = id(x1 := x2, x2 := x1) \<circ> id(x1 := y, y := x1) 
              \<and>
              actTrans swp [(a, b), (y, x2)] = actTrans swp [(x1, x2), (x1, y)]"
            apply safe 
            subgoal unfolding bx1 ay using comx2 neq by auto
            subgoal unfolding bx1 ay actTrans.simps
            swp[unfolded nswapping_def, THEN conjunct2, THEN conjunct2, rule_format, of _ y x2]
            unfolding sw_eqL sw_diff[OF comx2[symmetric] neq[symmetric]]
            nswapping_sym1[OF swp, of _ y] by simp done
        qed   
        done
  qed
qed

lemma actTransTrans_cmpTrans_push_left: assumes notem:"x1x2s \<noteq> []" 
  and swp:"nswapping swp"
  and inset:"\<exists> p. p \<in> set x1x2s \<and> (x2 = fst p \<or> x2 = snd p)"
  and image:"cmpTrans x1x2s x2 = x1"
shows "\<exists> x1x2s'. length x1x2s' = length x1x2s 
  \<and> actTrans swp x1x2s' = actTrans swp x1x2s 
  \<and> cmpTrans x1x2s' = cmpTrans x1x2s
  \<and> hd x1x2s' = (x1,x2)
  \<and> (\<forall> p. p \<in> set (tl x1x2s') \<longrightarrow> x2 \<noteq> fst p \<and> x2 \<noteq> snd p)"
  using notem inset image
proof(induct x1x2s arbitrary: x1 x2 rule: length_induct, simp)
  fix x1x2s x1 x2
  assume ih: "\<forall>ys. length ys < length x1x2s \<longrightarrow>
            ys \<noteq> [] \<longrightarrow>
            (\<forall>x. (\<exists>a b. (a, b) \<in> set ys \<and> (x = a \<or> x = b)) \<longrightarrow>
                 (\<exists>x1x2s'.
                     length x1x2s' = length ys \<and>
                     actTrans swp x1x2s' = actTrans swp ys \<and>
                     cmpTrans x1x2s' = cmpTrans ys \<and>
                     hd x1x2s' = (cmpTrans ys x, x) \<and>
                     (\<forall>a b. (a, b) \<in> set (tl x1x2s') \<longrightarrow> x \<noteq> a \<and> x \<noteq> b)))"
    and neq:"x1x2s \<noteq> []"
    and inset:"\<exists> a b. (a,b) \<in> set x1x2s \<and> (x2 = a \<or> x2 = b)"
    and comp:"cmpTrans x1x2s x2 = x1"  
  show "\<exists>x1x2s'.
          length x1x2s' = length x1x2s \<and>
          actTrans swp x1x2s' = actTrans swp x1x2s \<and> cmpTrans x1x2s' = cmpTrans x1x2s \<and>
          hd x1x2s' = (x1, x2) \<and> (\<forall>a b. (a, b) \<in> set (tl x1x2s') \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b)"
    apply(cases x1x2s, simp add:neq)
  proof safe
    fix a b y1y2s
    assume x1x2s:"x1x2s = (a,b) # y1y2s"
    show "\<exists>x1x2s'.
     length x1x2s' = length ((a,b) # y1y2s) \<and>
     actTrans swp x1x2s' = actTrans swp ((a,b) # y1y2s)  \<and> cmpTrans x1x2s' = cmpTrans ((a, b) # y1y2s)
     \<and> hd x1x2s' = (x1, x2)
     \<and> (\<forall> a b. (a,b) \<in> set (tl x1x2s') \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b)"
      apply (cases y1y2s) 
      subgoal proof(intro exI[of _ "[(x1,x2)]"])
        assume empty:"y1y2s = []"
        have eqset:"{a,b} = {x1,x2}" using comp inset 
          unfolding x1x2s empty cmpTrans.simps by force
        show "length [(x1, x2)] = length ((a, b) # y1y2s) \<and>
          actTrans swp [(x1, x2)] = actTrans swp ((a, b) # y1y2s) \<and>
          cmpTrans [(x1, x2)] = cmpTrans ((a, b) # y1y2s) \<and>
          hd [(x1, x2)] = (x1, x2) \<and> (\<forall>a b. (a, b) \<in> set (tl [(x1, x2)]) \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b)"
          using eqset unfolding empty actTrans.simps apply (simp, safe)
          subgoal by (metis doubleton_eq_iff nswapping_sym1 swp)
          subgoal by (metis doubleton_eq_iff fun_upd_twist) done
      qed
      subgoal for aa list proof(cases "\<forall>a b. (a, b) \<in> set (y1y2s) \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b")
        assume ny:"y1y2s = aa # list"
          and casen:"\<forall>a b. (a, b) \<in> set y1y2s \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b"
        have fromcasen:"cmpTrans y1y2s x2 = x2"
          using cmpTrans_support0 casen by force
        have fromcasen2:"cmpTrans [(a,b)] x2 = x1"
          unfolding comp[symmetric] x1x2s cmpTrans.simps o_apply fromcasen by simp
        have seteq:"x1 \<noteq> x2 \<Longrightarrow> {a,b}={x1,x2}"
          using fromcasen2 unfolding cmpTrans.simps
          using casen doubleton_eq_iff inset x1x2s by fastforce
        have eqeq:"x1 = x2 \<Longrightarrow> a = b" using fromcasen2 unfolding cmpTrans.simps
          by (metis Pair_inject casen cmpTrans_pair_fix fromcasen2 inset set_ConsD x1x2s)
        show ?thesis apply(rule exI[of _ "(x1,x2) # y1y2s"], simp add: casen, cases "x1 = x2")
          subgoal using eqeq             
            apply simp unfolding actTrans.simps 
              unfolding swp[unfolded nswapping_def, THEN conjunct1, rule_format] by simp
          subgoal using seteq actTransTrans_hd_sym[OF swp] fromcasen2 by fastforce
          done
      next
        assume ny:"y1y2s = aa # list"
          and casey:" \<not> (\<forall>a b. (a, b) \<in> set y1y2s \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b)"
        have expair:"\<exists> a b. (a, b) \<in> set y1y2s \<and> (x2 = a \<or> x2 = b)" using casey by blast
        obtain z1z2s where z1z2s:"length z1z2s = length y1y2s"
          "cmpTrans z1z2s = cmpTrans y1y2s"
          "actTrans swp z1z2s = actTrans swp y1y2s" "hd z1z2s = (cmpTrans y1y2s x2, x2)"
          "\<forall>a b. (a, b) \<in> set (tl z1z2s) \<longrightarrow> x2 \<noteq> a \<and> x2 \<noteq> b"
          using ih[rule_format, of y1y2s x2, OF _ _ expair] using ny x1x2s by auto
        have step:"cmpTrans ((a, b) # y1y2s) = cmpTrans ((a,b)#(cmpTrans y1y2s x2, x2)# tl z1z2s)"
          unfolding cmpTrans.simps(2)[of a b] z1z2s(2)[symmetric] using z1z2s(4)
          by (metis length_0_conv list.exhaust_sel list.simps(3) ny z1z2s(1) z1z2s(2))
        have step_actTrans:"actTrans swp ((a, b) # y1y2s) = actTrans swp ((a,b)#(cmpTrans y1y2s x2, x2)# tl z1z2s)"
          unfolding actTrans.simps(2)[of swp a b] z1z2s(3)[symmetric] using z1z2s(4)
          by (metis length_0_conv list.exhaust_sel list.simps(3) ny z1z2s(1) z1z2s(3))
        have step0:"cmpTrans ((a, b) # y1y2s) x2  = cmpTrans [(a,b),(cmpTrans y1y2s x2, x2)] x2"
          unfolding step unfolding cmpTrans.simps
          using z1z2s(5) cmpTrans_support0 by fastforce
        have step1:"cmpTrans [(a,b),(cmpTrans y1y2s x2, x2)] x2 = x1"
          using step0 comp x1x2s by auto
        obtain a0 b0 where final:
          "cmpTrans [(a,b),(cmpTrans y1y2s x2, x2)] = cmpTrans [(x1,x2),(a0,b0)]"
          "actTrans swp [(a,b),(cmpTrans y1y2s x2, x2)] = actTrans swp [(x1,x2),(a0,b0)]"
          "x2 \<notin> {a0,b0}"
          using actTransTrans_cmpTrans_pair_push_left[OF step1 swp] by blast 
        show ?thesis
          apply(rule exI[of _ "(x1,x2) # (a0,b0) # tl z1z2s"], safe)
          subgoal by (simp add: ny z1z2s(1))
          subgoal using final(2) unfolding step_actTrans unfolding actTrans.simps by metis
          subgoal using final unfolding step unfolding cmpTrans.simps by (simp add: o_assoc)
          subgoal by simp
          subgoal using final z1z2s(5) by auto
          subgoal using final z1z2s(5) by auto
          done
      qed
      done
  qed
qed

(* Every finite permutation is the composition of a list of permutations: *)
lemma fsupp_ex_cmpTrans: 
assumes "fsupp \<sigma>" "bij \<sigma>"
shows "\<exists> z1z2s. \<sigma> = cmpTrans z1z2s"
  using assms
proof(induct "card {x. \<sigma> x \<noteq> x}" arbitrary: \<sigma> rule: less_induct)
  fix \<sigma>
  assume ih:"\<And>\<sigma>'. card {x. \<sigma>' x \<noteq> x} < card {x. \<sigma> x \<noteq> x} \<Longrightarrow>
                fsupp \<sigma>' \<Longrightarrow> bij \<sigma>' \<Longrightarrow> \<exists>z1z2s. \<sigma>' = cmpTrans z1z2s"
    and fsupp:"fsupp \<sigma>" and bij:"bij \<sigma>"
  show "\<exists>z1z2s. \<sigma> = cmpTrans z1z2s" apply (cases "card {x. \<sigma> x \<noteq> x}") 
    subgoal apply(rule exI[of _ "[]"], simp add: fsupp[unfolded fsupp_def]) by fastforce
    subgoal for n proof-
      assume succ:"card {x. \<sigma> x \<noteq> x} = Suc n"
      obtain x1 x2 where x1x2:"\<sigma> x2 = x1" "x1 \<noteq> x2"
        using succ by fastforce
      have supp':"{x. (cmpTrans [(x1,x2)] o \<sigma>) x \<noteq> x} \<subseteq> {x. \<sigma> x \<noteq> x}-{x2}"
        apply safe
        subgoal for x unfolding o_apply
          by (metis bij bij_is_inj cmpTrans_support injD 
              list.set(1) list.simps(15) prod.sel(1) prod.sel(2) singletonD x1x2(1) x1x2(2))
        subgoal unfolding o_apply x1x2 cmpTrans.simps using x1x2(2) by simp
        done
      obtain z1z2s' where z1z2s':"cmpTrans z1z2s' = cmpTrans [(x1,x2)] o \<sigma>"
        using ih[of "cmpTrans [(x1,x2)] o \<sigma>"] supp'
        by (smt bij bij_o card_Diff1_less card_eq_0_iff cmpTrans.simps(1) 
            cmpTrans.simps(2) bij_cmpTrans finite_Diff fsupp fsupp_id fsupp_o 
            fsupp_upd less_le less_trans 
            mem_Collect_eq psubset_card_mono succ x1x2(1) x1x2(2) zero_less_Suc)
      show "\<exists>z1z2s. \<sigma> = cmpTrans z1z2s"
        by(rule exI[of _ "(x1,x2) # z1z2s'"], auto simp add: z1z2s')
    qed
    done 
qed

(* Need a sharper version, that assumes nonredundancy: *)

lemma fsupp_ex_cmpTrans_strong: 
assumes "fsupp \<sigma>" "bij \<sigma>"
shows "\<exists> z1z2s. \<sigma> = cmpTrans z1z2s \<and> {x. \<sigma> x \<noteq> x} = fst ` (set z1z2s) \<union> snd ` (set z1z2s)"
using assms proof(induct "card {x. \<sigma> x \<noteq> x}" arbitrary: \<sigma> rule: less_induct)
  case less note ih = less(1) and fsupp = less(2) and bij = less(3)
  show ?case proof (cases "card {x. \<sigma> x \<noteq> x}") 
    case 0 thus ?thesis 
    apply - apply(rule exI[of _ "[]"], simp add: fsupp[unfolded fsupp_def]) by fastforce
  next
    case (Suc n) 
    then obtain x1 x2 where x1x2: "\<sigma> x2 = x1" "x1 \<noteq> x2" by fastforce
    have supp': "{x. (cmpTrans [(x1,x2)] o \<sigma>) x \<noteq> x} \<subseteq> {x. \<sigma> x \<noteq> x} - {x2}"
    apply safe
      subgoal for x unfolding o_apply
      by (metis bij bij_is_inj cmpTrans_support injD 
           list.set(1) list.simps(15) prod.sel(1) prod.sel(2) singletonD x1x2(1) x1x2(2))
      subgoal unfolding o_apply x1x2 cmpTrans.simps using x1x2(2) by simp .
      obtain z1z2s' where z1z2s':"cmpTrans z1z2s' = cmpTrans [(x1,x2)] o \<sigma>"
      and 0: "{x. (cmpTrans [(x1, x2)] \<circ> \<sigma>) x \<noteq> x} = fst ` set z1z2s' \<union> snd ` set z1z2s'"
        using ih[of "cmpTrans [(x1,x2)] o \<sigma>"] supp'
        by (smt bij bij_o card_Diff1_less card_eq_0_iff cmpTrans.simps(1) 
            cmpTrans.simps(2) bij_cmpTrans finite_Diff fsupp fsupp_id fsupp_o 
            fsupp_upd less_le less_trans 
            mem_Collect_eq psubset_card_mono Suc x1x2(1) x1x2(2) zero_less_Suc)
    show ?thesis
        apply(rule exI[of _ "(x1,x2) # z1z2s'"], auto simp add: z1z2s') 
        apply (smt (z3) "0" UnE cmpTrans_support_im list.set(1) list.set(2) mem_Collect_eq o_apply 
          prod.sel(1) prod.sel(2) singletonD)
         apply (auto simp add: x1x2) 
        apply (metis bij bij_is_inj injD x1x2(1) x1x2(2))
       using "0" insert_absorb supp' by auto
  qed
qed

lemma auxx: "x12 # z1z2s' = h1 @ h2 \<Longrightarrow> (h1 = [] \<and> h2 = x12 # z1z2s') \<or> (\<exists>h1'. h1 = x12 # h1' \<and> z1z2s' = h1' @ h2)"
by (metis Cons_eq_append_conv)

(* *)
definition nonredundant where 
"nonredundant z1z2s \<equiv> 
 (\<forall> h1 h2. z1z2s = h1 @ h2 \<longrightarrow> {x. cmpTrans h2 x \<noteq> x} = fst ` (set h2) \<union> snd ` (set h2))"

lemma nonredundant_append: 
"nonredundant (h1 @ h2) \<Longrightarrow> nonredundant h2"
unfolding nonredundant_def by simp

lemma nonredundant_Cons: 
"nonredundant (z1z2 # h) \<Longrightarrow> nonredundant h"
unfolding nonredundant_def by simp

lemma nonredundant_cmpTrans: 
"nonredundant h \<Longrightarrow> {x. cmpTrans h x \<noteq> x} = fst ` (set h) \<union> snd ` (set h)"
unfolding nonredundant_def by simp

(* *)

lemma fsupp_ex_cmpTrans_even_stronger: 
assumes "fsupp \<sigma>" "bij \<sigma>"
shows "\<exists> z1z2s. \<sigma> = cmpTrans z1z2s \<and> nonredundant z1z2s"
using assms proof(induct "card {x. \<sigma> x \<noteq> x}" arbitrary: \<sigma> rule: less_induct)
  case less note ih = less(1) and fsupp = less(2) and bij = less(3)
  show ?case proof (cases "card {x. \<sigma> x \<noteq> x}") 
    case 0 thus ?thesis 
    by (intro exI[of _ "[]"], fastforce simp add: fsupp[unfolded fsupp_def] nonredundant_def) 
  next
    case (Suc n) 
    then obtain x1 x2 where x1x2: "\<sigma> x2 = x1" "x1 \<noteq> x2" by fastforce
    have supp': "{x. (cmpTrans [(x1,x2)] o \<sigma>) x \<noteq> x} \<subseteq> {x. \<sigma> x \<noteq> x} - {x2}"
    apply safe
      subgoal for x unfolding o_apply
      by (metis bij bij_is_inj cmpTrans_support injD 
           list.set(1) list.simps(15) prod.sel(1) prod.sel(2) singletonD x1x2(1) x1x2(2))
      subgoal unfolding o_apply x1x2 cmpTrans.simps using x1x2(2) by simp .
      obtain z1z2s' where z1z2s':"cmpTrans z1z2s' = cmpTrans [(x1,x2)] o \<sigma>"
      and 0: "cmpTrans [(x1, x2)] \<circ> \<sigma> = cmpTrans z1z2s' \<and> nonredundant z1z2s'"
        using ih[of "cmpTrans [(x1,x2)] o \<sigma>"] supp'          
        by (smt (verit, ccfv_threshold) Diff_empty Suc bij bij_cmpTrans bij_o card.infinite 
           card_Diff1_less card_mono cmpTrans.simps(1) cmpTrans.simps(2) finite_Diff_insert 
           fsupp fsupp_id fsupp_o fsupp_upd linorder_not_le mem_Collect_eq nat.simps(3) 
           order_less_le_trans x1x2(1) x1x2(2)) 
    show ?thesis unfolding nonredundant_def
    apply(rule exI[of _ "(x1,x2) # z1z2s'"], auto simp add: z1z2s') 
      subgoal using cmpTrans_support by blast 
      subgoal for h1 h2 x y  apply(drule auxx) apply (cases h1)
        subgoal apply simp apply(cases "cmpTrans z1z2s' x = x2")
          subgoal by (metis (mono_tags, lifting) "0" comp_def comp_eq_id_dest cmpTrans.simps(1) 
          cmpTrans.simps(2) cmpTrans_diff_implies_diff_im fun_upd_same id_swapTwice x1x2) 
          subgoal apply(cases "cmpTrans z1z2s' x = x2") 
            subgoal by simp
            subgoal apply(cases "cmpTrans z1z2s' x = x1") 
              subgoal apply simp by (metis comp_apply cmpTrans_pair_fix x1x2(1) z1z2s')
              subgoal apply simp using "0" Un_iff append_Nil imageI mem_Collect_eq prod.sel(1) 
              unfolding nonredundant_def by (metis (mono_tags, lifting)) . . .              
        subgoal apply simp 
          by (metis (mono_tags, lifting) "0" nonredundant_def Un_iff fst_eqD imageI mem_Collect_eq) .
      subgoal for h1 h2 x y  apply(drule auxx) apply (cases h1)
        subgoal apply simp apply(cases "cmpTrans z1z2s' y = x2")
          subgoal by (metis (mono_tags, lifting) "0" comp_def comp_eq_id_dest cmpTrans.simps(1) 
          cmpTrans.simps(2) cmpTrans_diff_implies_diff_im fun_upd_same id_swapTwice x1x2) 
          subgoal apply(cases "cmpTrans z1z2s' y = x2") 
            subgoal by simp
            subgoal apply(cases "cmpTrans z1z2s' y = x1") 
              subgoal apply simp by (metis comp_apply cmpTrans_pair_fix x1x2(1) z1z2s')
              subgoal apply simp using "0" nonredundant_def Un_iff append_Nil imageI mem_Collect_eq prod.sel(2) 
               by (metis (mono_tags, lifting)) . . .  
        subgoal apply simp 
        	by (metis (mono_tags, lifting) "0" nonredundant_def  UnCI image_eqI mem_Collect_eq prod.sel(2)) . .    
  qed
qed

(* decomposition as transpositions: *)
definition asTrans :: "(var \<Rightarrow> var) \<Rightarrow> (var \<times> var) list" where 
"asTrans \<sigma> \<equiv> SOME z1z2s. \<sigma> = cmpTrans z1z2s"

lemma cmpTrans_asTrans: "fsupp \<sigma> \<Longrightarrow> bij \<sigma> \<Longrightarrow> cmpTrans (asTrans \<sigma>) = \<sigma>"
  by (metis (full_types) asTrans_def fsupp_ex_cmpTrans someI_ex)


(* For swapping algebras, cmpTrans uniquely determines the actTransion *)
lemma cmpTrans_actTransTrans_unique:
assumes swp:"nswapping swp"
and compeq:"cmpTrans z1z2s = cmpTrans z1z2s'" 
shows "actTrans swp z1z2s = actTrans swp z1z2s'"
  using compeq
proof(induct "length z1z2s + length z1z2s'"  arbitrary: z1z2s z1z2s' rule: less_induct)
  fix z1z2s z1z2s'  
  assume ih:"\<And> x1x2s x1x2s'.
           length x1x2s + length x1x2s' < length z1z2s + length z1z2s' \<Longrightarrow>
           cmpTrans x1x2s = cmpTrans x1x2s' \<Longrightarrow> actTrans swp x1x2s = actTrans swp x1x2s'"
    and comp:"cmpTrans z1z2s = cmpTrans z1z2s'"
  show "actTrans swp z1z2s = actTrans swp z1z2s'"
  proof(cases "cmpTrans z1z2s = id")
    case True
    have True':"cmpTrans z1z2s' = id" using comp True by argo
    show ?thesis
    proof(cases "z1z2s = []")
      assume em:"z1z2s = []"
      show "actTrans swp z1z2s = actTrans swp z1z2s'"
        apply(cases "z1z2s' = []", simp add: em)
      proof-
        assume notem:"z1z2s' \<noteq> []"
        obtain a b x1x2s' where abtl:"z1z2s' = (a,b) # x1x2s'" using notem cmpTrans.cases by blast
        have step_comp:"cmpTrans [(a,b)] = cmpTrans x1x2s'" using comp unfolding em abtl
          unfolding cmpTrans.simps  by (metis id_comp id_swapTwice o_assoc)
        show "actTrans swp z1z2s = actTrans swp z1z2s'"
          apply(cases "a = b")
          subgoal unfolding em abtl apply simp unfolding actTrans.simps(2)
            swp[unfolded nswapping_def, THEN conjunct1, rule_format, of _ b ]
            apply(intro ih) unfolding abtl em step_comp[symmetric] by simp_all
          subgoal proof-
            assume anb:"a \<noteq> b"
            have triv:"x1x2s' \<noteq> []" using step_comp anb unfolding cmpTrans.simps 
              using cmpTrans.simps(1) by (metis comp_id fun_upd_eqD fun_upd_id_same)
            have triv2:"cmpTrans x1x2s' b = a" unfolding step_comp[symmetric]
              unfolding cmpTrans.simps by simp
            have triv3:"\<exists>p. p \<in> set x1x2s' \<and> (b = fst p \<or> b = snd p)"
              using anb cmpTrans_support triv2 by blast
            obtain y1y2s' where y1y2s':
              "length x1x2s' = length ((a,b) # y1y2s')"
              "cmpTrans x1x2s' = cmpTrans ((a,b) # y1y2s')"
              "actTrans swp x1x2s' = actTrans swp ((a,b) # y1y2s')"
              using actTransTrans_cmpTrans_push_left[OF triv swp triv3 triv2]
              by (metis length_0_conv list.exhaust_sel triv)
            have last:"cmpTrans [] = cmpTrans y1y2s'"
              using step_comp unfolding y1y2s' 
              unfolding cmpTrans.simps
              by (metis True' abtl comp_assoc comp_id cmpTrans.simps(2) fun.map_id y1y2s'(2))
            show "actTrans swp z1z2s = actTrans swp z1z2s'"
              unfolding abtl em actTrans.simps(2) y1y2s' unfolding
              swp[unfolded nswapping_def, THEN conjunct2, THEN conjunct1, rule_format, of _ a b]
              apply(rule ih[OF _ last]) unfolding em abtl using y1y2s'(1) by simp
          qed
          done
      qed
    next
      assume notem:"z1z2s \<noteq> []"
      obtain a b x1x2s where abtl:"z1z2s = (a,b) # x1x2s" using notem cmpTrans.cases by blast
      have step_comp:"cmpTrans [(a,b)] = cmpTrans x1x2s" using True unfolding abtl
        cmpTrans.simps by (metis comp_assoc id_comp id_swapTwice)
      show "actTrans swp z1z2s = actTrans swp z1z2s'"
        apply(cases "a = b")
        subgoal unfolding abtl apply simp unfolding actTrans.simps(2)
            swp[unfolded nswapping_def, THEN conjunct1, rule_format, of _ b ]
          apply(intro ih) unfolding abtl step_comp[symmetric] 
          by (simp_all add:True comp[symmetric])
        subgoal proof-
          assume anb:"a \<noteq> b"
          have triv:"x1x2s \<noteq> []" using step_comp anb unfolding cmpTrans.simps 
            using cmpTrans.simps(1) by (metis comp_id fun_upd_eqD fun_upd_id_same)
          have triv2:"cmpTrans x1x2s b = a" unfolding step_comp[symmetric]
            unfolding cmpTrans.simps by simp
          have triv3:"\<exists>p. p \<in> set x1x2s \<and> (b = fst p \<or> b = snd p)"
            using anb cmpTrans_support triv2 by blast
          obtain y1y2s where y1y2s:
            "length x1x2s = length ((a,b) # y1y2s)"
            "cmpTrans x1x2s = cmpTrans ((a,b) # y1y2s)"
            "actTrans swp x1x2s = actTrans swp ((a,b) # y1y2s)"
            using actTransTrans_cmpTrans_push_left[OF triv swp triv3 triv2]
          by (metis length_0_conv list.exhaust_sel triv)
          have last:"cmpTrans [] = cmpTrans y1y2s"
            using step_comp unfolding y1y2s
            unfolding cmpTrans.simps
            by (metis True abtl comp_assoc comp_id cmpTrans.simps(2) fun.map_id y1y2s(2))
          show "actTrans swp z1z2s = actTrans swp z1z2s'"
            unfolding abtl actTrans.simps(2) y1y2s
              swp[unfolded nswapping_def, THEN conjunct2, THEN conjunct1, rule_format, of _ a b]
            apply(rule ih) unfolding abtl using y1y2s(1) apply simp using True comp last by force
        qed
        done
    qed
  next
    case False
    have nem:"z1z2s \<noteq> []" using False cmpTrans.simps(1) by blast
    have nem':"z1z2s' \<noteq> []" using False unfolding comp using cmpTrans.simps(1) by blast
    obtain x1 x2 where x1x2:"cmpTrans z1z2s x2 = x1""x1 \<noteq> x2" 
      using False by fastforce
    have hp:"\<exists> p. p \<in> set z1z2s \<and> (x2 = fst p \<or> x2 = snd p)"
      using x1x2 cmpTrans_support by blast
    have x1x2':"cmpTrans z1z2s' x2 = x1"
      using x1x2 unfolding comp by simp
    have hp':"\<exists> p. p \<in> set z1z2s' \<and> (x2 = fst p \<or> x2 = snd p)"
      using x1x2' x1x2(2) cmpTrans_support by blast
    obtain x1x2s where x1x2s:"length ((x1,x2) # x1x2s) = length z1z2s"
      "actTrans swp ((x1,x2) # x1x2s) = actTrans swp z1z2s"
      "cmpTrans ((x1,x2) # x1x2s) = cmpTrans z1z2s" 
      using actTransTrans_cmpTrans_push_left[OF nem swp hp x1x2(1)]
      by (metis length_0_conv list.exhaust_sel nem)
    obtain x1x2s' where x1x2s':"length ((x1,x2) # x1x2s') = length z1z2s'"
      "actTrans swp ((x1,x2) # x1x2s') = actTrans swp z1z2s'"
      "cmpTrans ((x1,x2) # x1x2s') = cmpTrans z1z2s'" 
      using actTransTrans_cmpTrans_push_left[OF nem' swp hp' x1x2']
      by (metis length_0_conv list.exhaust_sel nem')
    have fromih:"actTrans swp x1x2s = actTrans swp x1x2s'"
      apply(intro ih) using x1x2s x1x2s' apply simp
      by (metis comp comp_assoc cmpTrans.simps(2) fun.map_id id_swapTwice x1x2s'(3) x1x2s(3))
    show ?thesis
      unfolding x1x2s(2)[symmetric] x1x2s'(2)[symmetric] actTrans.simps 
      using fromih by simp
  qed 
qed

lemma cmpTrans_actTransTrans_unique2:
assumes "nswapping swp"
and "cmpTrans z1z2s = cmpTrans z1z2s'" 
shows "actTrans swp z1z2s c = actTrans swp z1z2s' c"
using cmpTrans_actTransTrans_unique[OF assms] by auto

definition toPerm :: "('c \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> (var \<Rightarrow> var) \<Rightarrow> 'c)" where 
"toPerm swp c \<sigma> \<equiv> actTrans swp (asTrans \<sigma>) c"

theorem permut_toPerm: 
assumes "nswapping swp"
shows "permut (toPerm swp)"
unfolding permut_def proof safe
  fix c 
  have 0: "actTrans swp (asTrans id) = actTrans swp []" 
  using assms by (intro cmpTrans_actTransTrans_unique) (auto simp: cmpTrans_asTrans)
  show "toPerm swp c id = c" unfolding toPerm_def 0 by simp
next
  fix c \<sigma> \<tau> assume 0: "bij \<sigma>" "fsupp \<sigma>" "bij \<tau>" "fsupp \<tau>"  
  have 1: "actTrans swp (asTrans \<tau> @ asTrans \<sigma>) = actTrans swp (asTrans (\<tau> \<circ> \<sigma>))" 
  using assms 
  by (intro cmpTrans_actTransTrans_unique) (auto simp: 0 fun_eq_iff cmpTrans_append cmpTrans_asTrans fsupp_o bij_o) 
  show "toPerm swp (toPerm swp c \<sigma>) \<tau> = toPerm swp c (\<tau> \<circ> \<sigma>)" 
  unfolding toPerm_def unfolding actTransTrans_append[symmetric] 1 .. 
qed


lemma fsupp_cmpTrans[simp,intro!]: "fsupp (cmpTrans z1z2s)" 
proof(induct z1z2s rule: list_induct_Pair)
  case Nil
  then show ?case by (auto simp add: fsupp_def)
next
  case (Cons z1 z2 z1z2s)
  have "{x. cmpTrans ((z1, z2) # z1z2s) x \<noteq> x} \<subseteq> 
        {x. cmpTrans z1z2s x \<noteq> x} \<union> {z1,z2}" by auto
  with Cons show ?case unfolding fsupp_def  
  	by (meson finite.emptyI finite.insertI finite_UnI finite_subset)
qed 

(* End results: *)
thm fsupp_cmpTrans bij_cmpTrans
thm permut_toPerm
thm nswapping_toSwp 


(* Some properties of swapping and permutation on terms: *)

definition perm :: "trm \<Rightarrow> (var \<Rightarrow> var) \<Rightarrow> trm" 
where "perm = toPerm swap"

lemma nswapping_swap: "nswapping swap"
unfolding nswapping_def using swap_cmpTrans by auto 

lemma toPerm_swap[simp]: "toPerm swap t (id(z1 := z2, z2 := z1)) = swap t z1 z2"
unfolding toPerm_def 
	by (metis actTrans.simps(1) actTrans.simps(2) bij_cmpTrans comp_id cmpTrans.simps(1) cmpTrans.simps(2) 
    cmpTrans_actTransTrans_unique cmpTrans_asTrans fsupp_cmpTrans nswapping_swap) 

lemma perm_swap[simp]: "perm t (id(z1 := z2, z2 := z1)) = swap t z1 z2"
by (simp add: perm_def)

lemma perm_id[simp]: "perm t id = t" 
unfolding perm_def by (metis fun_upd_id_same swap_id toPerm_swap)

lemma perm_id'[simp]: "perm t (\<lambda>x. x) = t"
	by (metis eq_id_iff perm_id)

lemma perm_comp: "fsupp pi \<Longrightarrow> bij pi \<Longrightarrow> fsupp pi' \<Longrightarrow> bij pi' \<Longrightarrow> 
perm t (pi o pi') = perm (perm t pi') pi"
unfolding perm_def 
by (metis nswapping_swap permut_def permut_toPerm)

find_theorems toPerm cmpTrans

(* *)
lemma toPerm_toSwp_cmpTrans: 
assumes 1: "permut prm"  
shows "toPerm (toSwp prm) a (cmpTrans z1z2s) = prm a (cmpTrans z1z2s)"
proof(induct z1z2s arbitrary: a rule: list_induct_Pair)
  case Nil
  then show ?case  
  by simp (metis assms comp_id fun.map_ident nswapping_toSwp permut_def permut_toPerm)
next
  case (Cons z1 z2 z1z2s)
  then show ?case 
  	by (smt (verit, ccfv_threshold) actTrans.simps(2) assms bij_cmpTrans bij_id_upd2 cmpTrans.simps(2) 
     cmpTrans_actTransTrans_unique2 cmpTrans_asTrans fsupp_cmpTrans fsupp_id fsupp_upd nswapping_toSwp 
     permut_def toPerm_def toSwp_def)   
qed

theorem toPerm_toSwp: 
assumes 1: "permut prm" and 2: "fsupp \<sigma>" "bij \<sigma>"
shows "toPerm (toSwp prm) a \<sigma> = prm a \<sigma>"
by (metis "1" assms(2) assms(3) cmpTrans_asTrans toPerm_toSwp_cmpTrans)

lemma toPerm_id_update_eq: 
assumes "nswapping swp"
shows "toPerm swp c (id(z1 := z2, z2 := z1)) = swp c z1 z2"
by (metis (no_types, opaque_lifting) actTrans.simps(1) actTrans.simps(2) assms bij_cmpTrans comp_id 
cmpTrans.simps(1) cmpTrans.simps(2) cmpTrans_actTransTrans_unique cmpTrans_asTrans fsupp_cmpTrans toPerm_def)

theorem toSwp_toPerm: 
assumes "nswapping swp"
shows "toSwp (toPerm swp) = swp"
unfolding toSwp_def fun_eq_iff toPerm_id_update_eq[OF assms] by simp


(* Extension to include a free-variable-like operator: *)

(* This predicate is called "swapping" in the paper 
"Recursive Function Definition for Types with Binders" by Michael Norrish, 
where what we call the swap/free recursor was introduced: *)

definition swappingFvars :: "('c \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> var set) \<Rightarrow> bool" where 
"swappingFvars swp fvars \<equiv>
  (\<forall> c x. swp c x x = c) \<and> 
  (\<forall> c x y. swp (swp c x y) x y = c) \<and> 
  (\<forall> c x y. x \<notin> fvars c \<and> y \<notin> fvars c \<longrightarrow> swp c x y = c) \<and>
  (\<forall> x c z1 z2. x \<in> fvars (swp c z1 z2) \<longleftrightarrow> sw x z1 z2 \<in> fvars c)"

lemma nswapping_imp_swappingFvars_def2:   
"nswapping swp \<and> 
  (\<forall> c x y. x \<notin> fvars c \<and> y \<notin> fvars c \<longrightarrow> swp c x y = c) \<and>
  (\<forall> x c z1 z2. x \<in> fvars (swp c z1 z2) \<longleftrightarrow> sw x z1 z2 \<in> fvars c)
 \<Longrightarrow> swappingFvars swp fvars"
unfolding nswapping_def swappingFvars_def by auto

(* Equivalent version of the above using freshness instead of swapping: *)
definition swapping :: "('c \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'c) \<Rightarrow> (var \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> bool" where 
"swapping swp frs \<equiv>
  (\<forall> c x. swp c x x = c) \<and> 
  (\<forall> c x y. swp (swp c x y) x y = c) \<and> 
  (\<forall> c x y. frs x c \<and> frs y c \<longrightarrow> swp c x y = c) \<and>
  (\<forall> x c z1 z2. frs x (swp c z1 z2) \<longleftrightarrow> frs (sw x z1 z2) c)"


definition permutFvars :: "('c \<Rightarrow> (var \<Rightarrow> var) \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> var set) \<Rightarrow> bool" where 
"permutFvars prm fvars \<equiv>
  (\<forall>c. prm c id = c) \<and> 
  (\<forall>c \<sigma> \<tau>. bij \<sigma> \<and> fsupp \<sigma> \<and> bij \<tau> \<and> fsupp \<tau> \<longrightarrow> prm (prm c \<sigma>) \<tau> = prm c (\<tau> \<circ> \<sigma>)) \<and> 
  (\<forall> c \<sigma>. bij \<sigma> \<and> fsupp \<sigma> \<and> (\<forall>x \<in> fvars c. \<sigma> x = x) \<longrightarrow> prm c \<sigma> = c) \<and>
  (\<forall> x c \<sigma>. bij \<sigma> \<and> fsupp \<sigma> \<longrightarrow> (x \<in> fvars (prm c \<sigma>) \<longleftrightarrow> inv \<sigma> x \<in> fvars c))"

lemma permutFvars_def2: 
"permutFvars prm fvars \<longleftrightarrow> 
  permut prm \<and>  
  (\<forall> c \<sigma>. bij \<sigma> \<and> fsupp \<sigma> \<and> (\<forall>x \<in> fvars c. \<sigma> x = x) \<longrightarrow> prm c \<sigma> = c) \<and>
  (\<forall> x c \<sigma>. bij \<sigma> \<and> fsupp \<sigma> \<longrightarrow> (x \<in> fvars (prm c \<sigma>) \<longleftrightarrow> inv \<sigma> x \<in> fvars c))"
unfolding permutFvars_def permut_def by auto

lemma permutFvars_permut: "permutFvars prm fvars \<Longrightarrow> permut prm"
unfolding permutFvars_def2 by auto

lemma permutPmFr: "permutFvars prm fvars \<Longrightarrow> 
 bij \<sigma> \<Longrightarrow> fsupp \<sigma> \<Longrightarrow> (\<forall>x \<in> fvars c. \<sigma> x = x) \<Longrightarrow> prm c \<sigma> = c"
unfolding permutFvars_def2 by auto

lemma permutFrPm: "permutFvars prm fvars \<Longrightarrow> 
 bij \<sigma> \<Longrightarrow> fsupp \<sigma> \<Longrightarrow> bij \<sigma> \<Longrightarrow> fsupp \<sigma> \<Longrightarrow> (x \<in> fvars (prm c \<sigma>) \<longleftrightarrow> inv \<sigma> x \<in> fvars c)"
unfolding permutFvars_def2 by auto

(* *)
theorem swappingFvars_toSwp: 
assumes "permutFvars prm fvars"
shows "swappingFvars (toSwp prm) fvars"
apply(rule nswapping_imp_swappingFvars_def2)
using assms unfolding permutFvars_def2 apply safe
  subgoal using nswapping_toSwp by blast
  subgoal for c x y apply(erule allE[of _ c], erule allE[of _ "id(x:=y,y:=x)"])
  unfolding toSwp_def by auto
  subgoal for x c z1 z2 apply(erule allE[of _ x], elim allE[of _ c], 
      elim allE[of _ "id(z1:=z2,z2:=z1)"]) unfolding toSwp_def sw_def 
    by (metis (no_types, lifting) bij_id_upd2 fsupp_id fsupp_upd fun_upd_other 
    fun_upd_same id_apply id_swapTwice inv_unique_comp)
  subgoal for x c z1 z2 apply(erule allE[of _ x], elim allE[of _ c], 
      elim allE[of _ "id(z1:=z2,z2:=z1)"]) unfolding toSwp_def sw_def 
    by (metis bij_id_upd2 eq_id_iff fsupp_id fsupp_upd fun_upd_apply 
    id_swapTwice inv_unique_comp) .


 
lemma toPerm_cong_id_cmpTrans: 
assumes s: "swappingFvars swp fvars" and n: "nswapping swp"
and 2: "\<forall>x\<in>fvars c. (cmpTrans z1z2s) x = x"
and 3: "nonredundant z1z2s"
shows "toPerm swp c (cmpTrans z1z2s) = c"
proof-
  have "permut (toPerm swp)"  
  	by (simp add: n permut_toPerm)
  hence aux:  "\<And>c. toPerm swp c id = c"
   "\<And>c \<sigma> \<tau>. bij \<sigma> \<Longrightarrow> fsupp \<sigma> \<Longrightarrow> bij \<tau> \<and> fsupp \<tau> \<Longrightarrow> 
    toPerm swp c (\<tau> \<circ> \<sigma>) = toPerm swp (toPerm swp c \<sigma>) \<tau>" 
  unfolding permut_def by auto
  show ?thesis
  using 2 3 proof(induction z1z2s arbitrary: c rule: list_induct_Pair)
    case Nil
    then show ?case    
  	by simp (metis fun.map_ident n o_id permut_def permut_toPerm)
  next
    case (Cons z1 z2 z1z2s)
    have nr: "nonredundant z1z2s"  
    	using Cons.prems(2) nonredundant_Cons by blast
     have 0: \<open>\<And>z2 z1 c. toPerm swp c (id(z1 := z2, z2 := z1)) = swp c z1 z2\<close> 
     by (simp add: n toPerm_id_update_eq)  

    show ?case  unfolding cmpTrans.simps(2) apply(subst aux(2))
    subgoal by auto subgoal by auto subgoal by auto 
    subgoal unfolding toPerm_id_update_eq[OF n] apply(subst Cons.IH)
      subgoal using Cons(2,3)  apply - apply(drule nonredundant_cmpTrans) 
      by simp (smt (verit, best) fun_upd_apply id_apply insert_iff mem_Collect_eq)
      subgoal using Cons(3) nonredundant_Cons by blast 
      subgoal by (smt (verit) Cons.prems(1) 0 \<open>\<forall>x\<in>fvars c. cmpTrans z1z2s x = x\<close> aux(1) 
         comp_def comp_id cmpTrans.simps(2) fun_upd_id_same fun_upd_other fun_upd_same 
         fun_upd_triv fun_upd_twist id_apply id_comp id_swapTwice 
         prod.sel(1) rewriteR_comp_comp s swappingFvars_def type_copy_map_cong0) . .  
  qed
qed

lemma toPerm_cong_id: 
assumes s: "swappingFvars swp fvars" and n: "nswapping swp"
and 1: "bij \<sigma>" "fsupp \<sigma>" and 2: "\<forall>x\<in>fvars c. \<sigma> x = x"
shows "toPerm swp c \<sigma> = c"
using assms fsupp_ex_cmpTrans_even_stronger n toPerm_cong_id_cmpTrans by fastforce

lemma inv_id_upd[simp]: 
"inv (id(z1 := z2, z2 := z1)) = id(z1 := z2, z2 := z1)"
unfolding fun_eq_iff by (metis id_swapTwice inv_unique_comp) 


lemma toPerm_free_cmpTrans: 
assumes s: "swappingFvars swp fvars" and n: "nswapping swp"
shows "x \<in> fvars (toPerm swp c (cmpTrans z1z2s)) \<longleftrightarrow> inv (cmpTrans z1z2s) x \<in> fvars c"
proof-
  have "permut (toPerm swp)"  
  	by (simp add: n permut_toPerm)
  hence aux:  "\<And>c. toPerm swp c id = c"
   "\<And>c \<sigma> \<tau>. bij \<sigma> \<Longrightarrow> fsupp \<sigma> \<Longrightarrow> bij \<tau> \<Longrightarrow> fsupp \<tau> \<Longrightarrow> 
    toPerm swp c (\<tau> \<circ> \<sigma>) = toPerm swp (toPerm swp c \<sigma>) \<tau>" 
  unfolding permut_def by auto
  show ?thesis using bij_cmpTrans[of z1z2s] fsupp_cmpTrans[of z1z2s] 
  proof(induction z1z2s arbitrary: c x rule: list_induct_Pair)
    case Nil
    then show ?case using n s toPerm_cong_id by fastforce
  next
    case (Cons z1 z2 z1z2s)
    show ?case unfolding cmpTrans.simps apply(subst aux(2))
      subgoal by auto subgoal by auto subgoal by auto  subgoal by auto  
      subgoal unfolding toPerm_id_update_eq[OF n]
      unfolding s[unfolded swappingFvars_def, THEN conjunct2, THEN conjunct2, 
          THEN conjunct2, rule_format]
      apply(subst Cons.IH)
        subgoal by auto subgoal by auto
        subgoal apply(subst o_inv_distrib) by auto . .
  qed 
qed

lemma toPerm_free: 
assumes s: "swappingFvars swp fvars" and n: "nswapping swp"
and 1: "bij \<sigma>" "fsupp \<sigma>" 
shows "x \<in> fvars (toPerm swp c \<sigma>) \<longleftrightarrow> inv \<sigma> x \<in> fvars c"
by (metis assms cmpTrans_asTrans toPerm_free_cmpTrans)

theorem permutFvars_toPerm: 
assumes s: "swappingFvars swp fvars" and n: "nswapping swp"
shows "permutFvars (toPerm swp) fvars"
unfolding permutFvars_def2 
using assms toPerm_cong_id[OF assms] toPerm_free[OF assms] permut_toPerm by auto


(******)
(* perm vs swap *)

lemma permut_perm: "permut perm"
unfolding permut_def using perm_id perm_comp by auto

(* perm versus the term constructors *)

lemma perm_Vr_cmpTrans: 
"perm (Vr x) (cmpTrans z1z2s) = Vr (cmpTrans z1z2s x)"
apply(induct z1z2s rule: list_induct_Pair)  
  subgoal by auto
  subgoal for z1 z2 z1z2s  
  unfolding cmpTrans.simps apply(subst perm_comp) by auto .

lemma perm_Vr[simp]: 
assumes "fsupp \<sigma>" "bij \<sigma>"
shows "perm (Vr x) \<sigma> = Vr (\<sigma> x)"
using assms fsupp_ex_cmpTrans perm_Vr_cmpTrans by blast

lemma perm_Ap_cmpTrans: 
"perm (Ap t1 t2) (cmpTrans z1z2s) = Ap (perm t1 (cmpTrans z1z2s)) (perm t2 (cmpTrans z1z2s))"
apply(induct z1z2s rule: list_induct_Pair) 
  subgoal by auto
  subgoal for z1 z2 z1z2s  
  unfolding cmpTrans.simps apply(subst perm_comp) by (auto simp: perm_comp) . 
 
lemma perm_Ap[simp]: 
assumes "fsupp \<sigma>" "bij \<sigma>"
shows "perm (Ap t1 t2) \<sigma> = Ap (perm t1 \<sigma>) (perm t2 \<sigma>)"
using assms fsupp_ex_cmpTrans perm_Ap_cmpTrans by blast

lemma perm_Lm_cmpTrans: 
"perm (Lm x t) (cmpTrans z1z2s) = Lm (cmpTrans z1z2s x) (perm t (cmpTrans z1z2s))"
apply(induct z1z2s rule: list_induct_Pair) 
  subgoal by auto
  subgoal for z1 z2 z1z2s  
  unfolding cmpTrans.simps apply(subst perm_comp) by (auto simp: perm_comp) . 

lemma perm_Lm[simp]: 
assumes "fsupp \<sigma>" "bij \<sigma>"
shows "perm (Lm x t) \<sigma> = Lm (\<sigma> x) (perm t \<sigma>)"
using assms fsupp_ex_cmpTrans perm_Lm_cmpTrans by blast

definition nswappingFvars where 
"nswappingFvars swp fvars \<equiv>
 (\<forall>c x. swp c x x = c) \<and>
 (\<forall>c x y. swp (swp c x y) x y = c) \<and>
 (\<forall>x y c z1 z2. swp (swp c x y) z1 z2 = swp (swp c z1 z2) (sw x z1 z2) (sw y z1 z2)) \<and> 
 (\<forall>c x y. x \<notin> fvars c \<and> y \<notin> fvars c \<longrightarrow> swp c x y = c) \<and>
 (\<forall>x c z1 z2. (x \<in> fvars (swp c z1 z2)) = (sw x z1 z2 \<in> fvars c))"

lemma nswappingFvars_iff_swappingFvars_nswapping:
"nswappingFvars swp fvars \<longleftrightarrow> swappingFvars swp fvars \<and> nswapping swp"
unfolding nswappingFvars_def nswapping_def swappingFvars_def by auto

 
(* For the "co" world, we need the fully symmetric relationship 
between swapping and permutation, so we need stronger axiomatization 
of swapping that is able to produce well-behaved permutations.
*)

proposition nswappingFvars_toSwp: 
"permutFvars prm fvars \<Longrightarrow> nswappingFvars (toSwp prm) fvars"
unfolding nswappingFvars_iff_swappingFvars_nswapping
using nswapping_toSwp swappingFvars_toSwp permutFvars_permut by blast

proposition permutFvars_toPerm_nswappingFvars: 
"nswappingFvars swp fvars \<Longrightarrow> permutFvars (toPerm swp) fvars"
by (simp add: nswappingFvars_iff_swappingFvars_nswapping permutFvars_toPerm)


(* Higher granularity of the concepts, distinguishing between the 
two fresh-swapping or fresh-permutation axioms *)

definition "swappingSwFr swp fr \<equiv> \<forall>c x y. fr x c \<and> fr y c \<longrightarrow> swp c x y = c"
definition "swappingFrSw swp fr \<equiv> \<forall>x c z1 z2. fr x (swp c z1 z2) \<longleftrightarrow> fr (sw x z1 z2) c"

definition "nswappingFresh swp fr \<equiv> nswapping swp \<and> 
  swappingSwFr swp fr \<and>
  swappingFrSw swp fr"

lemma nswappingFresh_nswapping: "nswappingFresh swp fr \<Longrightarrow> nswapping swp"
unfolding nswappingFresh_def by auto

lemma nswappingFresh_swappingSwFr: 
"nswappingFresh swp fr \<Longrightarrow> swappingSwFr swp fr"
unfolding nswappingFresh_def by auto

lemma nswappingFresh_swappingFrSw: 
"nswappingFresh swp fr \<Longrightarrow> swappingFrSw swp fr"
unfolding nswappingFresh_def by auto

lemma nswappingFresh_nswappingFvars: 
"nswappingFresh swp fr \<longleftrightarrow> nswappingFvars swp (\<lambda>c. {x. \<not> fr x c})"
unfolding nswappingFresh_def nswappingFvars_iff_swappingFvars_nswapping 
swappingFvars_def nswapping_def swappingSwFr_def swappingFrSw_def by auto

lemma nswappingFvars_nswappingFresh: 
"nswappingFvars swp fvars \<longleftrightarrow> nswappingFresh swp (\<lambda>x c. x \<notin> fvars c)"
unfolding nswappingFresh_def nswappingFvars_iff_swappingFvars_nswapping 
swappingFvars_def nswapping_def swappingSwFr_def swappingFrSw_def by auto


(* *)

definition "swappingSwFv swp fv \<equiv> \<forall>c x y. x \<notin> fv c \<and> y \<notin> fv c  \<longrightarrow> swp c x y = c"
definition "swappingFvSw swp fv \<equiv> \<forall>x c z1 z2. x \<in> fv (swp c z1 z2) \<longleftrightarrow> sw x z1 z2 \<in> fv c"

lemma swappingSwFr_swappingSwFv: 
"swappingSwFr swp fr \<longleftrightarrow> swappingSwFv swp (\<lambda>c. {x. \<not> fr x c})"
unfolding swappingSwFr_def swappingSwFv_def by auto

lemma swappingSwFv_swappingSwFr: 
"swappingSwFv swp SwFv \<longleftrightarrow> swappingSwFr swp (\<lambda>x c. x \<notin> SwFv c)"
unfolding swappingSwFr_def swappingSwFv_def by auto

lemma swappingFrSw_swappingFvSw: 
"swappingFrSw swp fr \<longleftrightarrow> swappingFvSw swp (\<lambda>c. {x. \<not> fr x c})"
unfolding swappingFrSw_def swappingFvSw_def by auto

lemma swappingFvSw_swappingFrSw: 
"swappingFvSw swp fv \<longleftrightarrow> swappingFrSw swp (\<lambda>x c. x \<notin> fv c)"
unfolding swappingFrSw_def swappingFvSw_def by auto

(* *)
(* *)
definition "permutPmFv prm fvars \<equiv>  
  (\<forall> c \<sigma>. bij \<sigma> \<and> fsupp \<sigma> \<and> (\<forall>x \<in> fvars c. \<sigma> x = x) \<longrightarrow> prm c \<sigma> = c)"

definition "permutFvPm prm fvars \<equiv>  
   (\<forall> x c \<sigma>. bij \<sigma> \<and> fsupp \<sigma> \<longrightarrow> (x \<in> fvars (prm c \<sigma>) \<longleftrightarrow> inv \<sigma> x \<in> fvars c))"
(* *)

lemma swappingSwFv_toSwp: 
assumes "permutPmFv prm fvars"
shows "swappingSwFv (toSwp prm) fvars"
by (smt (verit) assms bij_id_upd2 fsupp_id fsupp_upd fun_upd_apply 
id_apply permutPmFv_def swappingSwFv_def toSwp_def)

lemma swappingFvSw_toSwp: 
assumes "permutFvPm prm fvars"
shows "swappingFvSw (toSwp prm) fvars"
by (smt (z3) assms bij_id_upd2 bij_inv_eq_iff fsupp_id 
fsupp_upd fun_upd_other fun_upd_same id_apply permutFvPm_def sw_diff sw_eqL sw_eqR swappingFvSw_def toSwp_def)

lemma swappingSwFr_toSwp: 
assumes "permutPmFv prm fvars"
shows "swappingSwFr (toSwp prm) (\<lambda>x c. x \<notin> fvars c)"
using assms swappingSwFv_swappingSwFr swappingSwFv_toSwp by blast

lemma swappingFrSw_toSwp: 
assumes "permutFvPm prm fvars"
shows "swappingFrSw (toSwp prm) (\<lambda>x c. x \<notin> fvars c)"
using assms swappingFvSw_swappingFrSw swappingFvSw_toSwp by auto

(* *)

lemma toPerm_cong_id_swappingSwFv_cmpTrans: 
assumes s: "swappingSwFv swp fvars" and n: "nswapping swp"
and 2: "\<forall>x\<in>fvars c. (cmpTrans z1z2s) x = x"
and 3: "nonredundant z1z2s"
shows "toPerm swp c (cmpTrans z1z2s) = c"
proof-
  have "permut (toPerm swp)"  
  	by (simp add: n permut_toPerm)
  hence aux:  "\<And>c. toPerm swp c id = c"
   "\<And>c \<sigma> \<tau>. bij \<sigma> \<Longrightarrow> fsupp \<sigma> \<Longrightarrow> bij \<tau> \<and> fsupp \<tau> \<Longrightarrow> 
    toPerm swp c (\<tau> \<circ> \<sigma>) = toPerm swp (toPerm swp c \<sigma>) \<tau>" 
  unfolding permut_def by auto
  show ?thesis
  using 2 3 proof(induction z1z2s arbitrary: c rule: list_induct_Pair)
    case Nil
    then show ?case    
  	by simp (metis fun.map_ident n o_id permut_def permut_toPerm)
  next
    case (Cons z1 z2 z1z2s)
    have nr: "nonredundant z1z2s"  
    	using Cons.prems(2) nonredundant_Cons by blast
     have 0: \<open>\<And>z2 z1 c. toPerm swp c (id(z1 := z2, z2 := z1)) = swp c z1 z2\<close> 
     by (simp add: n toPerm_id_update_eq)  

    show ?case  unfolding cmpTrans.simps(2) apply(subst aux(2))
    subgoal by auto subgoal by auto subgoal by auto 
    subgoal unfolding toPerm_id_update_eq[OF n] apply(subst Cons.IH)
      subgoal using Cons(2,3)  apply - apply(drule nonredundant_cmpTrans) 
      by simp (smt (verit, best) fun_upd_apply id_apply insert_iff mem_Collect_eq)
      subgoal using Cons(3) nonredundant_Cons by blast 
      subgoal by (smt (verit) Cons.prems(1) 0 \<open>\<forall>x\<in>fvars c. cmpTrans z1z2s x = x\<close> aux(1) 
         comp_def comp_id cmpTrans.simps(2) fun_upd_id_same fun_upd_other fun_upd_same 
         fun_upd_triv fun_upd_twist id_apply id_comp id_swapTwice 
         prod.sel(1) rewriteR_comp_comp s swappingSwFv_def type_copy_map_cong0) . .  
  qed
qed

lemma toPerm_cong_id_swappingSwFv: 
assumes s: "swappingSwFv swp fvars" and n: "nswapping swp"
and 1: "bij \<sigma>" "fsupp \<sigma>" and 2: "\<forall>x\<in>fvars c. \<sigma> x = x"
shows "toPerm swp c \<sigma> = c"
using assms fsupp_ex_cmpTrans_even_stronger n toPerm_cong_id_swappingSwFv_cmpTrans by fastforce

lemma permutFvPm_toPerm: 
assumes "nswapping swp" "swappingSwFv swp fvars"
shows "permutPmFv (toPerm swp) fvars"  
unfolding permutPmFv_def 
by (meson assms toPerm_cong_id_swappingSwFv)

(* *)

lemma permutFvars_perm_Fvars: 
"permutFvars perm Fvars"  
by (simp add: nswapping_imp_swappingFvars_def2 nswapping_swap perm_def 
 permutFvars_toPerm swap_fresh_eq)

lemma fresh_perm: 
assumes \<sigma>: "fsupp \<sigma>" "bij \<sigma>" "fresh x t"
shows "fresh (\<sigma> x) (perm t \<sigma>)"
using permutFvars_perm_Fvars[unfolded permutFvars_def, 
  THEN conjunct2, THEN conjunct2, THEN conjunct2, rule_format, of \<sigma> "\<sigma> x" t, simplified]
using assms by simp (metis bij_inv_eq_iff)


(* Set-based version: *)
definition "swappingSwFrOn D swp fr \<equiv> \<forall>c x y. c \<in> D \<and> fr x c \<and> fr y c \<longrightarrow> swp c x y = c"



end