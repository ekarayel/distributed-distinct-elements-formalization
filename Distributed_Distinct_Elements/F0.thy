theory F0
  imports 
    "HOL-Library.Log_Nat"
    "Median_Method.Median"
    "Pseudorandom_Combinators"
begin

definition C3 :: int where "C3 = 17"
definition C6 :: nat where "C6 = 17"

context
  fixes n :: nat
  fixes \<epsilon> :: rat
  fixes \<delta> :: rat
  assumes n_gt_0: "n > 0" 
begin

definition b :: nat where "b = nat (\<lceil>1/ \<delta>\<^sup>2\<rceil>)"
definition l :: nat where "l = nat (\<lceil>ln (1/real_of_rat \<epsilon>)\<rceil>)"
definition k :: nat where "k = nat (\<lceil>ln (b\<^sup>2)\<rceil>)"

lemma l_gt_0: "l > 0" sorry
lemma b_gt_0: "b > 0" sorry

definition \<Omega> where 
  "\<Omega> = \<E> ((\<G> 2 n) \<times>\<^sub>S (\<H> 2 n (C6*b\<^sup>2)) \<times>\<^sub>S (\<H> k (C6*b\<^sup>2) b)) l 0.1"

type_synonym f0_state = "(nat \<Rightarrow> nat \<Rightarrow> int) \<times> (nat)"

fun is_too_large :: "(nat \<Rightarrow> nat \<Rightarrow> int) \<Rightarrow> bool" where
  "is_too_large B = ((\<Sum> (i,j) \<in> {..<l} \<times> {..<b}.  \<lfloor>log 2 (max (B i j) (-1) + 2)\<rfloor>) > C3 * b * l)" 

fun compress_step :: "f0_state \<Rightarrow> f0_state" where
  "compress_step (B,s) = (\<lambda> i j. max (B i j - 1) (-1), s+1)"

function compress :: "f0_state \<Rightarrow> f0_state" where
  "compress (B,s) = (
    if is_too_large B 
      then (compress (compress_step (B,s)))
      else (B,s))"
  by auto

fun compress_termination_measure :: "f0_state \<Rightarrow> nat" where
  "compress_termination_measure (B,s) = (\<Sum> (i,j) \<in> {..<l} \<times> {..<b}. nat (B i j + 1))"

lemma compress_termination: 
  assumes "is_too_large B"
  shows "compress_termination_measure (compress_step (B,s)) < compress_termination_measure (B,s)"
proof (rule ccontr)
  let ?I = "{..<l} \<times> {..<b}"
  have a: "nat (max (B i j - 1) (- 1) + 1) \<le> nat (B i j + 1)" for i j
    by simp
  assume "\<not> compress_termination_measure (compress_step (B, s)) < compress_termination_measure (B, s)"
  hence "(\<Sum> (i,j) \<in> ?I. nat (B i j + 1)) \<le> (\<Sum> (i,j) \<in> ?I. nat (max (B i j - 1) (-1) + 1))"
    by simp
  moreover have "(\<Sum> (i,j) \<in> ?I. nat (B i j + 1)) \<ge> (\<Sum> (i,j) \<in> ?I. nat (max (B i j - 1) (-1) + 1))"
    by (intro sum_mono) auto
  ultimately have b:
    "(\<Sum> (i,j) \<in> ?I. nat (max (B i j - 1) (-1) + 1)) = (\<Sum> (i,j) \<in> ?I. nat (B i j + 1))"
    using order_antisym by simp
  have "nat (B i j + 1) = nat (max (B i j - 1) (-1) + 1)" if "(i,j) \<in> ?I" for i j
    using sum_mono_inv[OF b] that a by auto
  hence "max (B i j) (-1) = -1" if "(i,j) \<in> ?I" for i j
    using that by fastforce
  hence "(\<Sum>(i,j) \<in> ?I. \<lfloor>log 2 (max (B i j) (-1) + 2)\<rfloor>) = (\<Sum>(i,j) \<in> ?I. 0)"
    by (intro sum.cong, auto)
  also have "... = 0" by simp
  also have "... \<le> C3 * b * l" unfolding C3_def by simp
  finally have "\<not> is_too_large B" by simp
  thus "False" using assms by simp
qed

termination compress
  using measure_def compress_termination
  by (relation "Wellfounded.measure (compress_termination_measure)", auto)

fun merge1 :: "f0_state \<Rightarrow> f0_state \<Rightarrow> f0_state" where
  "merge1 (B1,s1) (B2, s2) = (
    let s = max s1 s2 in (\<lambda> i j. max (B1 i j + s1 - s) (B2 i j + s2 -s), s))"

fun merge :: "f0_state \<Rightarrow> f0_state \<Rightarrow> f0_state" where
  "merge x y = compress (merge1 x y)"

fun single1 :: "nat \<Rightarrow> nat \<Rightarrow> f0_state" where
  "single1 \<omega> x = (\<lambda> i j. 
     let (f,g,h) = select \<Omega> \<omega> i in (
     if h (g x) = j then int (f x) else (-1)), 0)"

fun single :: "nat \<Rightarrow> nat \<Rightarrow> f0_state" where
  "single x coins = compress (single1 x coins)"

fun estimate1 :: "f0_state \<Rightarrow> nat \<Rightarrow> real" where
  "estimate1 (B,s) i = (
    let t = max 0 (Max ((B i) ` {..<b}) + s - \<lfloor>log 2 b\<rfloor> + 8); 
        p = card { j. j \<in> {..<b} \<and> B i j + s \<ge> t } in
        2 powr t * ln (1-p/b) / ln(1-1/b))"

fun estimate :: "f0_state \<Rightarrow> real" where
  "estimate x = median l (estimate1 x)"

section "History Independence"

fun \<tau>\<^sub>0 :: "((nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> nat)) \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> int" 
  where "\<tau>\<^sub>0 (f,g,h) A j = Max ({ int (f a) | a . a \<in> A \<and> h (g a) = j } \<union> {-1}) "

fun \<tau>\<^sub>1 :: "((nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> nat)) \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" 
  where "\<tau>\<^sub>1 \<psi> A s j = max (\<tau>\<^sub>0 \<psi> A j - s) (-1)"

fun \<tau>\<^sub>2 :: "nat \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" 
  where "\<tau>\<^sub>2 \<omega> A s i j = \<tau>\<^sub>1 (select \<Omega> \<omega> i) A s j"

fun \<tau>\<^sub>3 :: "nat \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> f0_state" 
  where "\<tau>\<^sub>3 \<omega> A s = (\<tau>\<^sub>2 \<omega> A s, s)"

fun s :: "nat \<Rightarrow> nat set \<Rightarrow> nat" 
  where "s \<omega> A = (LEAST s . \<not>(is_too_large (\<tau>\<^sub>2 \<omega> A s)))"

fun \<tau> :: "nat \<Rightarrow> nat set \<Rightarrow> f0_state" 
  where "\<tau> \<omega> A = \<tau>\<^sub>3 \<omega> A (s \<omega> A)"

lemma \<tau>\<^sub>2_step: "\<tau>\<^sub>2 \<omega> A (x+y) = (\<lambda>i j. max (\<tau>\<^sub>2 \<omega> A x i j - y) (- 1))"
  by (intro ext) simp

lemma \<tau>\<^sub>3_step: "compress_step (\<tau>\<^sub>3 \<omega> A x) = \<tau>\<^sub>3 \<omega> A (x+1)"
  using \<tau>\<^sub>2_step[where y="1"] by (simp del:\<tau>\<^sub>2.simps)


(*
1011    0     1/2
0101    1     1/4
0011    2     1/8
0001    3     1/16
0000    4     1/16
*)

lemma max_s': "\<tau>\<^sub>2 \<omega> A (nat \<lceil>log 2 n\<rceil>+1) i j = (-1)"
proof -
  obtain f g h where w_i: "select \<Omega> \<omega> i  = (f,g,h)" 
    by (metis prod_cases3)

  have "(- 1) < log 2 (real n) " sorry
  have "\<tau>\<^sub>0 (select \<Omega> \<omega> i) A j \<le> \<lceil>log 2 (real n)\<rceil>"
    unfolding w_i \<tau>\<^sub>0.simps
    apply (intro iffD2[OF Max_le_iff])
      defer
      apply simp
    apply auto
    defer
    sorry
  thus ?thesis
    unfolding \<tau>\<^sub>2.simps \<tau>\<^sub>1.simps
    by (intro max_absorb2) linarith
qed

lemma max_s: "\<not> (is_too_large (\<tau>\<^sub>2 \<omega> A (nat \<lceil>log 2 n\<rceil>+1)))"
  using max_s' by (simp add:C3_def mult_less_0_iff del:\<tau>\<^sub>2.simps)

lemma max_mono: "x \<le> (y::int) \<Longrightarrow> max x z \<le> max y z"
  by simp


lemma \<tau>\<^sub>0_mono: 
  assumes "B \<subseteq> {..<n}"
  assumes "A \<subseteq> B"
  shows "\<tau>\<^sub>0 \<omega> A j \<le> \<tau>\<^sub>0 \<omega> B j"
proof -
  obtain f g h where w_i: "\<omega> = (f,g,h)" 
    by (metis prod_cases3)
  show ?thesis
    unfolding \<tau>\<^sub>0.simps w_i using assms
    by (intro Max_mono subsetI) (auto simp add:finite_subset) 
qed

lemma \<tau>\<^sub>2_mono: 
  assumes "B \<subseteq> {..<n}"
  assumes "A \<subseteq> B"
  shows "\<tau>\<^sub>2 \<omega> A x i j \<le> \<tau>\<^sub>2 \<omega> B x i j"
  unfolding \<tau>\<^sub>2.simps \<tau>\<^sub>1.simps
  by (intro max_mono diff_mono \<tau>\<^sub>0_mono assms) auto

lemma is_too_large_antimono: 
  assumes "B \<subseteq> {..<n}" "A \<subseteq> B"
  assumes "is_too_large (\<tau>\<^sub>2 \<omega> A x)" 
  shows "is_too_large (\<tau>\<^sub>2 \<omega> B x)"
proof -
  have "C3 * b * l < (\<Sum> (i,j) \<in> {..<l} \<times> {..<b}.  \<lfloor>log 2 (max (\<tau>\<^sub>2 \<omega> A x i j) (-1) + 2)\<rfloor>)"
    using assms(3) by simp
  also have "... = (\<Sum> y \<in> {..<l} \<times> {..<b}.  \<lfloor>log 2 (max (\<tau>\<^sub>2 \<omega> A x (fst y) (snd y)) (-1) + 2)\<rfloor>)" 
    by (simp add:case_prod_beta del:\<tau>\<^sub>2.simps) 
  also have "... \<le> (\<Sum> y \<in> {..<l} \<times> {..<b}.  \<lfloor>log 2 (max (\<tau>\<^sub>2 \<omega> B x (fst y) (snd y)) (-1) + 2)\<rfloor>)" 
    by (intro sum_mono floor_mono iffD2[OF log_le_cancel_iff] iffD2[OF of_int_le_iff] 
        add_mono max_mono \<tau>\<^sub>2_mono[OF assms(1,2)]) auto
  also have "... = (\<Sum> (i,j) \<in> {..<l} \<times> {..<b}.  \<lfloor>log 2 (max (\<tau>\<^sub>2 \<omega> B x i j) (-1) + 2)\<rfloor>)" 
    by (simp add:case_prod_beta del:\<tau>\<^sub>2.simps) 
  finally have "(\<Sum> (i,j) \<in> {..<l} \<times> {..<b}.  \<lfloor>log 2 (max (\<tau>\<^sub>2 \<omega> B x i j) (-1) + 2)\<rfloor>) > C3 * b * l"
    by simp
  thus ?thesis by simp
qed

lemma s_compact: "\<not> (is_too_large (\<tau>\<^sub>2 \<omega> A (s \<omega> A)))"
  unfolding s.simps using max_s
  by (intro wellorder_Least_lemma(1)) blast

lemma s_mono: 
  assumes "B \<subseteq> {..<n}" "A \<subseteq> B"
  shows "s \<omega> A \<le> s \<omega> B"
proof -
  have "\<not> (is_too_large (\<tau>\<^sub>2 \<omega> A (s \<omega> B)))" 
    using is_too_large_antimono[OF assms] s_compact by blast
  hence "(LEAST s . \<not>(is_too_large (\<tau>\<^sub>2 \<omega> A s))) \<le> s \<omega> B"
    by (intro Least_le) blast
  thus ?thesis
    unfolding s.simps by simp
qed

lemma lt_s_too_large: "x < s \<omega> A \<Longrightarrow> is_too_large (\<tau>\<^sub>2 \<omega> A x)"
  unfolding s.simps using not_less_Least by auto

lemma compress_result_1: "compress (\<tau>\<^sub>3 \<omega> A (s \<omega> A - i)) = \<tau> \<omega> A"
proof (induction i)
  case 0
  then show ?case 
    using s_compact by (simp del:\<tau>\<^sub>2.simps)
next
  case (Suc i)
  show ?case
  proof (cases "i < s \<omega> A")
    case True
    have "is_too_large (\<tau>\<^sub>2 \<omega> A (s \<omega> A - Suc i))" 
      using True by (intro lt_s_too_large) simp
    hence "compress (\<tau>\<^sub>3 \<omega> A (s \<omega> A - Suc i)) = compress (compress_step (\<tau>\<^sub>3 \<omega> A (s \<omega> A - Suc i)))"
      unfolding \<tau>\<^sub>3.simps compress.simps
      by (simp del: compress.simps compress_step.simps)
    also have "... = compress (\<tau>\<^sub>3 \<omega> A ((s \<omega> A - Suc i)+1))"
      by (subst \<tau>\<^sub>3_step) blast
    also have "... = compress (\<tau>\<^sub>3 \<omega> A (s \<omega> A - i))"
      using True by (metis Suc_diff_Suc Suc_eq_plus1)
    also have "... = \<tau> \<omega> A" using Suc by auto
    finally show ?thesis by simp
  next
    case False
    then show ?thesis using Suc by simp
  qed
qed

lemma compress_result:
  assumes "x \<le> s \<omega> A"
  shows "compress (\<tau>\<^sub>3 \<omega> A x) = \<tau> \<omega> A"
proof -
  obtain i where i_def: "x = s \<omega> A - i" using assms by (metis diff_diff_cancel)
  have "compress (\<tau>\<^sub>3 \<omega> A x) = compress (\<tau>\<^sub>3 \<omega> A (s \<omega> A - i))"
    by (subst i_def) blast
  also have "... = \<tau> \<omega> A"
    using compress_result_1 by blast
  finally show ?thesis by simp
qed

lemma \<tau>\<^sub>0_merge:
  assumes "A \<subseteq> {..<n}" "B \<subseteq> {..<n}"
  shows "\<tau>\<^sub>0 (f,g,h) (A \<union> B) j = max (\<tau>\<^sub>0 (f,g,h) A j) (\<tau>\<^sub>0 (f,g,h) B j)" (is "?L = ?R")
proof-
  let ?f = "\<lambda>a. int (f a)" 
  have "?L = Max (?f ` { a . a \<in> (A \<union> B) \<and> h (g a) = j } \<union> {-1})"
    by (simp add: setcompr_eq_image)
  also have "... = Max ((?f ` { a . a \<in> A \<and> h (g a) = j } \<union> {-1}) \<union>
                        (?f ` { a . a \<in> B \<and> h (g a) = j } \<union> {-1}))"
    by (intro arg_cong[where f="Max"]) auto
  also have "... = max (Max (?f ` { a . a \<in> A \<and> h (g a) = j } \<union> {-1})) 
                       (Max (?f ` { a . a \<in> B \<and> h (g a) = j } \<union> {-1}))"
    using assms finite_nat_iff_bounded
    by (intro Max_Un finite_UnI finite_imageI) auto
  also have "... = ?R"
    by (simp add: setcompr_eq_image)
  finally show ?thesis by simp
qed

lemma \<tau>\<^sub>2_merge:
  assumes "A \<subseteq> {..<n}" "B \<subseteq> {..<n}"
  shows "\<tau>\<^sub>2 \<omega> (A \<union> B) x i j = max (\<tau>\<^sub>2 \<omega> A x i j) (\<tau>\<^sub>2 \<omega> B x i j)"
proof -
  obtain f g h where w_i: "select \<Omega> \<omega> i = (f,g,h)" 
    by (metis prod_cases3)
  show ?thesis
    by (simp add:w_i \<tau>\<^sub>0_merge[OF assms] del:\<tau>\<^sub>0.simps)
qed

lemma merge1_result:
  assumes "A \<subseteq> {..<n}" "B \<subseteq> {..<n}"
  shows "merge1 (\<tau> \<omega> A) (\<tau> \<omega> B) = \<tau>\<^sub>3 \<omega> (A \<union> B) (max (s \<omega> A) (s \<omega> B))"
proof -
  let ?smax = "max (s \<omega> A) (s \<omega> B)"
  obtain u where u_def: "s \<omega> A + u = ?smax" 
    by (metis add.commute max.commute nat_minus_add_max)
  obtain v where v_def: "s \<omega> B + v = ?smax" 
    by (metis add.commute nat_minus_add_max)

  have "u = 0 \<or> v = 0" using u_def v_def by linarith
  hence a:"max (\<tau>\<^sub>2 \<omega> A (s \<omega> A) i j - u) (\<tau>\<^sub>2 \<omega> B (s \<omega> B) i j - v) \<ge> (-1)" for i j
    by (auto simp del:s.simps)

  have "\<tau>\<^sub>2 \<omega> (A \<union> B) ?smax = (\<lambda> i j.  max (\<tau>\<^sub>2 \<omega> A ?smax i j) (\<tau>\<^sub>2 \<omega> B ?smax i j))"
    using \<tau>\<^sub>2_merge[OF assms] by (intro ext)
  also have "... = (\<lambda> i j.  max (\<tau>\<^sub>2 \<omega> A (s \<omega> A + u) i j) (\<tau>\<^sub>2 \<omega> B (s \<omega> B + v) i j))"
    unfolding u_def v_def by blast
  also have "... = (\<lambda> i j.  max (max (\<tau>\<^sub>2 \<omega> A (s \<omega> A) i j - u) (-1)) (max (\<tau>\<^sub>2 \<omega> B (s \<omega> B) i j - v) (-1)))"
    by (simp only: \<tau>\<^sub>2_step)
  also have "... = (\<lambda> i j.  max (max (\<tau>\<^sub>2 \<omega> A (s \<omega> A) i j - u) (\<tau>\<^sub>2 \<omega> B (s \<omega> B) i j - v)) (-1))"
    by (metis (no_types, opaque_lifting) max.commute max.left_commute max.left_idem)
  also have "... = (\<lambda> i j. max (\<tau>\<^sub>2 \<omega> A (s \<omega> A) i j - u) (\<tau>\<^sub>2 \<omega> B (s \<omega> B) i j - v))"
    using a by (simp del:s.simps)
  also have "... =  (\<lambda>i j. max (\<tau>\<^sub>2 \<omega> A (s \<omega> A) i j + int (s \<omega> A) - ?smax)
    (\<tau>\<^sub>2 \<omega> B (s \<omega> B) i j + int (s \<omega> B) - ?smax))" 
    by (subst u_def[symmetric], subst v_def[symmetric]) (simp del:s.simps \<tau>\<^sub>2.simps)
  finally have "\<tau>\<^sub>2 \<omega> (A \<union> B) (max (s \<omega> A) (s \<omega> B)) = 
    (\<lambda>i j. max (\<tau>\<^sub>2 \<omega> A (s \<omega> A) i j + int (s \<omega> A) - int (?smax))
             (\<tau>\<^sub>2 \<omega> B (s \<omega> B) i j + int (s \<omega> B) - int (?smax)))" by (simp del:s.simps)
  thus ?thesis
    by (simp add:Let_def del:s.simps \<tau>\<^sub>2.simps)
qed

lemma merge_result:
  assumes "A \<subseteq> {..<n}" "B \<subseteq> {..<n}"
  shows "merge (\<tau> \<omega> A) (\<tau> \<omega> B) = \<tau> \<omega> (A \<union> B)" (is "?L = ?R")
proof -
  have a:"max (local.s \<omega> A) (local.s \<omega> B) \<le> local.s \<omega> (A \<union> B)" 
    using s_mono assms by (simp del:s.simps)

  have "?L = compress (merge1 (\<tau> \<omega> A) (\<tau> \<omega> B))"
    by (simp del:\<tau>.simps)
  also have "... = compress ( \<tau>\<^sub>3 \<omega> (A \<union> B) (max (s \<omega> A) (s \<omega> B)))"
    by (subst merge1_result[OF assms]) blast 
  also have "... = ?R"
    by (intro compress_result a)
  finally show ?thesis by blast
qed


lemma single1_result: "single1 \<omega> x = \<tau>\<^sub>3 \<omega> {x} 0"
proof -
  have "(case select \<Omega> \<omega> i of (f, g, h) \<Rightarrow> if h (g x) = j then int (f x) else - 1) = \<tau>\<^sub>2 \<omega> {x} 0 i j" 
    (is ?ths) for i j
  proof -
    obtain f g h where w_i:"select \<Omega> \<omega> i = (f, g,h)" by (metis prod_cases3)
    show ?ths
      by (simp add:w_i)
  qed
  thus ?thesis
    by fastforce
qed

lemma single_result:
  "single \<omega> x = \<tau> \<omega> {x}" (is "?L = ?R")
proof -
  have "?L = compress (single1 \<omega> x)"
    by (simp)
  also have "... = compress ( \<tau>\<^sub>3 \<omega> {x} 0)"
    by (subst single1_result) blast
  also have "... = ?R"
    by (intro compress_result) simp
  finally show ?thesis by blast
qed



end

print_statement "single.simps"
lemma "estimate 2 = undefined"
  sorry


end