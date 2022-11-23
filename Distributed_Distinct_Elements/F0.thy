theory F0
  imports 
    "HOL-Library.Log_Nat"
    "Median_Method.Median"
    "Pseudorandom_Combinators"
begin

definition C2 :: real where "C2 = 3^2*2^22"
definition C3 :: int where "C3 = 34"
definition C6 :: nat where "C6 = 2^5"

context
  fixes n :: nat
  fixes \<epsilon> :: rat
  fixes \<delta> :: rat
  assumes n_gt_0: "n > 0" 
  assumes \<epsilon>_gt_0: "\<epsilon> > 0" and \<epsilon>_lt_1: "\<epsilon> < 1"
  assumes \<delta>_gt_0: "\<delta> > 0" and \<delta>_lt_1: "\<delta> < 1"
begin

definition b_base :: nat where "b_base = nat (\<lceil>log 2 (C2 / (of_rat \<delta>)^2)\<rceil>)"
definition b :: nat where "b = 2^b_base"
definition l :: nat where "l = nat (\<lceil>ln (1/real_of_rat \<epsilon>)\<rceil>)"
definition k :: nat where "k = nat (\<lceil>ln (b\<^sup>2)\<rceil>)"

lemma powr_less_1: "x > 0 \<Longrightarrow> x < 1 \<Longrightarrow> (x::real)^2 < 1"
  using power_strict_decreasing
  by (metis pos2 power_0)

lemma k_gt_0: "k > 0" sorry

lemma l_gt_0: "l > 0" sorry
lemma b_base_ge_26: "b_base \<ge> 26"
proof -
  have "2 powr 25 < C2" unfolding C2_def by simp
  also have "... < (C2*1) / (real_of_rat \<delta>)\<^sup>2"
    using \<delta>_gt_0 \<delta>_lt_1 unfolding C2_def
    by (intro iffD2[OF pos_less_divide_eq] zero_less_power mult_strict_left_mono powr_less_1) auto
  finally have "2 powr 25 < C2 / (real_of_rat \<delta>)\<^sup>2" by simp
  hence "log 2 (C2 / (real_of_rat \<delta>)\<^sup>2) > 25" 
    using \<delta>_gt_0 unfolding C2_def
    by (intro iffD2[OF less_log_iff] divide_pos_pos zero_less_power) auto
  hence "\<lceil>log 2 (C2 / (real_of_rat \<delta>)\<^sup>2)\<rceil> \<ge> 26" by simp
  thus ?thesis
    unfolding b_base_def by linarith
qed

lemma b_min: "b \<ge> 2^26"
  unfolding b_def
  by (meson b_base_ge_26  nat_power_less_imp_less not_less power_eq_0_iff power_zero_numeral)

definition \<Psi> where 
  "\<Psi> = (\<G> 2 n) \<times>\<^sub>S (\<H> 2 n [(C6*b\<^sup>2)]\<^sub>S) \<times>\<^sub>S (\<H> k (C6*b\<^sup>2) [b]\<^sub>S)"

definition \<Omega> where 
  "\<Omega> = \<E> l 0.1 \<Psi>"

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

lemma prod_right_mono: "B \<subseteq> C \<Longrightarrow> A \<times> B \<subseteq> A \<times> C"
  by auto

lemma sample_set_\<Psi>:
  "sample_set \<Psi> \<subseteq> sample_set (\<G> 2 n) \<times> sample_set (\<H> 2 n [(C6*b\<^sup>2)]\<^sub>S) \<times> sample_set (\<H> k (C6*b\<^sup>2) [b]\<^sub>S)" (is "_ \<subseteq> ?R")
proof -
  have "sample_set \<Psi> \<subseteq> sample_set (\<G> 2 n) \<times> sample_set (\<H> 2 n [(C6*b\<^sup>2)]\<^sub>S \<times>\<^sub>S (\<H> k (C6*b\<^sup>2) [b]\<^sub>S))"
    unfolding \<Psi>_def by (intro prod_sample_set)
  also have "... \<subseteq> ?R"
    by (intro prod_right_mono prod_sample_set)
  finally show ?thesis
    by simp
qed

lemma f_range: 
  assumes "(f,g,h) \<in> sample_set \<Psi>"
  shows "f x \<le> max (nat \<lceil>log 2 n\<rceil>) 1"
proof -
  have "f \<in> sample_set (\<G> 2 n)"
    using sample_set_\<Psi> assms by auto
  then obtain i where f_def:"f = select (\<G> 2 n) i" unfolding sample_set_def by auto
  show ?thesis
    unfolding f_def
    by (intro \<G>_range n_gt_0) auto
qed

lemma fin_f:
  assumes "(f,g,h) \<in> sample_set \<Psi>"
  shows "finite { int (f a) | a. P a }" (is "finite ?M")
proof -
  have "finite (range f)"
    using f_range[OF assms] finite_nat_set_iff_bounded_le by auto
  hence "finite (range (int \<circ> f))"
    by (simp add:image_image[symmetric])
  moreover have "?M \<subseteq> (range (int \<circ> f))"
    using image_mono by (auto simp add: setcompr_eq_image)    
  ultimately show ?thesis
    using finite_subset by auto
qed

lemma Max_int_range: "x \<le> (y::int) \<Longrightarrow> Max {x..y} = y"
  by auto

lemma family_1_conditions: "0 < (2::nat)" "0 < n"
  using n_gt_0 by auto

lemma family_2_conditions:
  shows "is_prime_power (size [(C6*b\<^sup>2)]\<^sub>S)" "(2::nat) > 0"
proof -
  have a:"C6 * b^2 = (2^(5 + b_base*2))" 
    unfolding C6_def b_def by (simp add: power_mult power_add) 
  have "is_prime_power (C6 * b\<^sup>2)" 
    unfolding a by (intro is_prime_power) auto
  thus "is_prime_power (size [C6 * b\<^sup>2]\<^sub>S)"
    unfolding nat_sample_space_def by simp
  show "(2::nat) > 0" by simp
qed

lemma family_3_conditions:
  shows "is_prime_power (size [b]\<^sub>S)" "k > 0"
proof -
  have "is_prime_power b" 
    unfolding b_def using b_base_ge_26 by (intro is_prime_power) auto
  thus "is_prime_power (sample_space.size [b]\<^sub>S)"
    unfolding nat_sample_space_def by simp
  show "k > 0" using k_gt_0 by simp
qed

lemma select_\<Omega>_range: "select \<Omega> \<omega> i \<in> sample_set \<Psi>"
proof -
  have "size (\<G> 2 n) > 0" 
    using \<G>_size[OF family_1_conditions] by simp
  moreover have "size  (\<H> 2 n [(C6*b\<^sup>2)]\<^sub>S) > 0" 
    using \<H>_size[OF family_2_conditions] by simp
  moreover have "size (\<H> k (C6*b\<^sup>2) [b]\<^sub>S) > 0"
    using \<H>_size[OF family_3_conditions] by simp
  ultimately have "size \<Psi> > 0" 
    unfolding \<Psi>_def by (simp add:prod_sample_space_def) 

  thus ?thesis
    unfolding \<Omega>_def by (intro \<E>_range) auto
qed

lemma max_s': "\<tau>\<^sub>2 \<omega> A (nat \<lceil>log 2 n\<rceil>+2) i j = (-1)"
proof -
  obtain f g h where w_i: "select \<Omega> \<omega> i = (f,g,h)" 
    by (metis prod_cases3)

  let ?max_s = "max \<lceil>log 2 (real n)\<rceil> 1"

  have c: "(f,g,h) \<in> sample_set \<Psi>" 
    using w_i select_\<Omega>_range by metis
  have a:"int (f x) \<le> ?max_s" for x 
  proof -
    have "int (f x) \<le> int (max (nat \<lceil>log 2 n\<rceil>) 1)" 
      by (intro of_nat_mono f_range[OF c])
    also have "... = ?max_s" by simp
    finally show ?thesis by simp
  qed
  have "\<tau>\<^sub>0 (select \<Omega> \<omega> i) A j \<le> Max {(-1)..?max_s}"
    unfolding w_i \<tau>\<^sub>0.simps using a by (intro Max_mono)  auto
  also have "... = ?max_s" 
    by (intro Max_int_range) auto
  finally have "\<tau>\<^sub>0 (select \<Omega> \<omega> i) A j \<le> ?max_s" by simp
  thus ?thesis
    unfolding \<tau>\<^sub>2.simps \<tau>\<^sub>1.simps
    by (intro max_absorb2) linarith
qed

lemma max_s: "\<not> (is_too_large (\<tau>\<^sub>2 \<omega> A (nat \<lceil>log 2 n\<rceil>+2)))"
  using max_s' by (simp add:C3_def mult_less_0_iff del:\<tau>\<^sub>2.simps)

lemma max_mono: "x \<le> (y::int) \<Longrightarrow> max x z \<le> max y z"
  by simp

lemma \<tau>\<^sub>0_mono: 
  assumes "\<psi> \<in> sample_set \<Psi>"
  assumes "A \<subseteq> B"
  shows "\<tau>\<^sub>0 \<psi> A j \<le> \<tau>\<^sub>0 \<psi> B j"
proof -
  obtain f g h where w_i: "\<psi> = (f,g,h)" 
    by (metis prod_cases3)
  show ?thesis
    using assms fin_f unfolding \<tau>\<^sub>0.simps w_i 
    by (intro Max_mono) auto 
qed

lemma \<tau>\<^sub>2_mono: 
  assumes "A \<subseteq> B"
  shows "\<tau>\<^sub>2 \<omega> A x i j \<le> \<tau>\<^sub>2 \<omega> B x i j"
  unfolding \<tau>\<^sub>2.simps \<tau>\<^sub>1.simps using select_\<Omega>_range
  by (intro max_mono diff_mono \<tau>\<^sub>0_mono assms) auto

lemma is_too_large_antimono: 
  assumes  "A \<subseteq> B"
  assumes "is_too_large (\<tau>\<^sub>2 \<omega> A x)" 
  shows "is_too_large (\<tau>\<^sub>2 \<omega> B x)"
proof -
  have "C3 * b * l < (\<Sum> (i,j) \<in> {..<l} \<times> {..<b}.  \<lfloor>log 2 (max (\<tau>\<^sub>2 \<omega> A x i j) (-1) + 2)\<rfloor>)"
    using assms(2) by simp
  also have "... = (\<Sum> y \<in> {..<l} \<times> {..<b}.  \<lfloor>log 2 (max (\<tau>\<^sub>2 \<omega> A x (fst y) (snd y)) (-1) + 2)\<rfloor>)" 
    by (simp add:case_prod_beta del:\<tau>\<^sub>2.simps) 
  also have "... \<le> (\<Sum> y \<in> {..<l} \<times> {..<b}.  \<lfloor>log 2 (max (\<tau>\<^sub>2 \<omega> B x (fst y) (snd y)) (-1) + 2)\<rfloor>)" 
    by (intro sum_mono floor_mono iffD2[OF log_le_cancel_iff] iffD2[OF of_int_le_iff] 
        add_mono max_mono \<tau>\<^sub>2_mono[OF assms(1)]) auto
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
  assumes "A \<subseteq> B"
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
  assumes "(f,g,h) \<in> sample_set \<Psi>"
  shows "\<tau>\<^sub>0 (f,g,h) (A \<union> B) j = max (\<tau>\<^sub>0 (f,g,h) A j) (\<tau>\<^sub>0 (f,g,h) B j)" (is "?L = ?R")
proof-
  let ?f = "\<lambda>a. int (f a)" 
  have "?L = Max (({ int (f a) |  a . a \<in> A \<and> h (g a) = j } \<union> {-1}) \<union>
                  ({ int (f a) | a . a \<in> B \<and> h (g a) = j } \<union> {-1}))"
    unfolding \<tau>\<^sub>0.simps
    by (intro arg_cong[where f="Max"])  auto
  also have "... = max (Max ({ int (f a) | a . a \<in> A \<and> h (g a) = j } \<union> {-1})) 
                       (Max ({ int (f a) | a . a \<in> B \<and> h (g a) = j } \<union> {-1}))"
    by (intro Max_Un finite_UnI fin_f[OF assms]) auto 
  also have "... = ?R"
    by (simp)
  finally show ?thesis by simp
qed

lemma \<tau>\<^sub>2_merge:
  "\<tau>\<^sub>2 \<omega> (A \<union> B) x i j = max (\<tau>\<^sub>2 \<omega> A x i j) (\<tau>\<^sub>2 \<omega> B x i j)"
proof -
  obtain f g h where w_i: "select \<Omega> \<omega> i = (f,g,h)" 
    by (metis prod_cases3)
  have a:"(f,g,h) \<in> sample_set \<Psi>"
    using select_\<Omega>_range w_i by metis
  show ?thesis
    by (simp add:w_i \<tau>\<^sub>0_merge[OF a] del:\<tau>\<^sub>0.simps)
qed

lemma merge1_result:
   "merge1 (\<tau> \<omega> A) (\<tau> \<omega> B) = \<tau>\<^sub>3 \<omega> (A \<union> B) (max (s \<omega> A) (s \<omega> B))"
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
    using \<tau>\<^sub>2_merge by (intro ext)
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
  "merge (\<tau> \<omega> A) (\<tau> \<omega> B) = \<tau> \<omega> (A \<union> B)" (is "?L = ?R")
proof -
  have a:"max (local.s \<omega> A) (local.s \<omega> B) \<le> local.s \<omega> (A \<union> B)" 
    using s_mono by (simp del:s.simps)

  have "?L = compress (merge1 (\<tau> \<omega> A) (\<tau> \<omega> B))"
    by (simp del:\<tau>.simps)
  also have "... = compress ( \<tau>\<^sub>3 \<omega> (A \<union> B) (max (s \<omega> A) (s \<omega> B)))"
    by (subst merge1_result) blast 
  also have "... = ?R"
    by (intro compress_result a Un_least)
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
    by (intro compress_result) auto
  finally show ?thesis by blast
qed


end

print_statement "single.simps"
lemma "estimate 2 = undefined"
  sorry


end