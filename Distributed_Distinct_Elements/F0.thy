theory F0
  imports 
    "HOL-Library.Log_Nat"
    "Median_Method.Median"
    "Pseudorandom_Combinators_Hash"
    "Pseudorandom_Combinators_Expander"
    "DDE_Preliminary"
begin

hide_const Discrete_Topology.discrete

section \<open>Algorithm\<close>

definition C2 :: real where "C2 = 3^2*2^23"
definition C3 :: int where "C3 = 33"
definition C6 :: nat where "C6 = 2^5"

locale inner_algorithm =
  fixes n :: nat
  fixes \<epsilon> :: rat
  fixes \<delta> :: rat
  assumes n_gt_0: "n > 0" 
  assumes \<epsilon>_gt_0: "\<epsilon> > 0" and \<epsilon>_lt_1: "\<epsilon> < 1"
  assumes \<delta>_gt_0: "\<delta> > 0" and \<delta>_lt_1: "\<delta> < 1"
begin

definition b_exp :: nat 
  where "b_exp = nat (\<lceil>log 2 (C2 / (of_rat \<delta>)^2)\<rceil>)"

definition b :: nat 
  where "b = 2^b_exp"

definition \<rho> :: "real \<Rightarrow> real"
  where "\<rho> x = b * (1 - (1-1/b) powr x)"

definition \<rho>' :: "real \<Rightarrow> real"
  where "\<rho>' x = ln (1-x/b) / ln (1-1/b)"

definition l :: nat 
  where "l = nat \<lceil>ln (1/real_of_rat \<epsilon>)\<rceil>"

definition k :: nat 
  where "k = nat \<lceil>7.5*ln b + 16\<rceil>"

definition \<Lambda> :: real
  where "\<Lambda> = min (1/16) (exp (-l * ln l^3))"

lemma k_min: "7.5 * ln (real b) + 16 \<le> real k"
  unfolding k_def by linarith

lemma \<Lambda>_gt_0: "\<Lambda> > 0" sorry

lemma l_gt_0: "l > 0" sorry

lemma b_exp_ge_26: "b_exp \<ge> 26"
proof -
  have "2 powr 25 < C2 / 1 " unfolding C2_def by simp
  also have "... \<le> C2 / (real_of_rat \<delta>)\<^sup>2"
    using \<delta>_gt_0 \<delta>_lt_1 unfolding C2_def
    by (intro divide_left_mono power_le_one) auto
  finally have "2 powr 25 < C2 / (real_of_rat \<delta>)\<^sup>2" by simp
  hence "log 2 (C2 / (real_of_rat \<delta>)\<^sup>2) > 25" 
    using \<delta>_gt_0 unfolding C2_def
    by (intro iffD2[OF less_log_iff] divide_pos_pos zero_less_power) auto
  hence "\<lceil>log 2 (C2 / (real_of_rat \<delta>)\<^sup>2)\<rceil> \<ge> 26" by simp
  thus ?thesis
    unfolding b_exp_def by linarith
qed

lemma b_min: "b \<ge> 2^26"
  unfolding b_def
  by (meson b_exp_ge_26  nat_power_less_imp_less not_less power_eq_0_iff power_zero_numeral)

lemma k_gt_0: "k > 0"
proof -
  have "(0::real) < 7.5 * 0 + 16" by simp
  also have "... \<le> 7.5 * ln(real b) + 16"
    using b_min
    by (intro add_mono mult_left_mono ln_ge_zero) auto
  finally have "0 < real k"
    using k_min by simp
  thus ?thesis by simp
qed
  
lemma b_ne: "{..<b} \<noteq> {}"
proof -
  have "0 \<in> {0..<b}"
    using b_min by simp
  thus ?thesis
    by auto
qed

lemma b_lower_bound: "C2 / (of_rat \<delta>)^2 \<le> real b"
proof -
  have "C2 / (of_rat \<delta>)^2 = 2 powr (log 2 (C2 / (of_rat \<delta>)^2))"
    using \<delta>_gt_0 unfolding C2_def by (intro powr_log_cancel[symmetric] divide_pos_pos) auto
  also have "... \<le> 2 powr (nat \<lceil>log 2 (C2 / (of_rat \<delta>)^2)\<rceil>)"
    by (intro powr_mono of_nat_ceiling) simp
  also have "... = real b"
    unfolding b_def b_exp_def by (simp add:powr_realpow)
  finally show ?thesis by simp
qed

definition n_exp where "n_exp = max (nat \<lceil>log 2 n\<rceil>) 1"

lemma n_exp_gt_0: "n_exp > 0"
  unfolding n_exp_def by simp

abbreviation \<Psi>\<^sub>1 where "\<Psi>\<^sub>1 \<equiv> \<H> 2 n (\<G> n_exp)"
abbreviation \<Psi>\<^sub>2 where "\<Psi>\<^sub>2 \<equiv> \<H> 2 n [C6*b\<^sup>2]\<^sub>S"
abbreviation \<Psi>\<^sub>3 where "\<Psi>\<^sub>3 \<equiv> \<H> k (C6*b\<^sup>2) [b]\<^sub>S"

definition \<Psi> where "\<Psi> = \<Psi>\<^sub>1 \<times>\<^sub>S \<Psi>\<^sub>2 \<times>\<^sub>S \<Psi>\<^sub>3"

abbreviation \<Omega> where "\<Omega> \<equiv> \<E> l \<Lambda> \<Psi>"

type_synonym f0_state = "(nat \<Rightarrow> nat \<Rightarrow> int) \<times> (nat)"

fun is_too_large :: "(nat \<Rightarrow> nat \<Rightarrow> int) \<Rightarrow> bool" where
  "is_too_large B = ((\<Sum> (i,j) \<in> {..<l} \<times> {..<b}. \<lfloor>log 2 (max (B i j) (-1) + 2)\<rfloor>) > C3 * b * l)" 

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

subsection \<open>History Independence\<close>

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

lemma prod_right_mono: "B \<subseteq> C \<Longrightarrow> A \<times> B \<subseteq> A \<times> C" (* REMOVE? *)
  by auto

sublocale \<Psi>\<^sub>1: \<H>_locale "2" "n" "\<G> n_exp" "\<Psi>\<^sub>1"
proof -
  have 0:"size (\<G> n_exp) = 2 ^ n_exp"
    unfolding \<G>_def by simp

  have "is_prime_power (size (\<G> n_exp))"
    unfolding 0 by (intro is_prime_power n_exp_gt_0) auto

  thus "\<H>_locale 2 (\<G> n_exp)"
    unfolding \<H>_locale_def by simp
  show "\<Psi>\<^sub>1 \<equiv> \<Psi>\<^sub>1" by simp
qed

sublocale \<Psi>\<^sub>2: \<H>_locale "2" "n" "[(C6*b\<^sup>2)]\<^sub>S" "\<Psi>\<^sub>2"
proof -
  have a:"C6 * b^2 = 2^(5 + b_exp*2)" 
    unfolding C6_def b_def by (simp add: power_mult power_add) 
  have "is_prime_power (C6 * b\<^sup>2)" 
    unfolding a by (intro is_prime_power) auto
  hence "is_prime_power (size [C6 * b\<^sup>2]\<^sub>S)"
    unfolding nat_sample_space_def by simp
  thus "\<H>_locale 2 [C6 * b\<^sup>2]\<^sub>S"
    unfolding \<H>_locale_def using n_gt_0 by simp
  show "\<H> 2 n [(C6*b\<^sup>2)]\<^sub>S \<equiv> \<H> 2 n [(C6*b\<^sup>2)]\<^sub>S" by simp
qed

sublocale \<Psi>\<^sub>3: \<H>_locale "k" "C6*b\<^sup>2" "[b]\<^sub>S" "(\<H> k (C6*b\<^sup>2) [b]\<^sub>S)"
proof -
  have "is_prime_power b" 
    unfolding b_def using b_exp_ge_26 by (intro is_prime_power) auto
  hence "is_prime_power (size [b]\<^sub>S)"
    unfolding nat_sample_space_def by simp
  thus "\<H>_locale k [b]\<^sub>S" using k_gt_0
    unfolding \<H>_locale_def by simp
  show "\<H> k (C6*b\<^sup>2) [b]\<^sub>S \<equiv> \<H> k (C6*b\<^sup>2) [b]\<^sub>S" by simp
qed

lemma sample_pmf_\<Psi>: "sample_pmf \<Psi> = pair_pmf \<Psi>\<^sub>1 (pair_pmf \<Psi>\<^sub>2 \<Psi>\<^sub>3)" 
  unfolding \<Psi>_def
  using \<Psi>\<^sub>1.sample_space \<Psi>\<^sub>2.sample_space \<Psi>\<^sub>3.sample_space
  by (simp add:prod_sample_pmf)

lemma sample_set_\<Psi>:
  "sample_set \<Psi> = sample_set \<Psi>\<^sub>1 \<times> sample_set \<Psi>\<^sub>2 \<times> sample_set \<Psi>\<^sub>3"
  using \<Psi>\<^sub>1.sample_space \<Psi>\<^sub>2.sample_space \<Psi>\<^sub>3.sample_space unfolding \<Psi>_def
  by (simp add: prod_sample_set)

lemma sample_space_\<Psi>: "sample_space \<Psi>"
  unfolding \<Psi>_def
  using \<Psi>\<^sub>1.sample_space \<Psi>\<^sub>2.sample_space \<Psi>\<^sub>3.sample_space
  by simp

lemma f_range: 
  assumes "(f,g,h) \<in> sample_set \<Psi>"
  shows "f x \<le> n_exp"
proof -
  have "f \<in> sample_set \<Psi>\<^sub>1"
    using sample_set_\<Psi> assms by auto
  then obtain i where f_def:"f = select \<Psi>\<^sub>1 i" unfolding sample_set_def by auto
  hence "f x \<in> sample_set (\<G> n_exp)"
    using \<Psi>\<^sub>1.\<H>_range by auto
  also have "... \<subseteq> {..n_exp}"
    by (intro \<G>_range)
  finally have "f x \<in> {..n_exp}" 
    by simp
  thus ?thesis by simp
qed

lemma g_range_1: 
  assumes "g \<in> sample_set \<Psi>\<^sub>2"
  shows "g x < C6*b^2"
proof -
  obtain i where f_def:"g = select (\<H> 2 n [(C6*b\<^sup>2)]\<^sub>S) i"
    using assms unfolding sample_set_def by auto
  hence "range g \<subseteq> sample_set ([(C6*b\<^sup>2)]\<^sub>S)"
    unfolding f_def by (intro \<Psi>\<^sub>2.\<H>_range) 
  thus ?thesis
    unfolding sample_set_alt[OF \<Psi>\<^sub>2.sample_space_R] 
    unfolding nat_sample_space_def by auto
qed

lemma h_range_1: 
  assumes "h \<in> sample_set \<Psi>\<^sub>3"
  shows "h x < b"
proof -
  obtain i where f_def:"h = select \<Psi>\<^sub>3 i"
    using assms unfolding sample_set_def by auto
  hence "range h \<subseteq> sample_set ([b]\<^sub>S)"
    unfolding f_def by (intro \<Psi>\<^sub>3.\<H>_range) 
  thus ?thesis
    unfolding sample_set_alt[OF \<Psi>\<^sub>3.sample_space_R] 
    unfolding nat_sample_space_def by auto
qed

lemma g_range: 
  assumes "(f,g,h) \<in> sample_set \<Psi>"
  shows "g x < C6*b^2"
proof -
  have "g \<in> sample_set \<Psi>\<^sub>2"
    using sample_set_\<Psi> assms by auto
  thus ?thesis
    using g_range_1 by simp
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

sublocale \<Omega>: expander_sample_space l \<Lambda> \<Psi>
  unfolding expander_sample_space_def using sample_space_\<Psi> l_gt_0 \<Lambda>_gt_0 by auto

lemma select_\<Omega>_range: "select \<Omega> \<omega> i \<in> sample_set \<Psi>"
  using \<Omega>.range by simp

lemma max_s': "\<tau>\<^sub>2 \<omega> A (nat \<lceil>log 2 n\<rceil>+2) i j = (-1)"
proof -
  obtain f g h where w_i: "select \<Omega> \<omega> i = (f,g,h)" 
    by (metis prod_cases3)

  let ?max_s = "max \<lceil>log 2 (real n)\<rceil> 1"

  have c: "(f,g,h) \<in> sample_set \<Psi>" 
    using w_i select_\<Omega>_range by metis
  have a:"int (f x) \<le> ?max_s" for x 
  proof -
    have "int (f x) \<le> int n_exp"
      using f_range[OF c] by auto
    also have "... = ?max_s" unfolding n_exp_def by simp
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
  have "C3 * b * l < (\<Sum> (i,j) \<in> {..<l} \<times> {..<b}. \<lfloor>log 2 (max (\<tau>\<^sub>2 \<omega> A x i j) (-1) + 2)\<rfloor>)"
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

lemma compress_result\<^sub>1: "compress (\<tau>\<^sub>3 \<omega> A (s \<omega> A - i)) = \<tau> \<omega> A"
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
    using compress_result\<^sub>1 by blast
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
  moreover have "\<tau>\<^sub>2 \<omega> A (s \<omega> A) i j - u \<ge> (-1)" if "u = 0" for i j
    using that by (simp del:s.simps)
  moreover have "\<tau>\<^sub>2 \<omega> B (s \<omega> B) i j - v \<ge> (-1)" if "v = 0" for i j
    using that by (simp del:s.simps)
  ultimately have a:"max (\<tau>\<^sub>2 \<omega> A (s \<omega> A) i j - u) (\<tau>\<^sub>2 \<omega> B (s \<omega> B) i j - v) \<ge> (-1)" for i j
    unfolding le_max_iff_disj by blast 

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

locale inner_algorithm_fix_A = inner_algorithm +
  fixes A
  assumes A_range: "A \<subseteq> {..<n}"
  assumes A_nonempty: "{} \<noteq> A"
begin

definition Y where "Y = card A"

definition s\<^sub>M where "s\<^sub>M = nat (\<lceil>log 2 Y\<rceil> - b_exp)"

subsection \<open>Accuracy for $s=0$\<close>

definition t\<^sub>1 :: "(nat \<Rightarrow> nat) \<Rightarrow> int" 
  where "t\<^sub>1 f = int (Max (f ` A)) - b_exp + 9"

definition t :: "(nat \<Rightarrow> nat) \<Rightarrow> nat"
  where "t f = nat (t\<^sub>1 f)"

definition R :: "(nat \<Rightarrow> nat) \<Rightarrow> nat set"
  where "R f = {a. a \<in> A \<and> f a \<ge> t f}"

definition r :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat"
  where "r x f = card {a. a \<in> A \<and> f a \<ge> x}"

definition p where "p =(\<lambda>(f,g,h). card {j\<in> {..<b}. \<tau>\<^sub>1 (f,g,h) A 0 j \<ge> t f})"

definition A\<^sub>S where "A\<^sub>S = (\<lambda>(f,g,h). 2 ^ t f * \<rho>' (p (f,g,h)))"

lemma fin_A: "finite A"
  using A_range finite_nat_iff_bounded by auto

lemma Y_le_n: "Y \<le> n"
proof -
  have "card A \<le> card {..<n}" 
    by (intro card_mono A_range) simp
  thus ?thesis
    unfolding Y_def  by simp
qed

lemma Y_ge_1: "Y \<ge> 1"
  unfolding Y_def 
  using fin_A A_nonempty by (simp add: leI)

lemma of_bool_square: "(of_bool x)\<^sup>2 = ((of_bool x)::real)"
  by (cases x, auto)

lemma r_eq: "r x f = (\<Sum> a \<in> A.( of_bool( x \<le> f a) :: real))"
  unfolding r_def of_bool_def sum.If_cases[OF fin_A]
  by (simp add: Collect_conj_eq)

lemma 
  shows 
    r_exp: "(\<integral>\<omega>. real (r x \<omega>) \<partial> \<Psi>\<^sub>1) = real Y * (of_bool (x \<le> max (nat \<lceil>log 2 n\<rceil>) 1) / 2^x)" and
    r_var: "measure_pmf.variance \<Psi>\<^sub>1 (\<lambda>\<omega>. real (r x \<omega>)) \<le> (\<integral>\<omega>. real (r x \<omega>) \<partial> \<Psi>\<^sub>1)"
proof -
  define V :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> real" where "V = (\<lambda>a f. of_bool (x \<le> f a))"

  have V_exp: "(\<integral>\<omega>. V a \<omega> \<partial>\<Psi>\<^sub>1) = of_bool (x \<le> max (nat \<lceil>log 2 n\<rceil>) 1)/2^x" 
    (is "?L = ?R") if "a \<in> A" for a
  proof -
    have a_le_n: "a < n"
      using that A_range by auto

    have "?L = (\<integral>\<omega>. indicator {f. x \<le> f a} \<omega> \<partial> \<Psi>\<^sub>1)"
      unfolding V_def by (intro integral_cong_AE) auto
    also have "... = measure (map_pmf (\<lambda>\<omega>. \<omega> a) (sample_pmf \<Psi>\<^sub>1)) {f. x \<le> f}"
      by simp
    also have "... = measure (\<G> n_exp) {f. x \<le> f}"
      unfolding \<Psi>\<^sub>1.\<H>_single[OF a_le_n] by simp
    also have "... = of_bool (x \<le> max (nat \<lceil>log 2 n\<rceil>) 1)/2^x"
      unfolding \<G>_prob n_exp_def by simp
    finally show ?thesis by simp
  qed

  have b:"(\<integral>\<omega>. real (r x \<omega>) \<partial> \<Psi>\<^sub>1) = (\<Sum> a \<in> A. (\<integral>\<omega>. V a \<omega> \<partial>\<Psi>\<^sub>1))" 
    unfolding r_eq V_def  using \<Psi>\<^sub>1.sample_space
    by (intro Bochner_Integration.integral_sum) auto 
  also have "... = (\<Sum> a \<in> A.  of_bool (x \<le> max (nat \<lceil>log 2 n\<rceil>) 1)/2^x)"
    using V_exp by (intro sum.cong) auto
  also have "... = Y * ( of_bool (x \<le> max (nat \<lceil>log 2 n\<rceil>) 1) / 2^x)"
    using Y_def by simp
  finally show "(\<integral>\<omega>. real (r x \<omega>) \<partial> \<Psi>\<^sub>1) = real Y * (of_bool (x \<le> max (nat \<lceil>log 2 n\<rceil>) 1)/ 2^x)"
    by simp

  have "(\<integral>\<omega>. (V a \<omega>)^2 \<partial> \<Psi>\<^sub>1) = (\<integral>\<omega>. V a \<omega> \<partial> \<Psi>\<^sub>1)" for a
    unfolding V_def of_bool_square by simp

  hence a:"measure_pmf.variance \<Psi>\<^sub>1 (V a) \<le> measure_pmf.expectation \<Psi>\<^sub>1 (V a)"  for a 
    using \<Psi>\<^sub>1.sample_space by (subst measure_pmf.variance_eq) auto

  have "J \<subseteq> A \<Longrightarrow> card J = 2 \<Longrightarrow> prob_space.indep_vars \<Psi>\<^sub>1 (\<lambda>_. borel) V J" for J
    unfolding V_def using A_range finite_subset[OF _ fin_A]
    by (intro prob_space.indep_vars_compose2[where Y="\<lambda>i y. of_bool(x \<le> y)" and M'="\<lambda>_. discrete"]
        prob_space.k_wise_indep_vars_subset[OF _ \<Psi>\<^sub>1.\<H>_indep]) (auto simp:prob_space_measure_pmf)
  hence "measure_pmf.variance \<Psi>\<^sub>1 (\<lambda>\<omega>. real (r x \<omega>)) = (\<Sum> a \<in> A. measure_pmf.variance \<Psi>\<^sub>1 (V a))"
    unfolding r_eq V_def using \<Psi>\<^sub>1.sample_space
    by (intro measure_pmf.var_sum_pairwise_indep_2 fin_A) (simp_all)
  also have "... \<le> (\<Sum> a \<in> A. (\<integral>\<omega>. V a \<omega> \<partial> \<Psi>\<^sub>1))"
    by (intro sum_mono a) 
  also have "... = (\<integral>\<omega>. real (r x \<omega>) \<partial> \<Psi>\<^sub>1)"
    unfolding b by simp
  finally show "measure_pmf.variance \<Psi>\<^sub>1 (\<lambda>\<omega>. real (r x \<omega>)) \<le> (\<integral>\<omega>. real (r x \<omega>) \<partial> \<Psi>\<^sub>1)" by simp
qed

end

end