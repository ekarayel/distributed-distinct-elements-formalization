theory F0
  imports 
    Pseudorandom_Combinators
    DDE_Preliminary
    Prefix_Free_Code_Combinators.Prefix_Free_Code_Combinators
begin

unbundle intro_cong_syntax
hide_const Abstract_Rewriting.restrict

section \<open>Algorithm\<close>

definition C2 :: real where "C2 = 3^2*2^23"
definition C3 :: int where "C3 = 33"
definition C5 :: real where "C5 = 4"
definition C6 :: nat where "C6 = 2^5"

locale inner_algorithm =
  fixes n :: nat
  fixes \<epsilon> :: real
  fixes \<delta> :: real
  assumes n_gt_0: "n > 0"
  assumes \<epsilon>_gt_0: "\<epsilon> > 0" and \<epsilon>_lt_1: "\<epsilon> < 1"
  assumes \<delta>_gt_0: "\<delta> > 0" and \<delta>_lt_1: "\<delta> < 1"
begin

definition b_exp where "b_exp = nat \<lceil>log 2 (C2 / \<delta>^2)\<rceil>"
definition b :: nat where "b = 2^b_exp"
definition l where "l = nat \<lceil>C5 * ln (2/ \<epsilon>)\<rceil>"
definition k where "k = nat \<lceil>7.5*ln b + 16\<rceil>"
definition \<Lambda> :: real where "\<Lambda> = min (1/16) (exp (-l * ln l^3))"
definition \<rho> :: "real \<Rightarrow> real" where "\<rho> x = b * (1 - (1-1/b) powr x)"
definition \<rho>' :: "real \<Rightarrow> real" where "\<rho>' x = ln (1-x/b) / ln (1-1/b)"

lemma l_lbound: "C5 * ln (2 / \<epsilon>) \<le> l"
  unfolding l_def by linarith



lemma k_min: "7.5 * ln (real b) + 16 \<le> real k"
  unfolding k_def by linarith

lemma \<Lambda>_gt_0: "\<Lambda> > 0" 
  unfolding \<Lambda>_def min_less_iff_conj by auto

lemma \<Lambda>_le_1: "\<Lambda> \<le> 1" 
  unfolding \<Lambda>_def by auto

lemma l_gt_0: "l > 0" 
proof -
  have "0 < C5 * ln (2 / \<epsilon>)"
    unfolding C5_def using \<epsilon>_gt_0 \<epsilon>_lt_1
    by (intro Rings.mult_pos_pos ln_gt_zero) auto
  also have "... \<le> l"
    by (intro l_lbound)
  finally show ?thesis 
    by simp
qed

lemma l_ubound: "l \<le> C5 * ln(1 / \<epsilon>)+C5*ln 2 + 1"
proof -
  have "l = of_int \<lceil>C5 * ln (2/ \<epsilon>)\<rceil>"
    using l_gt_0 unfolding l_def 
    by (intro of_nat_nat) simp
  also have "... \<le> C5 * ln (1/ \<epsilon>*2)+1"
    by simp
  also have "... = C5 * ln (1/ \<epsilon>)+C5 * ln 2+1"
    using \<epsilon>_gt_0 \<epsilon>_lt_1
    by (subst ln_mult) (auto simp add:algebra_simps)
  finally show ?thesis by simp
qed

lemma b_exp_ge_26: "b_exp \<ge> 26"
proof -
  have "2 powr 25 < C2 / 1 " unfolding C2_def by simp
  also have "... \<le> C2 / \<delta>^2"
    using \<delta>_gt_0 \<delta>_lt_1 unfolding C2_def
    by (intro divide_left_mono power_le_one) auto
  finally have "2 powr 25 < C2 / \<delta>^2" by simp
  hence "log 2 (C2 / \<delta>^2) > 25" 
    using \<delta>_gt_0 unfolding C2_def
    by (intro iffD2[OF less_log_iff] divide_pos_pos zero_less_power) auto
  hence "\<lceil>log 2 (C2 / \<delta>^2)\<rceil> \<ge> 26" by simp
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

lemma b_lower_bound: "C2 / \<delta>^2 \<le> real b"
proof -
  have "C2 /  \<delta>^2 = 2 powr (log 2 (C2 / \<delta>^2))"
    using \<delta>_gt_0 unfolding C2_def by (intro powr_log_cancel[symmetric] divide_pos_pos) auto
  also have "... \<le> 2 powr (nat \<lceil>log 2 (C2 /  \<delta>^2)\<rceil>)"
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

type_synonym \<Omega>_space = "nat \<Rightarrow> (nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> nat)"

fun single1 :: "\<Omega>_space \<Rightarrow> nat \<Rightarrow> f0_state" where
  "single1 \<omega> x = (\<lambda> i j. 
     let (f,g,h) = \<omega> i in (
     if h (g x) = j \<and> i < l then int (f x) else (-1)), 0)"

fun single :: "\<Omega>_space \<Rightarrow> nat \<Rightarrow> f0_state" where
  "single \<omega> x = compress (single1 \<omega> x)"

fun estimate1 :: "f0_state \<Rightarrow> nat \<Rightarrow> real" where
  "estimate1 (B,s) i = (
    let t = max 0 (Max ((B i) ` {..<b}) + s - \<lfloor>log 2 b\<rfloor> + 9); 
        p = card { j. j \<in> {..<b} \<and> B i j + s \<ge> t } in
        2 powr t * ln (1-p/b) / ln(1-1/b))"

fun estimate :: "f0_state \<Rightarrow> real" where
  "estimate x = median l (estimate1 x)"

subsection \<open>History Independence\<close>

fun \<tau>\<^sub>0 :: "((nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> nat)) \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> int" 
  where "\<tau>\<^sub>0 (f,g,h) A j = Max ({ int (f a) | a . a \<in> A \<and> h (g a) = j } \<union> {-1}) "

fun \<tau>\<^sub>1 :: "((nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> nat)) \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" 
  where "\<tau>\<^sub>1 \<psi> A s j = max (\<tau>\<^sub>0 \<psi> A j - s) (-1)"

fun \<tau>\<^sub>2 :: "\<Omega>_space \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" 
  where "\<tau>\<^sub>2 \<omega> A s i j = (if i < l then  \<tau>\<^sub>1 (\<omega> i) A s j else (-1))"

fun \<tau>\<^sub>3 :: "\<Omega>_space \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> f0_state" 
  where "\<tau>\<^sub>3 \<omega> A s = (\<tau>\<^sub>2 \<omega> A s, s)"

fun s :: "\<Omega>_space \<Rightarrow> nat set \<Rightarrow> nat" 
  where "s \<omega> A = (LEAST s . \<not>(is_too_large (\<tau>\<^sub>2 \<omega> A s)))"

fun \<tau> :: "\<Omega>_space \<Rightarrow> nat set \<Rightarrow> f0_state" 
  where "\<tau> \<omega> A = \<tau>\<^sub>3 \<omega> A (s \<omega> A)"

lemma \<tau>\<^sub>2_step: "\<tau>\<^sub>2 \<omega> A (x+y) = (\<lambda>i j. max (\<tau>\<^sub>2 \<omega> A x i j - y) (- 1))"
  by (intro ext) auto

lemma \<tau>\<^sub>3_step: "compress_step (\<tau>\<^sub>3 \<omega> A x) = \<tau>\<^sub>3 \<omega> A (x+1)"
  using \<tau>\<^sub>2_step[where y="1"] by (simp del:\<tau>\<^sub>2.simps)

sublocale \<Psi>\<^sub>1: hash_sample_space 2 n 2 n_exp "\<G> n_exp"
  using n_exp_gt_0 unfolding hash_sample_space_def \<G>_def by auto

sublocale \<Psi>\<^sub>2: hash_sample_space 2 n 2 "5 + b_exp*2" "[(C6*b\<^sup>2)]\<^sub>S"
  unfolding hash_sample_space_def nat_sample_space_def b_def C6_def 
  by (auto simp add:power_mult power_add)

sublocale \<Psi>\<^sub>3: hash_sample_space k "C6*b\<^sup>2" 2 "b_exp" "[b]\<^sub>S"
  unfolding hash_sample_space_def b_def nat_sample_space_def using k_gt_0 b_exp_ge_26
  by auto

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

lemma h_range: 
  assumes "(f,g,h) \<in> sample_set \<Psi>"
  shows "h x < b"
proof -
  have "h \<in> sample_set \<Psi>\<^sub>3"
    using sample_set_\<Psi> assms by auto
  thus ?thesis
    using h_range_1 by simp
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

lemma max_s': 
  assumes "\<omega> \<in> sample_set \<Omega>"
  shows "\<tau>\<^sub>2 \<omega> A (nat \<lceil>log 2 n\<rceil>+2) i j = (-1)"
proof (cases "i < l")
  case True
  obtain f g h where w_i: "\<omega> i = (f,g,h)" 
    by (metis prod_cases3)

  let ?max_s = "max \<lceil>log 2 (real n)\<rceil> 1"

  have "\<omega> i \<in> sample_set \<Psi>"
    using \<Omega>.sample_set assms unfolding Pi_def by auto
  hence c: "(f,g,h) \<in> sample_set \<Psi>" 
    using  w_i  by auto
  have a:"int (f x) \<le> ?max_s" for x 
  proof -
    have "int (f x) \<le> int n_exp"
      using f_range[OF c] by auto
    also have "... = ?max_s" unfolding n_exp_def by simp
    finally show ?thesis by simp
  qed
  have "\<tau>\<^sub>0 (\<omega> i) A j \<le> Max {(-1)..?max_s}"
    unfolding w_i \<tau>\<^sub>0.simps using a by (intro Max_mono)  auto
  also have "... = ?max_s" 
    by (intro Max_int_range) auto
  finally have "\<tau>\<^sub>0 (\<omega> i) A j \<le> ?max_s" by simp
  hence "max (\<tau>\<^sub>0 (\<omega> i) A j - int (nat \<lceil>log 2 (real n)\<rceil> + 2)) (- 1) = (-1)"
    by (intro max_absorb2) linarith
  thus ?thesis
    unfolding \<tau>\<^sub>2.simps \<tau>\<^sub>1.simps using True by auto
next
  case False
  thus ?thesis by simp
qed

lemma max_s: 
  assumes "\<omega> \<in> sample_set \<Omega>"
  shows "\<not> (is_too_large (\<tau>\<^sub>2 \<omega> A (nat \<lceil>log 2 n\<rceil>+2)))"
  using max_s'[OF assms] by (simp add:C3_def case_prod_beta mult_less_0_iff del:\<tau>\<^sub>2.simps) 

lemma max_s_2:
  assumes "\<omega> \<in> sample_set \<Omega>"
  shows "s \<omega> A \<le> (nat \<lceil>log 2 n\<rceil>+2)"
  unfolding s.simps by (intro wellorder_Least_lemma(2) max_s assms)

lemma max_mono: "x \<le> (y::'a::linorder) \<Longrightarrow> max x z \<le> max y z"
  using max.coboundedI1 by auto

lemma max_mono_2: "y \<le> (z::'a::linorder) \<Longrightarrow> max x y \<le> max x z"
  using max.coboundedI2 by auto 

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
  assumes "\<omega> \<in> sample_set \<Omega>"
  assumes "A \<subseteq> B"
  shows "\<tau>\<^sub>2 \<omega> A x i j \<le> \<tau>\<^sub>2 \<omega> B x i j"
proof -
  have "max (\<tau>\<^sub>0 (\<omega> i) A j - int x) (- 1) \<le> max (\<tau>\<^sub>0 (\<omega> i) B j - int x) (- 1)" if "i < l"
    using assms(1) \<Omega>.sample_set that
    by (intro max_mono diff_mono \<tau>\<^sub>0_mono assms(2) order.refl) auto
  thus ?thesis
    by (cases "i < l") auto
qed

lemma is_too_large_antimono: 
  assumes "\<omega> \<in> sample_set \<Omega>"
  assumes  "A \<subseteq> B"
  assumes "is_too_large (\<tau>\<^sub>2 \<omega> A x)" 
  shows "is_too_large (\<tau>\<^sub>2 \<omega> B x)"
proof -
  have "C3 * b * l < (\<Sum> (i,j) \<in> {..<l} \<times> {..<b}. \<lfloor>log 2 (max (\<tau>\<^sub>2 \<omega> A x i j) (-1) + 2)\<rfloor>)"
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

lemma s_compact: 
  assumes "\<omega> \<in> sample_set \<Omega>"
  shows "\<not> (is_too_large (\<tau>\<^sub>2 \<omega> A (s \<omega> A)))"
  unfolding s.simps using max_s[OF assms]
  by (intro wellorder_Least_lemma(1)) blast

lemma s_mono: 
  assumes "\<omega> \<in> sample_set \<Omega>"
  assumes "A \<subseteq> B"
  shows "s \<omega> A \<le> s \<omega> B"
proof -
  have "\<not> (is_too_large (\<tau>\<^sub>2 \<omega> A (s \<omega> B)))" 
    using is_too_large_antimono[OF assms] s_compact[OF assms(1)] by blast
  hence "(LEAST s . \<not>(is_too_large (\<tau>\<^sub>2 \<omega> A s))) \<le> s \<omega> B"
    by (intro Least_le) blast
  thus ?thesis
    unfolding s.simps by simp
qed

lemma lt_s_too_large: "x < s \<omega> A \<Longrightarrow> is_too_large (\<tau>\<^sub>2 \<omega> A x)"
  unfolding s.simps using not_less_Least by auto

lemma compress_result_1: 
  assumes "\<omega> \<in> sample_set \<Omega>"
  shows "compress (\<tau>\<^sub>3 \<omega> A (s \<omega> A - i)) = \<tau> \<omega> A"
proof (induction i)
  case 0
  then show ?case 
    using s_compact[OF assms] by (simp del:\<tau>\<^sub>2.simps)
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
  assumes "\<omega> \<in> sample_set \<Omega>"
  assumes "x \<le> s \<omega> A"
  shows "compress (\<tau>\<^sub>3 \<omega> A x) = \<tau> \<omega> A"
proof -
  obtain i where i_def: "x = s \<omega> A - i" using assms by (metis diff_diff_cancel)
  have "compress (\<tau>\<^sub>3 \<omega> A x) = compress (\<tau>\<^sub>3 \<omega> A (s \<omega> A - i))"
    by (subst i_def) blast
  also have "... = \<tau> \<omega> A"
    using compress_result_1[OF assms(1)] by blast
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
  assumes "\<omega> \<in> sample_set \<Omega>"
  shows "\<tau>\<^sub>2 \<omega> (A \<union> B) x i j = max (\<tau>\<^sub>2 \<omega> A x i j) (\<tau>\<^sub>2 \<omega> B x i j)"
proof (cases "i < l")
  case True

  obtain f g h where w_i: "\<omega> i = (f,g,h)" 
    by (metis prod_cases3)

  have "\<omega> i \<in> sample_set \<Psi>"
    using \<Omega>.sample_set assms unfolding Pi_def by auto
  hence a: "(f,g,h) \<in> sample_set \<Psi>" 
    using  w_i  by auto
  show ?thesis 
    using True by (simp add:w_i \<tau>\<^sub>0_merge[OF a] del:\<tau>\<^sub>0.simps)
next
  case False
  thus ?thesis by simp
qed

lemma merge1_result:
  assumes "\<omega> \<in> sample_set \<Omega>"
  shows "merge1 (\<tau> \<omega> A) (\<tau> \<omega> B) = \<tau>\<^sub>3 \<omega> (A \<union> B) (max (s \<omega> A) (s \<omega> B))"
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
    using \<tau>\<^sub>2_merge[OF assms] by blast
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
  assumes "\<omega> \<in> sample_set \<Omega>"
  shows "merge (\<tau> \<omega> A) (\<tau> \<omega> B) = \<tau> \<omega> (A \<union> B)" (is "?L = ?R")
proof -
  have a:"max (s \<omega> A) (s \<omega> B) \<le> s \<omega> (A \<union> B)" 
    using s_mono[OF assms] by (simp del:s.simps)

  have "?L = compress (merge1 (\<tau> \<omega> A) (\<tau> \<omega> B))"
    by (simp del:\<tau>.simps)
  also have "... = compress ( \<tau>\<^sub>3 \<omega> (A \<union> B) (max (s \<omega> A) (s \<omega> B)))"
    by (subst merge1_result[OF assms]) blast 
  also have "... = ?R"
    by (intro compress_result[OF assms] a Un_least)
  finally show ?thesis by blast
qed

lemma single1_result: "single1 \<omega> x = \<tau>\<^sub>3 \<omega> {x} 0"
proof -
  have "(case \<omega> i of (f, g, h) \<Rightarrow> if h (g x) = j \<and> i < l then int (f x) else - 1) = \<tau>\<^sub>2 \<omega> {x} 0 i j"  
      for i j
  proof -
    obtain f g h where w_i:"\<omega> i = (f, g,h)" by (metis prod_cases3)
    show ?thesis
      by (simp add:w_i)
  qed
  thus ?thesis
    by fastforce
qed

lemma single_result:
  assumes "\<omega> \<in> sample_set \<Omega>"
  shows "single \<omega> x = \<tau> \<omega> {x}" (is "?L = ?R")
proof -
  have "?L = compress (single1 \<omega> x)"
    by (simp)
  also have "... = compress (\<tau>\<^sub>3 \<omega> {x} 0)"
    by (subst single1_result) blast
  also have "... = ?R"
    by (intro compress_result[OF assms]) auto
  finally show ?thesis by blast
qed

subsection \<open>Encoding states of the inner algorithm\<close>

definition is_state_table :: "(nat \<times> nat \<Rightarrow> int) \<Rightarrow> bool" where 
  "is_state_table g = (range g \<subseteq> {-1..} \<and> g ` (-({..<l} \<times> {..<b})) \<subseteq> {-1})"

text \<open>Encoding for state table values:\<close>

definition V\<^sub>e :: "int encoding"
  where "V\<^sub>e x = (if x \<ge> -1 then N\<^sub>e (nat (x+1)) else None)"

text \<open>Encoding for state table:\<close>

definition T\<^sub>e' :: "(nat \<times> nat \<Rightarrow> int) encoding" where 
  "T\<^sub>e' g = (
    if is_state_table g 
      then (List.product [0..<l] [0..<b] \<rightarrow>\<^sub>e V\<^sub>e) (restrict g ({..<l}\<times>{..<b})) 
      else None)"

definition T\<^sub>e :: "(nat \<Rightarrow> nat \<Rightarrow> int) encoding" 
  where "T\<^sub>e f = T\<^sub>e' (case_prod f)"

definition encode_state :: "f0_state encoding"
  where "encode_state = T\<^sub>e \<times>\<^sub>e Nb\<^sub>e (nat \<lceil>log 2 n\<rceil>+3)"

lemma inj_on_restrict:
  assumes "B \<subseteq> {f. f ` (- A) \<subseteq> {c}}"
  shows "inj_on (\<lambda>x. restrict x A) B"
proof (rule inj_onI)
  fix f g assume a:"f \<in> B" "g \<in> B" "restrict f A = restrict g A"

  have "f x = g x" if "x \<in> A"  for x
    by (intro restrict_eq_imp[OF a(3) that])
  moreover have "f x = g x" if "x \<notin> A"  for x
  proof -
    have "f x = c" "g x = c"
      using that a(1,2) assms(1) by auto
    thus ?thesis by simp
  qed  
  ultimately show "f = g"
    by (intro ext) auto
qed

lemma encode_state: "is_encoding encode_state"
proof -
  have "is_encoding V\<^sub>e" 
    unfolding V\<^sub>e_def
    by (intro encoding_compose[OF exp_golomb_encoding] inj_onI) auto
  hence 0:"is_encoding (List.product [0..<l] [0..<b] \<rightarrow>\<^sub>e V\<^sub>e)"
    by (intro fun_encoding)
  have "is_encoding T\<^sub>e'"
    unfolding T\<^sub>e'_def is_state_table_def
    by (intro encoding_compose[OF 0] inj_on_restrict[where c="-1"]) auto
  moreover have " inj case_prod" 
    by (intro injI)  (metis curry_case_prod) 
  ultimately have "is_encoding T\<^sub>e" 
    unfolding T\<^sub>e_def by (rule encoding_compose_2)

  thus ?thesis
    unfolding encode_state_def
    by (intro dependent_encoding bounded_nat_encoding)
qed

lemma state_bit_count:
  assumes "\<omega> \<in> sample_set \<Omega>"
  shows "bit_count (encode_state (\<tau> \<omega> A)) \<le>  2^36 * (ln(1/\<epsilon>)+1)/ \<delta>^2 + log 2 (log 2 n + 3)" 
    (is "?L \<le> ?R")
proof -
  define t where "t = \<tau>\<^sub>2 \<omega> A (s \<omega> A)"

  have "log 2 (real n) \<ge> 0" 
    using n_gt_0 by simp
  hence 0: "- 1 < log 2 (real n)"
    by simp
  
  have "t x y = -1" if "x < l" "y \<ge> b" for x y
  proof -
    obtain f g h where \<omega>_def: "\<omega> x = (f,g,h)"
      by (metis prod_cases3)
    have "(f, g, h) \<in> sample_set \<Psi>"
      using \<Omega>.sample_set assms unfolding Pi_def \<omega>_def[symmetric] by auto
    hence "h (g a) < b" for a
      using h_range by auto
    hence "y \<noteq> h (g a)" for a
      using that(2) not_less by blast
    hence aux_4: "{int (f a) |a. a \<in> A \<and> h (g a) = y} = {}" 
      by auto
    hence "max (Max (insert (- 1) {int (f a) |a. a \<in> A \<and> h (g a) = y}) - int (s \<omega> A)) (- 1) = - 1"
      unfolding aux_4 by simp
    thus ?thesis
      unfolding t_def by (simp add:\<omega>_def del:s.simps)
  qed
  moreover have "t x y = -1" if "x \<ge> l" for x y
     using that unfolding t_def by simp
  ultimately have 1: "t x y = -1" if "x \<ge> l \<or> y \<ge> b" for x y
    using that by (meson not_less)

  have 2: "t x y \<ge> -1" for x y
    unfolding t_def by simp
  hence 3: "t x y + 1 \<ge> 0" for x y
    by (metis add.commute le_add_same_cancel1 minus_add_cancel)

  have 4:"is_state_table (case_prod t)"
    using 2 1 unfolding is_state_table_def by auto 

  have "bit_count(T\<^sub>e (\<tau>\<^sub>2 \<omega> A (s \<omega> A))) = bit_count(T\<^sub>e t)"
    unfolding t_def by simp
  also have "... = bit_count ((List.product [0..<l] [0..<b] \<rightarrow>\<^sub>e V\<^sub>e) (\<lambda>(x, y)\<in>{..<l}\<times>{..<b}. t x y))"
    using 4 unfolding T\<^sub>e_def T\<^sub>e'_def by simp
  also have "... = 
    (\<Sum>x\<leftarrow>List.product [0..<l] [0..<b]. bit_count (V\<^sub>e ((\<lambda>(x, y)\<in>{..<l} \<times> {..<b}. t x y) x)))"
    using restrict_extensional atLeast0LessThan by (simp add:fun_bit_count)
  also have "... = (\<Sum>(x,y)\<leftarrow>List.product [0..<l] [0..<b]. bit_count (V\<^sub>e (t x y)))"
    by (intro arg_cong[where f="sum_list"] map_cong refl)
     (simp add:atLeast0LessThan case_prod_beta)
  also have "... = (\<Sum>x\<in>{0..<l} \<times> {0..<b}. bit_count (V\<^sub>e (t (fst x) (snd x))))"
    by (subst sum_list_distinct_conv_sum_set)
     (auto intro:distinct_product simp add:case_prod_beta)
  also have "... = (\<Sum>x\<in>{..<l} \<times> {..<b}. bit_count ( N\<^sub>e (nat (t (fst x) (snd x)+1))))"
    using 2 unfolding V\<^sub>e_def not_less[symmetric]
    by (intro sum.cong refl arg_cong[where f="bit_count"]) auto
  also have "...=(\<Sum>x\<in>{..<l}\<times>{..<b}. 1+2* of_int\<lfloor>log 2(1+real(nat(t (fst x)(snd x)+1)))\<rfloor>)"
    unfolding exp_golomb_bit_count_exact is_too_large.simps not_less by simp
  also have "...=(\<Sum>x\<in>{..<l}\<times>{..<b}. 1+2* of_int\<lfloor>log 2(2+ of_int(t (fst x)(snd x)))\<rfloor>)"
    using 3 by (subst of_nat_nat) (auto simp add:ac_simps)
  also have "...=b*l + 2* of_int (\<Sum>(i,j)\<in>{..<l}\<times>{..<b}. \<lfloor>log 2(2+ of_int(max (t i j) (-1)))\<rfloor>)"
    using 2 by (subst max_absorb1) (auto simp add:case_prod_beta sum.distrib sum_distrib_left)
  also have "... \<le> b*l + 2 * of_int (C3 * int b * int l)"
    using s_compact[OF assms, where A="A"] unfolding is_too_large.simps not_less t_def[symmetric]
    by (intro add_mono ereal_mono iffD2[OF of_int_le_iff] mult_left_mono order.refl) 
      (simp_all add:ac_simps)
  also have "... = (2 * C3 + 1) * b * l"
    by (simp add:algebra_simps)
  finally have 5:"bit_count (T\<^sub>e (\<tau>\<^sub>2 \<omega> A (s \<omega> A))) \<le> (2 * C3 + 1) * b * l"
    by simp

  have "C2 \<ge> 1" 
    unfolding C2_def by simp
  moreover have "\<delta>\<^sup>2 \<le> 1"
    using \<delta>_lt_1 \<delta>_gt_0
    by (intro power_le_one) auto
  ultimately have "0 \<le> log 2 (C2 / \<delta>\<^sup>2)"
    using \<delta>_gt_0 \<delta>_lt_1  
    by (intro iffD2[OF zero_le_log_cancel_iff] divide_pos_pos)auto
  hence 6: "- 1 < log 2 (C2 / \<delta>\<^sup>2)"
    by simp

  have "b = 2 powr (real (nat \<lceil>log 2 (C2 / \<delta>\<^sup>2)\<rceil>))"
    unfolding b_def b_exp_def by (simp add:powr_realpow)
  also have "... = 2 powr (\<lceil>log 2 (C2 / \<delta>^2)\<rceil>)"
    using 6 by (intro arg_cong2[where f="(powr)"] of_nat_nat refl) simp
  also have "... \<le> 2 powr (log 2 (C2 / \<delta>^2) + 1)"
    by (intro powr_mono) auto
  also have "... = 2 * C2 / \<delta>^2"
    using \<delta>_gt_0 unfolding powr_add C2_def
    by (subst powr_log_cancel) (auto intro:divide_pos_pos)
  finally have 7:"b \<le> 2 * C2 / \<delta>^2" by simp

  have "l \<le> C5 * ln (1 / \<epsilon>) + C5 * ln 2 + 1"
    by (intro l_ubound)
  also have "... \<le> 4 * ln(1/\<epsilon>) + 3+1"
    unfolding C5_def by (intro add_mono order.refl) (approximation 5)
  also have "... = 4 * (ln(1/\<epsilon>)+1)"
    by simp
  finally have 8:"l \<le> 4 * (ln(1/\<epsilon>)+1)" 
    by simp

  have "\<delta>\<^sup>2 = 0 + \<delta>\<^sup>2"
    by simp
  also have "... \<le> ln (1 / \<epsilon>) + 1"
    using \<epsilon>_gt_0 \<epsilon>_lt_1 \<delta>_gt_0 \<delta>_lt_1
    by (intro add_mono power_le_one) auto
  finally have 9: "\<delta>\<^sup>2 \<le> ln (1 / \<epsilon>) + 1" 
    by simp

  have 10: "0 \<le> ln (1 / \<epsilon>) + 1"
    using \<epsilon>_gt_0 \<epsilon>_lt_1 by (intro add_nonneg_nonneg) auto

  have "?L = bit_count (T\<^sub>e (\<tau>\<^sub>2 \<omega> A (s \<omega> A))) + bit_count (Nb\<^sub>e (nat \<lceil>log 2 (real n)\<rceil>+3) (s \<omega> A))"
    unfolding encode_state_def by (simp del:s.simps add:dependent_bit_count)
  also have "...=bit_count(T\<^sub>e(\<tau>\<^sub>2 \<omega> A (s \<omega> A)))+ereal (1+ of_int\<lfloor>log 2 (2 + real (nat \<lceil>log 2 n\<rceil>))\<rfloor>)"
    using max_s_2[OF assms] by (subst bounded_nat_bit_count_2)
      (simp_all add:numeral_eq_Suc le_imp_less_Suc floorlog_def del:s.simps \<tau>\<^sub>2.simps)
  also have  "... = bit_count(T\<^sub>e(\<tau>\<^sub>2 \<omega> A (s \<omega> A)))+ereal (1+ of_int\<lfloor>log 2 (2 + of_int \<lceil>log 2 n\<rceil>)\<rfloor>)"
    using 0 by (simp del:s.simps \<tau>\<^sub>2.simps)
  also have  "... \<le> bit_count(T\<^sub>e(\<tau>\<^sub>2 \<omega> A (s \<omega> A)))+ereal (1+log 2 (2 + of_int \<lceil>log 2 n\<rceil>))"
    by (intro add_mono ereal_mono) simp_all
  also have  "... \<le> bit_count(T\<^sub>e(\<tau>\<^sub>2 \<omega> A (s \<omega> A)))+ereal (1+log 2 (2 + (log 2 n + 1)))"
    using 0 n_gt_0 by (intro add_mono ereal_mono iffD2[OF log_le_cancel_iff] add_pos_nonneg) auto
  also have  "... = bit_count(T\<^sub>e(\<tau>\<^sub>2 \<omega> A (s \<omega> A)))+ereal (1+log 2 (log 2 n + 3))"
    by (simp del:s.simps add:ac_simps)
  also have "... \<le> ereal ((2 * C3 + 1) * b * l) + ereal (1+log 2 (log 2 n + 3))"
    by (intro add_mono 5) auto
  also have "... = (2 * C3 + 1) * real b * real l + log 2 (log 2 n + 3) + 1"
    by simp
  also have "... \<le> (2 * C3 + 1) * (2 * C2 / \<delta>^2) * real l + log 2 (log 2 n + 3) + 1"
    unfolding C3_def
    by (intro ereal_mono mult_right_mono mult_left_mono add_mono 7) auto
  also have "... = (4 * of_int C3+2)*C2*real l/ \<delta>^2 + log 2 (log 2 n + 3) + 1" 
    by simp
  also have "... \<le> (4 * of_int C3+2)*C2*(4*(ln(1/ \<epsilon>)+1))/ \<delta>^2 + log 2 (log 2 n + 3) + 1"
    using \<delta>_gt_0 unfolding C3_def C2_def
    by (intro ereal_mono add_mono order.refl divide_right_mono mult_left_mono 8) auto
  also have "... = ((2*33+1)*9*2^26)*(ln(1/ \<epsilon>)+1)/ \<delta>^2 + log 2 (log 2 n + 3) + 1"
    unfolding C3_def C2_def by simp
  also have "... \<le> (2^36-1) * (ln(1/\<epsilon>)+1)/ \<delta>^2 + log 2 (log 2 n + 3) + (ln (1/ \<epsilon>)+1)/ \<delta>^2"
    using \<delta>_gt_0 \<epsilon>_gt_0 \<delta>_lt_1 9 10
    by (intro add_mono ereal_mono divide_right_mono mult_right_mono mult_left_mono) simp_all
  also have "... = 2^36* (ln(1/\<epsilon>)+1)/ \<delta>^2 + log 2 (log 2 n + 3)"
    by (simp add:divide_simps)
  finally show ?thesis
    by simp
qed

lemma random_bit_count:
  "size \<Omega> \<le> 2 powr (4 * log 2 n + 48 * (log 2 (1 / \<delta>) + 16)^2 + (55 + 60 * ln (1 / \<epsilon>))^3)" 
  (is "?L \<le> ?R")
proof -
  have 1:"log 2 (real n) \<ge> 0" 
    using n_gt_0 by simp
  hence 0: "- 1 < log 2 (real n)"
    by simp

  have 10: "log 2 C2 \<le> 27"
    unfolding C2_def by (approximation 10)
  have "\<delta>\<^sup>2 \<le> 1"
    using \<delta>_gt_0 \<delta>_lt_1 by (intro power_le_one) auto
  also have "... \<le> C2"
    unfolding C2_def by simp
  finally have " \<delta>\<^sup>2 \<le> C2" by simp
  hence 9: "0 \<le> log 2 (C2 / \<delta>\<^sup>2)"
    using \<delta>_gt_0 unfolding C2_def
    by (intro iffD2[OF zero_le_log_cancel_iff]) simp_all
  hence 2: "- 1 < log 2 (C2 / \<delta>\<^sup>2)"
    by simp

  have 3: "0 < C6 * b\<^sup>2" 
    unfolding C6_def using b_min 
    by (intro Rings.mult_pos_pos) auto

  have "0 \<le> log 2 (real C6) + real (b_exp * 2)"
    unfolding C6_def
    by (intro add_nonneg_nonneg) auto
  hence 4: "-1 < log 2 (real C6) + real (b_exp * 2)"
    by simp

  have "real (size \<Psi>\<^sub>1) = 2 ^ (max (nat \<lceil>log 2 (real n)\<rceil>) 1 * 2)"
    using \<Psi>\<^sub>1.size[OF n_gt_0] unfolding n_exp_def by simp
  also have "... \<le> 2 powr (2 * max (nat \<lceil>log 2 (real n)\<rceil>) 1)"
    by (subst powr_realpow) auto
  also have "... = 2 powr (2 * max (real (nat \<lceil>log 2 (real n)\<rceil>)) 1)"
    using n_gt_0 unfolding of_nat_mult of_nat_max by simp
  also have "... = 2 powr (2 * max (of_int \<lceil>log 2 (real n)\<rceil>) 1)"
    using 0 by (subst of_nat_nat) simp_all
  also have "... \<le> 2 powr (2 * max (log 2 (real n) + 1) 1)"
    by (intro powr_mono mult_left_mono max_mono) auto
  also have "... = 2 powr (2 * (log 2 (real n) + 1))"
    using 1 by (subst max_absorb1) auto
  finally have 5:"real (size \<Psi>\<^sub>1) \<le> 2 powr (2 * log 2 n + 2)"
    by simp

  have "real (size \<Psi>\<^sub>2) = 2 ^ (max (5 + b_exp * 2) (nat \<lceil>log 2 (real n)\<rceil>) * 2)"
    unfolding \<Psi>\<^sub>2.size[OF n_gt_0] by simp 
  also have "... \<le> 2 ^ (((5 + b_exp * 2) + (nat \<lceil>log 2 (real n)\<rceil>)) * 2)"
    by (intro power_increasing mult_right_mono) auto
  also have "... = 2 powr ((5 + b_exp * 2 + real (nat \<lceil>log 2 (real n)\<rceil>))*2)"
    by (subst powr_realpow[symmetric]) auto
  also have "... = 2 powr ((5 + of_int b_exp * 2 + of_int \<lceil>log 2 (real n)\<rceil>)*2)"
    using 0 by (subst of_nat_nat) auto
  also have "... \<le> 2 powr ((5 + of_int b_exp * 2 + (log 2 (real n) + 1))*2)"
    by (intro powr_mono mult_right_mono add_mono) simp_all
  also have "... = 2 powr (12 + 4 * real( nat \<lceil>log 2 (C2 / \<delta>\<^sup>2)\<rceil>) + log 2 (real n) * 2)"
    unfolding b_exp_def by (simp add:ac_simps)
  also have "... = 2 powr (12 + 4 * real_of_int \<lceil>log 2 (C2 / \<delta>\<^sup>2)\<rceil> + log 2 (real n) * 2)"
    using 2 by (subst of_nat_nat) simp_all
  also have "... \<le> 2 powr (12 + 4 * (log 2 (C2 / \<delta>\<^sup>2) + 1) + log 2 (real n) * 2)"
    by (intro powr_mono add_mono order.refl mult_left_mono) simp_all
  also have "... = 2 powr (2 * log 2 n + 4 * log 2 (C2 / \<delta>\<^sup>2) + 16)"
    by (simp add:ac_simps)
  finally have 6:"real (size \<Psi>\<^sub>2) \<le> 2 powr (2 * log 2 n + 4 * log 2 (C2 / \<delta>\<^sup>2) + 16)" 
    by simp

  have "real (size \<Psi>\<^sub>3) = 2 ^ (max b_exp (nat \<lceil>log 2 (real C6 * (2 ^ (b_exp*2)))\<rceil>) * k)"
    unfolding \<Psi>\<^sub>3.size[OF 3] power_mult by (simp add:b_def) 
  also have "... = 2 ^ (max b_exp (nat \<lceil>log 2 C6 + log 2 (2 ^ (b_exp*2))\<rceil>) * k)"
    unfolding C6_def by (subst log_mult) simp_all
  also have "... = 2 ^ (max b_exp (nat \<lceil>log 2 C6 + (b_exp*2)\<rceil>) * k)"
    by (subst log_nat_power) simp_all
  also have "... = 2 powr (max (real b_exp) (real (nat \<lceil>log 2 C6 + (b_exp*2)\<rceil>)) * real k)"
    by (subst powr_realpow[symmetric]) simp_all
  also have "... = 2 powr (max (real b_exp) (of_int \<lceil>log 2 C6 + (b_exp*2)\<rceil>) * real k)"
    using 4 by (subst of_nat_nat) simp_all
  also have "... \<le> 2 powr (max (real b_exp) (log 2 C6 + real b_exp*2 +1) * real k)"
    by (intro powr_mono mult_right_mono max_mono_2) simp_all
  also have "... = 2 powr ((log 2 (2^5) + real b_exp*2 +1) * real k)"
    unfolding C6_def by (subst max_absorb2) simp_all
  also have "... = 2 powr ((real b_exp*2 +6) * real k)"
    unfolding C6_def by (subst log_nat_power) (simp_all add:ac_simps)
  also have "... = 2 powr ((of_int \<lceil>log 2 (C2 / \<delta>\<^sup>2)\<rceil> * 2 + 6) * real k)"
    using 2 unfolding b_exp_def by (subst of_nat_nat) simp_all
  also have "... \<le> 2 powr (((log 2 (C2 / \<delta>^2)+1) * 2 + 6) * real k)"
    by (intro powr_mono mult_right_mono add_mono) simp_all
  also have "... = 2 powr ((log 2 (C2 / \<delta>\<^sup>2) * 2 + 8 ) * real k)"
    by (simp add:ac_simps)
  finally have 7:"real (size \<Psi>\<^sub>3) \<le> 2 powr ((log 2 (C2 / \<delta>\<^sup>2) * 2 + 8 ) * real k)" 
    by simp

  have "ln (real b) \<ge> 0" 
    using b_min by simp
  hence "real k = of_int \<lceil>7.5  * ln (real b) + 16\<rceil>"
    unfolding k_def by (subst of_nat_nat) simp_all
  also have "... \<le> (7.5 * ln (real b) + 16) + 1"
    unfolding b_def by (intro of_int_ceiling_le_add_one)
  also have "... = 7.5 * ln (2 powr b_exp) + 17"
    unfolding b_def using powr_realpow by simp
  also have "... = real b_exp * (7.5 * ln 2) + 17"
    unfolding powr_def by simp
  also have "... \<le> real b_exp * 6 + 17"
    by (intro add_mono mult_left_mono order.refl of_nat_0_le_iff) (approximation 5)
  also have "... = of_int \<lceil>log 2 (C2 / \<delta>\<^sup>2)\<rceil> * 6 + 17"
    using 2 unfolding b_exp_def by (subst of_nat_nat) simp_all
  also have "... \<le> (log 2 (C2 / \<delta>^2) + 1) * 6 + 17"
    by (intro add_mono mult_right_mono) simp_all
  also have "... = 6 * log 2 (C2 / \<delta>^2) + 23"
    by simp
  finally have 8:"real k \<le> 6 * log 2 (C2 / \<delta>^2) + 23" 
    by simp

  have "real (size \<Psi>) = real (size \<Psi>\<^sub>1) * real (size \<Psi>\<^sub>2) * real (size \<Psi>\<^sub>3)"
    unfolding \<Psi>_def prod_sample_space_def by simp 
  also have "... \<le> 
    2 powr(2*log 2 n+2)*2 powr (2*log 2 n+4*log 2 (C2/\<delta>\<^sup>2)+16)*2 powr((log 2 (C2/\<delta>\<^sup>2)*2+8)*real k)"
    by (intro mult_mono 5 6 7 mult_nonneg_nonneg) simp_all
  also have "... = 2 powr (2*log 2 n + 2 + 2 * log 2 n+4*log 2 (C2/\<delta>\<^sup>2)+16+(log 2 (C2/\<delta>\<^sup>2)*2+8)*real k)"
    unfolding powr_add by simp
  also have "... = 2 powr (4*log 2 n + 4*log 2 (C2/\<delta>\<^sup>2) + 18 + (2*log 2 (C2/\<delta>\<^sup>2)+8)*real k)"
    by (simp add:ac_simps)
  also have "... \<le> 
    2 powr (4* log 2 n + 4* log 2 (C2/ \<delta>^2) + 18 + (2*log 2 (C2/\<delta>\<^sup>2)+8)*(6 * log 2 (C2 / \<delta>^2) + 23))"
    using 9 by (intro powr_mono add_mono order.refl mult_left_mono 8 add_nonneg_nonneg) simp_all
  also have "... = 2 powr (4 * log 2 n+12 * log 2 (C2 / \<delta>^2)^2 + 98 * log 2 (C2 / \<delta>^2)+202)"
    by (simp add:algebra_simps power2_eq_square)
  also have "... \<le> 2 powr (4 * log 2 n+12 * log 2 (C2 / \<delta>^2)^2 + 120 * log 2 (C2 / \<delta>^2)+300)"
    using 9 by (intro powr_mono add_mono order.refl mult_right_mono) simp_all
  also have "... = 2 powr (4 * log 2 n+12 * (log 2 (C2* (1/ \<delta>)^2) + 5)^2)"
    by (simp add:power2_eq_square algebra_simps)
  also have "... = 2 powr (4 * log 2 n + 12 * (log 2 C2 + log 2 ((1 / \<delta>)^2) + 5)^2)"
    unfolding C2_def using \<delta>_gt_0 by (subst log_mult) auto
  also have "... \<le> 2 powr (4 * log 2 n + 12 * (27 + log 2 ((1/ \<delta>)^2) + 5)^2)"
    using \<delta>_gt_0 \<delta>_lt_1 
    by (intro powr_mono add_mono order.refl mult_left_mono power_mono add_nonneg_nonneg 10)
     (simp_all add:C2_def)
  also have "... = 2 powr (4 * log 2 n + 12 * (2 * (log 2 (1 / \<delta>) + 16))^2)"
    using \<delta>_gt_0 by (subst log_nat_power)  (simp_all add:ac_simps)
  also have "... = 2 powr (4 * log 2 n + 48 * (log 2 (1 / \<delta>) + 16)^2)"
    unfolding power_mult_distrib by simp
  finally have 19:"real (size \<Psi>) \<le> 2 powr (4 * log 2 n + 48 * (log 2 (1 / \<delta>) + 16)^2)" 
    by simp

  have "0 \<le> ln \<Lambda> / ln (19 / 20)" 
    using \<Lambda>_gt_0 \<Lambda>_le_1
    by (intro divide_nonpos_neg) simp_all
  hence 11: "-1 < ln \<Lambda> / ln (19 / 20)" 
    by simp

  have 12: "ln (19 / 20) \<le> -(0.05::real)" "- ln (1 / 16) \<le> (2.8::real)"
    by (approximation 10)+

  have 13: "ln l \<ge> 0"
    using l_gt_0 by auto

  have "ln l^3 = 27 * (0 + ln l/3)^3" 
    by (simp add:power3_eq_cube)
  also have "... \<le> 27 * (1 + ln l/real 3)^3"
    using l_gt_0 by (intro mult_left_mono add_mono power_mono) auto
  also have "... \<le> 27 * (exp (ln l))"
    using l_gt_0 13
    by (intro mult_left_mono exp_ge_one_plus_x_over_n_power_n) linarith+
  also have "... = 27 * real l"
    using l_gt_0 by (subst exp_ln) auto
  finally have 14:"ln l^3 \<le> 27 * real l"
    by simp

  have 15:"C5 * ln (2 / \<epsilon>) > 0" 
    using \<epsilon>_lt_1 \<epsilon>_gt_0 unfolding C5_def
    by (intro Rings.mult_pos_pos ln_gt_zero) auto
  hence "1 \<le> real_of_int \<lceil>C5 * ln (2 / \<epsilon>)\<rceil>" 
    by simp
  hence 16: "1 \<le> 3 * real_of_int \<lceil>C5 * ln (2 / \<epsilon>)\<rceil>" 
    by argo

  have 17: "12 * ln 2 \<le> (9::real)" 
    by (approximation 5)

  have "16 ^ ((l - 1) * nat\<lceil>ln \<Lambda> / ln 0.95\<rceil>) = 16 powr (real (l-1)*real(nat \<lceil>ln \<Lambda> / ln (19 / 20)\<rceil>))"
    by (subst powr_realpow[symmetric]) auto
  also have "... = 16 powr (real (l-1)* of_int \<lceil>ln \<Lambda> / ln (19 / 20)\<rceil>)"
    using 11 by (subst of_nat_nat) simp_all
  also have "... \<le> 16 powr (real (l-1)* (ln \<Lambda> / ln (19/20)+1))"
    by (intro powr_mono mult_left_mono) auto
  also have "... = 16 powr ((real l - 1)*(ln \<Lambda> / ln (19/20)+1))"
    using l_gt_0 by (subst of_nat_diff) auto
  also have "... \<le> 16 powr ((real l - 1)*(ln \<Lambda> / (-0.05)+1))"
    using l_gt_0 \<Lambda>_gt_0 \<Lambda>_le_1
    by (intro powr_mono mult_left_mono add_mono divide_left_mono_neg 12) auto
  also have "... = 16 powr ((real l - 1)*(20 * (-ln \<Lambda>)+1))"
    by (simp add:algebra_simps)
  also have "... = 16 powr ((real l - 1)*(20 * -(min (ln (1/16)) (-l*ln l^3))+1))"
    unfolding \<Lambda>_def by (subst ln_min_swap) auto
  also have "... = 16 powr ((real l - 1)*(20 * max (-ln (1/16)) (l*ln l^3)+1))"
    by (intro_cong "[\<sigma>\<^sub>2 (powr), \<sigma>\<^sub>2(+), \<sigma>\<^sub>2 (*)]") simp
  also have "... \<le> 16 powr ((real l - 1)*(20 * max (2.8) (l*ln l^3)+1))"
    using l_gt_0 by (intro powr_mono mult_left_mono add_mono max_mono 12) auto
  also have "... \<le> 16 powr ((real l - 1)*(20 * (2.8+l*ln l^3)+1))"
    using l_gt_0 by (intro powr_mono mult_left_mono add_mono) auto
  also have "... = 16 powr ((real l - 1)*(20 * (l*ln l^3)+57))"
    by (simp add:algebra_simps)
  also have "... \<le> 16 powr ((real l - 1)*(20 * (real l*(27*real l))+57))"
    using l_gt_0 by (intro powr_mono mult_left_mono add_mono 14) auto
  also have "... = 16 powr (540 * real l^3 - 540 * real l^2 + 57* real l - 57)"
    by (simp add:algebra_simps numeral_eq_Suc)
  also have "... \<le> 16 powr (540 * real l^3 - 540 * real l^2 + 180* real l - 20)"
    by (intro powr_mono add_mono diff_mono order.refl mult_right_mono) auto
  also have "... = 16 powr (20 * (3*real l - 1)^3)"
    by (simp add: algebra_simps power3_eq_cube power2_eq_square)
  also have "... = 16 powr (20 * (3 * of_int \<lceil>C5 * ln (2 / \<epsilon>)\<rceil> - 1) ^ 3)"
    using 15 unfolding l_def by (subst of_nat_nat) auto
  also have "... \<le> 16 powr (20 * (3 * (C5 * ln (2 / \<epsilon>) + 1) - 1) ^ 3)"
    using 16 by (intro powr_mono mult_left_mono power_mono diff_mono) auto
  also have "... = 16 powr (20 * (2 + 12 * ln (2 * (1 / \<epsilon>))) ^ 3)"
    by (simp add:algebra_simps C5_def)
  also have "... = (2 powr 4) powr (20 * (2+ 12 * (ln 2 + ln(1/ \<epsilon>)))^3)"
    using \<epsilon>_gt_0 by (subst ln_mult) auto
  also have "... = 2 powr (80 * (2 + 12 * ln 2 + 12 * ln (1 / \<epsilon>)) ^ 3)"
    unfolding powr_powr by (simp add:ac_simps)
  also have "... \<le> 2 powr (80 * (2 + 9 + 12 * ln (1 / \<epsilon>)) ^ 3)"
    using \<epsilon>_gt_0 \<epsilon>_lt_1
    by (intro powr_mono mult_left_mono power_mono add_mono 17 add_nonneg_nonneg) auto
  also have "... = 2 powr (80 * (11 + 12 * ln (1 / \<epsilon>)) ^ 3)"
    by simp
  also have "... \<le> 2 powr (5^3 * (11 + 12 * ln (1 / \<epsilon>)) ^ 3)"
    using \<epsilon>_gt_0 \<epsilon>_lt_1
    by (intro powr_mono mult_right_mono) (auto intro!:add_nonneg_nonneg)
  also have "... = 2 powr ((55 + 60 * ln (1 / \<epsilon>))^3)"
    unfolding power_mult_distrib[symmetric] by simp
  finally have 18:"16^((l - 1) * nat\<lceil>ln \<Lambda> / ln (19/20)\<rceil>) \<le> 2 powr ((55 + 60 * ln (1 / \<epsilon>))^3)"
    by simp

  have "?L = real (size \<Psi>) * 16 ^ ((l - 1) * nat \<lceil>ln \<Lambda> / ln (19 / 20)\<rceil>)"
    unfolding \<Omega>.size by simp
  also have "... \<le> 2 powr (4*log 2 n+48*(log 2 (1/\<delta>)+16)^2)*2 powr ((55 + 60 * ln (1 / \<epsilon>))^3)"
    by (intro mult_mono 18 19) simp_all
  also have "... = 2 powr (4 * log 2 n + 48 * (log 2 (1 / \<delta>) + 16)^2 + (55 + 60 * ln (1 / \<epsilon>))^3)"
    unfolding powr_add[symmetric] by simp
  finally show ?thesis by simp
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

definition p where "p = (\<lambda>(f,g,h). card {j\<in> {..<b}. \<tau>\<^sub>1 (f,g,h) A 0 j \<ge> t f})"

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

unbundle no_intro_cong_syntax

end