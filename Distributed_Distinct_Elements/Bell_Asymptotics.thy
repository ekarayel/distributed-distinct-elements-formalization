section \<open>Approximation of the Bell numbers\<close>

text \<open>Important note: I intend to move the formalization in this file to the existing AFP entry 
Bell_Numbers_Spivey, assuming Lukas Bulwahn has no objections --- if/after this submission is
accepted.\<close>

theory Bell_Asymptotics
  imports 
    Bell_Numbers_Spivey.Bell_Numbers 
    "HOL-Decision_Procs.Approximation"
    "Stirling_Formula.Stirling_Formula" 
    "Lambert_W.Lambert_W"
begin

subsection \<open>Some preliminary generic results\<close>

lemma powr_mono_rev:
  fixes x :: real
  assumes "a \<le> b" and  "x > 0" "x \<le> 1"
  shows "x powr b \<le> x powr a"
proof -
  have "x powr b = (1/x) powr (-b)"
    using assms by (simp add: powr_divide powr_minus_divide)
  also have "... \<le> (1/x) powr (-a)"
    using assms by (intro powr_mono) auto
  also have "... = x powr a"
    using assms by (simp add: powr_divide powr_minus_divide)
  finally show ?thesis by simp
qed

lemma exp_powr: "(exp x) powr y = exp (x*y)" for x :: real
  unfolding powr_def by simp

lemma fact_lower_bound:
  "sqrt(2*pi*n)*(n/exp(1))^n \<le> fact n" (is "?L \<le> ?R")
proof (cases "n > 0")
  case True
  have "ln ?L = ln (2*pi*n)/2 + n * ln n - n"
    using True by (simp add: ln_mult ln_sqrt ln_realpow ln_div algebra_simps)
  also have "... \<le> ln ?R" 
    by (intro ln_fact_bounds True)
  finally show ?thesis 
    using iffD1[OF ln_le_cancel_iff] True by simp
next
  case False
  then show ?thesis by simp
qed

text \<open>This is a loose lower bound for the factorials used in the proof by Berend and Tassa.\<close>

lemma fact_lower_bound_1:
  assumes "n > 0"
  shows "(n/exp 1)^n \<le> fact n" (is "?L \<le> ?R")
proof -
  have "2 * pi \<ge> 1" using pi_ge_two by auto
  moreover have "n \<ge> 1" using assms by simp
  ultimately have "2 * pi * n \<ge> 1*1" 
    by (intro mult_mono) auto
  hence a:"2 * pi * n \<ge> 1" by simp 

  have "?L = 1 * ?L" by simp
  also have "... \<le> sqrt(2 * pi * n) * ?L"
    using a by (intro mult_right_mono) auto
  also have "... \<le> ?R"
    using fact_lower_bound by simp
  finally show ?thesis by simp
qed

subsection \<open>Fast evaluation of Bell numbers\<close>

text \<open>The proof by Berend and Tassa below requires explicit values of the Bell numbers upto 54.
It however is difficult/extremely slow to compute Bell numbers in that range without dynamic 
programming (DP). The following is a DP algorithm derived from the recursion formula 
@{thm [source] Bell_recursive_eq}.\<close>

fun bell_list_aux :: "nat \<Rightarrow> nat list"
  where 
  "bell_list_aux 0 = [1]" |
  "bell_list_aux (Suc n) = (
    let x = bell_list_aux n; 
        y = sum_list (map (\<lambda>(k, z). z * (n choose (n-k))) (List.enumerate 0 x)) 
    in y#x)"

definition bell_list :: "nat \<Rightarrow> nat list"
  where "bell_list n = rev (bell_list_aux n)"

lemma bell_list_eq: "bell_list n = map Bell [0..<n+1]"
proof -
  have "bell_list_aux n = rev (map Bell [0..<Suc n])"
  proof (induction n)
    case 0
    then show ?case by (simp add:Bell_0)
  next
    case (Suc n)
    define x where "x = bell_list_aux n"
    define y where "y = sum_list (map (\<lambda>(k,z). z * (n choose (n-k))) (List.enumerate 0 x))"
    define sn where "sn = n+1"
    have b:"x = rev (map Bell [0..<sn])"
      using Suc x_def sn_def by simp
    have c: "length x = sn"
      unfolding b by simp

    have "snd i = Bell (n - fst i)" if "i \<in> set (List.enumerate 0 x)" for i
    proof -
      have "fst i < length x" "snd i = x ! fst i" 
        using iffD1[OF in_set_enumerate_eq that] by auto
      hence "snd i = Bell (sn - Suc (fst i))"
        unfolding b by (simp add:rev_nth)
      thus ?thesis
        unfolding sn_def by simp
    qed

    hence "y = sum_list (map (\<lambda>i. Bell (n-fst i) * (n choose (n-fst i))) (List.enumerate 0 x))"
      unfolding y_def by (intro arg_cong[where f="sum_list"] map_cong refl)  
        (simp add:case_prod_beta)
    also have "... = sum_list (map (\<lambda>i. Bell (n-i) * (n choose (n-i))) (map fst (List.enumerate 0 x)))"
      by (subst map_map) (simp add:comp_def)
    also have "... = (\<Sum>i= 0..<length x. Bell (n-i) * (n choose (n-i)))"
      by (simp add:interv_sum_list_conv_sum_set_nat)
    also have "... = (\<Sum>i\<le>n. Bell (n-i) * (n choose (n-i)))"
      using c sn_def by (intro sum.cong) auto
    also have "... = (\<Sum>i \<in> (\<lambda>k. n- k) ` {..n}. Bell i * (n choose i))"
      by (subst sum.reindex, auto simp add:inj_on_def)
    also have "... = (\<Sum>i \<le> n. Bell i * (n choose i))"
      by (intro sum.cong refl iffD2[OF set_eq_iff] allI)
        (simp add:image_iff atMost_def, presburger)  
    also have "... = Bell (Suc n)"
      using Bell_recursive_eq by (simp add:mult.commute)
    finally have a: "y = Bell (Suc n)" by simp

    have "bell_list_aux (Suc n) = y#x"
      unfolding x_def y_def by (simp add:Let_def)
    also have "... = Bell (Suc n)#(rev (map Bell [0..<Suc n]))"
      unfolding a b sn_def by simp
    also have "... = rev (map Bell [0..<Suc (Suc n)])"
      by simp
    finally show ?case by simp
  qed
  thus "bell_list n = map Bell [0..<n+1]"
    by (simp add:bell_list_def)
qed

subsection \<open>Dobi\'{n}ski's Formula\<close>

lemma dobinskis_formula_raw: "(\<lambda>k. real k^n / fact k) sums (exp 1 * Bell n)"
proof (induction n rule:nat_less_induct)
  case (1 n)
  show ?case 
  proof (cases n)
    case 0
    have "(\<lambda>k. (1::real) ^ k /\<^sub>R fact k) sums (exp 1)"
      by (intro exp_converges) 
    thus "(\<lambda>k. real k ^ n / fact k) sums (exp 1 * Bell n)"
      using 0 Bell_0 by (simp add:divide_inverse)
  next
    case (Suc m)
    have a: "real (k + 1) = real k+1" for k by simp

    have "(\<lambda>k. (\<Sum>j \<le> m. real (m choose j) *\<^sub>R (real k ^ j / fact k))) sums 
      (\<Sum>j \<le> m. real (m choose j) *\<^sub>R (exp 1 * Bell j))" (is "?L sums ?R")
      using Suc by (intro sums_sum sums_scaleR_right mp[OF spec[OF 1]]) simp
    hence "(\<lambda>k. (\<Sum>j \<le> m. real (m choose j) * (real k) ^ j * 1 ^ (m-j)) / fact k) sums
     (\<Sum>j \<le> m. exp 1 * real (m choose j) * Bell j)" 
      by (subst sum_divide_distrib) (simp add:algebra_simps)
    hence "(\<lambda>k. (real k+1) ^ m / fact k) sums (exp 1 * real (Bell (m+1)))" 
      unfolding binomial_ring Bell_recursive_eq by (simp add:sum_distrib_left algebra_simps)
    hence "(\<lambda>k. real (k+1) ^ m / fact k) sums (exp 1 * real (Bell (m+1)))" 
      by (subst a) simp
    hence "(\<lambda>k. real (k+1) ^ (m+1) / fact (Suc k)) sums (exp 1 * real (Bell (m + 1)))" 
      unfolding fact_Suc by simp
    hence "(\<lambda>k. real k ^ (m+1) / fact k) sums (exp 1 * Bell (m+1) + real 0^(m+1) / fact 0)"
      by (intro sums_Suc) simp
    hence "(\<lambda>k. real k ^ (m+1) / fact k) sums (exp 1 * Bell (m+1))"
      by simp
    thus "(\<lambda>k. real k ^ n / fact k) sums (exp 1 * Bell n)" 
      using Suc by simp
  qed
qed

theorem dobinskis_formula:
  shows "summable (\<lambda>k. real k^n / fact k)"
  and "Bell n = 1 / exp 1 * (\<Sum>k. real k^n / fact k)"
  using sums_summable dobinskis_formula_raw[of n] sums_unique
  by (auto simp add:algebra_simps eq_divide_eq)

subsection \<open>Approximation by Berend and Tassa\<close>

text \<open>In this subsection we verify \cite[Theorem 2.2]{berend2010} for the Bell numbers, which is the
approximation formula:
\[
  B_n < \left( \frac{e^{-0.6+\varepsilon} n}{\ln(n+1)} \right)^n
\]
iff $n \geq 55$ and $\eps > d(n)$ which is defined by 
$d(n) := \ln \ln (n+1) - \ln \ln n + \frac{1+e^{-1}}{\ln n}$.

The following is the corresponding Isabelle definition for $d$ above.\<close>

definition bell_approx_d :: "real \<Rightarrow> real" 
  where "bell_approx_d x = ln (ln (x+1)) - ln (ln x)  + (1 + exp(-1))/ln x" 

lemma bell_approx_d_nonneg: 
  assumes "1 < x"
  shows "bell_approx_d x \<ge> 0"
proof-
  have "(0::real) \<le> 0 + 0" by simp
  also have "... \<le> (ln (ln(x+1)) - ln (ln x)) + (1 + exp(-1))/ln x"
    using assms by (intro add_mono) auto
  also have "... = bell_approx_d x"
    unfolding bell_approx_d_def by simp
  finally show ?thesis by simp
qed

lemma bell_approx_d_decreasing:
  assumes "1 < x" "x \<le> y"
  shows "bell_approx_d y \<le> bell_approx_d x"
proof -
  have y_ge_1: "y > 1" using assms by auto

  have "ln (y+1)/ln y = 1+(ln (y+1)-ln y)/ln y"
    using y_ge_1 by (simp add:algebra_simps diff_divide_distrib)
  also have "... = 1 + ln(1+1/y)* (1/ln y)"
    using y_ge_1 by (subst ln_div[symmetric])
    (auto simp add:algebra_simps add_divide_distrib)
  also have "... \<le> 1 + ln(1+1/x) *(1/ln x)"
    using y_ge_1 assms
    by (intro add_mono mult_mono iffD2[OF ln_le_cancel_iff] add_pos_pos divide_left_mono) auto
  also have "... = 1+(ln (x+1)-ln x)/ln x"
    using assms by (subst ln_div[symmetric])
     (auto simp add:algebra_simps add_divide_distrib)
  also have "... = ln (x+1)/ln x"
    using assms by (simp add:algebra_simps diff_divide_distrib)
  finally have a:"ln (y+1)/ln y \<le> ln (x+1)/ln x"
    by simp
  have "ln (ln (y+1)) - ln (ln y) = ln (ln(y+1)/ln y)"
    using y_ge_1 by (subst ln_div) auto 
  also have "... \<le> ln (ln(x+1)/ln x)"
    using assms y_ge_1
    by (intro iffD2[OF ln_le_cancel_iff] a divide_pos_pos) auto
  also have "... = ln (ln (x+1)) - ln (ln x)"
    using assms by (subst ln_div) auto 
  finally have b:"ln (ln (y+1)) - ln (ln y) \<le> ln (ln (x+1)) - ln (ln x)"
    by simp
  show ?thesis
    unfolding bell_approx_d_def using y_ge_1 assms
    by (intro add_mono b divide_left_mono iffD2[OF ln_le_cancel_iff])
     auto
qed

text \<open>The theorem bellow corresponds to Theorem 2.2 from Berend and Tassa for the Bell numbers. 
Whenever possible I attached facts derived here with the corresponding Equation from their proof.

They introduce a generalization of the bell numbers called the Bell function defined
on the positive real numbers. Because I could not find any other sources that make use of that
generalization, I avoided introducing it, so the result below is a restriction of their theorem
to the "classical" Bell numbers.

Another distinction is that they define the extremal point $x_0$ of the function $h$ implicitly, 
while here a closed form expression is derived using the Lambert W function.\<close>

theorem bell_approx_1:
  assumes "bell_approx_d n \<le> \<epsilon>"
  assumes "n \<ge> 55"
  shows "real (Bell n) < (exp (-0.6+\<epsilon>) * n / ln (n + 1)) powr n" (is "?L < ?R")
proof -
  have apx:
    "exp(-0.0007::real) powr 55 < 0.97"
    "exp(-55::real) \<le> 0.03" 
    "2 * exp (- 1) \<le> (1::real)"
    "exp 1 \<le> (55::real)" 
    "exp 4 \<le> (110::real)"
    "ln (1 + 1 / exp 1) - 1 + (ln 55 + ln 2) / (55::real) \<le> - 0.6007"
    by (approximation 13)+

  text \<open>Since n > 0 we can omit the first term from Dobi\'{n}ski's formula.\<close>
  have zero_pow_n: "0^n = (0::real)" 
    using assms by simp
  have dobinski_suc: "(\<lambda>k. real (Suc k)^n / fact (Suc k)) sums (exp 1 * Bell n)"
    using dobinskis_formula_raw[of n] 
    by (intro iffD2[OF sums_Suc_iff]) (simp add:zero_pow_n)

  let ?p = "real n"

  have "0 \<le> bell_approx_d n" 
    using assms(2) by (intro bell_approx_d_nonneg) simp
  also have "... \<le> \<epsilon>" using assms(1) by simp
  finally have \<epsilon>_ge_0: "\<epsilon> \<ge> 0" by simp

  text \<open>The definitions @{term "\<alpha>"}, @{term "h"}, @{term "v"}, @{term "x0"} bellow correspond 
  to the variables of the same name from Lemma~3.1 and Theorem~2.2 from Berend and Tassa.\<close>

  define \<alpha> :: real where "\<alpha> = 1+1/exp 1"
  define h where "h = (\<lambda>x. x + ?p * ln x - x * ln x)"
  define h' where "h' = (\<lambda>x. ?p / x - ln x)"
  define h_max where "h_max = ?p * (ln ?p - ln (ln (?p+1))+\<epsilon>+ln \<alpha>-1)"
  define h_ub where "h_ub = (\<lambda>x. if x < 2*n then h_max else - (Suc x))"

  text \<open>This is the extremum of the function h.\<close>
  define x0 :: real where "x0 = exp (Lambert_W ?p)"

  define v :: "real \<Rightarrow> real" where "v = (\<lambda>x. \<alpha> * ln \<alpha> + (\<alpha>-1)*ln x - \<alpha>*ln (ln x))"
  define v' :: "real \<Rightarrow> real" where "v' = (\<lambda>x. (\<alpha>-1)/x - \<alpha>/(x*ln x))"

  text \<open>This is the zero point of the function @{term "v"}.\<close>
  define v0 :: real where "v0 = exp (exp 1+1)"

  have \<alpha>_gt_1: "\<alpha> > 1" 
    unfolding \<alpha>_def by (approximation 5)
  have v0_gt_1: "v0 > 1" 
    unfolding v0_def by (approximation 4)
  have v0_le_55: "v0 \<le> 55" 
    unfolding v0_def by (approximation 7)

  have "(v has_real_derivative (v' x)) (at x)" if "x > 1" for x
    unfolding v_def v'_def using that
    by (auto intro!: derivative_eq_intros)
  hence v_deriv: "(v has_real_derivative (v' x)) (at x)" if "x \<ge> v0" for x
    using that v0_gt_1 by simp

  have v_deriv_nonneg: "v' x \<ge> 0" if "x \<ge> v0" for x
  proof -
    have "0 \<le> (\<alpha>-1)*ln v0 - \<alpha>"
      unfolding \<alpha>_def v0_def by (simp add:algebra_simps add_divide_distrib) 
    also have "... \<le> (\<alpha>-1)*ln x - \<alpha>"
      using that v0_gt_1 \<alpha>_gt_1
      by (intro diff_mono mult_left_mono ln_le_cancel_iff[THEN iffD2]) auto
    finally have "0 \<le> (\<alpha>-1)*ln x - \<alpha>" by simp
    hence "0 \<le> ((\<alpha>-1)*ln x - \<alpha>) / (x*ln x)"
      using that v0_gt_1
      by (intro divide_nonneg_nonneg mult_nonneg_nonneg) auto
    also have "... = (\<alpha>-1)*ln x/(x*ln x) - \<alpha>/(x*ln x)"
      by (simp add:diff_divide_distrib)
    also have "... = v' x"
      using that v0_gt_1 unfolding v'_def by simp 
    finally show ?thesis by simp
  qed

  have v_mono: "v x \<le> v y" if "x \<le> y" "x \<ge> v0" for x y
    using v_deriv v_deriv_nonneg that order_trans
    by (intro DERIV_nonneg_imp_nondecreasing[OF that(1)]) blast

  have "v v0 = v (exp(\<alpha>/(\<alpha>-1)))"
    unfolding v0_def \<alpha>_def
    by (simp add:algebra_simps)
  also have "... = \<alpha> * ln \<alpha> + \<alpha> -  \<alpha> * ln (\<alpha> / (\<alpha> - 1))"
    using \<alpha>_gt_1 unfolding v_def by simp
  also have "... = \<alpha> * (ln \<alpha> + 1 - ln \<alpha> + ln (\<alpha>-1))"
    using \<alpha>_gt_1 by (simp add:algebra_simps ln_div)
  also have "... = 0"
    unfolding \<alpha>_def by (simp add:ln_div)
  finally have v_zero: "v v0 = 0" by simp 

  text \<open>The following block corresponds to Eq. 24.\<close>
  have x0_ge_1: "x0 \<ge> 1" unfolding x0_def by simp 
  have "- exp (-1) \<le> (0::real)" using exp_ge_zero by simp
  also have "... \<le> real n" by simp
  finally have "- exp (- 1) \<le> real n" by simp
  hence eqn_24: "x0 * ln x0 = ?p"
    unfolding  x0_def by (auto intro!: Lambert_W_times_exp_self') 

  text \<open>The following block corresponds to Eq. 25.\<close>
  have eqn_25: "x0 \<le> \<alpha> * ?p / ln ?p"
  proof (rule ccontr)
    assume "\<not> x0 \<le> \<alpha> * ?p / ln ?p"
    hence eqn_25_1: "\<alpha> * ?p / ln ?p < x0" by simp
    have "1 * ln (real n) \<le> \<alpha> * real n" 
      using \<alpha>_gt_1  assms(2)
      by (intro mult_mono less_imp_le[OF ln_less_self]) auto
    hence "(\<alpha> * ?p / ln ?p) * ln (\<alpha> * ?p / ln ?p) < x0 * ln x0" 
      using x0_ge_1 \<alpha>_gt_1 assms(2)
      by (intro mult_strict_mono iffD2[OF ln_less_cancel_iff] eqn_25_1) auto
    also have "... = ?p"
      using eqn_24 by simp
    finally have "?p * (\<alpha> / ln ?p * ln (\<alpha> * ?p / ln ?p)) < ?p * 1" 
      by (simp add:algebra_simps)
    hence "\<alpha> / ln ?p * ln (\<alpha> * ?p / ln ?p) < 1" 
      using assms(2) by (subst (asm) mult_less_cancel_left, simp)
    hence "\<alpha> * (ln \<alpha> + ln ?p - ln (ln ?p)) < ln ?p"
      using assms(2) \<alpha>_gt_1 by (simp add: ln_mult ln_div) 
    hence "v ?p < 0" (* rev of Eq. 26 *)
      by (simp add: v_def algebra_simps)
    also have "... = v v0"
      using v_zero by simp
    also have "... \<le> v ?p"
      using assms(2) v0_le_55 by (intro v_mono) auto
    finally have "v ?p < v ?p" by simp
    thus "False" by simp
  qed

  define sum_h_ub where "sum_h_ub = (2* ?p) * exp h_max + exp(-(2*?p+1))/(1-exp(-1))"

  have "(\<lambda>x. exp (- (1::real)) ^ x) sums (1 / (1 - exp (- 1)))" 
    by (intro geometric_sums) auto
  hence "(\<lambda>x. exp (- 1) powr real x) sums (1 / (1 - exp (- 1)))" 
    by (subst powr_realpow) simp
  hence "(\<lambda>k. (exp(-1) *\<^sub>R exp(-1) powr k) *\<^sub>R exp (-2*?p)) 
    sums ( (exp(-1) *\<^sub>R (1/(1-exp(-1)))) *\<^sub>R exp(-2*?p))"
    by (intro sums_scaleR_left sums_scaleR_right)
  hence "(\<lambda>k. exp (h_ub (k + 2*n))) sums (exp(-(2*?p+1))/(1-exp(-1)))"
    unfolding h_ub_def by (simp add:exp_powr exp_add[symmetric] algebra_simps)
  hence "(\<lambda>n. exp (h_ub n)) sums ((exp(-(2*?p+1))/(1-exp(-1))) + sum (\<lambda>n. exp (h_ub n)) {..<2*n})"
    by (intro iffD1[OF sums_iff_shift])
  hence a:"(\<lambda>n. exp (h_ub n)) sums sum_h_ub"
    unfolding sum_h_ub_def h_ub_def by (simp add:algebra_simps)

  have h_deriv: "(h has_real_derivative (h' x)) (at y)" if "x > 0" "y = x" for x y
    unfolding h_def h'_def using that
    by (auto intro!: derivative_eq_intros)

  have h'_ge_0: "h' x \<ge> 0" if "x \<le> x0" "x \<ge> 1" for x
  proof -
    have "ln x * x \<le> ln x0 * x0"
      using that by (intro mult_mono iffD2[OF ln_le_cancel_iff]) auto
    also have "... = ?p" 
      using eqn_24 by (simp add:algebra_simps)
    finally have "ln x * x \<le> ?p" by simp
    thus ?thesis
      using that unfolding h'_def by (simp add: mult_imp_le_div_pos)
  qed
  hence "\<exists>y. (h has_real_derivative y) (at x) \<and> y \<ge> 0" if "x \<le> x0" "x \<ge> 1" for x
    using that x0_ge_1 by (intro exI[where x="h' x"] h_deriv conjI) auto
  hence h_max_1: "h x \<le> h x0" if "x \<le> x0" " x\<ge>1" for x
    using  that
    by (intro DERIV_nonneg_imp_nondecreasing[OF that(1)]) simp

  have "h' x \<le> 0" if "x \<ge> x0" for x
  proof -
    have "?p = ln x0 * x0"
      using eqn_24 by (simp add:algebra_simps)
    also have "... \<le> ln x * x"
      using that x0_ge_1 by (intro mult_mono iffD2[OF ln_le_cancel_iff]) auto
    finally have "?p \<le> ln x * x" by simp
    thus ?thesis
      using that x0_ge_1 unfolding h'_def by (simp add:pos_divide_le_eq)
  qed
  hence "\<exists>y. (h has_real_derivative y) (at x) \<and> y \<le> 0" if "x \<ge> x0" for x
    using that x0_ge_1 by (intro exI[where x="h' x"] h_deriv conjI) auto
  hence h_max_2: "h x0 \<ge> h x" if "x0 \<le> x" for x
    by (intro DERIV_nonpos_imp_nonincreasing[OF that]) 

  have h_max: "h x \<le> h x0" if "x \<ge> 1" for x
    using h_max_1 h_max_2 that by (cases "x \<ge> x0") auto

  text \<open>The following block corresponds to Eq. 29.\<close>
  have eqn_29: "h x \<le> h_max" if "x \<ge> 1" for x
  proof -
    have "h x \<le> h x0" 
      using that by (intro h_max) auto
    also have "... = x0 + ?p * ln x0 - ?p"
      unfolding h_def eqn_24 by (simp add:algebra_simps)
    also have "... \<le> \<alpha> * ?p / ln ?p + ?p * ln (\<alpha> * ?p / ln ?p) - ?p"
      using that assms x0_ge_1 \<alpha>_gt_1
      by (intro add_mono diff_mono eqn_25 mult_mono iffD2[OF ln_le_cancel_iff]) auto
    also have "... = \<alpha> * ?p / ln ?p  + ?p * ln ?p - ?p * ln (ln ?p) + ?p * (ln \<alpha> - 1)"
      using assms \<alpha>_gt_1 by (simp add: ln_div ln_mult algebra_simps)
    also have "... = ?p * (\<alpha> / ln ?p + ln ?p - ln (ln (?p)) + (ln \<alpha> - 1))"
      by (simp add:algebra_simps)
    also have "... = ?p * (bell_approx_d ?p + ln ?p - ln (ln (?p + 1)) + ln \<alpha> - 1)"
      unfolding bell_approx_d_def \<alpha>_def by (simp add:exp_minus inverse_eq_divide) 
    also have "... \<le> ?p * (\<epsilon> + ln ?p - ln (ln (?p + 1)) + ln \<alpha> - 1)" (* 29 *)
      by (intro mult_left_mono add_mono diff_mono assms(1)) simp_all
    also have "... = h_max" unfolding h_max_def by simp
    finally show ?thesis by simp
  qed

  text \<open>The following block corresponds to Eq. 30.\<close>
  have eqn_30: "h x \<le> - x" if "x \<ge> 2*?p" for x
  proof -
    have "exp 4 \<le> 2*?p" using assms apx by simp
    also have "... \<le> x" using that by simp
    finally have eqn_30_1:  "exp 4 \<le> x" by simp

    have "h x = x - (x - ?p) * ln x"
      unfolding h_def by (simp add:algebra_simps)
    also have "... \<le> x - (x - x/2) * ln x"
      using assms(2) that by (intro diff_mono mult_right_mono) auto
    also have "... \<le> x - (x/2) * ln x"  by simp
    also have "... \<le> x - (x/2) * 4"
      using that assms
      by (intro diff_mono mult_left_mono iffD2[OF ln_ge_iff] eqn_30_1) auto
    also have "... = - x" by simp
    finally show ?thesis by simp
  qed

  have b: "real (Suc k) ^ n / fact (Suc k) \<le> exp (h_ub k)" 
    (is "?L1 \<le> ?R1")  for k 
  proof -
    define sk where "sk = (Suc k)"
    have sk_gt_0: "sk > 0" unfolding sk_def by simp
    have "?L1 \<le> real sk ^ n / (real sk / exp(1))^(sk)"
      unfolding sk_def
      by (intro divide_left_mono fact_lower_bound_1) auto
    also have "... = real sk ^ n * exp(1)^sk / real sk^sk"
      by (simp add:power_divide)
    also have "... = exp (ln (real sk ^ n * exp(1)^sk / real sk^sk))"
      using sk_gt_0 assms(2) by (subst exp_ln) auto
    also have "... = exp ( h(real sk))"
      unfolding h_def
      using sk_gt_0 assms(2) by (simp add: ln_div ln_mult ln_realpow)
    also have "... = exp (h (real (Suc k)))"
      unfolding sk_def by simp
    also have "... \<le> exp (h_ub k)" 
      using eqn_29[where x="real (Suc k)"] eqn_30[where x="real (Suc k)"]
      unfolding  h_ub_def by (simp add:not_less) 
    finally show ?thesis by simp
  qed

  have "exp(-1) = exp(-1) * 1" by simp
  also have "... \<le> exp(-0.6+\<epsilon>) * (?p / ln (1+?p))"
    using \<epsilon>_ge_0 assms
    by (intro mult_mono iffD2[OF pos_le_divide_eq])
     (auto simp add:ln_add_one_self_le_self)
  also have "... = exp (-0.6 + \<epsilon>) * ?p / ln (?p + 1)" by simp
  finally have c: "exp (-1) \<le> exp (-0.6 + \<epsilon>) * ?p / ln (?p + 1)" by simp

  text \<open>The following block corresponds to Eq.~32 and 33.\<close>
  have "sum_h_ub \<le> (2 * ?p) * exp(h_max)  + exp(-(2*?p)) * (exp(-1)/(1-exp(-1)))"
    unfolding sum_h_ub_def by (simp add:exp_add[symmetric])
  also have "... \<le> (2 * ?p) * exp(h_max) + exp(-(2*?p)) * 1"
    using apx by (intro add_mono mult_left_mono) auto
  also have "... = ((2 * real n) powr (1/n)) powr n * 
    (exp (ln (?p) - ln (ln (?p + 1)) + (\<epsilon> + ln \<alpha> - 1))) powr n + exp (- (2*?p))"
    unfolding h_max_def exp_powr by (simp add:algebra_simps powr_powr)
  also have "... = ((2 * ?p) powr (1/n)) powr n * 
    (n / ln (?p+1) * exp ((\<epsilon> + ln \<alpha> - 1))) powr n + exp (- (2 * ?p))"
    using assms by (simp add: exp_add exp_diff algebra_simps)
  also have "... = ((2 * ?p) powr (1/?p) * ((n / ln (?p+1) * exp ((\<epsilon> + ln \<alpha> - 1))))) powr n
    + exp (- (2 * ?p))"
    by (subst powr_mult[symmetric]) auto
  also have "... = (2 powr (1/?p) * ?p powr (1/?p) * 
    ((n / ln (?p+1) * exp (\<epsilon>+ln \<alpha>-1)))) powr n + exp (- (2 * ?p))"
    by (simp add:powr_mult)
  also have "... = (2 powr (1/?p) * exp (ln(?p)/?p) * 
    ((n / ln (?p+1) * exp (\<epsilon>+ln \<alpha>-1)))) powr n + exp (- (2 * ?p))"
    by (simp add:powr_def) 
  also have "... \<le> (2 powr (1/55) * exp (ln(55)/55) * 
    ((n / ln (?p+1) * exp (\<epsilon>+ln \<alpha>-1)))) powr n + exp (- (2 * ?p))"
    using assms apx by (intro add_mono powr_mono2 mult_mono 
        iffD2[OF exp_le_cancel_iff] ln_x_over_x_mono) auto
  also have "... = (n / ln (?p+1) * 
    exp (\<epsilon> + (ln (1+1/exp 1) - 1 + (ln (55) + ln(2)) / 55))) powr n + exp (- (2 * ?p))"
    by (simp add:powr_def exp_add[symmetric] \<alpha>_def)
  also have "... \<le> (n / ln (?p+1) * exp (\<epsilon> + (-0.6007))) powr n + exp (-(2*?p))"
    using apx by (intro add_mono powr_mono2 mult_left_mono iffD2[OF exp_le_cancel_iff]) auto
  text \<open>The following block corresponds to Eq.~35.\<close>
  also have "... = (exp (-0.6007+\<epsilon>) * n / ln (?p+1)) powr n + exp(-2*?p)" 
    by (simp add:algebra_simps)
  also have "... = ?R * exp(-0.0007) powr n + exp(-1) powr n *exp(-n)"
    by (subst powr_mult[symmetric]) 
      (auto simp add:algebra_simps exp_add[symmetric] exp_powr)
  also have "... \<le> ?R * exp(-0.0007) powr 55 + exp(-1) powr n *exp(-55)"
    using assms by (intro add_mono mult_left_mono powr_mono_rev) auto
  also have "... < ?R * 0.97 + exp(-1) powr n * 0.03"
    using assms(2)
    by (intro add_less_le_mono mult_strict_left_mono mult_left_mono apx) auto 
  also have "... \<le> ?R * 0.97 + ?R * 0.03"
    by (intro add_mono mult_right_mono powr_mono2 c) auto
  also have "... = ?R" by simp
  finally have d: "sum_h_ub < ?R" by simp

  have "?L = 1 * real (Bell n)" by simp
    also have "... \<le> exp 1 * Bell n"
    by (intro mult_right_mono) auto
  also have "... \<le> sum_h_ub"
    by (intro sums_le[OF b dobinski_suc a])
  also have "... < ?R"
    by (intro d)
  finally show ?thesis by simp
qed

subsection \<open>Approximation for all numbers\<close>

text \<open>Berend and Tassa also show an approximate formula that is true for all
Bell numbers~\cite[Theorem 2.1]{berend2010}:
\[
  B_n \leq \left( \frac{0.792 n}{ \ln (n+1)} \right)^n
\]
Their proof uses the previous result for $n \geq 55$, and for the cases $n=0,\ldots,54$ the 
formula is verified explicitly.\<close>

theorem bell_approx_2: "real (Bell n) \<le> (0.792 * n / ln (n + 1)) ^ n"
proof -
  consider 
    (i) "n = 0" | (ii) "n \<ge> 1 \<and> n \<le> 54" | (iii) "n \<ge> 55"
    by linarith
  then show ?thesis
  proof cases
    case i
    then show ?thesis by (simp add:Bell_0)
  next
    case ii

    define bell_init_seg where "bell_init_seg = drop 1 (List.enumerate 0 (bell_list 54))"
    define condition :: "(nat \<times> nat \<Rightarrow> bool)" 
      where "condition = (\<lambda>(k, bk). real bk < (0.792 * k / ln (real k + 1)) powr k)"
  
    have filter_empty_intros:
      "filter P xs = [] \<Longrightarrow> \<not>(P x) \<Longrightarrow> filter P (x#xs) = []"
      "filter P [] = []" for x xs and P :: "nat \<times> nat \<Rightarrow> bool"
      by auto
  
    have a:"[] = filter (Not \<circ> condition) bell_init_seg"
      apply (simp add: bell_init_seg_def numeral_eq_Suc)
      apply normalization
      apply (intro filter_empty_intros)
      by (simp add:condition_def not_le del:powr_numeral, approximation 15)+
  
    have "bell_init_seg = List.enumerate 1 (map Bell [1..<55])"
      unfolding bell_init_seg_def bell_list_eq  enumerate_eq_zip drop_zip drop_map
      by simp
    hence "set bell_init_seg = {i. fst i \<ge> 1 \<and> fst i < 55 \<and> snd i = Bell (fst i)}"
      by (intro iffD2[OF set_eq_iff] allI) (auto simp add:in_set_enumerate_eq)
    hence "(n, Bell n) \<in> set bell_init_seg"
      using ii by simp
    hence "condition (n, Bell n)" 
      using a by (simp add: empty_filter_conv) 
  
    then show ?thesis 
      using ii unfolding condition_def by (simp add: powr_realpow)
  next
    case iii
    define \<epsilon> :: real where "\<epsilon> = ln 0.792 + 0.6"
    have "bell_approx_d n \<le> bell_approx_d 55"
      using iii by (intro bell_approx_d_decreasing) auto
    also have "... \<le> \<epsilon>"
      unfolding bell_approx_d_def \<epsilon>_def by (approximation 10)
    finally have "bell_approx_d n \<le> \<epsilon>" by simp
    hence "real (Bell n) < (exp (-0.6+\<epsilon>) * n / ln (real n + 1)) powr n"
      using iii by (intro bell_approx_1) auto
    also have "... = (0.792 * n / ln (real n + 1)) ^ n"
      using iii unfolding \<epsilon>_def
      by (subst powr_realpow, auto)
    finally show ?thesis by simp
  qed
qed

end