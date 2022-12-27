theory DDE_Transcendental_Extras
  imports "Stirling_Formula.Stirling_Formula" 
begin

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

end