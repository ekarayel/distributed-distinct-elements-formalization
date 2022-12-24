theory Basel_Sum_Approx
  imports "HOL.Transcendental" "HOL-Analysis.Interval_Integral"
begin

text \<open>Inspired by Integral_Test.sum_integral_diff_series_nonneg.\<close>
lemma riemann_approx:
  fixes f :: "real \<Rightarrow> real"
  assumes "\<And>x y. x \<ge> a \<Longrightarrow> y \<le> b \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<ge> f y"
  assumes "continuous_on {a..b} f"
  assumes "a \<le> b"
  shows "(\<Sum>k=a+1..b. f (of_int k)) \<le> integral {a..b} f" (is "?L \<le> ?R")
proof -
  note int = integrable_continuous_real[OF continuous_on_subset[OF assms(2)]]
  obtain j :: nat where m_def: "b = a + int j" 
    using zle_iff_zadd assms(3) by blast

  have "integral {a..a+int j} f = (\<Sum>k=a+1..a+int j. integral {k-1..k} f)" if "a + int j \<le> b" for j
    using that
  proof (induction j)
    case 0
    then show ?case by simp
  next
    case (Suc j)
    have "integral {a..a+int (Suc j)} f = integral {a..a+int j} f + integral {a+int j..a+int (Suc j)} f"
      using Suc(2) by (intro integral_combine[symmetric] int) auto 
    also have "... = (\<Sum>k=a+1..a+ int j. integral {k-1..k} f) + integral {a+int j..a+int (Suc j)} f"
      using Suc(2) by (intro arg_cong2[where f="(+)"] Suc(1)) auto
    also have "... = (\<Sum>k \<in> insert (a+int (Suc j)) {a+1..a+ int j}. integral {k-1..k} f)"
      by simp
    also have "... = (\<Sum>k \<in> {a+1..a+ int (Suc j)}. integral {k-1..k} f)"
      by (intro sum.cong) auto
    finally show ?case by simp
  qed
  hence a:"integral {a..b} f = (\<Sum>k=a+1..b. integral {k-1..k} f)"
    using m_def by simp

  have "?L = (\<Sum>k=a+1..b. integral {k-1..k} (\<lambda>_. f (of_int k)))"
    by simp
  also have "... \<le> (\<Sum>k=a+1..b. integral {k-1..k} f)"
    using assms by (intro sum_mono integral_le int) auto
  also have "... = ?R"
    using a by simp
  finally show ?thesis by simp
qed

lemma basel_sum: 
  assumes "k > 0"
  shows "(\<Sum>y\<in>{k+1..m}. 1 / real y^2) \<le> 1/real k" (is "?L \<le> ?R")
proof (cases "m \<ge> k")
  case True
  have "?L = (\<Sum>y\<in>int ` {k+1..m}. 1 / real_of_int y^2)"
    by (subst sum.reindex) auto
  also have "... = (\<Sum>y\<in>{int k+1..int m}. 1 / real_of_int y^2)"
    using image_int_atLeastAtMost by (intro sum.cong refl)  auto
  also have "... \<le> integral {int k..int m} (\<lambda>y. 1 / y^2)"
    using assms True by (intro riemann_approx frac_le power_mono continuous_intros) auto
  also have "... \<le> integral {real k..real m} (\<lambda>y. 1 / y^2)"
    by simp
  also have "... = (-(1/m))-(-(1/k))"
    using assms True has_real_derivative_iff_has_vector_derivative[symmetric]
    by (intro integral_unique[OF fundamental_theorem_of_calculus] of_nat_mono True)
     (auto intro!:derivative_eq_intros simp add:power2_eq_square)
  also have "... \<le> 1/k"
    by simp
  finally show ?thesis by simp
next
  case False
  thus ?thesis by simp
qed

end