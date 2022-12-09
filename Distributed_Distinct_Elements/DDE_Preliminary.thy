theory DDE_Preliminary
  imports Main "HOL-Probability.Probability_Mass_Function"  "Frequency_Moments.Frequency_Moments_Preliminary_Results"
    "Frequency_Moments.Product_PMF_Ext" "Median_Method.Median"

begin

lemma (in prob_space) pmf_exp_of_fin_function:
  assumes "M = measure_pmf p"
  assumes "finite A" "g ` set_pmf p \<subseteq> A"
  shows "expectation (\<lambda>\<omega>. f (g \<omega>)) = (\<Sum>y \<in> A. f y * prob {\<omega>. g \<omega> = y})"
    (is "?L = ?R")
proof -
  have "?L = integral\<^sup>L (map_pmf g p) f"
    using integral_map_pmf assms by simp
  also have "... = (\<Sum>a\<in>A. f a * pmf (map_pmf g p) a)"
    using assms(2,3)
    by (intro integral_measure_pmf_real) auto
  also have " ... = (\<Sum>y \<in> A. f y * prob (g -` {y}))"
    unfolding assms(1) by (intro sum.cong arg_cong2[where f="(*)"] pmf_map) auto
  also have "... = ?R"
    by (intro sum.cong) (auto simp add: vimage_def) 
  finally show ?thesis by simp
qed

lemma (in prob_space) pmf_rev_mono:
  assumes "M = measure_pmf p"
  assumes "\<And>x. x \<in> set_pmf p \<Longrightarrow> x \<notin> Q \<Longrightarrow> x \<notin> P"
  shows "prob P \<le> prob Q"
  using assms pmf_mono by blast

lemma (in prob_space) pmf_exp_mono:
  fixes f g :: "'a \<Rightarrow> real"
  assumes "M = measure_pmf p"
  assumes "integrable M f" "integrable M g"
  assumes "\<And>x. x \<in> set_pmf p \<Longrightarrow> f x \<le> g x"
  shows "integral\<^sup>L M f \<le> integral\<^sup>L M g"
  using assms(2,3,4) unfolding assms(1)
  by (intro integral_mono_AE AE_pmfI) auto

lemma (in prob_space) pmf_markov:
  assumes "M = measure_pmf p"
  assumes "integrable M f" "c > 0"
  assumes "\<And>x. x \<in> set_pmf p \<Longrightarrow> f x \<ge> 0" 
  shows "prob {\<omega>. f \<omega> \<ge> c} \<le> expectation f / c" (is "?L \<le> ?R")
proof -
  have a:"AE \<omega> in M. 0 \<le> f \<omega>" 
    unfolding assms(1) by (intro AE_pmfI assms(4)) auto
  have b:"{} \<in> events" 
    unfolding assms(1) by simp

  have "?L = \<P>(\<omega> in M. f \<omega> \<ge> c)"
    using assms(1) by simp
  also have "... \<le>  expectation f / c"
    by (intro integral_Markov_inequality_measure[OF _ b] assms a)
  finally show ?thesis by simp
qed

lemma pair_pmf_prob_left: 
  "measure_pmf.prob (pair_pmf A B) {\<omega>. P (fst \<omega>)} = measure_pmf.prob A {\<omega>. P \<omega>}" (is "?L = ?R")
proof -
  have "?L = measure_pmf.prob (map_pmf fst (pair_pmf A B)) {\<omega>. P \<omega>}"
    by (subst measure_map_pmf) simp
  also have "... = ?R"
    by (subst map_fst_pair_pmf) simp
  finally show ?thesis by simp
qed

lemma integrable_pmf_iff_bounded:
  fixes f :: "'a \<Rightarrow> real"
  assumes "\<And>x. x \<in> set_pmf p \<Longrightarrow> abs (f x) \<le> C"
  shows "integrable (measure_pmf p) f"
proof -
  obtain x where "x \<in> set_pmf p"
    using set_pmf_not_empty by fast
  hence "C \<ge> 0" using assms(1) by fastforce
  hence " (\<integral>\<^sup>+ x. ennreal (abs (f x)) \<partial>measure_pmf p) \<le> (\<integral>\<^sup>+ x. C \<partial>measure_pmf p)" 
    using assms ennreal_le_iff
    by (intro nn_integral_mono_AE AE_pmfI) auto
  also have "... = C"
    by simp
  also have "... < Orderings.top"
    by simp
  finally have "(\<integral>\<^sup>+ x. ennreal (abs (f x)) \<partial>measure_pmf p) < Orderings.top" by simp
  thus ?thesis 
    by (intro iffD2[OF integrable_iff_bounded]) auto
qed

lemma split_pair_pmf: 
  "measure_pmf.prob (pair_pmf A B) S = integral\<^sup>L A (\<lambda>a. measure_pmf.prob B {b. (a,b) \<in> S})" (is "?L = ?R")
proof -
  have a:"integrable (measure_pmf A) (\<lambda>x. measure_pmf.prob B {b. (x, b) \<in> S})"
    by (intro integrable_pmf_iff_bounded[where C="1"]) simp

  have "?L = (\<integral>\<^sup>+x. indicator S x \<partial>(measure_pmf (pair_pmf A B)))"
    by (simp add: measure_pmf.emeasure_eq_measure)
  also have "... = (\<integral>\<^sup>+x. (\<integral>\<^sup>+y. indicator S (x,y) \<partial>B) \<partial>A)"
    by (simp add: nn_integral_pair_pmf')  
  also have "... = (\<integral>\<^sup>+x. (\<integral>\<^sup>+y. indicator {b. (x,b) \<in> S} y \<partial>B) \<partial>A)"
    by (simp add:indicator_def)
  also have "... = (\<integral>\<^sup>+x. (measure_pmf.prob B {b. (x,b) \<in> S}) \<partial>A)"
    by (simp add: measure_pmf.emeasure_eq_measure)
  also have "... = ?R"
    using a
    by (subst nn_integral_eq_integral) auto
  finally show ?thesis by simp
qed

lemma card_ordered_pairs':
  fixes M :: "('a ::linorder) set" 
  shows "card {(x,y) \<in> M \<times> M. x < y} = card M * (card M - 1) / 2"
proof (cases "finite M")
  case True
  show ?thesis using card_ordered_pairs[OF True] by linarith 
next
  case False
  then obtain p where p_in: "p \<in> M" by fastforce
  let ?f= "(\<lambda>x. if x < p then (x,p) else (p,x))"
  have "False" if "finite {(x,y) \<in> M \<times> M. x < y}" (is "finite ?X")
  proof -
    have "?f ` (M-{p}) \<subseteq> ?X"
      using p_in by (intro image_subsetI) auto
    hence "finite (?f ` (M-{p}))" using that finite_subset by auto
    moreover have "inj_on ?f (M-{p})" 
      by (intro inj_onI) (metis Pair_inject)
    ultimately have "finite (M - {p})"
      using finite_imageD by blast
    hence "finite M"
      using finite_insert[where a="p" and A="M-{p}"] by simp
    thus "False" using False by simp
  qed
  hence "infinite ?X" by auto
  then show ?thesis using False by simp
qed

lemma MVT_symmetric:
  assumes "\<And>x. \<lbrakk>min a b \<le> x; x \<le> max a b\<rbrakk> \<Longrightarrow> DERIV f x :> f' x"
  shows "\<exists>z::real. min a b \<le> z \<and> z \<le> max a b \<and> (f b - f a = (b - a) * f' z)"
proof -
  consider (a) "a < b" | (b) "a = b" | (c) "a > b"
    by argo
  then show ?thesis
  proof (cases)
    case a
    then obtain z :: real where r: "a < z" "z < b" "f b - f a = (b - a) * f' z"
      using assms MVT2[where a="a" and b="b" and f="f" and f'="f'"] by auto
    have "a \<le> z" "z \<le> b" using r(1,2) by auto
    thus ?thesis using a r(3) by auto
  next
    case b
    then show ?thesis by auto
  next
    case c
    then obtain z :: real where r: "b < z" "z < a" "f a - f b = (a - b) * f' z"
      using assms MVT2[where a="b" and b="a" and f="f" and f'="f'"] by auto
    have "f b - f a = (b-a) * f' z" using r by argo
    moreover have "b \<le> z" "z \<le> a" using r(1,2) by auto
    ultimately show ?thesis using c by auto
  qed
qed

lemma MVT_interval:
  fixes I :: "real set"
  assumes "interval I" "a \<in> I" "b \<in> I"
  assumes "\<And>x. x \<in> I \<Longrightarrow> DERIV f x :> f' x"
  shows "\<exists>z. z \<in> I \<and> (f b - f a = (b - a) * f' z)"
proof -
  have a:"min a b \<in> I"
    using assms(2,3) by (cases "a < b") auto
  have b:"max a b \<in> I"
    using assms(2,3) by (cases "a < b") auto
  have c:"x \<in> {min a b..max a b} \<Longrightarrow> x \<in> I" for x
    using interval_def assms(1) a b by auto
  have "\<lbrakk>min a b \<le> x; x \<le> max a b\<rbrakk> \<Longrightarrow> DERIV f x :> f' x" for x
    using c assms(4) by auto
  then obtain z where z:"z \<ge> min a b" "z \<le> max a b" "f b - f a = (b-a) * f' z"
    using MVT_symmetric by blast
  have "z \<in> I"
    using c z(1,2) by auto
  thus ?thesis using z(3) by auto
qed

end