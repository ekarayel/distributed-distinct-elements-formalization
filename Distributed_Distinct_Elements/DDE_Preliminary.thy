theory DDE_Preliminary
  imports Main "HOL-Probability.Probability_Mass_Function"  "Frequency_Moments.Frequency_Moments_Preliminary_Results"
begin

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

lemma split_pair_pmf: 
  "measure_pmf.prob (pair_pmf A B) S = integral\<^sup>L A (\<lambda>a. measure_pmf.prob B {b. (a,b) \<in> S})" (is "?L = ?R")
proof -
  have " (\<integral>\<^sup>+ x. ennreal (measure_pmf.prob B {b. (x, b) \<in> S}) \<partial>A) \<le> (\<integral>\<^sup>+ x. 1 \<partial>A)" 
    by (intro nn_integral_mono) simp
  also have "... = 1"
    by simp
  also have "... < Orderings.top"
    by simp
  finally have "(\<integral>\<^sup>+ x. ennreal (measure_pmf.prob B {b. (x, b) \<in> S}) \<partial>A) < Orderings.top" by simp
  hence a:"integrable (measure_pmf A) (\<lambda>x. measure_pmf.prob B {b. (x, b) \<in> S})"
    by (simp add: integrable_iff_bounded )

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


end