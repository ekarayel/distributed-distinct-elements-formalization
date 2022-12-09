theory E4
  imports E3
begin

context inner_algorithm_fix_A 
begin

definition E\<^sub>4 where "E\<^sub>4 = (\<lambda>(f,g,h). \<bar>p (f,g,h) - \<rho> (card (R f))\<bar> \<le> real_of_rat \<delta>/12 * card (R f))"

lemma e_4: "\<Psi>.prob {\<psi>. E\<^sub>1 \<psi> \<and> E\<^sub>2 \<psi> \<and> E\<^sub>3 \<psi> \<and> \<not>E\<^sub>4 \<psi>} \<le> 1/2^6" (is "?L \<le> ?R")
proof -
  show ?thesis sorry
qed

lemma (in prob_space)
  assumes "M = measure_pmf p"
  assumes "k_wise_indep_vars k (\<lambda>_. discrete) f D"
  assumes "\<And>x. x \<in> D \<Longrightarrow> map_pmf (f x) p = pmf_of_set R"
  defines "Y \<equiv> (\<lambda>\<omega>. real (card ((\<lambda>x. f x \<omega>) ` D)))"
  defines "\<rho> \<equiv> real (card R) * (1-(1-1/real (card R))^(card D))" 
  shows "prob {\<omega>. abs (Y \<omega> - \<rho>) > 9 * real (card D) / sqrt(card R)} \<le> 1/2^6"
  sorry

end

end