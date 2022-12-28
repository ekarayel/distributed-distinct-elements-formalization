theory E3
  imports E2
begin

context inner_algorithm_fix_A 
begin

definition E\<^sub>3 where "E\<^sub>3 = (\<lambda>(f,g,h). inj_on g (R f))"

lemma R_bound:
  fixes f g h
  assumes "E\<^sub>1 (f,g,h)"
  assumes "E\<^sub>2 (f,g,h)"
  shows "card (R f) \<le> 2/3 * b"
proof -
  have "real (card (R f)) \<le> (real_of_rat \<delta> / 3) * (real Y / 2 ^ t f) + real Y / 2 ^ t f"
    using assms(2) unfolding E\<^sub>2_def by simp
  also have "... \<le> (1/3) * (real Y / 2 ^ t f) + real Y / 2 ^ t f"
    using \<delta>_lt_1 by (intro add_mono mult_right_mono) auto
  also have "... = (4/3) * (real Y / 2 powr t f)"
    using powr_realpow by simp
  also have "... \<le> (4/3) * (real Y / 2 powr t\<^sub>1 f)"
    unfolding t_def
    by (intro mult_left_mono divide_left_mono powr_mono) auto
  also have "... = (4/3) * (2 powr (-(of_int (t\<^sub>1 f))) * real Y)"
    by (subst powr_minus_divide) simp
  also have "... = (4/3) * (2 powr (- t\<^sub>1 f) * real Y)"
    by simp
  also have "... \<le> (4/3) * (b/2)"
    using assms(1) unfolding E\<^sub>1_def
    by (intro mult_left_mono) auto
  also have "... \<le> (2/3) * b" by simp
  finally show ?thesis by simp
qed

lemma e_3: "\<Psi>.prob {\<psi>. E\<^sub>1 \<psi> \<and> E\<^sub>2 \<psi> \<and> \<not>E\<^sub>3 \<psi>} \<le> 1/2^6" (is "?L \<le> ?R")
proof -
  let ?\<alpha> = "(\<lambda>(z,x,y) f. z < C6*b^2 \<and> x \<in> R f \<and> y \<in> R f \<and> x < y)"
  let ?\<beta> = "(\<lambda>(z,x,y) g. g x = z \<and> g y = z)"

  have \<beta>_prob: "\<Psi>\<^sub>2.prob {g. ?\<beta> \<omega> g} \<le> (1/(C6*b^2)^2)" 
    if "?\<alpha> \<omega> f" for \<omega> f
  proof -
    obtain x y z where \<omega>_def: "\<omega> = (z,x,y)" by (metis prod_cases3)
    have a:"\<Psi>\<^sub>2.k_wise_indep_vars 2 (\<lambda>i. discrete) (\<lambda>x \<omega>. \<omega> x = z) {..<n}"
      by (intro \<Psi>\<^sub>2.k_wise_indep_vars_compose[OF \<Psi>\<^sub>2.\<H>_indep]) simp

    have "u \<in> R f \<Longrightarrow> u < n" for u
      unfolding R_def using A_range by auto
    hence b: "x < n" "y < n" "card {x, y} = 2" 
      using that \<omega>_def by auto
    have c: "z < C6*b\<^sup>2" using \<omega>_def that by simp

    have "\<Psi>\<^sub>2.prob {g. ?\<beta> \<omega> g} = \<Psi>\<^sub>2.prob {g. (\<forall>\<xi> \<in> {x,y}. g \<xi> = z)}"
      by (simp add:\<omega>_def)
    also have "... = (\<Prod>\<xi> \<in> {x,y}. \<Psi>\<^sub>2.prob {g. g \<xi> = z})"
      using b
      by (intro \<Psi>\<^sub>2.split_indep_events[OF \<Psi>\<^sub>2.M_def, where I="{x,y}"] \<Psi>\<^sub>2.k_wise_indep_vars_subset[OF a])
       auto
    also have "... = (\<Prod>\<xi> \<in> {x,y}. measure_pmf.prob (map_pmf (\<lambda>\<omega>. \<omega> \<xi>) (sample_pmf (\<H> 2 n [C6 * b\<^sup>2]\<^sub>S))) {g. g = z}) "
      unfolding \<Psi>\<^sub>2.M_def by (simp add:vimage_def) 
    also have "... = (\<Prod>\<xi> \<in> {x,y}. measure_pmf.prob (sample_pmf ([C6 * b\<^sup>2]\<^sub>S)) {g. g=z})"
      using b \<Psi>\<^sub>2.\<H>_single by (intro prod.cong) fastforce+ 
    also have "... = (\<Prod>\<xi> \<in> {x,y}. measure_pmf.prob (pmf_of_set {..<C6 * b\<^sup>2}) {z})"
      by (subst nat_sample_pmf) simp
    also have "... = (measure_pmf.prob (pmf_of_set {..<C6 * b\<^sup>2}) {z})^2"
      using b by simp
    also have "... \<le> (1 /(C6*b\<^sup>2))^2"
      using c by (subst measure_pmf_of_set) auto
    also have "... = (1 /(C6*b\<^sup>2)^2)"
      by (simp add:algebra_simps power2_eq_square)
    finally show ?thesis by simp
  qed
  
  have \<alpha>_card: "card {\<omega>. ?\<alpha> \<omega> f} \<le> (C6*b^2) * (card (R f) * (card (R f)-1)/2)" (is "?TL \<le> ?TR") and
    fin_\<alpha>: "finite {\<omega>. ?\<alpha> \<omega> f}" (is "?T2") for f
  proof -
    have t1: "{\<omega>. ?\<alpha> \<omega> f} \<subseteq> {..<C6*b^2} \<times> {(x,y) \<in> R f \<times> R f. x < y}" 
      by (intro subsetI) auto
    moreover have "card ({..<C6*b^2} \<times> {(x,y) \<in> R f \<times> R f. x < y}) = ?TR"
      using  card_ordered_pairs'[where M="R f"]
      by (simp add: card_cartesian_product) 
    moreover have "finite (R f)" 
      unfolding R_def using fin_A finite_subset by simp    
    hence "finite {(x, y). (x, y) \<in> R f \<times> R f \<and> x < y}"
      by (intro finite_subset[where B="R f \<times> R f", OF _ finite_cartesian_product]) auto
    hence t2: "finite ({..<C6*b^2} \<times> {(x,y) \<in> R f \<times> R f. x < y})"
      by (intro finite_cartesian_product) auto
    ultimately show "?TL \<le> ?TR" 
      using card_mono of_nat_le_iff by (metis (no_types, lifting)) 
    show ?T2 
      using finite_subset[OF t1 t2] by simp
  qed

  have "?L \<le> \<Psi>.prob {(f,g,h). card (R f) \<le> b \<and> (\<exists> x y z. ?\<alpha> (x,y,z) f \<and> ?\<beta> (x,y,z) g)}"
  proof (rule \<Psi>.pmf_mono[OF \<Psi>.M_def])
    fix \<psi> assume b:"\<psi> \<in> set_pmf (sample_pmf \<Psi>)"
    obtain f g h where \<psi>_def:"\<psi> = (f,g,h)" by (metis prod_cases3)
    have "(f,g,h) \<in> sample_set \<Psi>"
      using \<psi>_def \<Psi>.set_pmf_sample_pmf b by simp
    hence c:"g x < C6*b^2" for x
      using g_range by simp

    assume a:"\<psi> \<in> {\<psi>. E\<^sub>1 \<psi> \<and> E\<^sub>2 \<psi> \<and> \<not> E\<^sub>3 \<psi>}"
    hence "card (R f) \<le> 2/3 * b"
      using R_bound \<psi>_def by force
    moreover have "\<exists>a b. a \<in> R f \<and> b \<in> R f \<and> a \<noteq> b \<and> g a = g b"
      using a unfolding \<psi>_def E\<^sub>3_def inj_on_def by auto
    hence "\<exists>x y. x \<in> R f \<and> y \<in> R f \<and> x < y \<and> g x = g y"
      by (metis not_less_iff_gr_or_eq)
    hence "\<exists>x y z. ?\<alpha> (x,y,z) f \<and> ?\<beta> (x,y,z) g"
      using c by blast
    ultimately show "\<psi> \<in> {(f, g, h). card (R f) \<le> b \<and> (\<exists> x y z. ?\<alpha> (x,y,z) f \<and> ?\<beta> (x,y,z) g)}"
      unfolding \<psi>_def by auto
  qed
  also have "... = \<Psi>\<^sub>1.expectation (\<lambda>f. measure_pmf.prob 
     (pair_pmf (sample_pmf (\<H> 2 n [C6 * b\<^sup>2]\<^sub>S)) (sample_pmf (\<H> k (C6 * b\<^sup>2) [b]\<^sub>S)))
     {g. card (R f) \<le> b \<and> (\<exists>x y z. ?\<alpha> (x,y,z) f \<and> ?\<beta> (x,y,z) (fst g))})"
    by (simp add:\<Psi>.M_def \<Psi>\<^sub>1.M_def sample_pmf_\<Psi> case_prod_beta split_pair_pmf[where A="sample_pmf (\<G> 2 n)"])
  also have 
    "... = \<Psi>\<^sub>1.expectation (\<lambda>f. \<Psi>\<^sub>2.prob {g. card (R f) \<le> b \<and> (\<exists>x y z. ?\<alpha> (x,y,z) f \<and> ?\<beta> (x,y,z) g)})"
    by (subst pair_pmf_prob_left)  (simp add:\<Psi>\<^sub>2.M_def)
  also have "... \<le> \<Psi>\<^sub>1.expectation (\<lambda>f. 1/(2*C6))"
  proof (rule \<Psi>\<^sub>1.pmf_exp_mono[OF \<Psi>\<^sub>1.M_def \<Psi>\<^sub>1.integrable_M \<Psi>\<^sub>1.integrable_M]) 
    fix f assume "f \<in> set_pmf (sample_pmf (\<G> 2 n))"
    show "\<Psi>\<^sub>2.prob {g. card (R f) \<le> b \<and> (\<exists>x y z. ?\<alpha> (x,y,z) f \<and> ?\<beta> (x,y,z) g)} \<le> 1 / (2 * C6)" 
      (is "?L1 \<le> ?R1")
    proof (cases "card (R f) \<le> b")
      case True
      have "?L1 \<le> \<Psi>\<^sub>2.prob (\<Union> \<omega> \<in> {\<omega>. ?\<alpha> \<omega> f}. {g. ?\<beta> \<omega> g})"
        by (intro \<Psi>\<^sub>2.pmf_mono[OF \<Psi>\<^sub>2.M_def]) auto
      also have "... \<le> (\<Sum>\<omega> \<in> {\<omega>. ?\<alpha> \<omega> f}. \<Psi>\<^sub>2.prob {g. ?\<beta> \<omega> g})"
        unfolding \<Psi>\<^sub>2.M_def 
        by (intro measure_UNION_le fin_\<alpha>) auto
      also have "... \<le> (\<Sum>\<omega> \<in> {\<omega>. ?\<alpha> \<omega> f}. (1/(C6*b^2)^2))"
        by (intro sum_mono \<beta>_prob) auto
      also have "... = card {\<omega>. ?\<alpha> \<omega> f} /(C6*b^2)^2"
        by simp
      also have "... \<le> (C6*b^2) * (card (R f) * (card (R f)-1)/2) / (C6*b^2)^2"
        by (intro \<alpha>_card divide_right_mono) simp
      also have "... \<le> (C6*b^2) * (b * b / 2)  / (C6*b^2)^2"
        unfolding C6_def using True
        by (intro divide_right_mono of_nat_mono mult_mono) auto
      also have "... = 1/(2*C6)"
        using b_min by (simp add:algebra_simps power2_eq_square)
      finally show ?thesis by simp
    next
      case False
      then show ?thesis by simp
    qed
  qed
  also have "... \<le> 1/2^6"
    unfolding \<Psi>\<^sub>1.M_def C6_def by simp
  finally show ?thesis by simp
qed

end

end