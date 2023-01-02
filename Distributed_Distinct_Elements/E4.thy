theory E4
  imports E3 Balls_and_Bins
begin

context inner_algorithm_fix_A 
begin

definition E\<^sub>4 where "E\<^sub>4 = (\<lambda>(f,g,h). \<bar>p (f,g,h) - \<rho> (card (R f))\<bar> \<le> real_of_rat \<delta>/12 * card (R f))"

lemma e_4_h: "9 / sqrt b \<le> of_rat \<delta> / 12"
proof -
  have "108 \<le> sqrt (C2)"
    unfolding C2_def by (approximation 5)
  also have "... \<le> sqrt(of_rat \<delta>^2 * real b)"
    using b_lower_bound \<delta>_gt_0
    by (intro real_sqrt_le_mono) (simp add: pos_divide_le_eq algebra_simps)
  also have "... = of_rat \<delta> * sqrt b"
    using \<delta>_gt_0 by (simp add:real_sqrt_mult)
  finally have "108 \<le> of_rat \<delta> * sqrt b"  by simp
  thus ?thesis
    using b_min by (simp add:pos_divide_le_eq)
qed

lemma e_4: "\<Psi>.prob {\<psi>. E\<^sub>1 \<psi> \<and> E\<^sub>2 \<psi> \<and> E\<^sub>3 \<psi> \<and> \<not>E\<^sub>4 \<psi>} \<le> 1/2^6" (is "?L \<le> ?R")
proof -
  have a: "\<Psi>\<^sub>3.prob {h. E\<^sub>1 (f,g,h) \<and> E\<^sub>2 (f,g,h) \<and> E\<^sub>3 (f,g,h) \<and> \<not>E\<^sub>4 (f,g,h)} \<le> 1/2^6" 
    (is "?L1 \<le> ?R1")
    if "f \<in> set_pmf (sample_pmf (\<G> 2 n))" "g \<in> set_pmf(sample_pmf (\<H> 2 n [C6 * b\<^sup>2]\<^sub>S))"
    for f g 
  proof (cases "card (R f) \<le> b \<and> inj_on g (R f)")
    case True

    have g_inj: "inj_on g (R f)"
      using True by simp

    have fin_R: "finite (g ` R f)"
      unfolding R_def using fin_A
      by (intro finite_imageI) simp

    interpret B:balls_and_bins_abs "g ` R f" "{..<b}"
      using fin_R b_ne by unfold_locales auto 

    have "range g \<subseteq> sample_set [C6 * b\<^sup>2]\<^sub>S"
      using that(2) \<Psi>\<^sub>2.\<H>_range sample_set_def
      unfolding \<Psi>\<^sub>2.set_pmf_sample_pmf by (metis imageE)

    hence g_ran: "g ` R f \<subseteq> {..<C6 * b\<^sup>2}" 
      unfolding sample_set_def nat_sample_space_def by auto

    have "sample_pmf [b]\<^sub>S = pmf_of_set {..<b}" 
      unfolding sample_pmf_def nat_sample_space_def by simp
    hence " map_pmf (\<lambda>\<omega>. \<omega> x) (sample_pmf (\<H> k (C6 * b\<^sup>2) [b]\<^sub>S)) = pmf_of_set {..<b}"
      if "x \<in> g ` R f" for x 
      using g_ran \<Psi>\<^sub>3.\<H>_single that by auto
    moreover have "\<Psi>\<^sub>3.k_wise_indep_vars k (\<lambda>_. discrete) (\<lambda>x \<omega>. \<omega> x) (g ` R f)"
      by (intro \<Psi>\<^sub>3.k_wise_indep_subset[OF _ \<Psi>\<^sub>3.\<H>_indep] g_ran)
    ultimately have lim_balls_and_bins: "B.lim_balls_and_bins k (sample_pmf (\<H> k (C6 * b\<^sup>2) [b]\<^sub>S))"
      unfolding B.lim_balls_and_bins_def \<Psi>\<^sub>3.M_def by auto

    have card_g_R: "card (g ` R f) = card (R f)" 
      using True card_image by auto
    hence b_mu: "\<rho> (card (R f)) = B.\<mu>"
      unfolding B.\<mu>_def \<rho>_def using b_min by (simp add:powr_realpow)

    have card_g_le_b: "card (g ` R f) \<le> card {..<b}"
      unfolding card_g_R using True by simp

    have "?L1 \<le> \<Psi>\<^sub>3.prob {h. \<bar>B.Y h - B.\<mu>\<bar> > 9 * real (card (g ` R f)) / sqrt (card {..<b})}"
    proof (rule \<Psi>\<^sub>3.pmf_mono[OF \<Psi>\<^sub>3.M_def])
      fix h assume "h \<in> {h. E\<^sub>1 (f,g,h) \<and> E\<^sub>2 (f,g,h) \<and> E\<^sub>3 (f,g,h) \<and> \<not>E\<^sub>4 (f,g,h)}"
      hence b: "\<bar>p (f,g,h) -\<rho> (card (R f))\<bar> > of_rat \<delta>/12 * card (R f)"
        unfolding E\<^sub>4_def by simp
      assume "h \<in> set_pmf (sample_pmf (\<H> k (C6 * b\<^sup>2) [b]\<^sub>S))"
      hence "range h \<subseteq> sample_set [b]\<^sub>S"
        unfolding \<Psi>\<^sub>3.set_pmf_sample_pmf
        using \<Psi>\<^sub>3.\<H>_range sample_set_def by (metis imageE)
      hence h_range: "h x < b" for x
        unfolding sample_set_def nat_sample_space_def by auto

      have "{j \<in> {..<b}. int (t f) \<le> \<tau>\<^sub>1 (f, g, h) A 0 j} =
        {j \<in> {..<b}. int (t f) \<le> max (Max ({int (f a) |a. a \<in> A \<and> h (g a) = j} \<union> {-1})) (- 1)}"
        by simp
      also have "... = {j \<in> {..<b}. int (t f) \<le> Max ({int (f a) |a. a \<in> A \<and> h (g a) = j} \<union> {-1})}"
        using fin_A by (subst max_absorb1) (auto intro: Max_ge)
      also have "... = {j \<in> {..<b}. (\<exists>a \<in> R f. h (g a) = j)}"
        unfolding R_def using fin_A by (subst Max_ge_iff) auto
      also have "... = {j. \<exists>a \<in> R f. h (g a) = j}"
        using h_range by auto
      also have "... = (h \<circ> g) ` (R f)"
        by (auto simp add:set_eq_iff image_iff)
      also have "... = h ` (g ` (R f))"
        by (simp add:image_image)
      finally have c:"{j \<in> {..<b}. int (t f) \<le> \<tau>\<^sub>1 (f, g, h) A 0 j} = h ` (g ` R f)"
        by simp 
      have "9 * real (card (g ` R f)) / sqrt (card {..<b}) = 9/ sqrt b * real (card (R f))"
        using card_image[OF g_inj] by simp
      also have "... \<le> of_rat \<delta>/12 * card (R f)" 
        by (intro mult_right_mono e_4_h) simp
      also have "... < \<bar>B.Y h - B.\<mu>\<bar>"
        using b c unfolding B.Y_def p_def b_mu by simp
      finally show "h \<in> {h. \<bar>B.Y h - B.\<mu>\<bar> >  9 * real (card (g ` R f)) / sqrt (card {..<b})}"
        by simp
    qed
    also have "... \<le> 1/2^6"
      unfolding \<Psi>\<^sub>3.M_def using k_min
      by (intro B.devitation_bound[OF card_g_le_b lim_balls_and_bins]) auto
    finally show ?thesis by simp
  next
    case False
    have "?L1 \<le> \<Psi>\<^sub>3.prob {}"
    proof (rule \<Psi>\<^sub>3.pmf_mono[OF \<Psi>\<^sub>3.M_def])
      fix h assume b:"h \<in> {h. E\<^sub>1 (f, g, h) \<and> E\<^sub>2 (f, g, h) \<and> E\<^sub>3 (f, g, h) \<and> \<not> E\<^sub>4 (f, g, h)}"
      hence "card (R f) \<le> (2/3)*b"
        by (auto intro!: R_bound[simplified])
      hence "card (R f) \<le> b" 
        by simp
      moreover have "inj_on g (R f)"
        using b by (simp add:E\<^sub>3_def)
      ultimately have "False" using False by simp
      thus "h \<in> {}" by simp
    qed
    also have "... = 0" by simp
    finally show ?thesis by simp
  qed

  have "?L = \<Psi>\<^sub>1.expectation (\<lambda>f. \<Psi>\<^sub>2.expectation (\<lambda>g. 
    \<Psi>\<^sub>3.prob {h. E\<^sub>1 (f,g,h) \<and> E\<^sub>2 (f,g,h) \<and> E\<^sub>3 (f,g,h) \<and> \<not>E\<^sub>4 (f,g,h)}))"
    unfolding \<Psi>\<^sub>1.M_def \<Psi>\<^sub>2.M_def \<Psi>\<^sub>3.M_def \<Psi>.M_def sample_pmf_\<Psi> split_pair_pmf by simp
  also have "... \<le> \<Psi>\<^sub>1.expectation (\<lambda>f. \<Psi>\<^sub>2.expectation (\<lambda>g. 1/2^6))"
    using a
    by (intro integral_mono_AE \<Psi>\<^sub>1.AE_pmfI[OF \<Psi>\<^sub>1.M_def] \<Psi>\<^sub>2.AE_pmfI[OF \<Psi>\<^sub>2.M_def]) auto
  also have "... \<le> 1/2^6"
    unfolding \<Psi>\<^sub>1.M_def \<Psi>\<^sub>2.M_def by simp
  finally show ?thesis by simp
qed

end

end