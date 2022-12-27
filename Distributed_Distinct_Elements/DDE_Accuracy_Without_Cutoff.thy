theory DDE_Accuracy_Without_Cutoff
  imports E4  "HOL-Decision_Procs.Approximation" "Balls_and_Bins_2"
begin

context inner_algorithm_fix_A
begin

lemma \<rho>_inverse: "\<rho>' (\<rho> x) = x"
proof -
  have a:"1-1/b \<noteq> 0" 
    using b_min by simp

  have "\<rho> x = b * (1-(1-1/b) powr x)" 
    unfolding \<rho>_def by simp
  hence "\<rho> x / real b = 1-(1-1/b) powr x" by simp
  hence "ln (1 - \<rho> x / real b) = ln ((1-1/b) powr x)" by simp
  also have "... = x * ln (1 - 1/ b)" 
    using a by (intro ln_powr) 
  finally have "ln (1 - \<rho> x / real b) = x * ln (1- 1/ b)"
    by simp
  moreover have "ln (1-1/b) < 0" 
    using b_min by (subst ln_less_zero_iff) auto
  ultimately show ?thesis
    using \<rho>'_def by simp
qed

lemma rho_mono:
  assumes "x \<le> y"
  shows "\<rho> x \<le> \<rho> y" 
proof-
  have "(1 - 1 / real b) powr y \<le> (1 - 1 / real b) powr x" 
    using b_min
    by (intro powr_mono_rev assms) auto
  thus ?thesis 
    unfolding \<rho>_def by (intro mult_left_mono) auto
qed

lemma rho_two_thirds: "\<rho> (2/3 * b) \<le> 3/5 *b"
proof -
  have "1/3 \<le> exp ( - 13 / 12::real )" 
    by (approximation 8)
  also have "... \<le> exp ( - 1 - 2 / real b )" 
    using b_min by (intro iffD2[OF exp_le_cancel_iff]) (simp add:algebra_simps)
  also have "... \<le> exp ( b * (-(1/real b)-2*(1/real b)^2))" 
    using b_min by (simp add:algebra_simps power2_eq_square)
  also have  "... \<le> exp ( b * ln (1-1/real b))" 
    using b_min
    by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono ln_one_minus_pos_lower_bound) auto
  also have "... = exp ( ln ( (1-1/real b) powr b))"
    using b_min by (subst ln_powr) auto
  also have "... = (1-1/real b) powr b" 
    using b_min by (subst exp_ln) auto
  finally have a:"1/3 \<le> (1-1/real b) powr b" by simp

  have "2/5 \<le> (1/3) powr (2/3::real)"
    by (approximation 5)
  also have "... \<le> ((1-1/real b) powr b) powr (2/3)" 
    by (intro powr_mono2 a) auto
  also have "... = (1-1/real b) powr (2/3 * real b)" 
    by (subst powr_powr) (simp add:algebra_simps)
  finally have "2/5 \<le> (1 - 1 / real b) powr (2 / 3 * real b)" by simp
  hence "1 - (1 - 1 / real b) powr (2 / 3 * real b) \<le> 3/5"
    by simp
  hence "\<rho> (2/3 * b) \<le> b * (3/5)"
    unfolding \<rho>_def by (intro mult_left_mono) auto
  thus ?thesis
    by simp
qed

definition \<rho>'_deriv :: "real \<Rightarrow> real"
  where "\<rho>'_deriv x = -1 / (real b * (1-x / real b) * ln (1 - 1 / real b))"

lemma \<rho>'_deriv_bound:
  assumes "x \<ge> 0"
  assumes "x \<le> 59/90*b"
  shows "\<bar>\<rho>'_deriv x\<bar> \<le> 4"
proof -
  have c:"ln (1 - 1 / real b) < 0"
    using b_min
    by (subst ln_less_zero_iff) auto
  hence d:"real b * (1 - x / real b) * ln (1 - 1 / real b) < 0"
    using b_min assms by (intro mult_pos_neg mult_pos_pos) auto

  have "(1::real) \<le> 31/30" by simp
  also have "... \<le> (31/30) * (b * -(- 1 / real b))" 
    using b_min by simp
  also have "... \<le> (31/30) * (b * -ln (1 + (- 1 / real b)))" 
    using b_min
    by (intro mult_left_mono le_imp_neg_le  ln_add_one_self_le_self2) auto
  also have "... \<le> 3 * (31/90) * (- b * ln (1 - 1 / real b))"
    by simp
  also have "... \<le> 3 * (1 - x / real b) * (- b * ln (1 - 1 / real b))" 
    using assms b_min pos_divide_le_eq[where c="b"] c
    by (intro mult_right_mono mult_left_mono mult_nonpos_nonpos) auto
  also have "... \<le> 3 * (real b * (1 - x / real b) * (-ln (1 - 1 / real b)))"
    by (simp add:algebra_simps)
  finally have "3 * (real b * (1 - x / real b) * (-ln (1 - 1 / real b))) \<ge> 1" by simp
  hence "3 * (real b * (1 - x / real b) * ln (1 - 1 / real b)) \<le> -1" by simp
  hence "\<rho>'_deriv x \<le> 3"
    unfolding \<rho>'_deriv_def using d
    by (subst neg_divide_le_eq) auto
  moreover have "\<rho>'_deriv x > 0" 
    unfolding \<rho>'_deriv_def using d by (intro divide_neg_neg) auto
  ultimately show ?thesis by simp
qed

lemma \<rho>'_deriv:
  fixes x :: real
  assumes "x < b"
  shows "DERIV \<rho>' x :> \<rho>'_deriv x" 
proof -
  have "DERIV (ln \<circ> (\<lambda>x. (1 - x / real b))) x :> 1 / (1-x / real b) * (0 -1/b)"
    using assms b_min
    by (intro DERIV_chain DERIV_ln_divide DERIV_cdivide derivative_intros) auto
  hence "DERIV \<rho>' x :> (1 / (1-x / real b) * (-1/b)) / ln (1-1/real b)"
    unfolding comp_def \<rho>'_def by (intro DERIV_cdivide) auto
  thus ?thesis
    by (simp add:\<rho>'_deriv_def algebra_simps)
qed

lemma "\<Psi>.prob {(f,g,h). \<bar>A\<^sub>S (f,g,h) - real Y\<bar> > real_of_rat \<delta> * Y \<or> t f < s\<^sub>M} \<le> 1/2^4" 
  (is "?L \<le> ?R")
proof -
  have "?L \<le> \<Psi>.prob {\<psi>. \<not>E\<^sub>1 \<psi> \<or>  \<not>E\<^sub>2 \<psi> \<or>  \<not>E\<^sub>3 \<psi> \<or>  \<not>E\<^sub>4 \<psi>}"
  proof (rule \<Psi>.pmf_rev_mono[OF  \<Psi>.M_def])
    fix \<psi> assume "\<psi> \<in> set_pmf (sample_pmf \<Psi>)"
    obtain f g h where \<psi>_def: "\<psi> = (f,g,h)" by (metis prod_cases3)
    
    assume "\<psi> \<notin> {\<psi>. \<not> E\<^sub>1 \<psi> \<or> \<not> E\<^sub>2 \<psi> \<or> \<not> E\<^sub>3 \<psi> \<or> \<not> E\<^sub>4 \<psi>}"
    hence assms: "E\<^sub>1 (f,g,h)" "E\<^sub>2 (f,g,h)" "E\<^sub>3 (f,g,h)" "E\<^sub>4 (f,g,h)"
      unfolding \<psi>_def by auto

    define I :: "real set" where "I = {0..59/90*b}"

    have "p (f,g,h) \<le> \<rho> (card (R f)) + real_of_rat \<delta>/12 * card (R f)"
      using assms(4) E\<^sub>4_def unfolding abs_le_iff by simp
    also have "... \<le> \<rho>(2/3*b) + 1/12* (2/3*b)"
      using \<delta>_lt_1 R_bound[OF assms(1,2)]
      by (intro add_mono rho_mono mult_mono) auto
    also have "... \<le> 3/5 * b + 1/18*b"
      by (intro add_mono rho_two_thirds) auto
    also have "... \<le> 59/90 * b"
       by simp
    finally have "p (f,g,h) \<le> 59/90 * b" by simp
    hence p_in_I: "p (f,g,h) \<in> I"
      unfolding I_def by simp

    have "\<rho> (card (R f)) \<le> \<rho>(2/3 * b)"
      using  R_bound[OF assms(1,2)]
      by (intro rho_mono) auto
    also have "... \<le> 3/5 * b"
      using rho_two_thirds by simp
    also have "... \<le> b * 59/90" by simp
    finally have "\<rho> (card (R f)) \<le> b * 59/90" by simp
    moreover have "(1 - 1 / real b) powr (real (card (R f))) \<le> 1 powr (real (card (R f)))" 
      using b_min by (intro powr_mono2) auto
    hence "\<rho> (card (R f)) \<ge> 0"
      unfolding \<rho>_def by (intro mult_nonneg_nonneg) auto
    ultimately have "\<rho> (card (R f)) \<in> I"
      unfolding I_def by simp

    moreover have "interval I" 
      unfolding I_def interval_def by simp
    moreover have "59 / 90 * b < b" 
      using b_min by simp
    hence "DERIV \<rho>' x :> \<rho>'_deriv x" if "x \<in> I" for x
      using that I_def by (intro \<rho>'_deriv) simp 
    ultimately obtain \<xi> :: real where \<xi>_def: "\<xi> \<in> I"
      "\<rho>' (p(f,g,h)) - \<rho>' (\<rho> (card (R f))) = (p (f,g,h) - \<rho>(card (R f))) * \<rho>'_deriv \<xi>" 
      using p_in_I MVT_interval by blast

    have "\<bar>\<rho>'(p (f,g,h)) - card (R f)\<bar> = \<bar>\<rho>'(p (f,g,h)) - \<rho>'(\<rho>(card (R f)))\<bar>"
      by (subst \<rho>_inverse) simp
    also have "... = \<bar>(p (f,g,h) - \<rho> (card (R f)))\<bar> * \<bar>\<rho>'_deriv \<xi> \<bar>"
      using \<xi>_def(2) abs_mult by simp
    also have "... \<le> \<bar>p (f,g,h) - \<rho> (card (R f))\<bar> * 4"
      using \<xi>_def(1) I_def
      by (intro mult_left_mono \<rho>'_deriv_bound) auto
    also have "... \<le> (real_of_rat \<delta>/12 * card (R f)) * 4"
      using assms(4) E\<^sub>4_def by (intro mult_right_mono) auto
    also have "... = real_of_rat \<delta>/3 * card (R f)" by simp
    finally have b: "\<bar>\<rho>'(p (f,g,h)) - card (R f)\<bar> \<le> real_of_rat \<delta>/3 * card (R f)"  by simp

    have "\<bar>\<rho>'(p (f,g,h)) - Y / 2 ^ (t f)\<bar> \<le> 
      \<bar>\<rho>'(p (f,g,h)) - card (R f)\<bar> + \<bar>card (R f) - Y / 2 ^ (t f)\<bar>" 
      by simp
    also have "... \<le> real_of_rat \<delta>/3 * card (R f) + \<bar>card (R f) - Y / 2 ^ (t f)\<bar>"
      by (intro add_mono b) auto
    also have "... = real_of_rat \<delta>/3 * \<bar>Y / 2 ^ (t f) + (card (R f) - Y / 2 ^ (t f))\<bar> + 
      \<bar>card (R f) - Y / 2 ^ (t f)\<bar>" by simp
    also have "... \<le> real_of_rat \<delta>/3 * (\<bar>Y / 2 ^ (t f)\<bar> + \<bar>card (R f) - Y / 2 ^ (t f)\<bar>) + 
      \<bar>card (R f) - Y / 2 ^ (t f)\<bar>" 
      using \<delta>_gt_0 by (intro mult_left_mono add_mono abs_triangle_ineq) auto
    also have "... \<le> real_of_rat \<delta>/3 * \<bar>Y / 2 ^ (t f)\<bar> + 
      (1+ real_of_rat \<delta>/3) * \<bar>card (R f) - Y / 2 ^ (t f)\<bar>"
      using \<delta>_gt_0 \<delta>_lt_1 by (simp add:algebra_simps) 
    also have "... \<le> real_of_rat \<delta>/3 * \<bar>Y / 2 ^ (t f)\<bar> + 
      (4/3) * (real_of_rat \<delta> / 3 * real Y / 2 ^ t f)"
      using assms(2) \<delta>_gt_0 \<delta>_lt_1 
      unfolding E\<^sub>2_def by (intro add_mono mult_mono) auto
    also have "... = (7/9) * real_of_rat \<delta> * real Y / 2^t f"
      using Y_ge_1 by (subst abs_of_nonneg) auto
    also have "... \<le> 1 * real_of_rat \<delta> * real Y / 2^t f" 
      using \<delta>_gt_0 by (intro mult_mono divide_right_mono) auto
    also have "... = real_of_rat \<delta> * real Y / 2^t f" by simp
    finally have a:"\<bar>\<rho>'(p (f,g,h)) - Y / 2 ^ (t f)\<bar> \<le> real_of_rat \<delta> * Y / 2 ^ (t f)"
      by simp

    have "\<bar>A\<^sub>S (f, g, h) - real Y\<bar> = \<bar>2 ^ (t f)\<bar> * \<bar>\<rho>'(p (f,g,h)) - real Y / 2 ^ (t f)\<bar>"
      unfolding A\<^sub>S_def by (subst abs_mult[symmetric]) 
        (simp add:algebra_simps powr_add[symmetric])
    also have "... \<le> 2 ^ (t f) * (real_of_rat \<delta> * Y / 2 ^ (t f))"
      by (intro mult_mono a) auto
    also have "... = real_of_rat \<delta> * Y" 
      by (simp add:algebra_simps powr_add[symmetric])
    finally have "\<bar>A\<^sub>S (f, g, h) - real Y\<bar> \<le> real_of_rat \<delta> * Y" by simp
    moreover have "2 powr (\<lceil>log 2 (real Y)\<rceil> - t\<^sub>1 f) \<le> 2 powr b_exp" (is "?L1 \<le> ?R1")
    proof -
      have "?L1 \<le> 2 powr (1 + log 2 (real Y)- t\<^sub>1 f)"
        by (intro powr_mono, linarith) auto
      also have "... = 2 powr 1 * 2 powr (log 2 (real Y)) * 2 powr (- t\<^sub>1 f)"
        unfolding powr_add[symmetric] by simp
      also have "... = 2 * (2 powr (-t\<^sub>1 f) * Y)" 
        using Y_ge_1 by simp
      also have "... \<le> 2 * (b/2)" 
        using assms(1) unfolding E\<^sub>1_def by (intro mult_left_mono) auto
      also have "... = b" by simp
      also have "... = ?R1"
        unfolding b_def by (simp add: powr_realpow)
      finally show ?thesis by simp
    qed
    hence "\<lceil>log 2 (real Y)\<rceil> - t\<^sub>1 f \<le> real b_exp"
      unfolding not_less[symmetric] using powr_less_mono[where x="2"] by simp
    hence "t f \<ge> s\<^sub>M" unfolding t_def s\<^sub>M_def by (intro nat_mono) auto
    ultimately show "\<psi> \<notin> {(f, g, h). real_of_rat \<delta> * Y < \<bar>(A\<^sub>S (f, g, h) - real Y)\<bar> \<or> t f < s\<^sub>M}"
      unfolding \<psi>_def by auto
  qed
  also have "... \<le> 
    \<Psi>.prob {\<psi>. \<not>E\<^sub>1 \<psi> \<or> \<not>E\<^sub>2 \<psi> \<or> \<not>E\<^sub>3 \<psi>} + \<Psi>.prob {\<psi>. E\<^sub>1 \<psi> \<and> E\<^sub>2 \<psi> \<and> E\<^sub>3 \<psi> \<and> \<not>E\<^sub>4 \<psi>}"
    by (intro \<Psi>.pmf_add[OF \<Psi>.M_def]) auto
  also have "... \<le> (\<Psi>.prob {\<psi>. \<not>E\<^sub>1 \<psi> \<or> \<not>E\<^sub>2 \<psi>} + \<Psi>.prob {\<psi>. E\<^sub>1 \<psi> \<and> E\<^sub>2 \<psi> \<and> \<not>E\<^sub>3 \<psi>}) + 1/2^6"
    by (intro add_mono e_4 \<Psi>.pmf_add[OF \<Psi>.M_def]) auto
  also have "... \<le> ((\<Psi>.prob {\<psi>. \<not>E\<^sub>1 \<psi>} + \<Psi>.prob {\<psi>. E\<^sub>1 \<psi> \<and> \<not>E\<^sub>2 \<psi>}) + 1/2^6) + 1/2^6"
    by (intro add_mono e_3 \<Psi>.pmf_add[OF \<Psi>.M_def]) auto
  also have "... \<le> ((1/2^6 + 1/2^6) + 1/2^6) + 1/2^6"
    by (intro add_mono e_2 e_1) auto
  also have "... = ?R" by simp
  finally show ?thesis by simp
qed

end

end