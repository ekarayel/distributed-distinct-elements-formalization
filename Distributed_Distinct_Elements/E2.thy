theory E2
  imports E1
begin

context inner_algorithm_fix_A 
begin

definition E\<^sub>2 where "E\<^sub>2 = (\<lambda>(f,g,h). \<bar>card (R f) - Y / 2^(t f)\<bar> \<le> \<delta>/3 * Y / 2^(t f))"

lemma e_2: "measure \<Psi> {\<psi>. E\<^sub>1 \<psi> \<and> \<not>E\<^sub>2 \<psi>} \<le> 1/2^6" (is "?L \<le> ?R")
proof -
  define t\<^sub>m :: int where "t\<^sub>m = \<lfloor>log 2 (real Y)\<rfloor> + 16 - b_exp"

  have t_m_bound: "t\<^sub>m \<le> \<lfloor>log 2 (real Y)\<rfloor> - 10"
    unfolding t\<^sub>m_def using b_exp_ge_26 by simp

  have "real b / 2^16 = (real Y * (1/ Y)) * (real b / 2^16)"
    using Y_ge_1 by simp
  also have "... = (real Y * 2 powr (-log 2 Y)) * (real b / 2^16)" 
    using Y_ge_1 by (subst powr_minus_divide) simp
  also have "... \<le> (real Y * 2 powr (- \<lfloor>log 2 (real Y)\<rfloor>)) * (2 powr b_exp / 2^16)"
    unfolding b_def using powr_realpow
    by (intro mult_mono powr_mono) auto
  also have "... = real Y * (2 powr (- \<lfloor>log 2 (real Y)\<rfloor>) * 2 powr(real b_exp-16))"
    by (subst powr_diff) simp
  also have "... = real Y * 2 powr (- \<lfloor>log 2 (real Y)\<rfloor> + (int b_exp - 16))"
    by (subst powr_add[symmetric]) simp
  also have "... = real Y * 2 powr (-t\<^sub>m)"
    unfolding t\<^sub>m_def by (simp add:algebra_simps)
  finally have c:"real b / 2^16 \<le> real Y * 2 powr (-t\<^sub>m)" by simp

  define T :: "nat set" where "T = {x. (real Y / 2^x \<ge> real b / 2^16)}"

  have "x \<in> T \<longleftrightarrow> int x \<le> t\<^sub>m" for x
  proof -
    have "x \<in> T \<longleftrightarrow> 2^ x \<le> real Y * 2^16 / b"
      using b_min by (simp add: field_simps T_def)
    also have "... \<longleftrightarrow> log 2 (2^x) \<le> log 2 (real Y * 2^16 / b)"
      using Y_ge_1 b_min
      by (intro log_le_cancel_iff[symmetric] divide_pos_pos) auto
    also have "... \<longleftrightarrow> x \<le> log 2 (real Y * 2^16) - log 2 b"
      using Y_ge_1 b_min by (subst log_divide) auto
    also have "... \<longleftrightarrow> x \<le> log 2 (real Y) + log 2 (2 powr 16) - b_exp"
      unfolding b_def using Y_ge_1 by (subst log_mult) auto
    also have "... \<longleftrightarrow> x \<le> \<lfloor>log 2 (real Y) + log 2 (2 powr 16) - b_exp\<rfloor>"
      by linarith
    also have "... \<longleftrightarrow> x \<le> \<lfloor>log 2 (real Y) + 16 - real_of_int (int b_exp)\<rfloor>"
      by (subst log_powr_cancel) auto
    also have "... \<longleftrightarrow> x \<le> t\<^sub>m"
      unfolding t\<^sub>m_def by linarith
    finally show ?thesis by simp
  qed
  hence T_eq: "T = {x. int x \<le> t\<^sub>m}" by auto

  have "T = {x. int x < t\<^sub>m+1}"
    unfolding T_eq by simp
  also have "... = {x. x < nat (t\<^sub>m + 1)}"
    unfolding zless_nat_eq_int_zless by simp
  finally have T_eq_2: "T = {x. x < nat (t\<^sub>m + 1)}"
    by simp
                                              
  have inj_1: "inj_on ((-) (nat t\<^sub>m)) T"
    unfolding T_eq by (intro inj_onI) simp
  have fin_T: "finite T" 
    unfolding T_eq_2 by simp

  have r_exp: "(\<integral>\<omega>. real (r t \<omega>) \<partial>\<Psi>\<^sub>1) = real Y / 2^t" if "t \<in> T" for t 
  proof -
    have "t \<le> t\<^sub>m"
      using that unfolding T_eq by simp
    also have "... \<le> \<lfloor>log 2 (real Y)\<rfloor> - 10"
      using t_m_bound by simp
    also have "... \<le> \<lfloor>log 2 (real Y)\<rfloor>"
      by simp
    also have "... \<le> \<lfloor>log 2 (real n)\<rfloor>"
      using Y_le_n Y_ge_1
      by (intro floor_mono log_mono) auto
    also have "... \<le> \<lceil>log 2 (real n)\<rceil>"
      by simp
    finally have "t \<le> \<lceil>log 2 (real n)\<rceil>" by simp
    hence "t \<le> max (nat \<lceil>log 2 (real n)\<rceil>) 1"by simp
    thus ?thesis
      unfolding r_exp by simp
  qed

  have r_var: "measure_pmf.variance \<Psi>\<^sub>1 (\<lambda>\<omega>. real (r t \<omega>)) \<le> real Y / 2^t" if "t \<in> T" for t 
    using r_exp[OF that] r_var by metis

  have "9 = C2 / \<delta>\<^sup>2 * \<delta>^2/2^23" 
    using \<delta>_gt_0 by (simp add:C2_def)
  also have "... = 2 powr (log 2 (C2 /  \<delta>\<^sup>2)) *  \<delta>^2/2^23" 
    using \<delta>_gt_0 C2_def by (subst powr_log_cancel) auto
  also have "... \<le> 2 powr b_exp * \<delta>^2/2^23" 
    unfolding b_exp_def
    by (intro divide_right_mono mult_right_mono powr_mono, linarith) auto 
  also have "... = b * \<delta>^2/2^23"  
    using powr_realpow unfolding b_def by simp
  also have "... = (b/2^16) * (\<delta>^2/2^7)" 
    by simp
  also have "... \<le> (Y * 2 powr (-t\<^sub>m)) * (\<delta>^2/2^7)" 
    by (intro mult_mono c) auto
  also have "... = Y * (2 powr (-t\<^sub>m) * 2 powr (-7)) * \<delta>^2" 
    using powr_realpow by simp
  also have "... = 2 powr (-t\<^sub>m-7) * (\<delta>^2 * Y)" 
    by (subst powr_add[symmetric]) (simp )
  finally have "9 \<le> 2 powr (-t\<^sub>m-7) * (\<delta>^2 * Y)" by simp
  hence b: "9/ (\<delta>^2 * Y) \<le> 2 powr (-t\<^sub>m -7)"
    using \<delta>_gt_0 Y_ge_1
    by (subst pos_divide_le_eq) auto

  have a: "measure \<Psi>\<^sub>1 {f.\<bar>real (r t f)-real Y/2^t\<bar>> \<delta>/3 *real Y/2^t} \<le> 2 powr (real t-t\<^sub>m-7)" 
    (is"?L1 \<le> ?R1") if "t \<in> T" for t
  proof -
    have "?L1 \<le> \<P>(f in \<Psi>\<^sub>1. \<bar>real (r t f) - real Y / 2^t\<bar> \<ge>  \<delta>/3 * real Y / 2^t)"
      by (intro pmf_mono) auto
    also have "... = \<P>(f in \<Psi>\<^sub>1. \<bar>real (r t f)-(\<integral>\<omega>. real (r t \<omega>) \<partial> \<Psi>\<^sub>1)\<bar> \<ge> \<delta>/3 * real Y/2^t)"
      by (simp add: r_exp[OF that]) 
    also have "... \<le> measure_pmf.variance \<Psi>\<^sub>1 (\<lambda>\<omega>. real (r t \<omega>)) / (\<delta>/3 * real Y / 2^t)^2"
      using Y_ge_1 \<delta>_gt_0 \<Psi>\<^sub>1.sample_space
      by (intro measure_pmf.Chebyshev_inequality divide_pos_pos mult_pos_pos) auto
    also have "... \<le> (Y / 2^t) / (\<delta>/3 * Y / 2^t)^2"
      by (intro divide_right_mono r_var[OF that]) simp
    also have "... = 2^t*(9/ ( \<delta>^2 * Y))"
      by (simp add:power2_eq_square algebra_simps)
    also have "... \<le> 2^t*(2 powr (-t\<^sub>m-7))"
      by (intro mult_left_mono b) simp
    also have "... = 2 powr t * 2 powr (-t\<^sub>m-7)" 
      by (subst powr_realpow[symmetric]) auto
    also have "... = ?R1"
      by (subst powr_add[symmetric]) (simp add:algebra_simps)
    finally show "?L1 \<le> ?R1" by simp
  qed

  have "\<exists>y<nat (t\<^sub>m + 1). x = nat t\<^sub>m - y" if "x < nat (t\<^sub>m+1)" for x 
    using that by (intro exI[where x="nat t\<^sub>m - x"]) simp
  hence T_reindex: "(-) (nat t\<^sub>m) ` {x. x < nat (t\<^sub>m + 1)} = {..<nat (t\<^sub>m + 1)}"
    by (auto simp add: set_eq_iff image_iff) 

  have "?L \<le> measure \<Psi> {\<psi>. (\<exists>t \<in> T. \<bar>real (r t (fst \<psi>))-real Y/2^t\<bar> > \<delta>/3 * real Y / 2^t)}"
  proof (rule pmf_mono)
    fix \<psi>
    assume "\<psi> \<in> set_pmf (sample_pmf \<Psi>)"
    obtain f g h where \<psi>_def: "\<psi> = (f,g,h)" by (metis prod_cases3)
    assume "\<psi> \<in> {\<psi>. E\<^sub>1 \<psi> \<and> \<not> E\<^sub>2 \<psi>}"
    hence a:"2 powr ( -real_of_int (t\<^sub>1 f)) * real Y \<in> {real b/2^16..real b/2}" and
      b:"\<bar>card (R f) - real Y / 2^(t f)\<bar> >  \<delta>/3 * Y / 2^(t f)"
      unfolding E\<^sub>1_def E\<^sub>2_def by (auto simp add:\<psi>_def)
    have "\<bar>card (R f) - Y / 2^(t f)\<bar> = 0" if "t f= 0"
      using that by (simp add:R_def Y_def)
    moreover have "( \<delta>/3) * (Y / 2^(t f)) \<ge> 0" 
      using \<delta>_gt_0 Y_ge_1 by (intro mult_nonneg_nonneg) auto
    ultimately have "False" if "t f = 0" 
      using b that by simp
    hence "t f > 0" by auto
    hence "t\<^sub>1 f = t f" unfolding t_def by simp
    hence "2 powr (-real (t f)) * Y \<ge> b / 2^16"
      using a by simp
    hence "Y / 2 powr (real (t f)) \<ge> b / 2^16"
      by (simp add: divide_powr_uminus mult.commute)
    hence "real Y / 2 ^ (t f) \<ge> b / 2^16"
      by (subst (asm) powr_realpow, auto)
    hence "t f \<in> T" unfolding T_def by simp
    moreover have "\<bar>r (t f) f - Y / 2^t f\<bar> >  \<delta>/3 * Y / 2^t f" 
      using R_def r_def b by simp
    ultimately have "\<exists>t \<in> T. \<bar>r t (fst \<psi>) - Y / 2^t\<bar> >  \<delta>/3 * Y / 2^t"
      using \<psi>_def by (intro bexI[where x="t f"]) simp
    thus "\<psi> \<in> {\<psi>. (\<exists>t \<in> T. \<bar>r t (fst \<psi>) - Y / 2^t\<bar> >  \<delta>/3 * Y / 2^t)}" by simp
  qed
  also have "... = measure \<Psi>\<^sub>1 {f. (\<exists>t \<in> T. \<bar>real (r t f)-real Y / 2^t\<bar> > \<delta>/3 * real Y/2^t)}"
    unfolding sample_pmf_\<Psi> by (intro pair_pmf_prob_left)
  also have "... = measure \<Psi>\<^sub>1 (\<Union>t \<in> T. {f. \<bar>real (r t f)-real Y / 2^t\<bar> > \<delta>/3 * real Y/2^t})"
    by (intro measure_pmf_cong) auto
  also have "... \<le> (\<Sum>t \<in> T. measure \<Psi>\<^sub>1 {f.\<bar>real (r t f)-real Y / 2^t\<bar> > \<delta>/3 * real Y/2^t})"
    by (intro measure_UNION_le fin_T) (simp)
  also have "... \<le> (\<Sum>t \<in> T.  2 powr (real t - of_int t\<^sub>m - 7))"
    by (intro sum_mono a)
  also have "... = (\<Sum>t \<in> T.  2 powr (-int (nat t\<^sub>m-t) - 7))" 
    unfolding T_eq
    by (intro sum.cong refl arg_cong2[where f="(powr)"]) simp
  also have "... = (\<Sum>x \<in> (\<lambda>x. nat t\<^sub>m - x) ` T. 2 powr (-real x - 7))"
    by (subst sum.reindex[OF inj_1]) simp
  also have "... = (\<Sum>x \<in> (\<lambda>x. nat t\<^sub>m - x) ` T. 2 powr (-7) * 2 powr (-real x))"
    by (subst powr_add[symmetric]) (simp add:algebra_simps)
  also have "... = 1/2^7 * (\<Sum>x \<in> (\<lambda>x. nat t\<^sub>m - x) ` T. 2 powr (-real x))"
    by (subst sum_distrib_left) simp
  also have "... = 1/2^7 * (\<Sum>x <nat (t\<^sub>m+1). 2 powr (-real x))"
    unfolding T_eq_2 T_reindex
    by (intro arg_cong2[where f="(*)"] sum.cong) auto
  also have "... = 1/2^7 * (\<Sum>x <nat (t\<^sub>m+1). (2 powr (-1)) powr (real x))"
    by (subst powr_powr) simp
  also have "... = 1/2^7 * (\<Sum>x <nat (t\<^sub>m+1). (1/2)^x)"
    using powr_realpow by simp
  also have "... \<le> 1/2^7 * 2"
    by(subst geometric_sum) auto
  also have "... = 1/2^6" by simp
  finally show ?thesis by simp
qed

end

end