theory E1
  imports F0
begin

context inner_algorithm_fix_A 
begin

subsubsection \<open>Lemma for $E_1$\<close>  

definition E\<^sub>1 where 
  "E\<^sub>1 = (\<lambda>(f,g,h). 2 powr (-t\<^sub>1 f) * Y \<in> {b/2^16..b/2})"

lemma t\<^sub>1_low: 
  "\<Psi>\<^sub>1.prob {f. of_int (t\<^sub>1 f) < log 2 (real Y) + 1 - b_exp} \<le> 1/2^7" (is "?L \<le> ?R")
proof (cases "log 2 (real Y) \<ge> 8")
  case True
  define Z :: "(nat \<Rightarrow> nat) \<Rightarrow> real" where "Z = r (nat \<lceil>log 2 (real Y) - 8\<rceil>)"

  have " log 2 (real Y) \<le> log 2 (real n)"
    using Y_le_n Y_ge_1
    by (intro log_mono) auto
  hence "nat \<lceil>log 2 (real Y) - 8\<rceil> \<le> nat \<lceil>log 2 (real n)\<rceil>"
    by (intro nat_mono ceiling_mono) simp
  hence a:"(nat \<lceil>log 2 (real Y) - 8\<rceil> \<le> max (nat \<lceil>log 2 (real n)\<rceil>) 1)" 
    by simp

  have b:"real (nat (\<lceil>log 2 (real Y)\<rceil> - 8)) \<le> log 2 (real Y) - 7"
    using True by linarith

  have " 2 ^ 7 = real Y / (2 powr (log 2 Y) * 2 powr (-7))"
    using Y_ge_1 by simp
  also have "... = real Y / (2 powr (log 2 Y - 7))"
    by (subst powr_add[symmetric]) simp
  also have "... \<le> real Y / (2 powr (real (nat \<lceil>log 2 (real Y) - 8\<rceil>)))"
    using b by (intro divide_left_mono powr_mono) auto
  also have "... = real Y / 2 ^ nat \<lceil>log 2 (real Y) - 8\<rceil>"
    by (subst powr_realpow) auto
  finally have "2 ^ 7 \<le> real Y / 2 ^ nat \<lceil>log 2 (real Y) - 8\<rceil>" by simp
  hence exp_Z_gt_2_7: "\<Psi>\<^sub>1.expectation Z \<ge> 2^7" 
    using a unfolding Z_def r_exp by simp

  have var_Z_le_exp_Z: "\<Psi>\<^sub>1.variance Z \<le> \<Psi>\<^sub>1.expectation Z" 
    unfolding Z_def by (intro r_var)

  have "?L \<le> \<Psi>\<^sub>1.prob {f. of_nat (Max (f ` A)) < log 2 (real Y) - 8}"
    unfolding t\<^sub>1_def 
    by (intro \<Psi>\<^sub>1.pmf_mono[OF \<Psi>\<^sub>1.M_def]) (auto simp add:int_of_nat_def)
  also have "... \<le> \<Psi>\<^sub>1.prob {f.  \<Psi>\<^sub>1.expectation Z \<le> \<bar>Z f - \<Psi>\<^sub>1.expectation Z \<bar>}"
  proof (rule \<Psi>\<^sub>1.pmf_mono[OF \<Psi>\<^sub>1.M_def])
    fix f assume "f \<in> set_pmf (sample_pmf (\<G> 2 n))"
    have fin_f_A: "finite (f ` A)" using fin_A finite_imageI by blast
    assume " f \<in> {f. real (Max (f ` A)) < log 2 (real Y) - 8}"
    hence "real (Max (f ` A)) < log 2 (real Y) - 8" by auto
    hence "real (f a) < log 2 (real Y) - 8" if "a \<in> A" for a
      using Max_ge[OF fin_f_A] imageI[OF that]  order_less_le_trans by fastforce
    hence "of_nat (f a) < \<lceil>log 2 (real Y) - 8\<rceil>" if "a \<in> A" for a
      using that by (subst less_ceiling_iff) auto
    hence "f a < nat \<lceil>log 2 (real Y) - 8\<rceil>" if "a \<in> A" for a
      using that True by fastforce
    hence "r (nat \<lceil>log 2 (real Y) - 8\<rceil>) f = 0"
      unfolding r_def card_eq_0_iff using not_less by auto
    hence "Z f = 0"
      unfolding Z_def by simp
    thus "f \<in> {f. \<Psi>\<^sub>1.expectation Z \<le> \<bar>Z f - \<Psi>\<^sub>1.expectation Z \<bar>}"
      by auto
  qed
  also have "... \<le> \<Psi>\<^sub>1.variance Z / (\<Psi>\<^sub>1.expectation Z)^2" 
    using \<Psi>\<^sub>1.second_moment_method
    using \<Psi>\<^sub>1.Chebyshev_inequality[OF _ \<Psi>\<^sub>1.integrable_M] exp_Z_gt_2_7
    unfolding \<Psi>\<^sub>1.M_def by simp
  also have "... \<le> \<Psi>\<^sub>1.expectation Z / (\<Psi>\<^sub>1.expectation Z)^2" 
    by (intro divide_right_mono var_Z_le_exp_Z) simp
  also have "... = 1 / \<Psi>\<^sub>1.expectation Z" 
    using exp_Z_gt_2_7 by (simp add:power2_eq_square)
  also have "... \<le> ?R" 
    using exp_Z_gt_2_7 by (intro divide_left_mono) auto
  finally show ?thesis by simp
next
  case "False"
  have "?L \<le> \<Psi>\<^sub>1.prob {f. of_nat (Max (f ` A)) < log 2 (real Y) - 8}"
    unfolding t\<^sub>1_def 
    by (intro \<Psi>\<^sub>1.pmf_mono[OF \<Psi>\<^sub>1.M_def]) (auto simp add:int_of_nat_def)
  also have "... \<le> \<Psi>\<^sub>1.prob {}"
    using False by (intro \<Psi>\<^sub>1.pmf_mono[OF \<Psi>\<^sub>1.M_def]) simp
  also have "... = 0"
    by simp
  also have "... \<le> ?R" by simp
  finally show ?thesis by simp
qed

lemma t\<^sub>1_high: 
  "\<Psi>\<^sub>1.prob {f. of_int (t\<^sub>1 f) > log 2 (real Y) + 16 - b_exp} \<le> 1/2^7" (is "?L \<le> ?R")
proof -
  define Z :: "(nat \<Rightarrow> nat) \<Rightarrow> real" where "Z = r (nat \<lfloor>log 2 (real Y) + 8\<rfloor>)"

  have Z_nonneg: "Z f \<ge> 0" for f
    unfolding Z_def r_def by simp

  have "\<Psi>\<^sub>1.expectation Z \<le> real Y /(2 ^ nat \<lfloor>log 2 (real Y) + 8\<rfloor>)"
    unfolding Z_def r_exp by simp
  also have "... \<le> real Y / (2 powr (real (nat \<lfloor>log 2 (real Y) + 8\<rfloor>)))"
    by (subst powr_realpow) auto
  also have "... \<le> real Y / (2 powr \<lfloor>log 2 (real Y) + 8\<rfloor>)"
    by (intro divide_left_mono powr_mono) auto
  also have "... \<le> real Y / (2 powr (log 2 (real Y) + 7))"
    by (intro divide_left_mono powr_mono, linarith) auto
  also have "... = real Y / 2 powr (log 2 (real Y)) / 2 powr 7"
    by (subst powr_add) simp
  also have "... \<le> 1/2 powr 7"
    using Y_ge_1 by (subst powr_log_cancel) auto
  finally have Z_exp: "\<Psi>\<^sub>1.expectation Z \<le> 1/2^7" 
    by simp

  have "?L \<le> \<Psi>\<^sub>1.prob {f. of_nat (Max (f ` A)) > log 2 (real Y) + 7}"
    unfolding t\<^sub>1_def 
    by (intro \<Psi>\<^sub>1.pmf_mono[OF \<Psi>\<^sub>1.M_def]) (auto simp add:int_of_nat_def)
  also have "... \<le> \<Psi>\<^sub>1.prob {f. Z f \<ge> 1}"
  proof (rule \<Psi>\<^sub>1.pmf_mono[OF \<Psi>\<^sub>1.M_def])
    fix f assume "f \<in> set_pmf (sample_pmf (\<G> 2 n))"
    assume " f \<in> {f. real (Max (f ` A)) > log 2 (real Y) + 7}"
    hence "real (Max (f ` A)) > log 2 (real Y) + 7" by simp
    hence "int (Max (f ` A)) \<ge> \<lfloor>log 2 (real Y) + 8\<rfloor>"
      by linarith
    hence "Max (f ` A) \<ge> nat \<lfloor>log 2 (real Y) + 8\<rfloor>"
      by simp
    moreover have "f ` A \<noteq> {}" "finite (f ` A)"
      using fin_A finite_imageI A_nonempty by auto
    ultimately obtain fa where "fa \<in> f ` A" " fa \<ge>  nat \<lfloor>log 2 (real Y) + 8\<rfloor>"
      using Max_in by auto
    then obtain ae where ae_def: "ae \<in> A" "nat \<lfloor>log 2 (real Y) + 8\<rfloor> \<le> f ae"
      by auto
    hence "r (nat \<lfloor>log 2 (real Y) + 8\<rfloor>) f > 0"
      unfolding r_def card_gt_0_iff using fin_A by auto
    hence "Z f \<ge> 1"
      unfolding Z_def by simp
    thus "f \<in> {f. 1 \<le> Z f}" by simp
  qed
  also have "... \<le> \<Psi>\<^sub>1.expectation Z / 1"
    using Z_nonneg
    by (intro \<Psi>\<^sub>1.pmf_markov[OF \<Psi>\<^sub>1.M_def \<Psi>\<^sub>1.integrable_M]) auto
  also have "... \<le> ?R"
    using Z_exp by simp
  finally show ?thesis by simp
qed

lemma e_1: "\<Psi>.prob {\<psi>. \<not>E\<^sub>1 \<psi>} \<le> 1/2^6"
proof -
  have "\<Psi>\<^sub>1.prob {f. 2 powr (-t\<^sub>1 f) * Y \<notin> {b/2^16..b/2}} \<le> 
    \<Psi>\<^sub>1.prob {f. 2 powr (-t\<^sub>1 f) * Y < b/2^16} + \<Psi>\<^sub>1.prob {f. 2 powr (-t\<^sub>1 f) * Y > b/2}"
    by (intro \<Psi>\<^sub>1.pmf_add[OF \<Psi>\<^sub>1.M_def]) auto
  also have "... \<le> \<Psi>\<^sub>1.prob {f. t\<^sub>1 f > log 2 Y + 16 - b_exp} + \<Psi>\<^sub>1.prob {f. t\<^sub>1 f < log 2 Y + 1 - b_exp}"
  proof (rule add_mono)
    show "\<Psi>\<^sub>1.prob {f. 2 powr (-t\<^sub>1 f) * Y < b/2^16} \<le> \<Psi>\<^sub>1.prob {f. t\<^sub>1 f > log 2 Y + 16 - b_exp}"
    proof (rule \<Psi>\<^sub>1.pmf_mono[OF \<Psi>\<^sub>1.M_def])
      fix f assume "f \<in> {f. 2 powr real_of_int (- t\<^sub>1 f) * real Y < real b / 2 ^ 16}"
      hence "2 powr real_of_int (- t\<^sub>1 f) * real Y < real b / 2 ^ 16"
        by simp
      hence "log 2 (2 powr of_int (- t\<^sub>1 f) * real Y) < log 2 (real b / 2^16)"
        using b_min Y_ge_1 by (intro iffD2[OF log_less_cancel_iff]) auto
      hence "of_int (- t\<^sub>1 f) + log  2 (real Y) < log 2 (real b / 2^16)"
        using Y_ge_1 by (subst (asm) log_mult)  auto
      also have  "... = real b_exp - log 2 (2 powr 16)"
        unfolding b_def by (subst log_divide) auto 
      also have "... = real b_exp - 16"
        by (subst log_powr_cancel) auto
      finally have "of_int (- t\<^sub>1 f) + log 2 (real Y) < real b_exp - 16" by simp
      thus "f \<in> {f. of_int (t\<^sub>1 f) > log 2 (real Y) + 16 - b_exp}"
        by simp
    qed
  next
    show "\<Psi>\<^sub>1.prob {f. 2 powr (-t\<^sub>1 f) * Y > b/2} \<le> \<Psi>\<^sub>1.prob {f. t\<^sub>1 f < log 2 Y + 1 - b_exp}"
    proof (rule \<Psi>\<^sub>1.pmf_mono[OF \<Psi>\<^sub>1.M_def])
      fix f assume "f \<in> {f. 2 powr real_of_int (- t\<^sub>1 f) * real Y > real b / 2}"
      hence "2 powr real_of_int (- t\<^sub>1 f) * real Y > real b / 2"
        by simp
      hence "log 2 (2 powr of_int (- t\<^sub>1 f) * real Y) > log 2 (real b / 2)"
        using b_min Y_ge_1 by (intro iffD2[OF log_less_cancel_iff]) auto
      hence "of_int (- t\<^sub>1 f) + log  2 (real Y) > log 2 (real b / 2)"
        using Y_ge_1 by (subst (asm) log_mult)  auto
      hence  "of_int (- t\<^sub>1 f) + log  2 (real Y) > real b_exp - 1"
        unfolding b_def by (subst (asm) log_divide) auto 
      hence "of_int (t\<^sub>1 f) < log 2 (real Y) + 1 - b_exp"
        by simp
      thus "f \<in> {f. of_int (t\<^sub>1 f) < log 2 (real Y) + 1 - b_exp}"
        by simp
    qed
  qed
  also have "... \<le> 1/2^7 + 1/2^7"
    by (intro add_mono t\<^sub>1_low t\<^sub>1_high)
  also have "... = 1/2^6" by simp
  finally have "\<Psi>\<^sub>1.prob {f. 2 powr (-t\<^sub>1 f) * Y \<notin> {b/2^16..b/2}} \<le> 1/2^6" by simp

  thus ?thesis
    unfolding \<Psi>.M_def sample_pmf_\<Psi> E\<^sub>1_def \<Psi>\<^sub>1.M_def
    by (simp only:case_prod_beta) (subst pair_pmf_prob_left)
qed


end

end