theory Distributed_Distinct_Elements_Outer_Algorithm
  imports 
    DDE_Accuracy_With_Cutoff 
    Prefix_Free_Code_Combinators.Prefix_Free_Code_Combinators
    Frequency_Moments.Landau_Ext
    Landau_Symbols.Landau_More
begin

unbundle intro_cong_syntax

definition "state_space_usage = (\<lambda>(n,\<delta>,\<epsilon>). 2^40 * (ln(1/\<epsilon>)+1)/ \<delta>^2 + log 2 (log 2 n + 3))"
definition "seed_space_usage = (\<lambda>(n,\<delta>,\<epsilon>). 2^30 + 2^23*ln n+48*(log 2(1/\<delta>)+16)\<^sup>2 + 336*ln (1/\<epsilon>))"

locale outer_algorithm =
  fixes n :: nat
  fixes \<epsilon> :: real
  fixes \<delta> :: real
  assumes n_gt_0: "n > 0" 
  assumes \<epsilon>_gt_0: "\<epsilon> > 0" and \<epsilon>_lt_1: "\<epsilon> < 1"
  assumes \<delta>_gt_0: "\<delta> > 0" and \<delta>_lt_1: "\<delta> < 1"
begin

definition n0 where "n0 = max (real n) (exp (exp 5))"
definition stage_two where "stage_two = (\<epsilon> < (1/ln n0))"
definition \<epsilon>\<^sub>i :: real where "\<epsilon>\<^sub>i = (if stage_two then (1/ln n0) else \<epsilon>)"
definition l :: nat where "l = (if stage_two then nat \<lceil>4 * ln (1/ \<epsilon>)/ln (ln n0)\<rceil> else 1)"
definition \<Lambda> where "\<Lambda> = (if stage_two then (1/ln n0) else 1)"

lemma l_lbound:
  assumes "stage_two"
  shows "l \<ge> 4 * ln (1/ \<epsilon>)/ln(ln n0)"
proof -
  have "l = real (nat \<lceil>4 * ln (1 / \<epsilon>) / ln (ln n0)\<rceil>)"
    using assms unfolding l_def by simp
  also have "... \<ge> 4 * ln (1 / \<epsilon>) / ln (ln n0)"
    by linarith
  finally show ?thesis by simp
qed

lemma n_lbound:
  "n0 \<ge> exp (exp 5)" "ln n0 \<ge> exp 5" "5 \<le> ln (ln n0)" "ln n0 > 1" "n0 > 1"
proof -
  show 0:"n0 \<ge> exp (exp 5)"
    unfolding n0_def by simp
  have "(1::real) \<le> exp (exp 5)"
    by (approximation 5)
  hence "n0 \<ge> 1" 
    using 0 by argo
  thus 1:"ln n0 \<ge> exp 5"
    using 0 by (intro iffD2[OF ln_ge_iff]) auto
  moreover have "1 < exp (5::real)"
    by (approximation 5)
  ultimately show 2:"ln n0 > 1"
    by argo
  show "5 \<le> ln (ln n0)"
    using 1 2 by (subst ln_ge_iff) simp
  have "(1::real) < exp (exp 5)"
    by (approximation 5)
  thus "n0 > 1"
    using 0 by argo
qed

lemma \<epsilon>1_gt_0: "0 < \<epsilon>\<^sub>i"
  using n_lbound(4) \<epsilon>_gt_0 unfolding \<epsilon>\<^sub>i_def
  by (cases "stage_two") simp_all

lemma \<epsilon>1_lt_1: "\<epsilon>\<^sub>i < 1"
  using n_lbound(4) \<epsilon>_lt_1 unfolding \<epsilon>\<^sub>i_def
  by (cases "stage_two") simp_all

lemma l_gt_0_aux: 
  assumes "stage_two"
  shows "1 \<le> ln (1 / \<epsilon>) / ln (ln n0)"
proof -
  have "ln n0 \<le> 1 / \<epsilon>"
    using n_lbound(4)
    using assms unfolding pos_le_divide_eq[OF \<epsilon>_gt_0] stage_two_def 
    by (simp add:divide_simps ac_simps)
  hence "ln (ln n0) \<le> ln (1 / \<epsilon>)" 
    using n_lbound(4) \<epsilon>_gt_0 by (intro iffD2[OF ln_le_cancel_iff] divide_pos_pos) auto
  thus "1 \<le> ln (1 / \<epsilon>) / ln (ln n0)"
    using n_lbound(3)
    by (subst pos_le_divide_eq) auto
qed

lemma l_gt_0: "l > 0"
proof (cases "stage_two")
  case True
  have "0 < 4 * ln (1/ \<epsilon>)/ln(ln n0)"
    using l_gt_0_aux[OF True] by simp
  also have "... \<le> l"
    using l_lbound[OF True] by simp
  finally have "0 < real l"
    by simp
  then show ?thesis by simp  
next
  case False
  then show ?thesis unfolding l_def by simp
qed

lemma \<Lambda>_gt_0: "\<Lambda> > 0"
  using n_lbound(4) unfolding \<Lambda>_def
  by (cases "stage_two") auto

lemma \<Lambda>_le_1: "\<Lambda> \<le> 1"
  using n_lbound(4) unfolding \<Lambda>_def
  by (cases "stage_two") simp_all

sublocale I: inner_algorithm "n" "\<epsilon>\<^sub>i" "\<delta>"
  unfolding inner_algorithm_def using n_gt_0 \<delta>_gt_0 \<delta>_lt_1 \<epsilon>1_gt_0 \<epsilon>1_lt_1 by auto

abbreviation \<Theta> where "\<Theta> \<equiv> \<E> l \<Lambda> I.\<Omega>"

sublocale \<Theta>: expander_sample_space l \<Lambda> I.\<Omega>
  unfolding expander_sample_space_def using I.\<Omega>.sample_space \<Lambda>_gt_0 l_gt_0 by auto

type_synonym state = "inner_algorithm.f0_state list"

definition encode_state 
  where "encode_state = Lf\<^sub>e I.encode_state l"

lemma encode_state: "is_encoding encode_state"
  unfolding encode_state_def
  by (intro fixed_list_encoding I.encode_state)

fun single :: "nat \<Rightarrow> nat \<Rightarrow> state" where
  "single \<theta> x = map (\<lambda>j. I.single (select \<Theta> \<theta> j) x) [0..<l]"

fun merge :: "state \<Rightarrow> state \<Rightarrow> state" where
  "merge x y = map (\<lambda>(x,y). I.merge x y) (zip x y)"

fun estimate :: "state \<Rightarrow> real" where
  "estimate x = median l (\<lambda>i. I.estimate (x ! i))"

definition \<tau> :: "nat \<Rightarrow> nat set \<Rightarrow> state" 
  where "\<tau> \<theta> A = map (\<lambda>i. I.\<tau> (select \<Theta> \<theta> i) A) [0..<l]"

theorem merge_result: "merge (\<tau> \<omega> A) (\<tau> \<omega> B) = \<tau> \<omega> (A \<union> B)" (is "?L = ?R")
proof -
  have 0: "zip [0..<l] [0..<l] = map (\<lambda>x. (x,x)) [0..<l]" for l
    by (induction l, auto)

  have "?L = map (\<lambda>x. I.merge (I.\<tau> (select \<Theta> \<omega> x) A) (I.\<tau> (select \<Theta> \<omega> x) B)) [0..<l]"
    unfolding \<tau>_def 
    by (simp add:zip_map_map 0 comp_def case_prod_beta del:I.\<tau>.simps I.merge.simps)
  also have "... = map (\<lambda>x.  I.\<tau> (select \<Theta> \<omega> x) (A \<union> B)) [0..<l]"
    by (intro map_cong I.merge_result \<Theta>.range) auto
  also have "... = ?R"
    unfolding \<tau>_def by simp
  finally show ?thesis by simp
qed

theorem single_result: "single \<omega> x = \<tau> \<omega> {x}" (is "?L = ?R")
proof -
  have "?L = map (\<lambda>j. I.single (select \<Theta> \<omega> j) x) [0..<l]"
    by (simp del:I.single.simps)
  also have "... = ?R"
    unfolding \<tau>_def by (intro map_cong I.single_result \<Theta>.range) auto
  finally show ?thesis by simp
qed

theorem estimate_result:
  assumes "A \<subseteq> {..<n}" "A \<noteq> {}"
  defines "p \<equiv> (pmf_of_set {..<size \<Theta>})"
  shows "measure p {\<omega>. \<bar>estimate (\<tau> \<omega> A)- real (card A)\<bar> > \<delta> * real (card A)} \<le> \<epsilon>" (is "?L \<le> ?R")
proof (cases "stage_two")
  case True
  define I where "I = {x. \<bar>x - real (card A)\<bar> \<le> \<delta> * real (card A)}"
  have int_I: "interval I" 
    unfolding interval_def I_def by auto

  define \<mu> where "\<mu> = measure I.\<Omega> {\<omega>. I.estimate (I.\<tau> \<omega> A) \<notin> I}"

  have 2: "5 \<le> ln (ln n0)"
    using n_lbound by (subst ln_ge_iff) simp

  have 3:"\<mu> + \<Lambda> > 0" 
    unfolding \<mu>_def
    by (intro add_nonneg_pos \<Lambda>_gt_0) auto

  have "\<mu> \<le> \<epsilon>\<^sub>i"
    unfolding \<mu>_def I_def using I.theorem_6_2[OF assms(1,2)] 
    by (simp add: not_le del:I.estimate.simps I.\<tau>.simps)
  also have "... = 1/ln n0"
    using True unfolding \<epsilon>\<^sub>i_def by simp
  finally have "\<mu> \<le> 1/ln n0" by simp
  hence "\<mu> + \<Lambda> \<le> 1/ln n0 + 1/ln n0"
    unfolding \<Lambda>_def using True by (intro add_mono) auto
  also have "... = 2/ln n0"
    by simp
  finally have 5:"\<mu> + \<Lambda> \<le> 2 / ln n0"
    by simp
  hence 0:"ln n0 \<le> 2 / (\<mu> + \<Lambda>)"
    using 3 n_lbound by (simp add:field_simps)

  have 4: "2 * ln 2 + 8 * exp (- 1) \<le> (5::real)"
    by (approximation 5)

  have "\<mu> + \<Lambda> \<le> 2/ln n0"
    by (intro 5)
  also have "... \<le> 2/exp 5"
    using n_lbound by (intro divide_left_mono) simp_all
  also have "... \<le> 1/2"
    by (approximation 5)
  finally have 1:"\<mu> + \<Lambda> \<le> 1/2" by simp

  have "?L = measure p {\<omega>. median l (\<lambda>i. I.estimate (\<tau> \<omega> A  ! i)) \<notin> I}"
    unfolding I_def by (simp add:not_le)
  also have "... \<le> 
    measure p {\<theta>. real (card {i \<in> {..<l}. I.estimate (I.\<tau> (select \<Theta> \<theta> i) A) \<notin> I})\<ge> real l/2}"
  proof (rule pmf_mono)
    fix \<theta> assume "\<theta> \<in> set_pmf p"
    assume a:"\<theta> \<in> {\<omega>. median l (\<lambda>i. I.estimate (\<tau> \<omega> A ! i)) \<notin> I}"
    have "real l = 2 * real l - real l"
      by simp
    also have "... \<le> 2 * real l - 2 * card {i. i < l \<and> I.estimate (\<tau> \<theta> A ! i) \<in> I}"
      using median_est[OF int_I, where n="l"] a   
      by (intro diff_left_mono Nat.of_nat_mono)
       (auto simp add:not_less[symmetric] simp del:I.estimate.simps)
    also have "... = 2 * (real (card {..<l}) - card {i. i < l \<and> I.estimate (\<tau> \<theta> A ! i) \<in> I})"
      by (simp del:I.estimate.simps)
    also have "... = 2 * real (card {..<l} - card {i. i < l \<and> I.estimate (\<tau> \<theta> A ! i) \<in> I})"
      by (intro_cong "[\<sigma>\<^sub>2 (*)]" more:of_nat_diff[symmetric] card_mono)
        (auto simp del:I.estimate.simps)
    also have "... = 2 * real (card ({..<l} - {i. i < l \<and> I.estimate (\<tau> \<theta> A ! i) \<in> I}))"
      by (intro_cong "[\<sigma>\<^sub>2 (*), \<sigma>\<^sub>1 of_nat]" more:card_Diff_subset[symmetric]) 
        (auto simp del:I.estimate.simps)
    also have "... = 2 * real (card {i\<in>{..<l}. I.estimate (\<tau> \<theta> A ! i) \<notin> I})"
      by (intro_cong "[\<sigma>\<^sub>2 (*), \<sigma>\<^sub>1 of_nat, \<sigma>\<^sub>1 card]") (auto simp del:I.estimate.simps)
    also have "... = 2 * real (card {i \<in> {..<l}. I.estimate (I.\<tau> (select \<Theta> \<theta> i) A) \<notin> I})"
      unfolding \<tau>_def by (intro_cong "[\<sigma>\<^sub>2 (*), \<sigma>\<^sub>1 of_nat, \<sigma>\<^sub>1 card]" more:restr_Collect_cong)
       (simp del:I.estimate.simps I.\<tau>.simps)
    finally have "real l \<le> 2 * real (card {i \<in> {..<l}. I.estimate (I.\<tau> (select \<Theta> \<theta> i) A) \<notin> I})"
      by simp
    thus "\<theta> \<in> {\<theta>. real l / 2 \<le> real (card {i \<in> {..<l}. I.estimate (I.\<tau> (select \<Theta> \<theta> i) A) \<notin> I})}"
      by simp
  qed
  also have "...=measure \<Theta>{\<theta>. real(card {i \<in> {..<l}. I.estimate (I.\<tau> (\<theta> i) A) \<notin> I})\<ge>(1/2)*real l}"
    unfolding sample_pmf_alt[OF \<Theta>.sample_space] p_def by (simp del:I.estimate.simps I.\<tau>.simps)
  also have "... \<le> exp (-real l* ((1/2) * ln (1/ (\<mu> + \<Lambda>)) - 2*exp (-1)))"
    using 1 l_gt_0 \<Lambda>_gt_0 unfolding \<mu>_def by (intro \<Theta>.tail_bound) force+
  also have "... \<le> exp (-real l* ((1/2) * ln (ln n0 / 2) - 2*exp (-1)))"
    using 0 1 3 n_lbound
    by (intro iffD2[OF exp_le_cancel_iff] mult_right_mono mult_left_mono_neg[where c="-real l"]
        diff_mono mult_left_mono iffD2[OF ln_le_cancel_iff]) (simp_all)
  also have "... = exp (-real l * (ln (ln n0) / 2 - (ln 2/2 + 2*exp (-1))))"
    using n_lbound by (subst ln_div) (simp_all add:algebra_simps)
  also have "... \<le> exp (-real l * (ln (ln n0) / 2 - (ln (ln (exp(exp 5))) / 4)))"
    using 4
    by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono_neg[where c="-real l"] diff_mono) simp_all 
  also have "... \<le> exp (-real l * (ln (ln n0) / 2 - (ln (ln n0) / 4)))"
    using 2
    by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono_neg[where c="-real l"] diff_mono) simp_all
  also have "... = exp (- real l * (ln (ln n0)/ 4) )"
    by (simp add:algebra_simps)
  also have "... \<le> exp (- (4 * ln (1/ \<epsilon>)/ln(ln n0)) * (ln (ln n0)/4))"
    using l_lbound[OF True] 2
    by (intro iffD2[OF exp_le_cancel_iff] mult_right_mono divide_nonneg_pos) simp_all
  also have "... = exp (- ln (1/ \<epsilon>))"
    using 2 by simp
  also have "... = \<epsilon>"
    using \<epsilon>_gt_0 by (subst ln_inverse[symmetric]) auto
  finally show ?thesis by simp
next
  case False
  have l_eq: "l = 1"
    unfolding l_def using False by simp
  hence "?L = measure p {\<omega>. \<delta> * real (card A) < \<bar>I.estimate (\<tau> \<omega> A ! 0) - real (card A)\<bar>}"
    unfolding estimate.simps l_eq median_def by simp
  also have "... =  measure p {\<omega>. \<delta>*real(card A)<\<bar>I.estimate (I.\<tau> (select \<Theta> \<omega> 0) A)-real(card A)\<bar>}"
    unfolding \<tau>_def l_eq by (simp del: I.\<tau>.simps I.estimate.simps)
  also have "... = measure \<Theta> {\<omega>. \<delta>*real(card A) < \<bar>I.estimate (I.\<tau> (\<omega> 0) A)-real(card A)\<bar>}"
    unfolding sample_pmf_alt[OF \<Theta>.sample_space] p_def by (simp del:I.\<tau>.simps I.estimate.simps)
  also have "...= 
    measure (map_pmf (\<lambda>\<theta>. \<theta> 0) \<Theta>) {\<omega>. \<delta>*real(card A) < \<bar>I.estimate (I.\<tau> \<omega> A)-real(card A)\<bar>}"
    by simp
  also have "... = measure I.\<Omega> {\<omega>. \<delta>*real(card A) < \<bar>I.estimate (I.\<tau> \<omega> A)-real(card A)\<bar>}"
    using l_eq by (subst \<Theta>.uniform_property) auto
  also have "... \<le> \<epsilon>\<^sub>i"
    by (intro I.theorem_6_2[OF assms(1,2)])
  also have "... = ?R"
    unfolding \<epsilon>\<^sub>i_def using False by simp
  finally show ?thesis 
    by simp
qed

lemma state_bit_count:
  "bit_count (encode_state (\<tau> \<omega> A)) \<le> state_space_usage (real n, \<delta>, \<epsilon>)" 
    (is "?L \<le> ?R")
proof -
  have 0: "length (\<tau> \<omega> A) = l" 
    unfolding \<tau>_def by simp
  have "?L = (\<Sum>x\<leftarrow>\<tau> \<omega> A. bit_count (I.encode_state x))"
    using 0 unfolding encode_state_def fixed_list_bit_count by simp
  also have "... = (\<Sum>x\<leftarrow>[0..<l]. bit_count (I.encode_state (I.\<tau> (select \<Theta> \<omega> x) A)))"
    unfolding \<tau>_def by (simp del:I.\<tau>.simps add:comp_def)
  also have "... \<le> (\<Sum>x\<leftarrow>[0..<l]. ereal (2^36 *(ln (1/\<epsilon>\<^sub>i)+ 1)/\<delta>\<^sup>2 + log 2 (log 2 (real n) + 3)))"
    using I.state_bit_count by (intro sum_list_mono I.state_bit_count \<Theta>.range)
  also have "... = ereal ( real l * (2^36 *(ln (1/\<epsilon>\<^sub>i)+ 1)/\<delta>\<^sup>2 + log 2 (log 2 (real n) + 3)))"
    unfolding sum_list_triv_ereal by simp
  also have "... \<le> 2^40 * (ln(1/\<epsilon>)+1)/ \<delta>^2 + log 2 (log 2 n + 3)" (is "?L1 \<le> ?R1")
  proof (cases "stage_two")
    case True

    have "\<lceil>4*ln (1/\<epsilon>)/ln(ln n0)\<rceil> \<le> 4*ln (1/\<epsilon>)/ln(ln n0) + 1"
      by simp
    also have "... \<le> 4*ln (1/\<epsilon>)/ln(ln n0) + ln (1/\<epsilon>)/ln(ln n0)"
      using l_gt_0_aux[OF True] by (intro add_mono) auto
    also have "... = 5 * ln (1/\<epsilon>)/ln(ln n0)" by simp
    finally have 3: "\<lceil>4*ln (1/\<epsilon>)/ln(ln n0)\<rceil> \<le> 5 * ln (1/\<epsilon>)/ln(ln n0)"
      by simp

    have 4: "0 \<le> log 2 (log 2 (real n) + 3)" 
      using n_gt_0
      by (intro iffD2[OF zero_le_log_cancel_iff] add_nonneg_pos) auto

    have 5: "1 / ln 2 + 3 / exp 5 \<le> exp (1::real)"  "1.2 / ln 2 \<le> (2::real)"
      by (approximation 5)+

    have "log 2(log 2 (real n)+3) \<le> log 2 (log 2 n0 + 3)"
      using n_gt_0 by (intro iffD2[OF log_le_cancel_iff] add_mono add_nonneg_pos 
          iffD2[OF zero_le_log_cancel_iff]) (simp_all add:n0_def)
    also have "... = ln (ln n0 / ln 2 + 3) / ln 2"
      unfolding log_def by simp
    also have "... \<le> ln (ln n0/ln 2 + (3 / exp 5) * ln n0) / ln 2"
      using n_lbound by (intro divide_right_mono iffD2[OF ln_le_cancel_iff] add_mono add_nonneg_pos)
       (simp_all add:divide_simps)
    also have "... = ln ( ln n0 * (1 /ln 2 + 3/exp 5)) / ln 2"
      by (simp add:algebra_simps)
    also have "... \<le> ln ( ln n0 * exp 1) / ln 2"
      using n_lbound by (intro divide_right_mono iffD2[OF ln_le_cancel_iff] add_mono 
          mult_left_mono 5 Rings.mult_pos_pos add_pos_nonneg) auto
    also have "... = (ln (ln n0) + 1) / ln 2"
      using n_lbound by (subst ln_mult) simp_all
    also have "... \<le> (ln (ln n0) + 0.2 * ln (ln n0)) / ln 2"
      using n_lbound by (intro divide_right_mono add_mono) auto
    also have "... = (1.2/ ln 2) * ln (ln n0)"
      by simp
    also have "... \<le> 2 * ln (ln n0)"
      using n_lbound by (intro mult_right_mono 5) simp
    finally have "log 2(log 2 (real n)+3) \<le> 2 * ln (ln n0)"
      by simp
    hence 6: "log 2(log 2 (real n)+3)/ln(ln n0) \<le> 2"
      using n_lbound by (subst pos_divide_le_eq) simp_all

    have "?L1 = real(nat \<lceil>4*ln (1/\<epsilon>)/ln(ln n0)\<rceil>)*(2^36*(ln (ln n0)+1)/\<delta>^2+log 2(log 2 (real n)+3))"
      using True unfolding l_def \<epsilon>\<^sub>i_def by simp
    also have "... = \<lceil>4*ln (1/\<epsilon>)/ln(ln n0)\<rceil>*(2^36*(ln (ln n0)+1)/\<delta>^2+log 2(log 2 (real n)+3))"
      using l_gt_0_aux[OF True] by (subst of_nat_nat) simp_all
    also have "... \<le> (5*ln (1/\<epsilon>)/ln(ln n0)) *(2^36*(ln (ln n0)+1)/\<delta>^2+log 2(log 2 (real n)+3))"
      using n_lbound(3) \<delta>_gt_0  4 by (intro ereal_mono mult_right_mono 
          add_nonneg_nonneg divide_nonneg_pos mult_nonneg_nonneg 3) simp_all
    also have "... \<le> (5 * ln (1/\<epsilon>)/ln(ln n0))*((2^36+2^36)*ln (ln n0)/\<delta>^2+log 2(log 2 (real n)+3))"
      using n_lbound \<epsilon>_gt_0 \<epsilon>_lt_1
      by (intro ereal_mono mult_left_mono add_mono divide_right_mono divide_nonneg_pos) auto
    also have "... = 5*(2^37)* ln (1/\<epsilon>)/ \<delta>^2 + (5*ln (1/\<epsilon>)) * (log 2(log 2 (real n)+3)/ln(ln n0))"
      using n_lbound by (simp add:algebra_simps)
    also have "... \<le> 5*(2^37)* ln (1/\<epsilon>)/ \<delta>^2 + (5*ln(1/ \<epsilon>)) * 2"
      using \<epsilon>_gt_0 \<epsilon>_lt_1 by (intro add_mono ereal_mono order.refl mult_left_mono 6) auto
    also have "... = 5*(2^37)* ln (1/\<epsilon>)/ \<delta>^2 + 5*2*ln(1/ \<epsilon>) / 1"
      by simp
    also have "... \<le> 5*(2^37)* ln (1/\<epsilon>)/ \<delta>^2 + 5*2*ln(1/ \<epsilon>) / \<delta>^2"
      using \<delta>_gt_0 \<delta>_lt_1 \<epsilon>_gt_0 \<epsilon>_lt_1
      by (intro add_mono ereal_mono divide_left_mono Rings.mult_pos_pos power_le_one) auto
    also have "... = (5*(2^37+2))* (ln (1/\<epsilon>)+0)/ \<delta>^2 + 0"
      by (simp add:algebra_simps)
    also have "... \<le> 2^40 * (ln (1 / \<epsilon>)+1) / \<delta>^2 +  log 2 (log 2 (real n) + 3)"
      using \<delta>_gt_0 \<delta>_lt_1 \<epsilon>_gt_0 \<epsilon>_lt_1 n_gt_0 by (intro add_mono ereal_mono divide_right_mono 
          mult_right_mono iffD2[OF zero_le_log_cancel_iff] add_nonneg_pos) auto
    finally show ?thesis by simp
  next
    case False
    have "?L1 = 2^36 *(ln (1/\<epsilon>)+ 1)/\<delta>\<^sup>2 + log 2 (log 2 (real n) + 3)"
      using False unfolding \<epsilon>\<^sub>i_def l_def by simp
    also have "... \<le> ?R1"
      using \<delta>_gt_0 \<delta>_lt_1 \<epsilon>_gt_0 \<epsilon>_lt_1
      by (intro ereal_mono add_mono divide_right_mono mult_right_mono add_nonneg_nonneg) auto
    finally show ?thesis by simp
  qed
  finally show ?thesis 
    unfolding state_space_usage_def by simp
qed

definition encode_seed 
  where "encode_seed = Nb\<^sub>e (size \<Theta>)"

lemma encode_seed:
  "is_encoding encode_seed"
  unfolding encode_seed_def
  by (intro bounded_nat_encoding)

lemma random_bit_count:
  assumes "\<omega> < size \<Theta>"
  shows "bit_count (encode_seed \<omega>) \<le> seed_space_usage (real n, \<delta>, \<epsilon>)" 
    (is "?L \<le> ?R")
proof -
  have 0: "size \<Theta> > 0"
    using \<Theta>.sample_space unfolding sample_space_def by simp
  have 1: "size I.\<Omega> > 0" 
    using I.\<Omega>.sample_space unfolding sample_space_def by simp

  have "(55+60*ln (ln n0))^3 \<le> (180+60*ln (ln n0))^3"
    using n_lbound by (intro power_mono add_mono) auto
  also have "... = 180^3 * (1+ln (ln n0)/real 3)^3"
    unfolding power_mult_distrib[symmetric] by simp
  also have "... \<le> 180^3 * exp (ln (ln n0))"
    using n_lbound by (intro mult_left_mono exp_ge_one_plus_x_over_n_power_n) auto
  also have "... = 180^3 * ln n0"
    using n_lbound by (subst exp_ln) auto
  also have "... \<le> 180^3 * max (ln n) (ln (exp (exp 5)))"
    using n_gt_0 unfolding n0_def by (subst ln_max_swap) auto
  also have "... \<le> 180^3 * (ln n + exp 5)"
    using n_gt_0 unfolding ln_exp by (intro mult_left_mono) auto
  finally have 5:"(55+60*ln (ln n0))^3 \<le> 180^3 * ln n + 180^3*exp 5"
    by simp

  have 6:"((1::real)+180^3*exp 5) \<le> 2^30" "((4::real)/ln 2 + 180^3) \<le> 2^23"
    by (approximation 10)+

  have "?L = ereal (real (floorlog 2 (size \<Theta> - 1)))"
    using assms unfolding encode_seed_def bounded_nat_bit_count by simp
  also have "... \<le> ereal (real (floorlog 2 (size \<Theta>)))"
    by (intro ereal_mono Nat.of_nat_mono floorlog_mono) auto
  also have "... = ereal (1 + of_int \<lfloor>log 2 (real (sample_space.size \<Theta>))\<rfloor>)"
    using 0 unfolding floorlog_def by simp
  also have "... \<le> ereal (1 + log 2 (real (size \<Theta>)))"
    by (intro add_mono ereal_mono) auto
  also have "... = 1 + log 2 (real (size I.\<Omega>) * (2^4) ^ ((l - 1) * nat \<lceil>ln \<Lambda> / ln 0.95\<rceil>))"
    unfolding \<Theta>.size by simp
  also have "... = 1 + log 2 (real (size I.\<Omega>) * 2^ (4 * (l - 1) * nat \<lceil>ln \<Lambda> / ln 0.95\<rceil>))"
    unfolding power_mult by simp
  also have "... = 1 + log 2 (real (size I.\<Omega>)) + (4*(l-1)* nat\<lceil>ln \<Lambda> / ln 0.95\<rceil>)"
    using 1 by (subst log_mult) simp_all
  also have "... \<le> 1+log 2(2 powr (4*log 2 n + 48 * (log 2 (1/\<delta>)+16)\<^sup>2+ (55+60*ln (1/\<epsilon>\<^sub>i))^3))+
    (4*(l-1)* nat\<lceil>ln \<Lambda> / ln 0.95\<rceil>)"
    using 1 by (intro ereal_mono add_mono iffD2[OF log_le_cancel_iff] I.random_bit_count) auto
  also have "...=1+4*log 2 n+48*(log 2(1/\<delta>)+16)\<^sup>2+(55+60*ln (1/\<epsilon>\<^sub>i))^3+(4*(l-1)*nat\<lceil>ln \<Lambda>/ln 0.95\<rceil>)"
    by (subst log_powr_cancel) auto
  also have "... \<le> 2^30 + 2^23*ln n+48*(log 2(1/\<delta>)+16)\<^sup>2 + 336*ln (1/\<epsilon>)" (is "?L1 \<le> ?R1")
  proof (cases "stage_two")
    case True

    have "-1 < (0::real)" by simp
    also have "... \<le> ln \<Lambda> / ln 0.95"
      using \<Lambda>_gt_0 \<Lambda>_le_1 by (intro divide_nonpos_neg) auto
    finally have 2: "- 1 < ln \<Lambda> / ln 0.95" by simp

    have 3: "- 1 / ln 0.95 \<le> (20::real)"
      by (approximation 10)

    have "(4*(l-1)*nat\<lceil>ln \<Lambda>/ln 0.95\<rceil>) = 4 * (real l-1) * of_int \<lceil>ln \<Lambda>/ln 0.95\<rceil>"
      using 2 l_gt_0 unfolding of_nat_mult by (subst of_nat_nat) auto
    also have "... \<le> 4 * (real l-1) * (ln \<Lambda>/ln 0.95 + 1)"
      using l_gt_0 by (intro mult_left_mono) auto
    also have "... = 4 * (real l-1) * (-ln (ln n0)/ln 0.95 + 1)"
      using n_lbound True unfolding \<Lambda>_def 
      by (subst ln_inverse[symmetric]) (simp_all add:inverse_eq_divide)
    also have "... = 4 * (real l - 1 ) * (ln (ln n0) * (-1/ln 0.95) + 1)"
      by simp
    also have "... \<le> 4 * (real l - 1 ) * (ln (ln n0) * 20 + 1)"
      using n_lbound l_gt_0 by (intro mult_left_mono add_mono 3) auto
    also have "... = 4 * (real (nat \<lceil>4 * ln (1 / \<epsilon>) / ln (ln n0)\<rceil>)-1) *  (ln (ln n0) * 20 + 1)"
      using True unfolding l_def by simp
    also have "... = 4 * (real_of_int \<lceil>4 * ln (1 / \<epsilon>) / ln (ln n0)\<rceil>-1) *  (ln (ln n0) * 20 + 1)"
      using l_gt_0_aux[OF True] by (subst of_nat_nat) simp_all
    also have "... \<le> 4 * (4 * ln (1 / \<epsilon>) / ln (ln n0)) * (ln (ln n0) * 20 + 1)"
      using n_lbound by (intro mult_left_mono mult_right_mono) auto
    also have "... \<le> 4 * (4 * ln (1 / \<epsilon>) / ln (ln n0)) * (ln (ln n0) * 20 + ln (ln n0))"
      using \<epsilon>_gt_0 \<epsilon>_lt_1 n_lbound 
      by (intro mult_left_mono mult_right_mono add_mono divide_nonneg_pos Rings.mult_nonneg_nonneg)
       simp_all
    also have "... = 336 * ln (1  / \<epsilon>)"
      using n_lbound by simp
    finally have 4: "4 * (l-1) * nat \<lceil>ln \<Lambda>/ln 0.95\<rceil> \<le> 336 * ln (1/\<epsilon>)" 
      by simp

    have "?L1 =1+4*log 2 n+48*(log 2(1/\<delta>)+16)\<^sup>2+(55+60*ln (ln n0))^3+(4*(l-1)*nat\<lceil>ln \<Lambda>/ln 0.95\<rceil>)"
      using True unfolding \<epsilon>\<^sub>i_def by simp
    also have "... \<le> 1+4*log 2 n+48*(log 2(1/\<delta>)+16)\<^sup>2+(180^3 * ln n + 180^3*exp 5) + 336 * ln (1/\<epsilon>)"
      by (intro add_mono 4 5 ereal_mono order.refl)
    also have "... = (1+180^3*exp 5)+ (4/ln 2 + 180^3)*ln n+48*(log 2(1/\<delta>)+16)\<^sup>2+ 336 * ln (1/\<epsilon>)"
      by (simp add:log_def algebra_simps)
    also have "... \<le> 2^30 + 2^23*ln n+48*(log 2(1/\<delta>)+16)\<^sup>2+ 336 * ln (1/\<epsilon>)"
      using n_gt_0 by (intro add_mono ereal_mono 6 order.refl mult_right_mono) auto
    finally show ?thesis by simp
  next
    case False
    hence "1 / \<epsilon> \<le> ln n0" 
      using \<epsilon>_gt_0 n_lbound
      unfolding stage_two_def not_less by (simp add:divide_simps ac_simps)
    hence 7: "ln (1 / \<epsilon>) \<le> ln (ln n0)"
      using n_lbound \<epsilon>_gt_0 \<epsilon>_lt_1
      by (intro iffD2[OF ln_le_cancel_iff]) auto

    have 8: "0 \<le> 336*ln (1/\<epsilon>) "
      using \<epsilon>_gt_0 \<epsilon>_lt_1 by auto

    have "?L1 = 1 + 4 * log 2 (real n) + 48 * (log 2 (1 / \<delta>) + 16)\<^sup>2 + (55 + 60 * ln (1 / \<epsilon>)) ^ 3"
      using False unfolding \<epsilon>\<^sub>i_def l_def by simp
    also have "... \<le> 1 + 4 * log 2 (real n) + 48 * (log 2 (1 / \<delta>) + 16)\<^sup>2 + (55 + 60 * ln (ln n0))^3"
      using \<epsilon>_gt_0 \<epsilon>_lt_1
      by (intro add_mono order.refl ereal_mono power_mono mult_left_mono add_nonneg_nonneg 7) auto
    also have "... \<le> 1+4*log 2(real n)+48*(log 2 (1 / \<delta>)+16)\<^sup>2+(180^3*ln (real n) + 180 ^ 3 * exp 5)"
      by (intro add_mono ereal_mono 5 order.refl)
    also have "... = (1+180^3*exp 5)+ (4/ln 2 + 180^3)*ln n+48*(log 2(1/\<delta>)+16)\<^sup>2+ 0"
      by (simp add:log_def algebra_simps)
    also have "... \<le> 2^30 + 2^23*ln n+48*(log 2(1/\<delta>)+16)\<^sup>2 + 336*ln (1/\<epsilon>)"
      using n_gt_0 by (intro add_mono ereal_mono 6 order.refl mult_right_mono 8) auto
    finally show ?thesis by simp
  qed
  also have "... = seed_space_usage (real n, \<delta>, \<epsilon>)"
    unfolding seed_space_usage_def by simp
  finally show ?thesis by simp
qed

end

context
begin

definition n_of :: "real \<times> real \<times> real \<Rightarrow> real" where "n_of = (\<lambda>(n, \<delta>, \<epsilon>). n)"
definition \<epsilon>_of :: "real \<times> real \<times> real \<Rightarrow> real" where "\<epsilon>_of = (\<lambda>(n, \<delta>, \<epsilon>). \<epsilon>)"
definition \<delta>_of :: "real \<times> real \<times> real \<Rightarrow> real" where "\<delta>_of = (\<lambda>(n, \<delta>, \<epsilon>). \<delta>)"

abbreviation F :: "(real \<times> real \<times> real) filter" 
  where "F \<equiv> (at_top \<times>\<^sub>F at_right 0 \<times>\<^sub>F at_right 0)"

lemma var_simps:
  "n_of = fst" "\<delta>_of = (\<lambda>x. fst (snd x))" "\<epsilon>_of = (\<lambda>x. snd (snd x))" 
  unfolding n_of_def \<delta>_of_def \<epsilon>_of_def by (auto simp add:case_prod_beta)

lemma evt_n: "eventually (\<lambda>x. n_of x \<ge> n) F"
  unfolding var_simps by (intro eventually_prod1' eventually_prod2' eventually_ge_at_top) 
      (simp add:prod_filter_eq_bot)

lemma evt_n_1: "\<forall>\<^sub>F x in F. 0 \<le> ln (n_of x)"
  by (intro eventually_mono[OF evt_n[of "1"]] ln_ge_zero) simp

lemma evt_n_2: "\<forall>\<^sub>F x in F. 0 \<le> ln (ln (n_of x))"
  using order_less_le_trans[OF exp_gt_zero]
  by (intro eventually_mono[OF evt_n[of "exp 1"]] ln_ge_zero iffD2[OF ln_ge_iff]) auto

lemma evt_\<delta>: "eventually (\<lambda>x. 1/\<delta>_of x \<ge> \<delta> \<and> \<delta>_of x > 0) F" 
  unfolding var_simps by (intro eventually_prod1' eventually_prod2' eventually_conj 
      real_inv_at_right_0_inf eventually_at_right_less) (simp_all add:prod_filter_eq_bot)

lemma evt_\<epsilon>: "eventually (\<lambda>x. 1/\<epsilon>_of x \<ge> \<epsilon> \<and> \<epsilon>_of x > 0) F" 
  unfolding var_simps by (intro eventually_prod1' eventually_prod2' eventually_conj 
      real_inv_at_right_0_inf eventually_at_right_less) (simp_all add:prod_filter_eq_bot)

lemma evt_\<epsilon>_1: "\<forall>\<^sub>F x in F. 0 \<le> ln (1 / \<epsilon>_of x)"
  by (intro eventually_mono[OF evt_\<epsilon>[of "1"]] ln_ge_zero) simp

theorem asymptotic_state_space_complexity:
  "state_space_usage \<in> O[at_top \<times>\<^sub>F at_right 0 \<times>\<^sub>F at_right 0](\<lambda>(n, \<delta>, \<epsilon>). ln (1/\<epsilon>)/\<delta>^2 + ln (ln n))"
  (is "_ \<in> O[?F](?rhs)")
proof -

  have 2:"(\<lambda>x. 1) \<in> O[?F](\<lambda>x. ln (1 / \<epsilon>_of x))"
    using order_less_le_trans[OF exp_gt_zero]
    by (intro landau_o.big_mono eventually_mono[OF evt_\<epsilon>[of "exp 1"]])
      (auto intro!: iffD2[OF ln_ge_iff] simp add:abs_ge_iff)

  have 3:"(\<lambda>x. 1) \<in> O[?F](\<lambda>x. ln (n_of x))"
    using order_less_le_trans[OF exp_gt_zero] 
    by (intro landau_o.big_mono eventually_mono[OF evt_n[of "exp 1"]]) 
      (auto intro!:iffD2[OF ln_ge_iff] simp add:abs_ge_iff)

  have "(\<lambda>x. ((ln (1/\<epsilon>_of x)+1)* (1/\<delta>_of x)\<^sup>2))\<in> O[?F](\<lambda>x. ln(1/\<epsilon>_of x)* (1/\<delta>_of x)\<^sup>2)"
    by (intro landau_o.mult sum_in_bigo 2) simp_all
  hence 0: "(\<lambda>x. 2^40*((ln (1/\<epsilon>_of x)+1)* (1/\<delta>_of x)\<^sup>2))\<in> O[?F](\<lambda>x. ln(1/\<epsilon>_of x)* (1/\<delta>_of x)\<^sup>2)"
    unfolding cmult_in_bigo_iff by simp

  have 4: "(1::real) \<le> exp 2"
    by (approximation 5)

  have "(\<lambda>x. ln (n_of x) / ln 2 + 3) \<in> O[?F](\<lambda>x. ln (n_of x))"
    using 3 by (intro sum_in_bigo) simp_all
  hence "(\<lambda>x. ln (ln (n_of x) / ln 2 + 3)) \<in> O[?F](\<lambda>x. ln (ln (n_of x)))"
    using order_less_le_trans[OF exp_gt_zero] order_trans[OF 4]
    by (intro landau_ln_2[where a="2"] eventually_mono[OF evt_n[of "exp 2"]])
     (auto intro!:iffD2[OF ln_ge_iff] add_nonneg_nonneg divide_nonneg_pos) 
  hence 1: "(\<lambda>x. log 2 (log 2 (n_of x) + 3))\<in> O[?F](\<lambda>x. ln(ln(n_of x)))"
    unfolding log_def by simp

  have 5: "\<forall>\<^sub>F x in ?F. 0 \<le> ln (1 / \<epsilon>_of x) * (1 / \<delta>_of x)\<^sup>2"
    by (intro eventually_mono[OF eventually_conj[OF evt_\<epsilon>_1 evt_\<delta>[of "1"]]]) auto

  have "state_space_usage = (\<lambda>x. state_space_usage (n_of x, \<delta>_of x, \<epsilon>_of x))"
    by (simp add:case_prod_beta' n_of_def \<epsilon>_of_def \<delta>_of_def)
  also have "... = (\<lambda>x. 2 ^ 40 * ((ln (1 / (\<epsilon>_of x)) + 1)* (1/\<delta>_of x)\<^sup>2) + log 2 (log 2 (n_of x)+3))"
    unfolding state_space_usage_def by (simp add:divide_simps)
  also have "... \<in> O[?F](\<lambda>x. ln (1/\<epsilon>_of x)* (1/\<delta>_of x)\<^sup>2 + ln (ln (n_of x)))"
    by (intro landau_sum 0 1 5 evt_n_2) 
  also have "... = O[?F](?rhs)"
    by (simp add:case_prod_beta' n_of_def \<epsilon>_of_def \<delta>_of_def divide_simps)
  finally show ?thesis by simp
qed

theorem asymptotic_seed_space_complexity:
  "seed_space_usage \<in> O[at_top \<times>\<^sub>F at_right 0 \<times>\<^sub>F at_right 0](\<lambda>(n, \<delta>, \<epsilon>). ln (1/\<epsilon>)+ln (1/\<delta>)^2 + ln n)"
  (is "_ \<in> O[?F](?rhs)")
proof -
  have 7: "\<forall>\<^sub>F x in ?F. 0 \<le> (ln (1 / \<delta>_of x))\<^sup>2"
    by simp

  have 5: "\<forall>\<^sub>F x in ?F. 0 \<le> ln (1 / \<epsilon>_of x) + (ln (1 / \<delta>_of x))\<^sup>2"
    by (intro eventually_mono[OF eventually_conj[OF evt_\<epsilon>_1 7]] add_nonneg_nonneg) auto

  have 9: "(\<lambda>x. 1) \<in> O[?F](\<lambda>x. ln (1 / \<delta>_of x))"
    using order_less_le_trans[OF exp_gt_zero]
    by (intro landau_o.big_mono eventually_mono[OF evt_\<delta>[of "exp 1"]])
      (auto intro!:iffD2[OF ln_ge_iff] simp add:abs_ge_iff)

  have "(\<lambda>x. 1) \<in> O[at_top \<times>\<^sub>F at_right 0 \<times>\<^sub>F at_right 0](\<lambda>x. ln (n_of x))"
    using order_less_le_trans[OF exp_gt_zero]
    by (intro landau_o.big_mono eventually_mono[OF evt_n[of "exp 1"]])
      (auto intro!:iffD2[OF ln_ge_iff] simp add:abs_ge_iff)
  hence 0: "(\<lambda>x. 1) \<in> O[?F](\<lambda>x. ln (1 / \<epsilon>_of x) + (ln (1 / \<delta>_of x))\<^sup>2 + ln (n_of x))"
    by (intro landau_sum_2 5 evt_n_1 7 evt_\<epsilon>_1) simp
  have 1: "(\<lambda>x. ln (n_of x)) \<in> O[?F](\<lambda>x. ln (1 / \<epsilon>_of x) + (ln (1 / \<delta>_of x))\<^sup>2 + ln (n_of x))"
    by (intro landau_sum_2 5 evt_n_1) simp
  have "(\<lambda>x. log 2 (1 / \<delta>_of x) + 16) \<in> O[?F](\<lambda>x. ln (1 / \<delta>_of x))"
    using 9 unfolding log_def by (intro sum_in_bigo) simp_all
  hence 4: "(\<lambda>x. (log 2 (1 / \<delta>_of x) + 16)\<^sup>2) \<in> O[?F](\<lambda>x. ln (1/\<epsilon>_of x)+(ln (1/\<delta>_of x))\<^sup>2)"
    using 7 unfolding power2_eq_square by (intro landau_sum_2 landau_o.mult evt_\<epsilon>_1) simp_all
  have 2: "(\<lambda>x. (log 2 (1 / \<delta>_of x) + 16)\<^sup>2) \<in> O[?F](\<lambda>x. ln (1/\<epsilon>_of x)+(ln (1/\<delta>_of x))\<^sup>2+ln (n_of x))"
    by (intro landau_sum_1[OF _ _ 4] 5 evt_n_1)
  have 3: "(\<lambda>x. ln (1/\<epsilon>_of x)) \<in> O[?F](\<lambda>x. ln (1/\<epsilon>_of x)+(ln (1/\<delta>_of x))\<^sup>2+ln (n_of x))"
    by (intro landau_sum_1 5 evt_\<epsilon>_1 7 evt_n_1) simp

  have "seed_space_usage = (\<lambda>x. seed_space_usage (n_of x, \<delta>_of x, \<epsilon>_of x))"
    by (simp add:case_prod_beta' n_of_def \<epsilon>_of_def \<delta>_of_def)
  also have "... = (\<lambda>x. 2^30+2^23*ln (n_of x)+48*(log 2 (1/(\<delta>_of x))+16)\<^sup>2 + 336 * ln (1 / \<epsilon>_of x))"
    unfolding seed_space_usage_def by (simp add:divide_simps)
  also have "... \<in> O[?F](\<lambda>x. ln (1/\<epsilon>_of x)+ln (1/\<delta>_of x)^2 + ln (n_of x))"
    using 0 1 2 3 by (intro sum_in_bigo) simp_all
  also have "... = O[?F](?rhs)"
    by (simp add:case_prod_beta' n_of_def \<epsilon>_of_def \<delta>_of_def)
  finally show ?thesis by simp
qed

definition "space_usage x = state_space_usage x + seed_space_usage x"

theorem asymptotic_space_complexity:
  "space_usage \<in> O[at_top \<times>\<^sub>F at_right 0 \<times>\<^sub>F at_right 0](\<lambda>(n, \<delta>, \<epsilon>). ln (1/\<epsilon>)/\<delta>^2 + ln n)"
  (is "_ \<in> O[?F](?rhs)")
proof -
  let ?f1 = "(\<lambda>x. ln (1/\<epsilon>_of x)*(1/\<delta>_of x^2)+ln (ln (n_of x)))"
  let ?f2 = "(\<lambda>x. ln(1/\<epsilon>_of x)+ln(1/\<delta>_of x)^2+ln (n_of x))"

  have 14: "\<forall>\<^sub>F x in ?F. 0 \<le> (1 / (\<delta>_of x)\<^sup>2)"
    unfolding var_simps by (intro eventually_prod1' eventually_prod2' eventually_inv)
      (simp_all add:prod_filter_eq_bot eventually_nonzero_simps)

  have 15: "\<forall>\<^sub>F x in ?F. 0 \<le> ln (1 / (\<delta>_of x)\<^sup>2)"
    unfolding power_one_over[symmetric]
    by (intro eventually_mono[OF evt_\<delta>[of "1"]] ln_ge_zero) simp

  have 10: "\<forall>\<^sub>F x in ?F. 0 \<le> ln (1 / \<epsilon>_of x) * (1 / (\<delta>_of x)\<^sup>2)"
    by (intro eventually_mono[OF eventually_conj[OF evt_\<epsilon>_1 14]] mult_nonneg_nonneg) auto

  have 0: "\<forall>\<^sub>F x in ?F. 0 \<le> ln (1 / \<epsilon>_of x) * (1 / (\<delta>_of x)\<^sup>2) + ln (ln (n_of x))"
    by (intro eventually_mono[OF eventually_conj[OF 10 evt_n_2]] add_nonneg_nonneg) auto

  have 1: "\<forall>\<^sub>F x in ?F. 0 \<le> ln (1 / \<epsilon>_of x) + (ln (1 / \<delta>_of x))\<^sup>2 + ln (n_of x)"
    by (intro eventually_mono[OF eventually_conj[OF evt_n_1 eventually_conj[OF evt_\<epsilon>_1 15]]] 
        add_nonneg_nonneg) auto

  have 11: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. 1 / (\<delta>_of x)\<^sup>2)"
    unfolding var_simps by (intro bigo_prod_1 bigo_prod_2 bigo_inv) 
      (simp_all add:power_divide prod_filter_eq_bot)

  have 12: "(\<lambda>_. 1) \<in> O[?F](\<lambda>x. ln (1 / \<epsilon>_of x))"
    unfolding var_simps by (intro bigo_prod_1 bigo_prod_2 bigo_inv) (simp_all add:prod_filter_eq_bot)

  have 2: "state_space_usage \<in> O[?F](\<lambda>x. ln (1 / \<epsilon>_of x) * (1 / (\<delta>_of x)\<^sup>2) + ln (ln (n_of x)))"
    using asymptotic_state_space_complexity unfolding \<epsilon>_of_def \<delta>_of_def n_of_def
    by (simp add:case_prod_beta')

  have 3: "seed_space_usage \<in> O[?F](\<lambda>x. ln (1 / \<epsilon>_of x) + (ln (1 / \<delta>_of x))\<^sup>2 + ln (n_of x))"
    using asymptotic_seed_space_complexity unfolding \<epsilon>_of_def \<delta>_of_def n_of_def
    by (simp add:case_prod_beta')

  have 4: "(\<lambda>x. ln (n_of x)) \<in> O[?F](\<lambda>x. ln (1 / \<epsilon>_of x) * (1 / (\<delta>_of x)\<^sup>2) + ln (n_of x))"
    by (intro landau_sum_2 evt_n_1 10) simp

  have "(\<lambda>x. (ln (1 / \<delta>_of x))\<^sup>2) \<in> O[?F](\<lambda>x. 1 / (\<delta>_of x)\<^sup>2)"
    unfolding var_simps
    by (intro bigo_prod_1 bigo_prod_2 bigo_inv) (simp_all add:power_divide prod_filter_eq_bot)
  hence 5: "(\<lambda>x. (ln (1 / \<delta>_of x))\<^sup>2) \<in> O[?F](\<lambda>x. ln (1 / \<epsilon>_of x) * (1 / (\<delta>_of x)\<^sup>2) + ln (n_of x))"
    by (intro landau_sum_1 evt_n_1 10 landau_o.big_mult_1' 12) 
  have 6: "(\<lambda>x. ln (1 / \<epsilon>_of x)) \<in> O[?F](\<lambda>x. ln (1 / \<epsilon>_of x) * (1 / (\<delta>_of x)\<^sup>2) + ln (n_of x))"
    by (intro landau_sum_1 evt_n_1 10 landau_o.big_mult_1 11) simp
  have 7: "(\<lambda>x. ln (1/\<epsilon>_of x) * (1/(\<delta>_of x)\<^sup>2)) \<in> O[?F](\<lambda>x. ln (1/\<epsilon>_of x)*(1/(\<delta>_of x)\<^sup>2)+ln (n_of x))"
    by (intro landau_sum_1 10 evt_n_1) simp

  have "(\<lambda>x. ln (ln (n_of x))) \<in> O[?F](\<lambda>x. ln (n_of x))"
    unfolding var_simps by (intro bigo_prod_1 bigo_prod_2) (simp_all add:prod_filter_eq_bot)
  hence 8: "(\<lambda>x. ln (ln (n_of x))) \<in> O[?F](\<lambda>x. ln (1 / \<epsilon>_of x) * (1 / (\<delta>_of x)\<^sup>2) + ln (n_of x))"
    by (intro landau_sum_2 evt_n_1 10)

  have "space_usage = (\<lambda>x. state_space_usage x + seed_space_usage x)"
    unfolding space_usage_def by simp
  also have "... \<in> O[?F](\<lambda>x. ?f1 x + ?f2 x)"
    by (intro landau_sum 0 1 2 3) 
  also have "... \<subseteq> O[?F](\<lambda>x. ln (1 / \<epsilon>_of x) * (1/\<delta>_of x^2) + ln (n_of x))"
    by (intro landau_o.big.subsetI sum_in_bigo 4 5 6 7 8)
  also have "... = O[?F](?rhs)"
    unfolding \<epsilon>_of_def \<delta>_of_def n_of_def
    by (simp add:case_prod_beta')

  finally show ?thesis by simp
qed

end

unbundle no_intro_cong_syntax

end