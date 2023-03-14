theory Distributed_Distinct_Elements_Outer_Algorithm
  imports DDE_Accuracy_With_Cutoff
begin

unbundle intro_cong_syntax

locale outer_algorithm =
  fixes n :: nat
  fixes \<epsilon> :: real
  fixes \<delta> :: real
  assumes n_gt_0: "n > 0" 
  assumes \<epsilon>_gt_0: "\<epsilon> > 0" and \<epsilon>_lt_1: "\<epsilon> < 1"
  assumes \<delta>_gt_0: "\<delta> > 0" and \<delta>_lt_1: "\<delta> < 1"
begin

definition stage_two where "stage_two = (\<epsilon> < (1/ln n) \<and> real n \<ge> exp(exp 5))"
definition \<epsilon>\<^sub>i :: real where "\<epsilon>\<^sub>i = (if stage_two then (1/ln n) else \<epsilon>)"
definition l :: nat where "l = (if stage_two then nat \<lceil>4 * ln (1/ \<epsilon>)/ln (ln n)\<rceil> else 1)"
definition \<Lambda> where "\<Lambda> = (if stage_two then (1/ln n) else 1)"

lemma l_lbound:
  assumes "stage_two"
  shows "l \<ge> 4 * ln (1/ \<epsilon>)/ln(ln n)"
proof -
  have "l = real (nat \<lceil>4 * ln (1 / \<epsilon>) / ln (ln (real n))\<rceil>)"
    using assms unfolding l_def by simp
  also have "... \<ge> 4 * ln (1 / \<epsilon>) / ln (ln (real n))"
    by linarith
  finally show ?thesis by simp
qed

lemma n_lbound:
  assumes "stage_two"
  shows "n \<ge> exp (exp 5)" "ln n \<ge> exp 5" "5 \<le> ln (ln (real n))" "ln n > 1" "real n > 1"
proof -
  show 0:"n \<ge> exp (exp 5)"
    using assms unfolding stage_two_def by simp
  thus 1:"ln n \<ge> exp 5"
    using n_gt_0
    by (intro iffD2[OF ln_ge_iff]) auto
  moreover have "1 < exp (5::real)"
    by (approximation 5)
  ultimately show 2:"ln n > 1"
    by argo
  show "5 \<le> ln (ln (real n))"
    using 1 2 by (subst ln_ge_iff) simp
  have "(1::real) < exp (exp 5)"
    by (approximation 5)
  thus "real n > 1"
    using 0 by argo
qed

lemma \<epsilon>1_gt_0: "0 < \<epsilon>\<^sub>i"
  using n_lbound(4) \<epsilon>_gt_0 unfolding \<epsilon>\<^sub>i_def
  by (cases "stage_two") simp_all

lemma \<epsilon>1_lt_1: "\<epsilon>\<^sub>i < 1"
  using n_lbound(4) \<epsilon>_lt_1 unfolding \<epsilon>\<^sub>i_def
  by (cases "stage_two") simp_all

lemma l_gt_0: "l > 0"
proof (cases "stage_two")
  case True
  have "0 < ln (1 / \<epsilon>)"
    using \<epsilon>_gt_0 \<epsilon>_lt_1
    by (intro ln_gt_zero) auto
  hence "0 < 4 * ln (1/ \<epsilon>)/ln(ln n)"
    using n_lbound[OF True] by (intro divide_pos_pos) auto
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

sublocale I: inner_algorithm "n" "\<epsilon>\<^sub>i" "\<delta>"
  unfolding inner_algorithm_def using n_gt_0 \<delta>_gt_0 \<delta>_lt_1 \<epsilon>1_gt_0 \<epsilon>1_lt_1 by auto

abbreviation \<Theta> where "\<Theta> \<equiv> \<E> l \<Lambda> I.\<Omega>"

sublocale \<Theta>: expander_sample_space l \<Lambda> I.\<Omega>
  unfolding expander_sample_space_def using I.\<Omega>.sample_space \<Lambda>_gt_0 l_gt_0 by auto

type_synonym state = "inner_algorithm.f0_state list"

fun single :: "nat \<Rightarrow> nat \<Rightarrow> state" where
  "single \<theta> x = map (\<lambda>j. I.single (select \<Theta> \<theta> j) x) [0..<l]"

fun merge :: "state \<Rightarrow> state \<Rightarrow> state" where
  "merge x y = map (\<lambda>(x,y). I.merge x y) (zip x y)"

fun estimate :: "state \<Rightarrow> real" where
  "estimate x = median l (\<lambda>i. I.estimate (x ! i))"

definition \<tau> :: "nat \<Rightarrow> nat set \<Rightarrow> state" 
  where "\<tau> \<theta> A = map (\<lambda>i. I.\<tau> (select \<Theta> \<theta> i) A) [0..<l]"

lemma merge_result: "merge (\<tau> \<omega> A) (\<tau> \<omega> B) = \<tau> \<omega> (A \<union> B)" (is "?L = ?R")
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

lemma single_result: "single \<omega> x = \<tau> \<omega> {x}" (is "?L = ?R")
proof -
  have "?L = map (\<lambda>j. I.single (select \<Theta> \<omega> j) x) [0..<l]"
    by (simp del:I.single.simps)
  also have "... = ?R"
    unfolding \<tau>_def by (intro map_cong I.single_result \<Theta>.range) auto
  finally show ?thesis by simp
qed

lemma estimate_result:
  assumes "A \<subseteq> {..<n}" "A \<noteq> {}"
  defines "p \<equiv> (pmf_of_set {..<size \<Theta>})"
  shows "measure p {\<omega>. \<bar>estimate (\<tau> \<omega> A)- real (card A)\<bar> > \<delta> * real (card A)} \<le> \<epsilon>" (is "?L \<le> ?R")
proof (cases "stage_two")
  case True
  define I where "I = {x. \<bar>x - real (card A)\<bar> \<le> \<delta> * real (card A)}"
  have int_I: "interval I" 
    unfolding interval_def I_def by auto

  define \<mu> where "\<mu> = measure I.\<Omega> {\<omega>. I.estimate (I.\<tau> \<omega> A) \<notin> I}"

  have 2: "5 \<le> ln (ln (real n))"
    using n_lbound[OF True] by (subst ln_ge_iff) simp

  have 3:"\<mu> + \<Lambda> > 0" 
    unfolding \<mu>_def
    by (intro add_nonneg_pos \<Lambda>_gt_0) auto

  have "\<mu> \<le> \<epsilon>\<^sub>i"
    unfolding \<mu>_def I_def using I.theorem_6_2[OF assms(1,2)] 
    by (simp add: not_le del:I.estimate.simps I.\<tau>.simps)
  also have "... = 1/ln n"
    using True unfolding \<epsilon>\<^sub>i_def by simp
  finally have "\<mu> \<le> 1/ln n" by simp
  hence "\<mu> + \<Lambda> \<le> 1/ln n + 1/ln n"
    unfolding \<Lambda>_def using True by (intro add_mono) auto
  also have "... = 2/ln n"
    by simp
  finally have 5:"\<mu> + \<Lambda> \<le> 2 / ln n"
    by simp
  hence 0:"ln (real n) \<le> 2 / (\<mu> + \<Lambda>)"
    using 3 n_lbound[OF True] by (simp add:field_simps)

  have 4: "2 * ln 2 + 8 * exp (- 1) \<le> (5::real)"
    by (approximation 5)

  have "\<mu> + \<Lambda> \<le> 2/ln n"
    by (intro 5)
  also have "... \<le> 2/exp 5"
    using n_lbound[OF True] by (intro divide_left_mono) simp_all
  also have "... \<le> 1/2"
    by (approximation 5)
  finally have 1:"\<mu> + \<Lambda> \<le> 1/2" by simp

  have "?L = measure p {\<omega>. median l (\<lambda>i. I.estimate (\<tau> \<omega> A  ! i)) \<notin> I}"
    unfolding I_def by (simp add:not_le)
  also have "... \<le> 
    measure p {\<theta>. real (card {i \<in> {..<l}. I.estimate (I.\<tau> (select \<Theta> \<theta> i) A) \<notin> I})\<ge> real l/2}"
  proof (rule pmf_mono')
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
  also have "... \<le> exp (-real l* ((1/2) * ln (ln n / 2) - 2*exp (-1)))"
    using 0 1 3 n_lbound[OF True]
    by (intro iffD2[OF exp_le_cancel_iff] mult_right_mono mult_left_mono_neg[where c="-real l"]
        diff_mono mult_left_mono iffD2[OF ln_le_cancel_iff]) (simp_all)
  also have "... = exp (-real l * (ln (ln n) / 2 - (ln 2/2 + 2*exp (-1))))"
    using n_lbound[OF True] by (subst ln_div) (simp_all add:algebra_simps)
  also have "... \<le> exp (-real l * (ln (ln n) / 2 - (ln (ln (exp(exp 5))) / 4)))"
    using 4
    by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono_neg[where c="-real l"] diff_mono) simp_all 
  also have "... \<le> exp (-real l * (ln (ln n) / 2 - (ln (ln n) / 4)))"
    using 2
    by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono_neg[where c="-real l"] diff_mono) simp_all
  also have "... = exp (- real l * (ln (ln n)/ 4) )"
    by (simp add:algebra_simps)
  also have "... \<le> exp (- (4 * ln (1/ \<epsilon>)/ln(ln n)) * (ln (ln n)/4))"
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

end

unbundle no_intro_cong_syntax

end