theory Constructive_Chernoff_Bound
  imports Main "HOL-Probability.Probability_Measure" "Frequency_Moments.Product_PMF_Ext"
    DDE_Transcendental_Extras DDE_Preliminary "Weighted_Arithmetic_Geometric_Mean.Weighted_Arithmetic_Geometric_Mean"
begin

definition KL_div :: "real \<Rightarrow> real \<Rightarrow> real" 
  where "KL_div p q = p * ln (p/q) + (1-p) * ln ((1-p)/(1-q))"


(* 
  KL_div 1 d = ln(1/d) = d_avg^n


  (card { Y i } \<ge> \<gamma> * n) = (card { Y i } \<ge> \<lceil>\<gamma>*n\<rceil>) \<le> exp (-n D (\<lceil>\<gamma>*n\<rceil>/n) \<delta>_avg) \<le> exp (-n D \<gamma> \<delta>_avg) ?

  D (\<lceil>\<gamma>*n\<rceil>/n) \<delta>_avg \<ge> D \<gamma> \<delta>_avg

  D a b \<ge> D a' b    if a \<ge> a' \<ge> b ?

  a ln(a/b) + (1-a) ln ((1-a)/(1-b)) \<ge> a' ln(a'/b) + (1-a') ln((1-a')/(1-b))

  a ln a - a ln b + (1-a) ln (1-a) - (1-a) ln (1-b) \<ge> a' ln a' - a' ln b + (1-a') ln (1-a') - (1-a') ln (1-b) 

  a ln a - a' ln a' + (a'-a) ln b + (1-a) ln(1-a) - (1-a') ln(1-a') + (a-a') ln(1-b)  \<ge> 0


  D x b = x ln(x/b) + (1-x) ln((1-x)/(1-b))

  D' x b = ln(x/b) + x/(x/b)*(1/b) + - ln((1-x)/(1-b)) + (1-x) / ((1-x)/(1-b)) * (1/(1-b))
        = ln(x/b) + 1 - ln((1-x)/(1-b)) - 1
        = ln(x/b) - ln((1-x)/(1-b))

  x > b



*)




theorem impagliazzo_kabanets_pmf:
  fixes Y :: "nat \<Rightarrow> 'a \<Rightarrow> bool" 
  fixes p :: "'a pmf"
  assumes "n > 0"
  assumes "\<And>i. i \<in> {..<n} \<Longrightarrow> \<delta> i \<in> {0..1}"
  assumes "\<And>S. S \<subseteq> {..<n} \<Longrightarrow> measure p {\<omega>. (\<forall>i \<in> S. Y i \<omega>)} \<le> (\<Prod>i \<in> S. \<delta> i)"
  defines "\<delta>_avg \<equiv> (\<Sum>i\<in> {..<n}. \<delta> i)/n"
  assumes "\<gamma> \<in> {\<delta>_avg..1}"
  shows "measure p {\<omega>. real (card {i \<in> {..<n}. Y i \<omega>}) \<ge> \<gamma> * n} \<le> exp (-real n * KL_div \<gamma> \<delta>_avg)" 
    (is "?L \<le> ?R")
proof -
  let ?n = "real n"
  define q :: real where "q = (\<gamma>-\<delta>_avg)/(\<gamma>*(1-\<delta>_avg))"
  define f where "f \<omega> = real (card {i. i < n \<and> Y i \<omega>})" for \<omega>
  define g where "g \<omega> = card {i. i < n \<and> \<not>Y i \<omega>}" for \<omega>
  let ?E = "(\<lambda>\<omega>. f \<omega> \<ge> \<gamma> * n)"
  let ?\<Xi> = "prod_pmf {..<n} (\<lambda>_. bernoulli_pmf q)"

  have q_range:"q < 1" "q \<ge> 0" sorry

  have abs_pos_le_1I: "abs x \<le> 1" if "x \<ge> 0" "x \<le> 1" for x :: real
    using that by auto

  have "\<gamma> * ?n \<le> 1 * ?n" 
    using assms(5) by (intro mult_right_mono) auto
  hence 1:" \<gamma> * ?n \<le> ?n" by simp

  have \<delta>_avg_ge_0: "\<delta>_avg \<ge> 0"
    unfolding \<delta>_avg_def using assms(1,2)
    by (intro divide_nonneg_pos sum_nonneg) auto

  have f_ge_0: "f \<omega> \<ge> 0" for \<omega>
    unfolding f_def by simp

  have 2:"(1-q) powr (?n - \<gamma>*?n) \<le> (1-q)^ g \<omega>" if "?E \<omega>" for \<omega>
  proof -
    have "real (g \<omega>) = real (card ({i. i < n} - {i. i < n \<and> Y i \<omega>}))"
      unfolding g_def by (intro arg_cong[where f="\<lambda>x. real (card x)"]) auto
    also have "... = real (card {i. i < n} - card {i. i < n \<and> Y i \<omega>})"
      unfolding f_def by (subst card_Diff_subset, auto)
    also have "... = real (card {i. i < n}) - f \<omega>"
      unfolding f_def by (intro of_nat_diff card_mono) auto
    also have "... = n - f \<omega>" by simp
    also have "... \<le> real n - \<gamma> * real n"
      using that by (intro diff_mono) auto
    finally have "real (g \<omega>) \<le> real n - \<gamma> * real n" by simp
    hence "(1-q) powr (?n - \<gamma>*?n) \<le> (1-q) powr (real (g \<omega>))"
      using q_range by (intro powr_mono_rev) auto
    also have "... = (1-q)^g \<omega>"
      using q_range by (simp add:powr_realpow)
    finally show ?thesis by simp
  qed

  have 3: "(\<delta>_avg * q + (1-q)) / (1-q) powr (1-\<gamma>) \<le> exp (- KL_div \<gamma> \<delta>_avg)"
    sorry

  define r where "r = n - nat \<lceil>\<gamma>*n\<rceil>"

  have "((1-q) powr (1-\<gamma>)) powr n * ?L = (1-q) powr (?n-\<gamma>*?n) * ?L"
    by (subst powr_powr, simp add:algebra_simps)
  also have "... = (1-q) powr (?n-\<gamma>*?n) * (\<integral>\<omega>. indicator {\<omega>. ?E \<omega>} \<omega> \<partial>p)"
    unfolding f_def by simp
  also have "... = (\<integral>\<omega>. indicator {\<omega>. ?E \<omega>} \<omega> * (1-q) powr (?n-\<gamma>*?n) \<partial>p)"
    by simp
  also have "... \<le> (\<integral>\<omega>. indicator {\<omega>. ?E \<omega>} \<omega> * (1-q) ^ g \<omega> \<partial>p)"
    using q_range 1 2 f_ge_0 by (intro integral_mono_AE integrable_pmf_iff_bounded[where C="1"] 
        abs_pos_le_1I mult_le_one powr_le1 power_le_one AE_pmfI) (simp_all split:split_indicator) 
  also have "... = (\<integral>\<omega>. indicator {\<omega>. ?E \<omega>} \<omega> * (\<Prod>i \<in> {i. i < n \<and> \<not>Y i \<omega>}. (1-q)) \<partial>p)"
    unfolding g_def using q_range
    by (intro integral_cong_AE AE_pmfI, simp_all add:powr_realpow)
  also have "... = (\<integral>\<omega>. indicator {\<omega>. ?E \<omega>} \<omega> * measure ?\<Xi> ({j. j < n \<and> \<not>Y j \<omega>} \<rightarrow> {False}) \<partial>p)"
    using q_range by (subst prob_prod_pmf') (auto simp add:measure_pmf_single)
  also have "... = (\<integral>\<omega>. measure ?\<Xi> {\<xi>. ?E \<omega> \<and> (\<forall>i\<in>{j. j < n \<and> \<not>Y j \<omega>}. \<not>\<xi> i)} \<partial>p)"
    by (intro integral_cong_AE AE_pmfI, simp_all add:Pi_def split:split_indicator)
  also have "... = (\<integral>\<omega>. measure ?\<Xi> {\<xi>. ?E \<omega> \<and> (\<forall>i\<in>{..<n}. \<xi> i \<longrightarrow> Y i \<omega>)} \<partial>p)"
    by (intro integral_cong_AE AE_pmfI measure_eq_AE) auto
  also have "... = measure (pair_pmf p ?\<Xi>) {\<phi>.?E (fst \<phi>)\<and>(\<forall>i \<in> {..<n}. snd \<phi> i \<longrightarrow> Y i (fst \<phi>))}" 
    unfolding split_pair_pmf by simp
  also have "... \<le> measure (pair_pmf p ?\<Xi>) {\<phi>. (\<forall>i \<in> {j. j < n \<and> snd \<phi> j}. Y i (fst \<phi>))}"
    by (intro measure_pmf.pmf_mono[OF refl], auto)
  also have "... = (\<integral>\<xi>. measure p {\<omega>. \<forall>i\<in>{j. j< n \<and> \<xi> j}. Y i \<omega>} \<partial> ?\<Xi>)"
    unfolding split_pair_pmf_2 by simp
  also have "... \<le> (\<integral>a. (\<Prod>i \<in> {j. j < n \<and> a j}. \<delta> i) \<partial> ?\<Xi>)"
    using assms(2) by (intro integral_mono_AE AE_pmfI assms(3) subsetI  prod_le_1 prod_nonneg 
        integrable_pmf_iff_bounded[where C="1"] abs_pos_le_1I) auto
  also have "... = (\<integral>a. (\<Prod>i \<in> {..<n}. \<delta> i^ of_bool(a i)) \<partial> ?\<Xi>)"
    unfolding of_bool_def by (intro integral_cong_AE AE_pmfI) 
      (auto simp add:if_distrib prod.If_cases Int_def)
  also have "... = (\<Prod>i<n. (\<integral>a. (\<delta> i ^ of_bool a) \<partial>(bernoulli_pmf q)))"
    using assms(2) by (intro expectation_prod_Pi_pmf integrable_pmf_iff_bounded[where C="1"]) auto
  also have "... = (\<Prod>i<n. \<delta> i * q + (1-q))"
    using q_range by simp
  also have "... = (root (card {..<n}) (\<Prod>i<n. \<delta> i * q + (1-q))) ^ (card {..<n})"
    using assms(1,2) q_range by (intro real_root_pow_pos2[symmetric] prod_nonneg) auto
  also have "... \<le> ((\<Sum>i<n. \<delta> i * q + (1-q))/card{..<n})^(card {..<n})"
    using assms(1,2) q_range by (intro power_mono arithmetic_geometric_mean) 
      (auto intro: prod_nonneg)
  also have "... = ((\<Sum>i<n. \<delta> i * q)/n + (1-q))^n"
    using assms(1) by (simp add:sum.distrib divide_simps mult.commute)
  also have "... = (\<delta>_avg * q + (1-q))^n"
    unfolding \<delta>_avg_def by (simp add: sum_distrib_right[symmetric])
  also have "... \<le> (\<delta>_avg * q + (1-q)) powr n" 
    using \<delta>_avg_ge_0 q_range by (subst powr_realpow) (auto intro:add_nonneg_pos) 
  finally have "((1-q) powr (1-\<gamma>)) powr n * ?L \<le> (\<delta>_avg * q + (1-q)) powr n" by simp
  hence "?L \<le> (\<delta>_avg * q + (1-q)) powr n / ((1-q) powr (1-\<gamma>)) powr n"
    using q_range by (subst pos_le_divide_eq) (auto simp add:algebra_simps)
  also have "... = ((\<delta>_avg * q + (1-q)) / (1-q) powr (1-\<gamma>)) powr n"
    using q_range \<delta>_avg_ge_0 by (subst powr_divide) auto
  also have "... \<le>  exp (- KL_div \<gamma> \<delta>_avg) powr n"
    using assms(1) q_range \<delta>_avg_ge_0 by (intro powr_mono2 3) auto
  also have "... = ?R"
    unfolding exp_powr by (simp add:algebra_simps)
  finally show ?thesis by simp
qed



text \<open>The distribution of a random variable with a countable range is discrete probability space, 
i.e., induces a PMF. Using this it is possible to generalize the previous result to arbitrary
probability spaces.\<close>

lemma (in prob_space) establish_pmf:
  fixes f :: "'a \<Rightarrow> 'b"
  assumes rv: "random_variable discrete f"
  assumes "countable (f ` space M)"
  shows "distr M discrete f \<in> {M. prob_space M \<and> sets M = UNIV \<and> (AE x in M. measure M {x} \<noteq> 0)}"
proof -
  define N where "N = {x \<in> space M.\<not> prob (f -` {f x} \<inter> space M) \<noteq> 0}"
  define I where "I = {z \<in> (f ` space M). prob (f -` {z}  \<inter> space M) = 0}"

  have countable_I: " countable I" 
    unfolding I_def by (intro countable_subset[OF _ assms(2)]) auto

  have disj: "disjoint_family_on (\<lambda>y. f -` {y} \<inter> space M) I" 
    unfolding disjoint_family_on_def by auto

  have N_alt_def: "N = (\<Union>y \<in> I. f -` {y} \<inter> space M)"
    unfolding N_def I_def by (auto simp add:set_eq_iff)
  have "emeasure M N = \<integral>\<^sup>+ y. emeasure M (f -` {y} \<inter> space M) \<partial>count_space I"
    using rv countable_I unfolding N_alt_def 
    by (subst emeasure_UN_countable) (auto simp add:disjoint_family_on_def) 
  also have "... =  \<integral>\<^sup>+ y. 0 \<partial>count_space I"
    unfolding I_def using emeasure_eq_measure ennreal_0
    by (intro nn_integral_cong) auto 
  also have "... = 0" by simp
  finally have 0:"emeasure M N = 0" by simp

  have 1:"N \<in> events" 
    unfolding N_alt_def using rv
    by (intro  sets.countable_UN'' countable_I) simp

  have " AE x in M. prob (f -` {f x} \<inter> space M) \<noteq> 0"
    using 0 1 by (subst AE_iff_measurable[OF _ N_def[symmetric]])  
  hence " AE x in M. measure (distr M discrete f) {f x} \<noteq> 0"
    by (subst measure_distr[OF rv], auto)
  hence "AE x in distr M discrete f. measure (distr M discrete f) {x} \<noteq> 0"
    by (subst AE_distr_iff[OF rv], auto)
  thus ?thesis 
    using prob_space_distr rv by auto
qed


(*

lemma establish_pmf_1:
  assumes "sets M = UNIV" "space M = UNIV"
  assumes "\<And>S. (\<forall>x. x \<in> S \<longrightarrow> measure M {x} = 0) \<Longrightarrow> emeasure M S = 0"
  shows  "AE x in M. measure M {x} \<noteq> 0"
  using assms assms(3)[of "{x. measure M {x} = 0}"]
  by (subst AE_iff_measurable[where N="{x. measure M {x} = 0}"], auto)
*)
lemma singletons_image_eq:
  "(\<lambda>x. {x}) ` T \<subseteq> Pow T"
  by auto


theorem (in prob_space) impagliazzo_kabanets:
  fixes Y :: "nat \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "n > 0"
  assumes "\<And>i. i \<in> {..<n} \<Longrightarrow> random_variable discrete (Y i)"
  assumes "\<And>i. i \<in> {..<n} \<Longrightarrow> \<delta> i \<in> {0..1}"
  assumes "\<And>S. S \<subseteq> {..<n} \<Longrightarrow> \<P>(\<omega> in M. (\<forall>i \<in> S. Y i \<omega>)) \<le> (\<Prod>i \<in> S. \<delta> i)"
  defines "\<delta>_avg \<equiv> (\<Sum>i\<in> {..<n}. \<delta> i)/n"
  assumes "\<gamma> \<in> {\<delta>_avg..1}"
  shows "\<P>(\<omega> in M. real (card {i \<in> {..<n}. Y i \<omega>}) \<ge> \<gamma> * n) \<le> exp (-real n * KL_div \<gamma> \<delta>_avg)" 
    (is "?L \<le> ?R")
proof -
  define f where "f = (\<lambda>\<omega> i. if i < n then Y i \<omega> else False)"
  define g where "g = (\<lambda>\<omega> i. if i < n then \<omega> i else False)"
  define T where "T = {\<omega>. (\<forall>i. \<omega> i \<longrightarrow> i < n)}"

  have g_idem: "g \<circ> f = f" unfolding f_def g_def by (simp add:comp_def)

  have f_range: " f \<in> space M \<rightarrow> T" 
    unfolding T_def f_def by simp

  have "T = PiE_dflt {..<n} False (\<lambda>_. UNIV)"
    unfolding T_def PiE_dflt_def by auto
  hence "finite T" 
    using finite_PiE_dflt by auto
  hence countable_T: "countable T" 
    by (intro countable_finite)
  moreover have "f ` space M \<subseteq> T" 
    using f_range by auto
  ultimately have countable_f: "countable (f ` space M)"
    using countable_subset by auto

  have "f -` y \<inter> space M \<in> events" if t:"y \<in> (\<lambda>x. {x}) ` T" for y
  proof -
    obtain t where "y = {t}" and t_range: "t \<in> T" using t by auto
    hence "f -` y \<inter> space M = {\<omega> \<in> space M. f \<omega> = t}" 
      by (auto simp add:vimage_def)
    also have "... = {\<omega> \<in> space M. (\<forall>i < n. Y i \<omega> = t i)}"
      using t_range unfolding f_def T_def by auto
    also have "... = (\<Inter>i \<in> {..<n}. {\<omega> \<in> space M. Y i \<omega> = t i})"
      using assms(1) by auto
    also have "... \<in> events"
      using assms(1,2)
      by (intro sets.countable_INT) auto
    finally show ?thesis by simp
  qed

  hence "random_variable (count_space T) f"
    using sigma_sets_singletons[OF countable_T] singletons_image_eq f_range
    by (intro measurable_sigma_sets[where \<Omega>="T" and A=" (\<lambda>x. {x}) ` T"]) simp_all
  moreover have "g \<in> measurable discrete (count_space T)"
    unfolding g_def T_def by simp
  ultimately have "random_variable discrete (g \<circ> f)"
    by simp
  hence rv:"random_variable discrete f"
    unfolding g_idem by simp
  
  define M' :: "(nat \<Rightarrow> bool) measure"
    where "M' = distr M discrete f" 

  define \<Omega> where "\<Omega> = Abs_pmf M'"
  have a:"measure_pmf (Abs_pmf M') = M'"
    unfolding M'_def
    by (intro Abs_pmf_inverse[OF establish_pmf] rv countable_f)

  have b:"{i. (i < n \<longrightarrow> Y i x) \<and> i < n} = {i. i < n \<and> Y i x}" for x
    by auto

  have c: "measure \<Omega> {\<omega>. \<forall>i\<in>S. \<omega> i} \<le> prod \<delta> S" (is "?L1 \<le> ?R1") if "S \<subseteq> {..<n}" for S
  proof -
    have d: "i \<in> S \<Longrightarrow> i < n" for i 
      using that by auto
    have "?L1 = measure M' {\<omega>. \<forall>i\<in>S. \<omega> i}"
      unfolding \<Omega>_def a by simp
    also have "... = \<P>(\<omega> in M. (\<forall>i \<in> S. Y i \<omega>))"
      unfolding M'_def using that d
      by (subst measure_distr[OF rv]) (auto simp add:f_def Int_commute Int_def)
    also have "... \<le> ?R1"
      using that assms(4) by simp
    finally show ?thesis by simp
  qed

  have "?L = measure M' {\<omega>. real (card {i. i < n \<and> \<omega> i}) \<ge> \<gamma> * n}"
    unfolding M'_def by (subst measure_distr[OF rv]) 
      (auto simp add:f_def algebra_simps Int_commute Int_def b)
  also have "... = measure_pmf.prob \<Omega> {\<omega>. real (card {i \<in> {..<n}. \<omega> i}) \<ge> \<gamma> * n}"
    unfolding \<Omega>_def a by simp
  also have "... \<le> ?R"
    using assms(6) c unfolding \<delta>_avg_def
    by (intro impagliazzo_kabanets_pmf assms(1,3)) auto
  finally show ?thesis by simp
qed

end