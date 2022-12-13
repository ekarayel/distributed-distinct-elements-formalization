theory Balls_and_Bins
  imports DDE_Preliminary 
    "HOL-Combinatorics.Stirling"
    "HOL-Computational_Algebra.Polynomial"
    "Discrete_Summation.Factorials" 
    "Twelvefold_Way.Twelvefold_Way_Entry3"
    "Basel_Sum_Approx"
    "Lp.Lp"
begin

hide_const Discrete_Topology.discrete

locale balls_and_bins_indep =
  fixes R B
  assumes "finite R"
  assumes "finite B"
begin

definition "M = measure_pmf (prod_pmf R (\<lambda>_. pmf_of_set B))"

sublocale prob_space "M"
  unfolding M_def using prob_space_measure_pmf by auto

definition Y where "Y \<omega> = real (card (\<omega> ` R))"
definition r where "r = real (card R)"
definition b where "b = real (card B)"

lemma exp: "expectation Y = b * (1-(1-1/b) powr r)"
  sorry
lemma var: "variance Y \<le> r * (r-1) / b"
  sorry



end





lemma prod_real:
  assumes "finite S"
  shows "\<Prod> (real` S) = real (\<Prod>S)" 
  using assms
proof (induction S rule:finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  have "\<Prod>(real ` insert x F) = \<Prod>(insert (real x) (real ` F))"
    by simp
  also have "... = real x * \<Prod>(real ` F)"
    using insert by (intro prod.insert) auto
  also have "... = real (x * \<Prod> F)"
    using insert by auto
  also have "... = real (\<Prod>(insert x F))"
    using insert by (subst prod.insert) auto
  finally show ?case by simp
qed

lemma sum_power_distrib:
  fixes f :: "'a \<Rightarrow> real"
  assumes "finite R"
  shows "(\<Sum>i\<in>R. f i) ^ s = (\<Sum>xs | set xs \<subseteq> R \<and> length xs = s. (\<Prod>x \<leftarrow> xs. f x))"
proof (induction s)
  case 0
  have "{xs. xs = [] \<and> set xs \<subseteq> R} = {[]}" 
    by (auto simp add:set_eq_iff) 
  then show ?case by simp
next
  case (Suc s)
  have a: "(\<Union>i\<in>R. (#) i ` {xs. set xs \<subseteq> R \<and> length xs = s}) = {xs. set xs \<subseteq> R \<and> length xs = Suc s}"
    by (subst lists_length_Suc_eq)  auto
  have "sum f R ^ Suc s = (sum f R) * (sum f R)^s"
    by simp
  also have "... = (sum f R) * (\<Sum>xs | set xs \<subseteq> R \<and> length xs = s. (\<Prod>x \<leftarrow> xs. f x))"
    using Suc by simp
  also have "... = (\<Sum>i \<in> R. (\<Sum>xs | set xs \<subseteq> R \<and> length xs = s. (\<Prod>x \<leftarrow> i#xs. f x)))"
    by (subst sum_product) simp
  also have "... = (\<Sum>i \<in> R. (\<Sum>xs \<in> (\<lambda>xs. i#xs) ` {xs. set xs \<subseteq> R \<and> length xs = s}. (\<Prod>x \<leftarrow> xs. f x)))"
    by (subst sum.reindex) (auto)
  also have "... =  (\<Sum>xs\<in>(\<Union>i\<in>R. (#) i ` {xs. set xs \<subseteq> R \<and> length xs = s}). (\<Prod>x \<leftarrow> xs. f x))"
    by (intro sum.UNION_disjoint[symmetric] assms ballI finite_imageI finite_lists_length_eq)
    auto
  also have "... = (\<Sum>xs| set xs \<subseteq> R \<and> length xs = Suc s. (\<Prod>x \<leftarrow> xs. f x))"
    by (intro sum.cong a) auto
  finally show ?case by simp
qed

lemma card_lists_set_eq:
  fixes V :: "'a set"
  assumes "finite V"
  shows "card {xs. set xs = V \<and> length xs = s} = Stirling s (card V) * fact (card V)"
    (is "card ?L = ?R")
proof -
  define M where "M = {f \<in> {..<s} \<rightarrow>\<^sub>E V. f ` {..<s} = V}"
  define f :: "(nat \<Rightarrow> 'a) \<Rightarrow> ('a list)" 
    where "f = (\<lambda>g. map (\<lambda>i. g i) [0..<s])"

  have "map (restrict ((!) y) {..<length y}) [0..<length y] = y" for y :: "'a list" 
    by (metis atLeast_upt map_eq_conv map_nth restrict_apply')
  hence "bij_betw f M ?L"
    unfolding M_def f_def
    by (intro bij_betwI[where g="\<lambda>xs. \<lambda>i \<in> {..<s}. xs ! i"])
     (auto simp add:Pi_def PiE_def extensional_def in_set_conv_nth) 

  hence "card ?L = card M"
    by (simp add: bij_betw_same_card)
  also have "... = ?R"
    unfolding M_def using assms
    by (subst card_extensional_funcset_surj_on) auto
  finally show ?thesis by simp
qed

lemma card_lists_with_image_size:
  assumes "finite R"
  shows "card {xs. set xs \<subseteq> R \<and> length xs = s \<and> card(set xs) = i} = Stirling s i * ffact i (card R)"
    (is "card ?L = ?R")
proof -
  have a: "finite {xs. set xs = V \<and> length xs = s}" if "V \<subseteq> R" for V 
  proof -
    have b:"finite {xs. set xs \<subseteq> V \<and> length xs = s}"
      using that finite_subset assms(1)
      by (intro finite_lists_length_eq) auto
    show ?thesis 
      by (intro finite_subset[OF _ b]) auto
  qed

  have "card ?L = card (\<Union>V \<in> {V. V \<subseteq> R \<and> card V = i}. {xs. set xs = V \<and> length xs = s})"
    by (intro arg_cong[where f="card"])  auto
  also have "... = (\<Sum>V | V \<subseteq> R \<and> card V = i. card {xs. set xs = V \<and> length xs = s})"
    using assms a by (intro card_UN_disjoint) auto 
  also have "... = (\<Sum>V | V \<subseteq> R \<and> card V = i. Stirling s (card V) * fact (card V))"
    using assms finite_subset by (intro sum.cong card_lists_set_eq) auto 
  also have "... = (\<Sum>V | V \<subseteq> R \<and> card V = i. Stirling s i * fact i)"
    by (intro sum.cong) auto
  also have "... = (card R choose i) * Stirling s i * fact i"
    using n_subsets[OF assms] by simp
  also have "... = ?R"
    by (subst ffact_eq_fact_mult_binomial) simp
  finally show ?thesis by simp
qed

lemma prod_list_le_1_iff:
  fixes xs :: "real list"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> \<bar>x\<bar>\<le> 1"
  shows "\<bar>prod_list xs\<bar> \<le> 1"
  using assms 
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have "abs a \<le> 1" 
    using Cons(2) by simp
  moreover have "abs (prod_list xs) \<le> 1"
    using Cons(2) by (intro Cons(1)) simp
  ultimately show ?case 
    by (simp add: abs_mult mult_le_one)
qed

lemma ffact_le_pow:
  fixes i n :: nat
  shows "ffact i n \<le> n^i"
proof -
  have "ffact i n = (\<Prod>k = 0..<i. n - k)"
    using prod_ffact_nat[symmetric] by simp
  also have "... \<le> (\<Prod>k = 0..<i. n)"
    by (intro prod_mono) auto
  also have "... = n^i" by simp
  finally show ?thesis by simp
qed

text \<open>A discrete probability space representing throwing |R| balls into |B| bins (k-wise independently)\<close>

locale lim_balls_and_bins =
  fixes R :: "'a set"  and B :: "'b set"
  fixes k :: nat and p :: "('a \<Rightarrow> 'b) pmf"
  fixes Z
  assumes "finite R"
  assumes "finite B"
  assumes "prob_space.k_wise_indep_vars (measure_pmf p) k (\<lambda>_. discrete) (\<lambda>x \<omega>. \<omega> x) R"
  assumes "\<And>x. x \<in> R \<Longrightarrow> map_pmf (\<lambda>\<omega>. \<omega> x) p = pmf_of_set B"
  defines "Z j \<omega> \<equiv> real (card {i. i \<in> R \<and> \<omega> i = (j::'b)})"
begin

(* Random variable counting the number of times bin j was hit *)

lemma hit_count_prod_exp:
  assumes "j1 \<in> B" "j2 \<in> B" "s+t \<le> k"
  assumes "j1 \<noteq> j2 \<or> s = 0 \<or> t = 0"
  defines "L \<equiv> {(xs,ys). set xs \<subseteq> R \<and> set ys \<subseteq> R \<and> set xs \<inter> set ys = {} \<and> length xs = s \<and> length ys = t}"
  shows "(\<integral>\<omega>. Z j1 \<omega>^s * Z j2 \<omega>^t \<partial>p) = (\<Sum>(xs,ys) \<in> L. (1/real (card B))^(card (set xs) + card (set ys)))"
  sorry

lemma hit_count_prod_approx:
  assumes "j1 \<in> B" "j2 \<in> B" "s+t \<le> k"
  shows "\<bar>(\<integral>\<omega>. Z j1 \<omega>^s * Z j2 \<omega>^t \<partial>p) \<bar> \<le> 2^k * Bell k"
  sorry

lemma hit_count_moments:
  assumes "s \<le> k"
  assumes "j \<in> B"
  shows "(\<integral>\<omega>. Z j \<omega>^s \<partial> p) = (\<Sum>i=0..s. real (Stirling s i) * (1 / real (card B))^i * ffact i (card R))" 
    (is "?L = ?R") 
  sorry


end

lemma hit_count_prod_exp:
  fixes R :: "'a set"
  fixes B :: "'b set"
  fixes s t :: nat
  assumes "finite R" "finite B" "s + t \<le> k"
  assumes "prob_space.k_wise_indep_vars (measure_pmf p) k (\<lambda>_. discrete) (\<lambda>x \<omega>. \<omega> x) R"
  assumes "\<And>x. x \<in> R \<Longrightarrow> map_pmf (\<lambda>\<omega>. \<omega> x) p = pmf_of_set B"
  assumes "j1 \<in> B" "j2 \<in> B"
  assumes "j1 \<noteq> j2 \<or> s = 0 \<or> t = 0"
  defines "Z1 \<equiv> (\<lambda>\<omega>. real (card {i. i \<in> R \<and> \<omega> i = j1}))"
  defines "Z2 \<equiv> (\<lambda>\<omega>. real (card {i. i \<in> R \<and> \<omega> i = j2}))"
  defines "L \<equiv> {(xs,ys). set xs \<subseteq> R \<and> set ys \<subseteq> R \<and> set xs \<inter> set ys = {} \<and> length xs = s \<and> length ys = t}"
  shows "measure_pmf.expectation p (\<lambda>\<omega>. Z1 \<omega>^s * Z2 \<omega>^t) =
      (\<Sum>(xs,ys) \<in> L. (1/card B)^(card (set xs) + card (set ys)))" (is "?L = ?R")
proof -
  define W1 :: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> real" where "W1 = (\<lambda>i \<omega>. of_bool (\<omega> i = j1) :: real)"
  define W2 :: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> real" where "W2 = (\<lambda>i \<omega>. of_bool (\<omega> i = j2) :: real)"

  have Z1_eq: "Z1 \<omega> = (\<Sum>i \<in> R. W1 i \<omega>)" for \<omega>
    using assms(1) unfolding Z1_def W1_def
    by (simp add:of_bool_def sum.If_cases Int_def)

  have Z2_eq: "Z2 \<omega> = (\<Sum>i \<in> R. W2 i \<omega>)" for \<omega>
    using assms(1) unfolding Z2_def W2_def
    by (simp add:of_bool_def sum.If_cases Int_def)

  define \<alpha> where "\<alpha> = 1 / real (card B)"

  have a: "measure_pmf.expectation p (\<lambda>\<omega>. (\<Prod>x\<leftarrow>a. W1 x \<omega>) * (\<Prod>y\<leftarrow>b. W2 y \<omega>)) = 0" (is "?L1 = 0")
    if "x \<in> set a \<inter> set b" "length a = s" "length b = t" for x a b
  proof -
    have "length a > 0" "length b > 0"
      using that by auto
    hence "s \<noteq> 0 \<and> t \<noteq> 0"
      using that by simp
    hence j_dist: "j1 \<noteq> j2" using assms by simp
    have  "(\<Prod>x\<leftarrow>a. W1 x \<omega>) * (\<Prod>y\<leftarrow>b. W2 y \<omega>) = 0" for \<omega>
    proof -
      have "W1 x \<omega> = 0 \<or> W2 x \<omega> = 0" 
        unfolding W1_def W2_def using j_dist by simp
      hence "(\<Prod>x\<leftarrow>a. W1 x \<omega>) = 0 \<or> (\<Prod>y\<leftarrow>b. W2 y \<omega>) = 0"
        unfolding prod_list_zero_iff using that(1) by auto
      thus ?thesis by simp
    qed
    hence "?L1 = measure_pmf.expectation p (\<lambda>\<omega>. 0)"
      by (intro arg_cong2[where f="measure_pmf.expectation"]) auto
    also have "... = 0"
      by simp
    finally show ?thesis by simp
  qed

  have b: 
    "prob_space.indep_vars (measure_pmf p) (\<lambda>_. discrete) (\<lambda>i \<omega>. \<omega> i) (set (fst x) \<union> set (snd x))"
    if "x \<in> L" for x
  proof -
    have "card (set (fst x) \<union> set (snd x)) \<le> card (set (fst x)) + card (set (snd x))"
      by (intro card_Un_le)
    also have "... \<le> length (fst x) + length (snd x)"
      by (intro add_mono card_length)  
    also have "... = s + t"
      using that L_def by auto
    also have "... \<le> k" using assms(3) by simp
    finally have "card (set (fst x) \<union> set (snd x)) \<le> k" by simp 
    moreover have "set (fst x) \<union> set (snd x) \<subseteq> R" 
      using that L_def by auto
    ultimately show ?thesis
      by (intro prob_space.k_wise_indep_vars_subset[OF prob_space_measure_pmf assms(4)])
       auto
  qed

  have c: "measure_pmf.expectation p (\<lambda>\<omega>. of_bool (\<omega> x = z)) = \<alpha>" (is "?L1 = _")
    if "z \<in> B" "x \<in> R" for x z
  proof -
    have "?L1 = measure_pmf.expectation p (indicator {\<omega>. \<omega> x = z})"
      unfolding indicator_def by simp
    also have "... = measure_pmf.prob p {\<omega>. \<omega> x = z}"
      by simp
    also have "... = measure_pmf.prob (map_pmf (\<lambda>\<omega>. \<omega> x) p) {z}"
      by (subst measure_map_pmf) (simp add:vimage_def)
    also have "... = measure_pmf.prob (pmf_of_set B) {z}"
      using that by (subst assms(5)) auto
    also have "... = 1/card B"
      using assms(2) that by (subst measure_pmf_of_set) auto
    also have "... = \<alpha>"
      unfolding \<alpha>_def by simp
    finally show ?thesis by simp
  qed

  have d: "abs x \<le> 1 \<Longrightarrow> abs y \<le> 1 \<Longrightarrow> abs (x*y) \<le> 1" for x y :: real 
    by (simp add:abs_mult mult_le_one) 
  have e:"(\<And>x. x \<in> set xs \<Longrightarrow> abs x \<le>1) \<Longrightarrow> abs(prod_list xs) \<le> 1 " for xs :: "real list"
    using d by (induction xs, simp, simp)

  have "?L = measure_pmf.expectation p (\<lambda>\<omega>. (\<Sum>j \<in> R. W1 j \<omega>)^s * (\<Sum>j \<in> R. W2 j \<omega>)^t)"
    unfolding Z1_eq Z2_eq by simp
  also have "... = measure_pmf.expectation p (\<lambda>\<omega>.
    (\<Sum>xs | set xs \<subseteq> R \<and> length xs = s. (\<Prod>x \<leftarrow> xs. W1 x \<omega>)) *
    (\<Sum>ys | set ys \<subseteq> R \<and> length ys = t. (\<Prod>y \<leftarrow> ys. W2 y \<omega>)))"
    unfolding sum_power_distrib[OF assms(1)] by simp
  also have "... = measure_pmf.expectation p (\<lambda>\<omega>. 
    (\<Sum>l\<in>{xs. set xs \<subseteq> R \<and> length xs = s} \<times> {ys. set ys \<subseteq> R \<and> length ys = t}. 
      (\<Prod>x\<leftarrow>fst l. W1 x \<omega>) * (\<Prod>y\<leftarrow>snd l. W2 y \<omega>)))"
    by (intro arg_cong[where f="measure_pmf.expectation p"]) 
      (simp add: sum_product sum.cartesian_product case_prod_beta) 
  also have "... = (\<Sum>l\<in>{xs. set xs \<subseteq> R \<and> length xs = s} \<times> {ys. set ys \<subseteq> R \<and> length ys = t}.
    measure_pmf.expectation p (\<lambda>\<omega>. (\<Prod>x\<leftarrow>fst l. W1 x \<omega>) * (\<Prod>y\<leftarrow>snd l. W2 y \<omega>)))"
    unfolding W1_def W2_def
    by (intro Bochner_Integration.integral_sum integrable_pmf_iff_bounded[where C="1"] d e) auto 
  also have "... = (\<Sum>l\<in> L. measure_pmf.expectation p 
    (\<lambda>\<omega>. (\<Prod>x\<leftarrow>fst l. W1 x \<omega>) * (\<Prod>y\<leftarrow>snd l. W2 y \<omega>)))"
    unfolding L_def using a by (intro sum.mono_neutral_right finite_cartesian_product 
        finite_lists_length_eq assms(1)) auto 
  also have "... = (\<Sum>l\<in> L. measure_pmf.expectation p (\<lambda>\<omega>. 
    (\<Prod>x \<in> set (fst l). W1 x \<omega>^count_list (fst l) x) * 
    (\<Prod>y \<in> set (snd l). W2 y \<omega>^count_list (snd l) y)))"
    unfolding prod_list_eval by simp
  also have "... = (\<Sum>l\<in> L. measure_pmf.expectation p (\<lambda>\<omega>. 
    (\<Prod>x \<in> set (fst l). of_bool(\<omega> x = j1)) * (\<Prod>y \<in> set (snd l). of_bool(\<omega> y = j2))))"
    unfolding W1_def W2_def using count_list_gr_1 by (intro sum.cong prod.cong 
        arg_cong[where f="measure_pmf.expectation p"] ext arg_cong2[where f="(*)"]) force+
  also have "... = (\<Sum>l\<in> L. measure_pmf.expectation p (\<lambda>\<omega>. 
    (\<Prod>x \<in> set (fst l). of_bool(\<omega> x = (if x \<in> set (fst l) then j1 else j2))) * 
    (\<Prod>y \<in> set (snd l). of_bool(\<omega> y = (if y \<in> set (fst l) then j1 else j2)))))"
    unfolding L_def by (intro sum.cong arg_cong[where f="measure_pmf.expectation p"] ext 
        arg_cong2[where f="(*)"] prod.cong) auto
  also have "... = (\<Sum>l \<in> L. measure_pmf.expectation p (\<lambda>\<omega>. 
    (\<Prod>x \<in> (set (fst l) \<union> set (snd l)). of_bool(\<omega> x = (if x \<in> set (fst l) then j1 else j2)))))"
    unfolding L_def by (intro sum.cong arg_cong[where f="measure_pmf.expectation p"] ext 
        prod.union_disjoint[symmetric]) auto
  also have "... = (\<Sum>l \<in> L. (\<Prod>x \<in> (set (fst l) \<union> set (snd l)). 
    measure_pmf.expectation p (\<lambda>\<omega>. of_bool(\<omega> x = (if x \<in> set (fst l) then j1 else j2)))))"
    by (intro sum.cong prob_space.indep_vars_lebesgue_integral[OF prob_space_measure_pmf] 
        integrable_pmf_iff_bounded[where C="1"] 
        prob_space.indep_vars_compose2[OF prob_space_measure_pmf b])  auto
  also have "... = (\<Sum>l \<in> L. (\<Prod>x \<in> (set (fst l) \<union> set (snd l)). \<alpha>))"
    using assms(6,7) unfolding L_def by (intro sum.cong prod.cong c) auto 
  also have "... = (\<Sum>l \<in> L. \<alpha>^(card (set (fst l) \<union> set (snd l))))"
    by simp
  also have "... = (\<Sum>l \<in> L. \<alpha>^(card (set (fst l)) + card (set (snd l))))"
    unfolding L_def by (intro sum.cong arg_cong[where f="\<lambda>x. \<alpha>^x"] card_Un_disjnt) 
     (auto simp add:disjnt_def)
  also have "... = ?R" 
    unfolding L_def \<alpha>_def by (simp add:case_prod_beta)
  finally show ?thesis by simp
qed


lemma hit_count_moments:
  assumes "finite R" "finite B" "s \<le> k"
  assumes "prob_space.k_wise_indep_vars (measure_pmf p) k (\<lambda>_. discrete) (\<lambda>x \<omega>. \<omega> x) R"
  assumes "\<And>x. x \<in> R \<Longrightarrow> map_pmf (\<lambda>\<omega>. \<omega> x) p = pmf_of_set B"
  assumes "j \<in> B"
  defines "Z \<equiv> (\<lambda>\<omega>. real (card {i. i \<in> R \<and> \<omega> i = j}))"
  shows "(\<integral>\<omega>. Z \<omega>^s \<partial> p) = (\<Sum>i=0..s. real (Stirling s i) * (1 / real (card B))^i * ffact i (card R))" 
    (is "?L = ?R") 
proof -
  define \<alpha> where "\<alpha> = 1 / real (card B)"

  have b:"finite {xs. set xs \<subseteq> R \<and> length xs = s \<and> card (set xs) = i}" for i
    by (intro finite_subset[OF _ finite_lists_length_eq[OF assms(1), where n="s"]]) auto  

  have "?L = (\<integral>\<omega>. real (card {i \<in> R. \<omega> i = j}) ^ s * real (card {i \<in> R. \<omega> i = j}) ^ 0 \<partial> p)"
    unfolding Z_def by simp
  also have "... = (\<Sum>(xs, ys)\<in>{(xs, ys). set xs \<subseteq> R \<and> set ys \<subseteq> R \<and> set xs \<inter> set ys = {} \<and> 
    length xs = s \<and> length ys = 0}. (1 / real (card B)) ^ (card (set xs) + card (set ys)))"
    using assms by (intro hit_count_prod_exp[OF assms(1,2) _ assms(4,5)]) auto
  also have "... = 
    (\<Sum>x\<in>{(xs, ys). set xs \<subseteq> R \<and> length xs = s \<and> ys = ([] :: 'a list)}. \<alpha> ^ (card (set (fst x))))"
    by (intro sum.cong) (auto simp add:\<alpha>_def)
  also have "... = 
    (\<Sum>x\<in>fst ` {(xs, ys). set xs \<subseteq> R \<and> length xs = s \<and> ys = ([] :: 'a list)}. \<alpha> ^ (card (set x)))"
    by (subst sum.reindex) (auto simp add:inj_on_def)
  also have "... = (\<Sum>xs| set xs \<subseteq> R \<and> length xs = s. \<alpha> ^ (card (set xs)))"
    by (intro sum.cong)  (auto simp add:image_iff)
  also have "... = 
    (\<Sum>xs \<in> (\<Union>i \<in> {0..s}.{xs. set xs \<subseteq> R \<and> length xs = s \<and> card (set xs) = i}). \<alpha>^ card (set xs))"
    using card_length by (intro sum.cong) auto
  also have "... = 
    (\<Sum>i=0..s. (\<Sum>xs | set xs \<subseteq> R \<and> length xs = s \<and> card(set xs) = i. \<alpha>^ card (set xs)))"
    using b by (subst sum.UNION_disjoint[symmetric]) auto 
  also have "... = (\<Sum>i=0..s. (\<Sum>xs | set xs \<subseteq> R \<and> length xs = s \<and> card(set xs) = i. \<alpha>^i))"
    by auto
  also have "... = (\<Sum>i=0..s. \<alpha>^i * card {xs. set xs \<subseteq> R \<and> length xs = s \<and> card(set xs) = i})"
    by (intro sum.cong) auto
  also have "... = ?R"
    unfolding \<alpha>_def
    by (subst card_lists_with_image_size[OF assms(1)]) (simp add:algebra_simps)
  finally show "?L = ?R" by simp
qed

lemma hit_count_approx:
  assumes "card B > 0" "card R \<le> card B" "s > 0"
  shows "(\<Sum>i=0..s. real (Stirling s i) * (1 / card B)^i * ffact i (card R)) \<le> 
    Bell s * real (card R) / real (card B)" (is "?L \<le> ?R")
proof -
  have "?L \<le> (\<Sum>i = 0..s. real (Stirling s i) * (1 / real (card B)) ^ i * real (card R^i))" 
    by (intro sum_mono mult_left_mono ffact_le_pow of_nat_mono) simp
  also have "... = (\<Sum>i\<le>s. real (Stirling s i) * (1 / real (card B)) ^ i * real (card R^i))"
    by (intro sum.cong) auto
  also have "... = (\<Sum>i\<le>s. real (Stirling s i) * (real (card R) / real (card B)) ^ i)" 
    by (simp add:algebra_simps power_divide)
  also have "... \<le> (\<Sum>i\<le>s. real (Stirling s i) * (real (card R) / real (card B)) ^ 1)"
  proof (rule sum_mono)
    fix i assume "i \<in> {..s}"
    show "real (Stirling s i) * (real (card R) / real (card B)) ^ i \<le> 
      real (Stirling s i) * (real (card R) / real (card B)) ^ 1"
    proof (cases "i")
      case 0
      then show ?thesis 
        using assms
        by (cases s) simp+
    next
      case (Suc nat)
      moreover have "real (card R) \<le> real (card B)" using assms by simp
      moreover have "real (card B) > 0" using assms by simp 
      ultimately show ?thesis 
        by (intro mult_left_mono power_decreasing) auto 
    qed
  qed
  also have "... = (\<Sum>i\<le>s. real (Stirling s i)) * (real (card R) / real (card B))"
    by (subst sum_distrib_right) simp
  also have "... = real (\<Sum>i\<le>s. (Stirling s i)) * (real (card R) / real (card B))"
    by simp
  also have "... \<le> ?R"
    by (subst Bell_Stirling_eq) simp
  finally show "?L \<le> ?R" by simp
qed

(*

  Condition 2:
    k\<ge> 2

  Condition 1:
    2 e B_(k+1)/k! \<le> eps

  card B eps/e * card R / card B  \<le> eps/e * card R \<le> eps * E Y

  Condition 3:
    TODO


*)

lemma
  fixes R :: "'a set"
  fixes B :: "'b set"
  fixes p :: "bool \<Rightarrow> ('a \<Rightarrow> 'b) pmf"
  assumes "finite R" "finite B" "card R \<le> card B"
  assumes "\<And>c. prob_space.k_wise_indep_vars (measure_pmf (p c)) (2*k+2) (\<lambda>_. discrete) (\<lambda>x \<omega>. \<omega> x) R"
  assumes "\<And>c x. x \<in> R \<Longrightarrow> map_pmf (\<lambda>\<omega>. \<omega> x) (p c) = pmf_of_set B"
  defines "Y \<equiv> (\<lambda>\<omega>. real (card ((\<lambda>x. \<omega> x) ` R)))"
  shows 
    exp_approx: "\<bar>measure_pmf.expectation (p False) Y - measure_pmf.expectation (p True) Y\<bar> \<le> 
      \<epsilon> / exp 1 * card R" (is "?A") and
    var_approx: "\<bar>measure_pmf.variance (p False) Y - measure_pmf.variance (p True) Y\<bar> \<le> \<epsilon>\<^sup>2" 
      (is "?B")
proof -
  define M1 where "M1 = measure_pmf (p False)"
  define M2 where "M2 = measure_pmf (p True)"
  define \<gamma> where "\<gamma> = Bell (k+1) / real (fact k)"
  have \<gamma>_nonneg: "\<gamma> \<ge> 0"
    unfolding \<gamma>_def by simp

  interpret M1: prob_space "M1"
    unfolding M1_def by (rule prob_space_measure_pmf)

  interpret M2: prob_space "M2"
    unfolding M2_def by (rule prob_space_measure_pmf)

  define Z :: "'b \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> real" 
    where "Z = (\<lambda>i \<omega>. real (card { j . j \<in> R \<and> \<omega> j = i}))"

  interpret H1: lim_balls_and_bins R B "2*k+2" "p False" "Z"
    using assms unfolding Z_def by unfold_locales auto

  interpret H2: lim_balls_and_bins R B "2*k+2" "p True" "Z"
    using assms unfolding Z_def by unfold_locales auto

  define I :: "real set" where "I = real ` {1..k}"
  define \<phi> :: "real \<Rightarrow> real" where "\<phi> = (\<lambda>x. min x 1)"

  define fp :: "real poly" where "fp = 1 - smult ((-1)^k / real (fact k)) (\<Prod>y \<in> I. [:- y, 1:])"
  define f where "f = poly fp"
  define g where "g = (\<lambda>x. \<phi> x - f x)"
  have \<phi>_exp: "\<phi> x = f x + g x" for x
    unfolding g_def by simp

  have k_ge_2: "k \<ge> 2" sorry


  have fin_I: "finite I"
    unfolding I_def by (intro finite_imageI) simp

  have f_eval: "f x = 1- (-1)^k / real (fact k) * (\<Prod>y \<in> I. (x - y))" for x
    unfolding fp_def f_def by (simp add:poly_prod)

  have g_diff: "\<bar>g x - g (x-1)\<bar> \<le> x^(k-1)/real (fact (k-1))" (is "?L \<le> ?R")
    if "x \<ge> k" for x :: real
  proof -
    have "plus 1 ` I = real ` plus 1 ` {1..k}"
      unfolding I_def image_image by simp
    also have "... = real ` {2..k+1}"
      by auto
    finally have plus_1_I: "plus 1 ` I = real ` {2..k+1}" by simp

    have "x \<ge> 2" using k_ge_2 that by simp
    hence "\<phi> x = \<phi> (x- 1)" 
      unfolding \<phi>_def by simp
    hence "\<bar>g x - g (x-1)\<bar> = \<bar>f (x-1) - f x\<bar>" 
      unfolding g_def by (simp add:algebra_simps)
    also have "... = \<bar>(-1)^k / real (fact k) * ((\<Prod>y \<in> I. (x - y)) - (\<Prod>y \<in> plus 1 ` I. (x - y)))\<bar>"
      unfolding f_eval by (simp add:algebra_simps comp_def prod.reindex)
    also have "... = 1 / real (fact k) * \<bar>(\<Prod>y \<in> I. (x - y)) - (\<Prod>y \<in> plus 1 ` I. (x - y))\<bar>"
      by (simp add:abs_mult)
    also have "... = 1 / real (fact k) * \<bar>(\<Prod>y \<in> {1..k}. (x - y)) - (\<Prod>y \<in> {2..k+1}. (x - y))\<bar>"
      unfolding plus_1_I unfolding I_def by (simp add:prod.reindex)
    also have "... = 1 / real (fact k) * 
      \<bar>(\<Prod>y \<in> insert 1 {2..k}. (x - y)) - (\<Prod>y \<in> insert (k+1) {2..k}. (x - y))\<bar>"
      using k_ge_2 by (subst Icc_eq_insert_lb_nat) (auto simp add:mult.commute numeral_eq_Suc)
    also have "... = 1 / real (fact k) * 
      \<bar>(x-1)*(\<Prod>y \<in> {2..k}. (x - y)) - (x-(k+1))*(\<Prod>y \<in> {2..k}. (x - y))\<bar>"
      by simp
    also have "... = 1 / real (fact k) * k * \<bar>(\<Prod>y \<in> {2..k}. (x - y))\<bar>"
      by (simp add:algebra_simps abs_mult)
    also have "... = 1 / real (fact (k-1)) * (\<Prod>y \<in> {2..k}. \<bar>x - y\<bar>)"
      using k_ge_2 abs_prod by (subst fact_reduce) auto 
    also have "... \<le> 1 / real (fact (k-1)) * (\<Prod>y \<in> {2..k}. x)"
      using that
      by (intro mult_left_mono prod_mono divide_nonneg_nonneg) auto 
    also have "... \<le> ?R" by simp
    finally show ?thesis by simp
  qed

  have "card I = card {1..k}"
    unfolding I_def by (intro card_image) simp
  also have "... = k" by simp
  finally have card_I: "card I = k" by simp

  have "degree (\<Prod>y\<in>I. [:- y, 1:]) \<le> sum (degree \<circ> (\<lambda>y. [:-y,1:])) I" 
    by (intro degree_prod_sum_le[OF fin_I])
  also have "... \<le> sum (\<lambda>_. 1) I"
    by (intro sum_mono) auto
  also have "... = k"
    using fin_I card_I by simp
  finally have "degree (\<Prod>y\<in>I. [:- y, 1:]) \<le> k" by simp
  hence "degree (smult ((-1)^k / real (fact k)) (\<Prod>y \<in> I. [:- y, 1:])) \<le> k" 
    using degree_smult_eq by simp
  moreover have "degree (1 :: real poly) \<le> k" 
    by simp
  ultimately have deg_fp: "degree fp \<le> k"
    unfolding fp_def using degree_diff_le  by blast

  have prod_I: "\<Prod>I = fact k"
    using prod_real unfolding I_def fact_prod by simp

  have f_approx_\<phi>: "f x = \<phi> x" if "x \<in> real ` {0..k}" for x
  proof (cases "x = 0")
    case True
    have "f x = 1 - (-1)^k / real (fact k) * (\<Prod>y \<in> I. - y)"
      unfolding f_eval True by simp
    also have "... = 1 - (-1)^k / real (fact k) * ((\<Prod>y \<in> I. (- 1)::real) * (\<Prod>y \<in> I. y))"
      by (subst prod.distrib[symmetric]) simp
    also have "... = 0"
      using prod_I card_I by simp
    also have "... = \<phi> x"
      using True \<phi>_def by simp
    finally show ?thesis by simp
  next
    case False
    hence a:"x \<in> I" unfolding I_def using that by auto
    hence "\<exists>a\<in>I. x - a = 0" by simp
    hence "f x = 1"
      unfolding f_eval by (subst prod_zero[OF fin_I]) auto
    also have "... = \<phi> x"
      using a unfolding \<phi>_def I_def by auto
    finally show ?thesis by simp
  qed


  have z_moment_eq: 
    "(\<integral>\<omega>. Z i \<omega>^s \<partial>(p False)) = (\<integral>\<omega>. Z i \<omega>^s \<partial>(p True))"  (is "?L = ?R")
    if "s \<le> 2*k+2" "i \<in> B" for s i
  proof -
    have "?L = (\<Sum>i = 0..s. (Stirling s i) * (1 / real (card B)) ^ i * real (ffact i (card R)))"
      unfolding Z_def M1_def by (intro hit_count_moments[OF _ _ that(1)] assms that) 
    also have "... = ?R"
      unfolding Z_def M2_def by (intro hit_count_moments[symmetric, OF _ _ that(1)] assms that) 
    finally show ?thesis by simp
  qed

  have z_moment_prod_eq:
    "M1.expectation (\<lambda>\<omega>. Z i \<omega>^s * Z j \<omega>^t) = M2.expectation (\<lambda>\<omega>. Z i \<omega>^s * Z j \<omega>^t)" 
    (is "?L = ?R") if "s+t \<le> 2*k+2" "i \<in> B" "j\<in> B" for s t i j
  proof (cases "i \<noteq> j")
    case True
    have "?L = (\<Sum>(xs, ys)\<in>{(xs, ys). set xs \<subseteq> R \<and> set ys \<subseteq> R \<and> set xs \<inter> set ys = {} \<and> 
      length xs = s \<and> length ys = t}. (1 / real (card B)) ^ (card (set xs) + card (set ys)))"
      unfolding Z_def M1_def M2_def using assms True that
      by (intro hit_count_prod_exp[OF assms(1,2) that(1)]) auto
    also have "... = ?R"
      unfolding Z_def M1_def M2_def using assms True that
      by (intro hit_count_prod_exp[OF assms(1,2) that(1),symmetric]) auto
    finally show ?thesis by simp
  next
    case False
    have "?L = M1.expectation (\<lambda>\<omega>. Z i \<omega>^(s+t))"
      using False by (simp add:power_add)
    also have "... = M2.expectation (\<lambda>\<omega>. Z i \<omega>^(s+t))"
      using that unfolding M1_def M2_def by (intro z_moment_eq)
    also have "... = ?R"
      using False by (simp add:power_add)
    finally show ?thesis by simp
  qed

  have z_sum_moment_eq:
    "M1.expectation (\<lambda>\<omega>. (Z i \<omega> + Z j \<omega>)^s) = M2.expectation (\<lambda>\<omega>. (Z i \<omega> + Z j \<omega>)^s)"  
    (is "?L = ?R") if "s \<le> 2*k+2" "i \<in> B" "j \<in> B" for s i j
  proof -
    have a: "\<bar>Z i x ^ l * Z j x ^ (s - l)\<bar> \<le> real (card R ^ s)"  if "l \<in> {..s}" for l x
    proof -
      have "\<bar>Z i x ^ l * Z j x ^ (s - l)\<bar> \<le> Z i x ^ l * Z j x ^ (s - l)" 
        unfolding Z_def by auto
      also have "... \<le> real (card R) ^ l * real (card R) ^ (s-l)"
        unfolding Z_def 
        by (intro mult_mono power_mono of_nat_mono card_mono assms(1)) auto
      also have "... = real (card R)^s" using that 
        by (subst power_add[symmetric]) simp
      also have "... = real (card R^s)"
        by simp
      finally show ?thesis by simp
    qed
    have "?L = M1.expectation (\<lambda>\<omega>. (\<Sum>l\<le>s. (s choose l) * Z i \<omega>^l * Z j \<omega>^(s-l)))"
      by (intro arg_cong[where f="M1.expectation"] ext binomial_ring)
    also have "... = M1.expectation (\<lambda>\<omega>. (\<Sum>l\<le>s. (s choose l) * (Z i \<omega>^l * Z j \<omega>^(s-l))))"
      by (intro arg_cong[where f="M1.expectation"] ext sum.cong) auto 
    also have "... = (\<Sum>l\<le>s. M1.expectation (\<lambda>\<omega>. (s choose l) * (Z i \<omega>^l * Z j \<omega>^(s-l))))"
      unfolding M1_def by (intro Bochner_Integration.integral_sum integrable_mult_right 
          integrable_pmf_iff_bounded[where C="card R^s"] a) auto
    also have "... = (\<Sum>l\<le>s. (s choose l) * M1.expectation (\<lambda>\<omega>. (Z i \<omega>^l * Z j \<omega>^(s-l))))"
      unfolding M1_def by (intro sum.cong integral_mult_right 
          integrable_pmf_iff_bounded[where C="card R^s"] a) auto
    also have "... = (\<Sum>l\<le>s. (s choose l) * M2.expectation (\<lambda>\<omega>. (Z i \<omega>^l * Z j \<omega>^(s-l))))"
      using that by (intro sum.cong arg_cong2[where f="(*)"] z_moment_prod_eq) auto
    also have "... = (\<Sum>l\<le>s. M2.expectation (\<lambda>\<omega>. (s choose l) * (Z i \<omega>^l * Z j \<omega>^(s-l))))"
      unfolding M2_def by (intro sum.cong integral_mult_right[symmetric] 
          integrable_pmf_iff_bounded[where C="card R^s"] a) auto
    also have "... = M2.expectation (\<lambda>\<omega>. (\<Sum>l\<le>s. (s choose l) * (Z i \<omega>^l * Z j \<omega>^(s-l))))"
      unfolding M2_def
      by (intro Bochner_Integration.integral_sum[symmetric] integrable_mult_right 
          integrable_pmf_iff_bounded[where C="card R^s"] a) auto
    also have "... = M2.expectation (\<lambda>\<omega>. (\<Sum>l\<le>s. (s choose l) * Z i \<omega>^l * Z j \<omega>^(s-l)))"
      by (intro arg_cong[where f="M2.expectation"] ext sum.cong) auto 
    also have "... = ?R"
      by (intro arg_cong[where f="M2.expectation"] ext binomial_ring[symmetric])
    finally show ?thesis by simp
  qed

  have Z_any_integrable:
    "integrable (p c) (\<lambda>\<omega>. f (Z i \<omega>))" for i c and f :: "real \<Rightarrow> real" 
    unfolding Z_def using assms(1) card_mono
    by (intro integrable_pmf_iff_bounded[where C="Max (abs ` f ` real ` {..card R})"])
     fastforce+ 

  have q:"real (card A) + real (card B) \<in> real ` {..2 * card R}" if "A \<subseteq> R" "B \<subseteq> R" for A B
  proof -
    have "card A + card B \<le> card R + card R"
      by (intro add_mono card_mono assms that)
    also have "... = 2 * card R" by simp
    finally show ?thesis by force
  qed

  hence Z_any_integrable':
    "integrable (p c) (\<lambda>\<omega>. f (Z i \<omega> + Z j \<omega>))" for i j c and f :: "real \<Rightarrow> real" 
    unfolding Z_def using assms(1) card_mono abs_triangle_ineq
    by (intro integrable_pmf_iff_bounded[where C="Max (abs ` f ` real ` {..2*card R})"] Max_ge 
        finite_imageI imageI) auto

  have z1_any_integrable:
    "integrable M1 (\<lambda>\<omega>. f (Z i \<omega>))" for i and f :: "real \<Rightarrow> real"
    unfolding M1_def using Z_any_integrable by simp

  have z2_any_integrable:
    "integrable M2 (\<lambda>\<omega>. f (Z i \<omega>))" for i and f :: "real \<Rightarrow> real"
    unfolding M2_def using Z_any_integrable by simp

  have z1_any_integrable':
    "integrable M1 (\<lambda>\<omega>. f (Z i \<omega> + Z j \<omega>))" for i j and f :: "real \<Rightarrow> real"
    unfolding M1_def using Z_any_integrable' by simp

  have z2_any_integrable':
    "integrable M2 (\<lambda>\<omega>. f (Z i \<omega> + Z j \<omega>))" for i j and f :: "real \<Rightarrow> real"
    unfolding M2_def using Z_any_integrable' by simp

  have Z_poly_eq: "M1.expectation (\<lambda>\<omega>. poly f (Z i \<omega>)) = M2.expectation (\<lambda>\<omega>. poly f (Z i \<omega>))"
    (is "?L = ?R") if "i \<in> B" "degree f \<le> 2*k+1" for f i
  proof -
    have "?L = (\<Sum>j\<le>degree f. M1.expectation (\<lambda>\<omega>. poly.coeff f j * Z i \<omega> ^ j))"
      unfolding poly_altdef
      by (intro Bochner_Integration.integral_sum integrable_mult_right z1_any_integrable)
    also have "... = (\<Sum>j\<le>degree f. poly.coeff f j * M1.expectation (\<lambda>\<omega>. Z i \<omega> ^ j))"
      by (intro sum.cong z_moment_eq Bochner_Integration.integral_mult_right z1_any_integrable)
       simp 
    also have "... = (\<Sum>j\<le>degree f. poly.coeff f j * M2.expectation (\<lambda>\<omega>. Z i \<omega> ^ j))"
      using that unfolding M1_def M2_def by (intro sum.cong arg_cong2[where f="(*)"] z_moment_eq) auto
    also have "... = (\<Sum>j\<le>degree f. M2.expectation (\<lambda>\<omega>. poly.coeff f j * Z i \<omega> ^ j))"
      by (intro sum.cong) auto 
    also have "... = ?R"
      unfolding poly_altdef by (intro Bochner_Integration.integral_sum[symmetric] 
          integrable_mult_right z2_any_integrable) 
    finally show ?thesis by simp
  qed

  have Z_poly_eq_2: "M1.expectation (\<lambda>\<omega>. poly f (Z i \<omega> + Z j \<omega>)) = M2.expectation (\<lambda>\<omega>. poly f (Z i \<omega> + Z j \<omega>))"
    (is "?L = ?R") if "i \<in> B" "j \<in> B" "degree f \<le> 2*k+1" for f i j 
  proof -
    have "?L = (\<Sum>d\<le>degree f. M1.expectation (\<lambda>\<omega>. poly.coeff f d * (Z i \<omega> + Z j \<omega>) ^ d))"
      unfolding poly_altdef
      by (intro Bochner_Integration.integral_sum integrable_mult_right z1_any_integrable')
    also have "... = (\<Sum>d\<le>degree f. poly.coeff f d * M1.expectation (\<lambda>\<omega>. (Z i \<omega> + Z j \<omega>) ^ d))"
      by (intro sum.cong z_moment_eq Bochner_Integration.integral_mult_right z1_any_integrable')
       simp 
    also have "... = (\<Sum>d\<le>degree f. poly.coeff f d * M2.expectation (\<lambda>\<omega>. (Z i \<omega> + Z j \<omega>) ^ d))"
      using that by (intro sum.cong arg_cong2[where f="(*)"] z_sum_moment_eq) auto
    also have "... = (\<Sum>d\<le>degree f. M2.expectation (\<lambda>\<omega>. poly.coeff f d * (Z i \<omega> + Z j \<omega>) ^ d))"
      by (intro sum.cong) auto 
    also have "... = ?R"
      unfolding poly_altdef by (intro Bochner_Integration.integral_sum[symmetric] 
          integrable_mult_right z2_any_integrable') 
    finally show ?thesis by simp
  qed

  have g_eq_0_iff_2: "abs (g x) * y = 0" if "x \<in> \<int>" "x \<ge> 0" "x \<le> k" for x y :: real 
  proof -
    have "\<exists>x'. x = real_of_int x' \<and> x' \<le> k \<and> x' \<ge> 0" 
      using that Ints_def by fastforce
    hence "\<exists>x'. x = real x' \<and> x' \<le> k" 
      by (metis nat_le_iff of_nat_nat)
    hence "x \<in> real ` {0..k}" 
      by auto
    hence "g x = 0"
      unfolding g_def using f_approx_\<phi> by simp
    thus ?thesis by simp
  qed

  have g_bound_abs: "\<bar>integral\<^sup>L (measure_pmf p) (\<lambda>\<omega>. g (f \<omega>))\<bar> \<le> 
    integral\<^sup>L (measure_pmf p) (\<lambda>\<omega>. f \<omega>^(k+1)) / real (fact k)" 
    (is "?L \<le> ?R") if "range f \<subseteq> real ` {..m}"  for m p and f :: "('a \<Rightarrow> 'b) \<Rightarrow> real"
  proof -
    define M where "M = measure_pmf p"
    interpret M: prob_space "M"
      unfolding M_def by (rule prob_space_measure_pmf)

    have f_any_integrable:
      "integrable M (\<lambda>\<omega>. h (f \<omega>))" for h :: "real \<Rightarrow> real"
      unfolding M_def using that
      by (intro integrable_pmf_iff_bounded[where C="Max (abs ` h` real ` {..m})"] 
          Max_ge finite_imageI imageI) auto

    have f_val: "f \<omega> \<in> real ` {..m}" for \<omega> using  that by auto

    have f_int: "f \<omega> \<ge> real y + 1" if "f \<omega> > real y" for y \<omega> 
    proof -
      obtain x where x_def: "f \<omega> = real x" "x \<le> m" using f_val by auto
      hence "y < x" using that by simp
      hence "y + 1 \<le> x" by simp
      then show ?thesis using x_def by simp
    qed

    have f_nonneg: "f \<omega> \<ge> 0" for \<omega> 
    proof -
      obtain x where x_def: "f \<omega> = real x" "x \<le> m" using f_val by auto
      hence "x \<ge> 0" by simp
      then show ?thesis using x_def by simp
    qed

    have "\<not>(real x \<le> f \<omega>)" if "x > m" for x \<omega> 
    proof -
      obtain x where x_def: "f \<omega> = real x" "x \<le> m" using f_val by auto
      then show ?thesis using x_def that by simp
    qed

    hence max_Z1: "M.prob {\<omega>. real x \<le> f \<omega>} = 0" if "x > m" for x 
      using that by auto

    have "?L \<le> M.expectation (\<lambda>\<omega>. \<bar>g (f \<omega>)\<bar>)"
      unfolding M_def by (intro integral_abs_bound)
    also have "... = (\<Sum>y\<in>real ` {..m}. \<bar>g y\<bar> * M.prob {\<omega>. f \<omega> = y})"
      using that by (intro M.pmf_exp_of_fin_function[OF M_def]) auto
    also have "... = (\<Sum>y\<in>{..m}. \<bar>g (real y)\<bar> * M.prob {\<omega>. f \<omega> = real y})"
      by (subst sum.reindex) (auto simp add:comp_def)
    also have "... = (\<Sum>y\<in>{..m}. \<bar>g (real y)\<bar> * 
      (M.prob ({\<omega>. f \<omega> = real y} \<union> {\<omega>. f \<omega> > real y}) - M.prob {\<omega>. f \<omega> > real y}))"
      unfolding M_def by (subst measure_Union) auto
    also have "... = (\<Sum>y\<in>{..m}. \<bar>g y\<bar> * (M.prob ({\<omega>. f \<omega> \<ge> y}) - M.prob {\<omega>. f \<omega> > y}))"
      by (intro sum.cong arg_cong2[where f="(*)"] arg_cong2[where f="(-)"] 
          arg_cong[where f="M.prob"]) auto
    also have "... = 
      (\<Sum>y\<in>{..m}. \<bar>g y\<bar> * M.prob {\<omega>. f \<omega> \<ge> y}) - (\<Sum>y\<in>{..m}. \<bar>g y\<bar> * M.prob {\<omega>. f \<omega> > y})"
      by (simp add:algebra_simps sum_subtractf)
    also have "... = (\<Sum>y\<in>{..m}. \<bar>g (real y)\<bar> * M.prob {\<omega>. f \<omega> \<ge> real y}) - 
       (\<Sum>y\<in>{..m}. \<bar>g (real y)\<bar> * M.prob {\<omega>. f \<omega> \<ge> real (y+1)})"
      using f_int
      by (intro sum.cong arg_cong2[where f="(-)"] arg_cong2[where f="(*)"]
          arg_cong[where f="M.prob"]) fastforce+ 
    also have "... = (\<Sum>y\<in>{..m}. \<bar>g (real y)\<bar> * M.prob {\<omega>. f \<omega> \<ge> real y}) - 
       (\<Sum>y\<in>Suc ` {..m}. \<bar>g (real y - 1)\<bar> * M.prob {\<omega>. f \<omega> \<ge> real y})"
      by (subst sum.reindex) (auto simp add:comp_def)
    also have "... = (\<Sum>y\<in>{..m}. \<bar>g (real y)\<bar> * M.prob {\<omega>. f \<omega> \<ge> real y}) - 
       (\<Sum>y\<in>{1..m}. \<bar>g (real y - 1)\<bar> * M.prob {\<omega>. f \<omega> \<ge> real y})" 
      using max_Z1 image_Suc_atMost
      by (intro arg_cong2[where f="(-)"] sum.mono_neutral_cong) auto 
    also have "... = (\<Sum>y\<in>{k+1..m}. \<bar>g (real y)\<bar> * M.prob {\<omega>. f \<omega> \<ge> real y}) - 
       (\<Sum>y\<in>{k+1..m}. \<bar>g (real y - 1)\<bar> * M.prob {\<omega>. f \<omega> \<ge> real y})"
      using k_ge_2
      by (intro arg_cong2[where f="(-)"] sum.mono_neutral_cong_right ballI g_eq_0_iff_2)
        auto 
    also have "... = (\<Sum>y\<in>{k+1..m}. (\<bar>g (real y)\<bar> - \<bar>g (real y-1)\<bar>) * 
      M.prob {\<omega>. f \<omega> \<ge> real y})"
      by (simp add:algebra_simps sum_subtractf)
    also have "... \<le> (\<Sum>y\<in>{k+1..m}. \<bar>g (real y)- g (real y-1)\<bar> * 
      M.prob {\<omega>. f \<omega> ^ (k+1) \<ge> real y ^ (k+1)})" 
      by (intro sum_mono mult_mono M.pmf_mono[OF M_def]) (auto simp del:power_Suc)
    also have "... \<le> (\<Sum>y\<in>{k+1..m}. real y^(k-1) / real (fact (k-1)) * 
      (M.expectation (\<lambda>\<omega>. f \<omega>^(k+1)) / real y^(k+1)))"
      using k_ge_2 f_nonneg 
      by (intro sum_mono mult_mono g_diff M.pmf_markov[OF M_def] f_any_integrable) 
        auto
    also have "... = (\<Sum>y\<in>{k+1..m}.
      M.expectation (\<lambda>\<omega>. f \<omega>^(k+1)) / real (fact (k-1)) * real y^(k-1)/ real y^(k+1))"
      by (intro sum.cong) (auto simp add:algebra_simps)
    also have "... = M.expectation (\<lambda>\<omega>. f \<omega>^(k+1)) / real (fact (k-1)) *
      (\<Sum>y\<in>{k+1..m}. real y^(k-1)/ real y^(k+1))"
      by (subst sum_distrib_left)  simp
    also have "... = M.expectation (\<lambda>\<omega>. f \<omega>^(k+1)) / real (fact (k-1)) * 
      (\<Sum>y\<in>{k+1..m}. 1 / real y^2)"
      using k_ge_2 by (intro arg_cong2[where f="(*)"] sum.cong refl)
        (auto simp add:frac_eq_eq power_add[symmetric])
    also have "... \<le> M.expectation (\<lambda>\<omega>. f \<omega>^(k+1)) / real (fact (k-1)) * 
      (1 / real k)" using k_ge_2 f_nonneg
      by (intro mult_left_mono basel_sum divide_nonneg_nonneg Bochner_Integration.integral_nonneg)
        auto 
    also have "... = ?R"
      using k_ge_2 unfolding M_def by (cases k) (auto simp add:algebra_simps)
    finally show ?thesis by simp
  qed

  have z1_g_bound: "\<bar>integral\<^sup>L (p c) (\<lambda>\<omega>. g (Z i \<omega>))\<bar> \<le> (real (card R) / real (card B)) * \<gamma>" 
    (is "?L1 \<le> ?R1") if "i \<in> B" for i c
  proof -
    have card_B_gt_0: "card B > 0" 
      using that card_gt_0_iff assms(2) by auto

    have "measure_pmf.expectation (p c) (\<lambda>\<omega>. Z i \<omega>^(k+1)) = 
      (\<Sum>i = 0..(k+1). (Stirling (k+1) i) * (1 / real (card B)) ^ i * real (ffact i (card R)))"
      unfolding Z_def using that 
      by (intro hit_count_moments[OF assms(1,2) _ assms(4,5)]) auto
    also have "... \<le> Bell (k+1) * real (card R) / real (card B)"
      by (intro hit_count_approx card_B_gt_0 assms(3)) auto 
    also have "... = real (card R) / real (card B) * Bell (k+1)" by simp
    finally have Z_pow_exp_bound: "measure_pmf.expectation (p c) (\<lambda>\<omega>. Z i \<omega>^(k+1)) \<le> 
      real (card R) / real (card B) * Bell (k+1)"
      by simp

    have "?L1 \<le> measure_pmf.expectation (p c) (\<lambda>\<omega>. Z i \<omega> ^ (k + 1)) / real (fact k)"
      unfolding Z_def using assms(1)
      by (intro g_bound_abs[where m1="card R"]) (auto intro!:imageI card_mono)
    also have "... \<le> real (card R) / real (card B) * Bell (k+1) / real (fact k)"
      by (intro divide_right_mono Z_pow_exp_bound) auto
    finally show ?thesis by (simp add:\<gamma>_def)
  qed

  have g_add_bound: "\<bar>integral\<^sup>L (p c) (\<lambda>\<omega>. g (Z i \<omega> + Z j \<omega>))\<bar> \<le> 2^(k+1) * \<gamma>" 
    (is "?L1 \<le> ?R1") if "i \<in> B" "j \<in> B" for i j c
  proof -
    have a:"(\<integral>\<omega>. (Z i \<omega>^d * Z j \<omega>^(k+1-d)) \<partial>(p c)) \<le> Bell (k+1)" (is "?L2 \<le> ?R2") if "d \<in> {..k+1}" for d
    proof -
      define p' :: real where "p' = real (k+1) / real d"
      define q' :: real where "q' = real (k+1) / real (k+1-d)"
      have "?L2 = (\<integral>\<omega>. \<bar>Z i \<omega>^d * Z j \<omega>^(k+1-d)\<bar> \<partial>(p c))"
        unfolding Z_def by simp
      also have "... \<le> (\<integral>\<omega>. \<bar>Z i \<omega>^d\<bar> powr p' \<partial>(p c)) powr (1/p') * (\<integral>\<omega>. \<bar>Z j \<omega>^(k+1-d)\<bar> powr q' \<partial>(p c)) powr (1/q')"
        apply (intro Holder_inequality(2) Z_any_integrable)
        apply auto
        sorry
      also have "... \<le> ?R2" sorry
      finally show ?thesis by simp
    qed

    have "?L1 \<le> measure_pmf.expectation (p c) (\<lambda>\<omega>. (Z i \<omega> + Z j \<omega>) ^ (k + 1)) / real (fact k)"
      unfolding Z_def using assms(1)
      by (intro g_bound_abs[where m1="2*card R"]) (auto intro!:imageI q)
    also have "... = (\<integral>\<omega>. (\<Sum>d \<le> k+1. real (k+1 choose d) * (Z i \<omega>^d * Z j \<omega>^(k+1-d))) \<partial>(p c)) / real (fact k)"
      by (subst binomial_ring) (simp add:algebra_simps)
    also have "... = (\<Sum>d \<le> k+1. (\<integral>\<omega>. real (k+1 choose d) * (Z i \<omega>^d * Z j \<omega>^(k+1-d)) \<partial>(p c))) / real (fact k)"
      apply (intro Bochner_Integration.integral_sum arg_cong2[where f="(/)"] integrable_mult_right)
      sorry
    also have "... = (\<Sum>d \<le> k+1. real (k+1 choose d) * (\<integral>\<omega>. (Z i \<omega>^d * Z j \<omega>^(k+1-d)) \<partial>(p c))) / real (fact k)"
      by (simp del:power_Suc)
    also have "... \<le> (\<Sum>d \<le> k+1. real (k+1 choose d) * Bell (k+1)) / real (fact k)"
      by (intro divide_right_mono sum_mono mult_left_mono a) auto
    also have "... = (\<Sum>d \<le> k+1. (k+1 choose d)) * Bell(k+1) / real (fact k)"
      by (subst sum_distrib_right) simp
    also have "... = ?R1"
      by (subst choose_row_sum) (simp add:\<gamma>_def)
    finally show ?thesis by simp
  qed

  have Z_poly_diff: 
    "\<bar>M1.expectation (\<lambda>\<omega>. \<phi> (Z i \<omega>)) - M2.expectation (\<lambda>\<omega>. \<phi> (Z i \<omega>))\<bar> \<le> 2 * ((real (card R) / real (card B)) * \<gamma>)" 
    (is "?L \<le> 2 * ?R") if "i \<in> B" for i
  proof -
    have "?L = \<bar>M1.expectation (\<lambda>\<omega>. f (Z i \<omega>)) + M1.expectation (\<lambda>\<omega>. g (Z i \<omega>)) -
      M2.expectation (\<lambda>\<omega>. f (Z i \<omega>)) - M2.expectation (\<lambda>\<omega>. g (Z i \<omega>))\<bar>" 
      using z1_any_integrable z2_any_integrable unfolding \<phi>_exp by simp
    also have "... = \<bar>M1.expectation (\<lambda>\<omega>. g (Z i \<omega>)) + (- M2.expectation (\<lambda>\<omega>. g (Z i \<omega>)))\<bar>"
      unfolding f_def using that deg_fp by (subst Z_poly_eq) auto
    also have "... \<le> \<bar>M1.expectation (\<lambda>\<omega>. g (Z i \<omega>))\<bar> + \<bar>M2.expectation (\<lambda>\<omega>. g (Z i \<omega>))\<bar>"
      by simp
    also have "... \<le> ?R + ?R"
      unfolding M1_def M2_def by (intro add_mono z1_g_bound that)
    also have "... = 2 * ?R" 
      by (simp add:algebra_simps)
    finally show ?thesis by simp
  qed

  have Z_poly_diff_2: "\<bar>M1.expectation (\<lambda>\<omega>. \<phi> (Z i \<omega>)) - M2.expectation (\<lambda>\<omega>. \<phi> (Z i \<omega>))\<bar> \<le> 2 * \<gamma>"
    (is "?L \<le> ?R") if "i \<in> B" for i
  proof -
    have "?L \<le> 2 * ((real (card R) / real (card B)) * \<gamma>)"
      by (intro Z_poly_diff that)
    also have "... \<le> 2 * (1 * \<gamma>)"
      using assms(3) assms(2) that card_gt_0_iff
      by (intro mult_right_mono mult_left_mono \<gamma>_nonneg that iffD2[OF pos_divide_le_eq]) auto
    also have "... = ?R" by simp
    finally show ?thesis by simp
  qed

  have Z_poly_diff_3: 
    "\<bar>M2.expectation (\<lambda>\<omega>. \<phi> (Z i \<omega> + Z j \<omega>)) - M1.expectation (\<lambda>\<omega>. \<phi> (Z i \<omega> + Z j \<omega>))\<bar> \<le> 2^(k+2) * \<gamma>" 
    (is "?L \<le> ?R") if "i \<in> B" "j \<in> B" for i j
  proof -
    have "?L = \<bar>M2.expectation (\<lambda>\<omega>. f (Z i \<omega> + Z j \<omega>)) + M2.expectation (\<lambda>\<omega>. g (Z i \<omega> + Z j \<omega>)) -
      M1.expectation (\<lambda>\<omega>. f (Z i \<omega> + Z j \<omega>)) - M1.expectation (\<lambda>\<omega>. g (Z i \<omega> + Z j \<omega>))\<bar>" 
      using z1_any_integrable' z2_any_integrable' unfolding \<phi>_exp by simp
    also have "... = \<bar>M2.expectation (\<lambda>\<omega>. g (Z i \<omega> + Z j \<omega>)) + (- M1.expectation (\<lambda>\<omega>. g (Z i \<omega> + Z j \<omega>)))\<bar>"
      unfolding f_def using that deg_fp by (subst Z_poly_eq_2) auto
    also have "... \<le> \<bar>M1.expectation (\<lambda>\<omega>. g (Z i \<omega> + Z j \<omega>))\<bar> + \<bar>M2.expectation (\<lambda>\<omega>. g (Z i \<omega> + Z j \<omega>))\<bar>"
      by simp
    also have "... \<le> 2^(k+1) * \<gamma> + 2^(k+1) * \<gamma>"
      unfolding M1_def M2_def by (intro add_mono g_add_bound that)
    also have "... = ?R" 
      by (simp add:algebra_simps)
    finally show ?thesis by simp
  qed

  have B_nonempty: "B \<noteq> {}" if "x \<in> R" for x 
  proof  -
    have "R \<noteq> {}" using that by auto
    hence "card R > 0" using assms(1) by auto
    hence "card B > 0" using assms by auto
    thus ?thesis by auto
  qed

  have Y_eq: "Y \<omega> = (\<Sum>i \<in> B. \<phi>(Z i \<omega>))" if "\<omega> \<in> set_pmf (p c)" for c \<omega>
  proof -
    have "\<omega> ` R \<subseteq> B"
    proof (rule image_subsetI)
      fix x assume a:"x \<in> R"
      have "\<omega> x \<in> set_pmf (map_pmf (\<lambda>\<omega>. \<omega> x) (p c))"
        using that by (subst set_map_pmf) simp
      also have "... = set_pmf (pmf_of_set B)"
        by (intro arg_cong[where f="set_pmf"] assms(5) a)
      also have "... = B"
        by (intro set_pmf_of_set assms(2) B_nonempty[OF a])
      finally show "\<omega> x \<in> B" by simp
    qed
    hence "(\<omega> ` R) = B \<inter> \<omega> ` R"
      by auto
    hence "Y \<omega> = card (B \<inter> \<omega> ` R)"
      unfolding Y_def by auto
    also have  "... = (\<Sum>i \<in> B. of_bool (i \<in> \<omega> ` R))"
      unfolding of_bool_def using assms(2) by (subst sum.If_cases) auto
    also have  "... = (\<Sum>i \<in> B. of_bool (card {r \<in> R.  \<omega> r = i} > 0))"
      using assms(1) by (intro sum.cong arg_cong[where f="of_bool"]) 
        (auto simp add:card_gt_0_iff) 
    also have "... = (\<Sum>i \<in> B. \<phi>(Z i \<omega>))"
      unfolding \<phi>_def Z_def by (intro sum.cong) (auto simp add:of_bool_def) 
    finally show ?thesis by simp
  qed

  have Y_sq_eq: "Y \<omega>^ 2 = 
    (\<Sum>i \<in> B \<times> B. \<phi>(Z (fst i) \<omega>) + \<phi>(Z (snd i) \<omega>) - \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>))" 
    if "\<omega> \<in> set_pmf (p c)" for c \<omega>
    using sum.cartesian_product sorry

  have "\<bar>M1.expectation Y - M2.expectation Y\<bar> = 
    \<bar>M1.expectation (\<lambda>\<omega>. \<Sum>i \<in> B. \<phi>(Z i \<omega>)) - M2.expectation (\<lambda>\<omega>. \<Sum>i \<in> B. \<phi>(Z i \<omega>))\<bar>"
    unfolding M1_def M2_def by (intro arg_cong[where f="abs"] arg_cong2[where f="(-)"] 
     Bochner_Integration.integral_cong_AE AE_pmfI Y_eq) auto
  also have "... = 
    \<bar>(\<Sum>i \<in> B. M1.expectation (\<lambda>\<omega>.  \<phi>(Z i \<omega>))) - (\<Sum>i \<in> B. M2.expectation (\<lambda>\<omega>. \<phi>(Z i \<omega>)))\<bar>"
    by (intro arg_cong[where f="abs"] arg_cong2[where f="(-)"] 
        Bochner_Integration.integral_sum z1_any_integrable z2_any_integrable)
  also have "... = \<bar>(\<Sum>i \<in> B. M1.expectation (\<lambda>\<omega>.  \<phi>(Z i \<omega>)) - M2.expectation (\<lambda>\<omega>.  \<phi>(Z i \<omega>)))\<bar>"
    by (subst sum_subtractf) simp
  also have "... \<le> (\<Sum>i \<in> B. \<bar>M1.expectation (\<lambda>\<omega>.  \<phi>(Z i \<omega>)) - M2.expectation (\<lambda>\<omega>.  \<phi>(Z i \<omega>))\<bar>)"
    by simp
  also have "... \<le> (\<Sum>i \<in> B. 2 * ((real (card R) / real (card B)) * \<gamma>))"
    by (intro sum_mono Z_poly_diff)
  also have "... \<le> 2 * real (card R) * \<gamma>"
    using \<gamma>_nonneg by simp
  finally have Y_exp_diff_1: "\<bar>M1.expectation Y - M2.expectation Y\<bar> \<le>  2 * real (card R) * \<gamma>" by simp

  have "\<bar>M1.expectation Y - M2.expectation Y\<bar> \<le>  2 * real (card R) * \<gamma>"
    using Y_exp_diff_1 by simp
  also have "... \<le> \<epsilon> / exp 1 * card R" sorry
  finally show ?A
    unfolding M1_def M2_def by simp

  have "\<bar>M1.expectation Y - M2.expectation Y\<bar> \<le>  2 * real (card R) * \<gamma>"
    using Y_exp_diff_1 by simp
  also have "... \<le> 2 * real (card B) * \<gamma>" 
    by (intro mult_right_mono mult_left_mono \<gamma>_nonneg of_nat_mono assms)auto
  finally have Y_exp_diff_2: "\<bar>M1.expectation Y - M2.expectation Y\<bar> \<le> 2 * \<gamma> * real (card B)"
    by (simp add:algebra_simps)

  have int_Y: "integrable (measure_pmf (p c)) Y" for c
    using assms(1) card_image_le unfolding Y_def
    by (intro integrable_pmf_iff_bounded[where C="card R"])  auto

  have int_Y_sq: "integrable (measure_pmf (p c)) (\<lambda>\<omega>. Y \<omega>^2)" for c
    using assms(1) card_image_le unfolding Y_def
    by (intro integrable_pmf_iff_bounded[where C="real (card R)^2"]) auto

  have "\<bar>M1.expectation (\<lambda>\<omega>. Y \<omega> ^2) - M2.expectation (\<lambda>\<omega>. Y \<omega>^2)\<bar> =
    \<bar>M1.expectation (\<lambda>\<omega>. (\<Sum>i \<in> B \<times> B. \<phi>(Z (fst i) \<omega>) + \<phi>(Z (snd i) \<omega>) - \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>))) - 
     M2.expectation (\<lambda>\<omega>. (\<Sum>i \<in> B \<times> B. \<phi>(Z (fst i) \<omega>) + \<phi>(Z (snd i) \<omega>) - \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>)))\<bar>" 
    unfolding M1_def M2_def by (intro arg_cong[where f="abs"] arg_cong2[where f="(-)"] 
       Bochner_Integration.integral_cong_AE AE_pmfI Y_sq_eq) auto
  also have "... = \<bar>(\<Sum>i \<in> B \<times> B. 
    M1.expectation (\<lambda>\<omega>. \<phi>(Z (fst i) \<omega>)) + M1.expectation (\<lambda>\<omega>. \<phi>(Z (snd i) \<omega>)) - 
    M1.expectation(\<lambda>\<omega>. \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>)) - ( M2.expectation (\<lambda>\<omega>. \<phi>(Z (fst i) \<omega>)) + 
    M2.expectation (\<lambda>\<omega>. \<phi>(Z (snd i) \<omega>)) - M2.expectation(\<lambda>\<omega>. \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>))))\<bar>"
    using z1_any_integrable z2_any_integrable z1_any_integrable'  z2_any_integrable'
    by (simp add:Bochner_Integration.integral_sum sum_subtractf)
  also have "... = \<bar>(\<Sum>i \<in> B \<times> B. 
    (M1.expectation (\<lambda>\<omega>. \<phi>(Z (fst i) \<omega>)) - M2.expectation (\<lambda>\<omega>. \<phi>(Z (fst i) \<omega>))) + 
    (M1.expectation (\<lambda>\<omega>. \<phi>(Z (snd i) \<omega>)) - M2.expectation (\<lambda>\<omega>. \<phi>(Z (snd i) \<omega>))) + 
    (M2.expectation(\<lambda>\<omega>. \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>)) - M1.expectation(\<lambda>\<omega>. \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>))))\<bar>"
    by (intro arg_cong[where f="abs"] sum.cong) auto
  also have "... \<le> (\<Sum>i \<in> B \<times> B. \<bar>
    (M1.expectation (\<lambda>\<omega>. \<phi>(Z (fst i) \<omega>)) - M2.expectation (\<lambda>\<omega>. \<phi>(Z (fst i) \<omega>))) + 
    (M1.expectation (\<lambda>\<omega>. \<phi>(Z (snd i) \<omega>)) - M2.expectation (\<lambda>\<omega>. \<phi>(Z (snd i) \<omega>))) + 
    (M2.expectation(\<lambda>\<omega>. \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>)) - M1.expectation(\<lambda>\<omega>. \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>)))\<bar>)"
    by (intro sum_abs)
  also have "... \<le> (\<Sum>i \<in> B \<times> B.
    \<bar>M1.expectation (\<lambda>\<omega>. \<phi>(Z (fst i) \<omega>)) - M2.expectation (\<lambda>\<omega>. \<phi>(Z (fst i) \<omega>))\<bar> + 
    \<bar>M1.expectation (\<lambda>\<omega>. \<phi>(Z (snd i) \<omega>)) - M2.expectation (\<lambda>\<omega>. \<phi>(Z (snd i) \<omega>))\<bar> + 
    \<bar>M2.expectation(\<lambda>\<omega>. \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>)) - M1.expectation(\<lambda>\<omega>. \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>))\<bar>)"
    by (intro sum_mono) auto
  also have "... \<le> (\<Sum>i \<in> B \<times> B. 2*\<gamma> + 2 * \<gamma> + 2^(k+2)*\<gamma>)"
    by (intro sum_mono add_mono Z_poly_diff_2 Z_poly_diff_3) auto 
  also have "... = (2^(k+2)+4) * \<gamma> * card B^2"
    by (simp add:card_cartesian_product power2_eq_square algebra_simps)
  finally have Y_sq_exp_diff: 
    "\<bar>M1.expectation (\<lambda>\<omega>. Y \<omega> ^2) - M2.expectation (\<lambda>\<omega>. Y \<omega>^2)\<bar> \<le> (2^(k+2)+4) * \<gamma> * card B^2" by simp

  have Y_exp_rough_bound: "\<bar>integral\<^sup>L (p c) Y\<bar> \<le> card B" for c sorry 

  have "\<bar>M1.variance Y - M2.variance Y\<bar> = \<bar>M1.expectation (\<lambda>\<omega>. Y \<omega> ^2) - 
    M1.expectation Y^2 - (M2.expectation (\<lambda>\<omega>. Y \<omega> ^2) - M2.expectation Y^2)\<bar>"
    unfolding M1_def M2_def
    by (intro arg_cong[where f="abs"] arg_cong2[where f="(-)"] measure_pmf.variance_eq
        int_Y int_Y_sq)
  also have "... \<le> \<bar>M1.expectation (\<lambda>\<omega>. Y \<omega> ^2) - M2.expectation (\<lambda>\<omega>. Y \<omega>^2)\<bar> + 
    \<bar>M1.expectation Y^2 - M2.expectation Y^2\<bar>"
    by simp
  also have "... = \<bar>M1.expectation (\<lambda>\<omega>. Y \<omega> ^2) - M2.expectation (\<lambda>\<omega>. Y \<omega>^2)\<bar> + 
    \<bar>M1.expectation Y - M2.expectation Y\<bar>*\<bar>M1.expectation Y + M2.expectation Y\<bar>"
    by (simp add:power2_eq_square algebra_simps abs_mult[symmetric])
  also have "... \<le> (2^(k+2)+4) * \<gamma> * card B^2 + (2 * \<gamma> * card B) * (\<bar>M1.expectation Y\<bar> + \<bar>M2.expectation Y\<bar>)"
    using \<gamma>_nonneg
    by (intro add_mono mult_mono Y_sq_exp_diff Y_exp_diff_2) auto
  also have "... \<le> (2^(k+2)+4) * \<gamma> * card B^2 + (2 * \<gamma> * card B) * (real (card B) + real (card B))"
    unfolding M1_def M2_def using \<gamma>_nonneg
    by (intro add_mono mult_left_mono Y_exp_rough_bound) auto
  also have "... = (2^(k+2)+8) * \<gamma> * card B^2"
    by (simp add:algebra_simps power2_eq_square)
  also have "... \<le> \<epsilon>^2" sorry
  finally show ?B 
    unfolding M1_def M2_def by simp
qed




end