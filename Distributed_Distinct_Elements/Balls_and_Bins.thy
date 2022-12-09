theory Balls_and_Bins
  imports DDE_Preliminary 
    "HOL-Combinatorics.Stirling"
    "HOL-Computational_Algebra.Polynomial"
    "Discrete_Summation.Factorials" 
    "Twelvefold_Way.Twelvefold_Way_Entry3"
begin

locale balls_and_bins_indep =
  fixes R B
  assumes "finite R"
  assumes "finite B"
begin

definition "M = measure_pmf (prod_pmf R (\<lambda>_. pmf_of_set B))"

sublocale prob_space "M"
  unfolding M_def using prob_space_measure_pmf by auto

definition Y where "Y \<omega> = real (card ((\<lambda>x. \<omega> x) ` R))"
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

lemma hit_count_moments:
  assumes "finite R" "finite B" "s \<le> k"
  assumes "prob_space.k_wise_indep_vars (measure_pmf p) k (\<lambda>_. discrete) f R"
  assumes "\<And>x. x \<in> R \<Longrightarrow> map_pmf (f x) p = pmf_of_set B"
  assumes "j \<in> B"
  defines "Z \<equiv> (\<lambda>\<omega>. real (card {i. i \<in> R \<and> f i \<omega> = j}))"
  shows "measure_pmf.expectation p (\<lambda>\<omega>. Z \<omega>^s) = 
    (\<Sum>i=0..s. real (Stirling s i) * (1 / card B)^i * ffact i (card R))" (is "?L = ?R")
proof -
  define W where "W = (\<lambda>i \<omega>. of_bool (f i \<omega> = j) :: real)"
  define \<alpha> where "\<alpha> = 1 / real (card B)"

  have Z_eq: "Z \<omega> = (\<Sum>i \<in> R. W i \<omega>)" for \<omega>
    using assms(1) unfolding Z_def W_def
    by (simp add:of_bool_def sum.If_cases Int_def)

  have Z_pow_eq: "(Z \<omega>)^s = (\<Sum>xs| set xs \<subseteq> R \<and> length xs = s. (\<Prod>j \<leftarrow> xs. W j \<omega>))" for \<omega>
    unfolding Z_eq sum_power_distrib[OF assms(1)] by simp

  have e:"prob_space.k_wise_indep_vars (measure_pmf p) k (\<lambda>_. borel) W R" 
    unfolding W_def 
    by (intro prob_space.k_wise_indep_vars_compose[OF _ assms(4)] prob_space_measure_pmf) simp

  have c:"prob_space.indep_vars (measure_pmf p) (\<lambda>_. borel) W I" if "I \<subseteq> R" "card I \<le> k" for I
    using that finite_subset assms(1)
    by (intro prob_space.k_wise_indep_vars_subset[OF _ e] prob_space_measure_pmf) auto

  have d: "integrable (measure_pmf p) (W x)" for x
    unfolding W_def
    by (intro integrable_pmf_iff_bounded[where C="1"]) simp

  have e: "measure_pmf.expectation p (W x) = \<alpha>" (is "?L2 = _") if "x \<in> R" for x
  proof -
    have "?L2 = measure_pmf.expectation p (indicator {\<omega>. f x \<omega> = j})"
      unfolding W_def indicator_def by simp
    also have "... = measure_pmf.prob p {\<omega>. f x \<omega> = j}"
      by simp
    also have "... = measure_pmf.prob (map_pmf (f x) p) {j}"
      by (subst measure_map_pmf) (simp add:vimage_def)
    also have "... = measure_pmf.prob (pmf_of_set B) {j}"
      using that by (subst assms(5)) auto
    also have "... = 1/card B"
      using assms(2,6) by (subst measure_pmf_of_set) auto
    also have "... = \<alpha>"
      unfolding \<alpha>_def by simp
    finally show ?thesis by simp
  qed

  have a:
    "measure_pmf.expectation p (\<lambda>\<omega>. (\<Prod>j \<leftarrow> xs. W j \<omega>)) = \<alpha>^ card (set xs)" (is "?L1 = ?R1")
    if "set xs \<subseteq> R" and "length xs \<le> k" for xs
  proof -
    have "?L1 = measure_pmf.expectation p (\<lambda>\<omega>. \<Prod>x\<in>set xs. W x \<omega> ^ count_list xs x)"
      by (simp add: prod_list_eval)
    also have "... = measure_pmf.expectation p (\<lambda>\<omega>. \<Prod>x\<in>set xs. W x \<omega>)"
      unfolding W_def using count_list_gr_1
      by (intro arg_cong[where f="measure_pmf.expectation p"] ext prod.cong) force+
    also have "... = (\<Prod>x\<in>set xs. measure_pmf.expectation p (\<lambda>\<omega>. W x \<omega>))"
      using that(1) order_trans[OF card_length that(2)]
      by (intro prob_space.indep_vars_lebesgue_integral[OF prob_space_measure_pmf] c d) auto
    also have "... = (\<Prod>x\<in>set xs. \<alpha>)" 
      using that by (intro prod.cong e) auto 
    also have "... = ?R1" by simp
    finally show ?thesis by simp
  qed

  have b:"finite {xs. set xs \<subseteq> R \<and> length xs = s \<and> card (set xs) = i}" for i
    by (intro finite_subset[OF _ finite_lists_length_eq[OF assms(1), where n="s"]]) auto  

  have "?L = (\<Sum>xs| set xs \<subseteq> R \<and> length xs = s. measure_pmf.expectation p (\<lambda>\<omega>. (\<Prod>j \<leftarrow> xs. W j \<omega>)))"
    unfolding Z_pow_eq W_def
    by (intro Bochner_Integration.integral_sum integrable_pmf_iff_bounded[where C="1"] prod_list_le_1_iff)
     auto
  also have "... = (\<Sum>xs| set xs \<subseteq> R \<and> length xs = s. \<alpha>^ card (set xs))"
    using assms(3) by (intro sum.cong a) auto
  also have "... = (\<Sum>xs \<in> (\<Union>i \<in> {0..s}.{ xs. set xs \<subseteq> R \<and> length xs = s \<and> card (set xs) = i}). \<alpha>^ card (set xs))"
    using card_length by (intro sum.cong) auto
  also have "... = (\<Sum>i=0..s. (\<Sum>xs | set xs \<subseteq> R \<and> length xs = s \<and> card(set xs) = i.  \<alpha>^ card (set xs)))"
    using b by (subst sum.UNION_disjoint[symmetric]) auto 
  also have "... = (\<Sum>i=0..s. (\<Sum>xs | set xs \<subseteq> R \<and> length xs = s \<and> card(set xs) = i.  \<alpha>^i))"
    by auto
  also have "... = (\<Sum>i=0..s. \<alpha>^i * card {xs. set xs \<subseteq> R \<and> length xs = s \<and> card(set xs) = i})"
    by (intro sum.cong) auto
  also have "... = ?R"
    unfolding \<alpha>_def
    by (subst card_lists_with_image_size[OF assms(1)]) (simp add:algebra_simps)
  finally show ?thesis by simp
qed


(* First step is to reduce this to a bernoulli problem *)
(* Z = \sum_R [f r = j] 
  E Z^s = \sum_{r1,..,rs} E [f r1=j][f r2=j]..[f rs=j]
        = \sum_{r1,..,rs} E 

  card R * (card R-1) * .. * (card R - i +1)
  -----------------------------------------   \<le> 
  card B * (card B) * .. * (card B) 

*)


thm monomial_ffact
(*
Using this theorem we can bound the expectation of Z^s \<le> (card R/card B)^s
*)


lemma
  assumes "finite R" "finite B"
  assumes "prob_space.k_wise_indep_vars (measure_pmf p1) (2*k+2) (\<lambda>_. discrete) f1 R"
  assumes "prob_space.k_wise_indep_vars (measure_pmf p2) (2*k+2) (\<lambda>_. discrete) f2 R"
  assumes "\<And>x. x \<in> R \<Longrightarrow> map_pmf (f1 x) p1 = pmf_of_set B"
  assumes "\<And>x. x \<in> R \<Longrightarrow> map_pmf (f2 x) p2 = pmf_of_set B"
  defines "Y1 \<equiv> (\<lambda>\<omega>. real (card ((\<lambda>x. f1 x \<omega>) ` R)))"
  defines "Y2 \<equiv> (\<lambda>\<omega>. real (card ((\<lambda>x. f2 x \<omega>) ` R)))"
  shows 
    exp_approx: "\<bar>measure_pmf.expectation p1 Y1 - measure_pmf.expectation p2 Y2\<bar> \<le> 
                    \<epsilon> * measure_pmf.expectation p2 Y2" (is "?A") and
    var_approx: "\<bar>measure_pmf.variance p1 Y1 - measure_pmf.variance p2 Y2\<bar> \<le> \<epsilon>\<^sup>2" (is "?B")
proof -
  define M1 where "M1 = measure_pmf p1"
  define M2 where "M2 = measure_pmf p2"

  interpret M1: prob_space "M1"
    unfolding M1_def by (rule prob_space_measure_pmf)

  interpret M2: prob_space "M2"
    unfolding M2_def by (rule prob_space_measure_pmf)


  define I :: "real set" where "I = real ` {1..k}"
  define \<phi> :: "real \<Rightarrow> real" where "\<phi> = (\<lambda>x. min x 1)"

  define fp :: "real poly" where "fp = 1 - smult ((-1)^k / real (fact k)) (\<Prod>y \<in> I. [:- y, 1:])"
  define f where "f = poly fp"
  define g where "g = (\<lambda>x. \<phi> x - f x)"
  have \<phi>_exp: "\<phi> x = f x + g x" for x
    unfolding g_def by simp

  have k_gt_1: "k \<ge> 1" sorry
  have k_ge_2: "k \<ge> 2" sorry


  have fin_I: "finite I"
    unfolding I_def by (intro finite_imageI) simp
  hence "poly (\<Prod>y\<in>I. [:- y, 1:]) x = prod ((-) x) I" for x
    by (induction I rule:finite_induct) (simp add:algebra_simps)+
  hence f_eval: "f x = 1- (-1)^k / real (fact k) * (\<Prod>y \<in> I. (x - y))" for x
    unfolding fp_def f_def by simp 

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
      using k_gt_1 by (subst Icc_eq_insert_lb_nat[OF k_gt_1]) (simp add:mult.commute numeral_eq_Suc)
    also have "... = 1 / real (fact k) * 
      \<bar>(x-1)*(\<Prod>y \<in> {2..k}. (x - y)) - (x-(k+1))*(\<Prod>y \<in> {2..k}. (x - y))\<bar>"
      by simp
    also have "... = 1 / real (fact k) * k * \<bar>(\<Prod>y \<in> {2..k}. (x - y))\<bar>"
      by (simp add:algebra_simps abs_mult)
    also have "... = 1 / real (fact (k-1)) * (\<Prod>y \<in> {2..k}. \<bar>x - y\<bar>)"
      using k_gt_1 abs_prod by (subst fact_reduce) auto 
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
    using prod_real 
    unfolding I_def fact_prod by simp

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

  define Z1 where "Z1 = (\<lambda>i \<omega>. real (card { j . j \<in> R \<and> f1 j \<omega> = i}))"
  define Z2 where "Z2 = (\<lambda>i \<omega>. real (card { j . j \<in> R \<and> f2 j \<omega> = i}))"

  have z_moment_eq: 
    "M1.expectation (\<lambda>\<omega>. Z1 i \<omega>^s) = M2.expectation (\<lambda>\<omega>. Z2 i \<omega>^s)" 
    if "s \<le> 2*k+2" "i \<in> B" for s i
    unfolding Z1_def Z2_def M1_def M2_def using assms that by (simp add:hit_count_moments)

  have z1_any_integrable:
    "integrable M1 (\<lambda>\<omega>. f (Z1 i \<omega>))" for i and f :: "real \<Rightarrow> real"
    unfolding M1_def Z1_def using assms(1) card_mono
    by (intro integrable_pmf_iff_bounded[where C="Max (abs ` f ` real ` {..card R})"])
     fastforce+ 

  have z2_any_integrable:
    "integrable M2 (\<lambda>\<omega>. f (Z2 i \<omega>))" for i and f :: "real \<Rightarrow> real"
    unfolding M2_def Z2_def using assms(1) card_mono
    by (intro integrable_pmf_iff_bounded[where C="Max (abs ` f ` real ` {..card R})"])
     fastforce+ 

  have Z_poly_eq: "M1.expectation (\<lambda>\<omega>. poly f (Z1 i \<omega>)) = M2.expectation (\<lambda>\<omega>. poly f (Z2 i \<omega>))"
    (is "?L = ?R") 
    if "i \<in> B" "degree f \<le> 2*k+1" for f i
  proof -
    have "?L = (\<Sum>j\<le>degree f. M1.expectation (\<lambda>\<omega>. poly.coeff f j * Z1 i \<omega> ^ j))"
      unfolding poly_altdef
      by (intro Bochner_Integration.integral_sum integrable_mult_right z1_any_integrable)
    also have "... = (\<Sum>j\<le>degree f. poly.coeff f j * M1.expectation (\<lambda>\<omega>. Z1 i \<omega> ^ j))"
      by (intro sum.cong z_moment_eq Bochner_Integration.integral_mult_right z1_any_integrable)
       simp 
    also have "... = (\<Sum>j\<le>degree f. poly.coeff f j * M2.expectation (\<lambda>\<omega>. Z2 i \<omega> ^ j))"
      using that by (intro sum.cong arg_cong2[where f="(*)"] z_moment_eq) auto
    also have "... = (\<Sum>j\<le>degree f. M2.expectation (\<lambda>\<omega>. poly.coeff f j * Z2 i \<omega> ^ j))"
      by (intro sum.cong) auto 
    also have "... = ?R"
      unfolding poly_altdef by (intro Bochner_Integration.integral_sum[symmetric] 
          integrable_mult_right z2_any_integrable) 
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

  have z1_g_bound: "\<bar>M1.expectation (\<lambda>\<omega>. g (Z1 i \<omega>))\<bar> \<le> undefined" (is "?L1 \<le> undefined") for i
  proof -
    have max_Z1: "M1.prob {\<omega>. real x \<le> Z1 i \<omega>} = 0" if "x > card R" for x 
    proof -
      have "Z1 i \<omega> \<le> card R" for \<omega> 
        using card_mono[OF assms(1)] unfolding Z1_def by auto 
      hence "Z1 i \<omega> < x" for \<omega>
        by (metis order_le_less_trans less_imp_of_nat_less that)
      hence "{\<omega>. real x \<le> Z1 i \<omega>} \<subseteq> {}"
        using linorder_not_le by auto
      thus ?thesis by simp
    qed

    have "?L1 \<le> M1.expectation (\<lambda>\<omega>. \<bar>g (Z1 i \<omega>)\<bar>)"
      by (intro integral_abs_bound)
    also have "... = (\<Sum>y\<in>real ` {..card R}. \<bar>g y\<bar> * M1.prob {\<omega>. Z1 i \<omega> = y})"
      unfolding Z1_def using assms(1)
      by (intro M1.pmf_exp_of_fin_function[OF M1_def]) (auto intro: imageI card_mono)
    also have "... = (\<Sum>y\<in>{..card R}. \<bar>g (real y)\<bar> * M1.prob {\<omega>. Z1 i \<omega> = real y})"
      by (subst sum.reindex) (auto simp add:comp_def)
    also have "... = (\<Sum>y\<in>{..card R}. \<bar>g (real y)\<bar> * 
      (M1.prob ({\<omega>. Z1 i \<omega> = real y} \<union> {\<omega>. Z1 i \<omega> > real y}) - M1.prob {\<omega>. Z1 i \<omega> > real y}))"
      unfolding M1_def by (subst measure_Union) auto
    also have "... = (\<Sum>y\<in>{..card R}. \<bar>g (real y)\<bar> * 
      (M1.prob ({\<omega>. Z1 i \<omega> \<ge> real y}) - M1.prob {\<omega>. Z1 i \<omega> > real y}))"
      by (intro sum.cong arg_cong2[where f="(*)"] arg_cong2[where f="(-)"] arg_cong[where f="M1.prob"])
       auto
    also have "... = (\<Sum>y\<in>{..card R}. \<bar>g (real y)\<bar> * M1.prob {\<omega>. Z1 i \<omega> \<ge> real y}) - 
       (\<Sum>y\<in>{..card R}. \<bar>g (real y)\<bar> * M1.prob {\<omega>. Z1 i \<omega> > real y})"
      by (simp add:algebra_simps sum_subtractf)
    also have "... = (\<Sum>y\<in>{..card R}. \<bar>g (real y)\<bar> * M1.prob {\<omega>. Z1 i \<omega> \<ge> real y}) - 
       (\<Sum>y\<in>{..card R}. \<bar>g (real y)\<bar> * M1.prob {\<omega>. Z1 i \<omega> \<ge> real (y+1)})"
      unfolding Z1_def
      by (intro sum.cong arg_cong2[where f="(-)"] arg_cong2[where f="(*)"] arg_cong[where f="M1.prob"])
       auto
    also have "... = (\<Sum>y\<in>{..card R}. \<bar>g (real y)\<bar> * M1.prob {\<omega>. Z1 i \<omega> \<ge> real y}) - 
       (\<Sum>y\<in>Suc ` {..card R}. \<bar>g (real y - 1)\<bar> * M1.prob {\<omega>. Z1 i \<omega> \<ge> real y})"
      by (subst sum.reindex) (auto simp add:comp_def)
    also have "... = (\<Sum>y\<in>{..card R}. \<bar>g (real y)\<bar> * M1.prob {\<omega>. Z1 i \<omega> \<ge> real y}) - 
       (\<Sum>y\<in>{1..card R}. \<bar>g (real y - 1)\<bar> * M1.prob {\<omega>. Z1 i \<omega> \<ge> real y})" 
      using max_Z1 image_Suc_atMost
      by (intro arg_cong2[where f="(-)"] sum.mono_neutral_cong) auto 
    also have "... = (\<Sum>y\<in>{k+1..card R}. \<bar>g (real y)\<bar> * M1.prob {\<omega>. Z1 i \<omega> \<ge> real y}) - 
       (\<Sum>y\<in>{k+1..card R}. \<bar>g (real y - 1)\<bar> * M1.prob {\<omega>. Z1 i \<omega> \<ge> real y})"
      using k_gt_1
      by (intro arg_cong2[where f="(-)"] sum.mono_neutral_cong_right ballI g_eq_0_iff_2)
        auto 
    also have "... = (\<Sum>y\<in>{k+1..card R}. (\<bar>g (real y)\<bar> - \<bar>g (real y-1)\<bar>) * M1.prob {\<omega>. Z1 i \<omega> \<ge> real y})"
      by (simp add:algebra_simps sum_subtractf)
    also have "... \<le> (\<Sum>y\<in>{k+1..card R}. \<bar>g (real y)- g (real y-1)\<bar> * M1.prob {\<omega>. Z1 i \<omega> \<ge> real y})" 
      by (intro sum_mono mult_right_mono) auto

    also have "... \<le> undefined" sorry
    finally show ?thesis by simp
  qed


  have Z_poly_diff: 
    "M1.expectation (\<lambda>\<omega>. \<phi> (Z1 i \<omega>)) - M2.expectation (\<lambda>\<omega>. \<phi> (Z2 i \<omega>)) \<le> 3" (is "?L \<le> 3") 
    if "i \<in> B" for i
  proof -
    have "?L = M1.expectation (\<lambda>\<omega>. f (Z1 i \<omega>)) + M1.expectation (\<lambda>\<omega>. g (Z1 i \<omega>)) -
      M2.expectation (\<lambda>\<omega>. f (Z2 i \<omega>)) - M2.expectation (\<lambda>\<omega>. g (Z2 i \<omega>))" 
      using z1_any_integrable z2_any_integrable unfolding \<phi>_exp by simp
    also have "... = M1.expectation (\<lambda>\<omega>. g (Z1 i \<omega>)) + (- M2.expectation (\<lambda>\<omega>. g (Z2 i \<omega>)))"
      unfolding f_def using that deg_fp by (subst Z_poly_eq) auto
    also have "... \<le> abs (M1.expectation (\<lambda>\<omega>. g (Z1 i \<omega>))) + abs (M2.expectation (\<lambda>\<omega>. g (Z2 i \<omega>)))"
      by (intro add_mono) auto
    also have "... \<le> 3" sorry

    finally show ?thesis by simp
  qed



  show ?A sorry
  show ?B sorry
qed




end