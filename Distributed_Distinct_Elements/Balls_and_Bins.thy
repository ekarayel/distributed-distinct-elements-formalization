theory Balls_and_Bins
  imports DDE_Preliminary 
    "HOL-Combinatorics.Stirling"
    "HOL-Computational_Algebra.Polynomial"
    "Discrete_Summation.Factorials" 
    "Twelvefold_Way.Twelvefold_Way_Entry3"
    "Basel_Sum_Approx"
begin

(* TODO: This is modified from Frequenct_Moment_k *)
lemma power_diff_sum:
  fixes a b :: "'a :: {comm_ring_1,power}"
  shows "a^k - b^k = (a-b) * (\<Sum>i = 0..<k. a ^ i * b ^ (k - 1 - i))" (is "?lhs = ?rhs")
proof (cases "k > 0")
  case True
  have insert_lb: "m < n \<Longrightarrow> insert m {Suc m..<n} = {m..<n}" for m n :: nat
    by auto

  have "?rhs = sum (\<lambda>i. a * (a^i * b^(k-1-i))) {0..<k} - 
    sum (\<lambda>i. b * (a^i * b^(k-1-i))) {0..<k}"
    by (simp add: sum_distrib_left[symmetric] algebra_simps)
  also have "... = sum ((\<lambda>i. (a^i * b^(k-i))) \<circ> (\<lambda>i. i+1)) {0..<k} - 
    sum (\<lambda>i. (a^i * (b^(1+(k-1-i))))) {0..<k}"
    by (simp add:algebra_simps)
  also have "... = sum ((\<lambda>i. (a^i * b^(k-i))) \<circ> (\<lambda>i. i+1)) {0..<k} - 
    sum (\<lambda>i. (a^i * b^(k-i))) {0..<k}"
    by (intro arg_cong2[where f="(-)"] sum.cong arg_cong2[where f="(*)"] 
        arg_cong2[where f="(\<lambda>x y. x ^ y)"]) auto
  also have "... = sum (\<lambda>i. (a^i * b^(k-i))) (insert k {1..<k}) - 
    sum (\<lambda>i. (a^i * b^(k-i))) (insert 0 {Suc 0..<k})"
    using True
    by (subst sum.reindex[symmetric], simp, subst insert_lb, auto)
  also have "... = ?lhs"
    by simp
  finally show ?thesis by presburger
next
  case False
  hence "k=0" by simp
  thus ?thesis by simp
qed

lemma power_diff_est:
  assumes "(a :: real) \<ge> b"
  assumes "b \<ge> 0"
  shows "a^k - b^k \<le> (a-b) * k * a^(k-1)"
proof -
  have "a^k - b^k = (a-b) * (\<Sum>i = 0..<k. a ^ i * b ^ (k - 1 - i))"
    by (rule power_diff_sum)
  also have "... \<le> (a-b) * (\<Sum>i = 0..<k. a^i * a^(k-1-i))"
    using assms by (intro mult_left_mono sum_mono mult_right_mono power_mono, auto)
  also have "... = (a-b) * (k * a^(k-1))"
    by (simp add:power_add[symmetric])
  finally show ?thesis by simp
qed

lemma power_diff_est_2:
  assumes "(a :: real) \<ge> b"
  assumes "b \<ge> 0"
  shows "a^k - b^k \<ge> (a-b) * k * b^(k-1)"
proof -
  have "(a-b) * k * b^(k-1) = (a-b) * (\<Sum>i=0..<k. b^i * b^(k-1-i))"
    by (simp add:power_add[symmetric])
  also have "... \<le>  (a-b)* (\<Sum>i=0..<k. a^i * b^(k-1-i))"
    using assms
    by (intro mult_left_mono sum_mono mult_right_mono power_mono) auto
  also have "... = a^k - b^k"
    by (rule power_diff_sum[symmetric])
  finally show ?thesis by simp
qed

lemma of_bool_prod:
  assumes "finite R" 
  shows "(\<Prod> j \<in> R. of_bool(f j)) = (of_bool(\<forall>j \<in> R. f j) :: real)"
  using assms by(induction R rule:finite_induct) auto


lemma 
  fixes R :: "'a set" and B :: "'b set"
  assumes "finite R"
  assumes "finite B" "card B \<ge> 1"
  defines "Y \<equiv> (\<lambda>\<omega>. real (card (\<omega> ` R)))"
  defines "p \<equiv> prod_pmf R (\<lambda>_. pmf_of_set B)"
  shows exp_balls_and_bins: 
      "measure_pmf.expectation p Y = real (card B) * (1 - (1 - 1 / real (card B))^(card R))" 
      (is "?AL = ?AR")
    and var_balls_and_bins: 
      "measure_pmf.variance p Y \<le> card R * (real (card R) - 1) / card B"
      (is "?BL \<le> ?BR")
proof -
  let ?b = "real (card B)"
  let ?r = "card R"
  define Z :: "'b \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> real" where "Z = (\<lambda>i \<omega>. of_bool(i \<notin> \<omega> ` R))"
  define \<alpha> where "\<alpha> = (1 - 1 / ?b)^?r"
  define \<beta> where "\<beta> = (1 - 2 / ?b)^?r"

  have "card (B \<times> B \<inter> {x. fst x = snd x}) = card ((\<lambda>x. (x,x)) ` B)"
    by (intro arg_cong[where f="card"]) auto
  also have "... = card B"
    by (intro card_image, simp add:inj_on_def)
  finally have d: "card (B \<times> B \<inter> {x. fst x = snd x}) = card B"
    by simp
  hence count_1: "real (card (B \<times> B \<inter> {x. fst x = snd x})) = card B"
    by simp

  have "card B + card (B \<times> B \<inter> -{x. fst x = snd x}) = 
    card (B \<times> B \<inter> {x. fst x = snd x}) + card (B \<times> B \<inter> -{x. fst x = snd x})"
    by (subst d) simp
  also have "... = card ((B \<times> B \<inter> {x. fst x = snd x}) \<union> (B \<times> B \<inter> -{x. fst x = snd x}))"
    using finite_subset[OF _ finite_cartesian_product[OF assms(2,2)]]
    by (intro card_Un_disjoint[symmetric]) auto
  also have "... = card (B \<times> B)"
    by (intro arg_cong[where f="card"]) auto
  also have "... = card B^2"
    unfolding card_cartesian_product by (simp add:power2_eq_square)
  finally have "card B + card (B \<times> B \<inter> -{x. fst x = snd x}) = card B^2" by simp
  
  hence count_2: "real (card (B \<times> B \<inter> -{x. fst x = snd x})) = real (card B)^2 - card B"
    by (simp add:algebra_simps flip: of_nat_add of_nat_power) 

  have B_ne: "B \<noteq> {}" 
    using assms(3) by auto
  hence set_pmf_p: "set_pmf p = (R \<rightarrow>\<^sub>E B)"
    unfolding p_def set_prod_pmf[OF assms(1)]
    using set_pmf_of_set[OF _ assms(2)] by simp
  hence "finite (set_pmf p)" 
    using assms(1,2) by (auto intro!:finite_PiE)
  hence int: "integrable (measure_pmf p) f" 
    for f :: "('a \<Rightarrow> 'b) \<Rightarrow> real"
    by (intro integrable_measure_pmf_finite) simp

  have a:"prob_space.indep_vars (measure_pmf p) (\<lambda>i. discrete) (\<lambda>x \<omega>. \<omega> x) R" 
    unfolding p_def using indep_vars_Pi_pmf[OF assms(1)] by metis
  have b: "(\<integral>\<omega>. of_bool(\<omega> ` R \<subseteq> A) \<partial>p) = (real (card (B \<inter> A)) / real (card B))^card R" 
    (is "?L = ?R") for A
  proof -
    have "?L = (\<integral>\<omega>. (\<Prod> j \<in> R. of_bool(\<omega> j \<in> A)) \<partial>p)"
      by (intro arg_cong[where f="measure_pmf.expectation p"] ext)
        (auto simp add: of_bool_prod[OF assms(1)])
    also have "... = (\<Prod> j \<in> R. (\<integral>\<omega>. of_bool(\<omega> j \<in> A) \<partial>p))"
      using assms(1)
      by (intro prob_space.indep_vars_lebesgue_integral[OF prob_space_measure_pmf] int
          prob_space.indep_vars_compose2[OF prob_space_measure_pmf a]) auto
    also have "... = (\<Prod> j \<in> R. (\<integral>\<omega>. of_bool(\<omega> \<in> A) \<partial>(map_pmf (\<lambda>\<omega>. \<omega> j) p)))"
      by simp
    also have "... = (\<Prod> j \<in> R. (\<integral>\<omega>. of_bool(\<omega> \<in> A) \<partial>(pmf_of_set B)))"
      unfolding p_def by (subst Pi_pmf_component[OF assms(1)]) simp
    also have "... = ((\<Sum>\<omega>\<in>B. of_bool (\<omega> \<in> A)) / real (card B)) ^ card R"
      by (simp add: integral_pmf_of_set[OF B_ne assms(2)])
    also have "... = ?R"
      unfolding of_bool_def sum.If_cases[OF assms(2)] by simp
    finally show ?thesis by simp
  qed

  have Z_exp: "(\<integral>\<omega>. Z i \<omega> \<partial>p) = \<alpha>" if "i \<in> B" for i
  proof -
    have "real (card (B \<inter> -{i})) = real (card (B - {i}))"
      by (intro arg_cong[where f="\<lambda>x. real (card x)"]) auto
    also have "... = real (card B - card {i})"
      using that by (subst card_Diff_subset)  auto
    also have "... = real (card B) - real (card {i})"
      using assms(2) that by (intro of_nat_diff card_mono) auto
    finally have c: "real (card (B \<inter> -{i})) = real (card B) - 1"
      by simp

    have "(\<integral>\<omega>. Z i \<omega> \<partial>p) = (\<integral>\<omega>. of_bool(\<omega> ` R \<subseteq> - {i}) \<partial>p)"
      unfolding Z_def by simp
    also have "... = (real (card (B \<inter> -{i})) / real (card B))^card R"
      by (intro b)
    also have "... = ((real (card B) -1) / real (card B))^card R"
      by (subst c) simp
    also have "... = \<alpha>"
      unfolding \<alpha>_def using assms(3)
      by (simp add:divide_eq_eq diff_divide_distrib)
    finally show ?thesis 
      by simp
  qed

  have Z_prod_exp: "(\<integral>\<omega>. Z i \<omega> * Z j \<omega> \<partial>p) = (if i = j then \<alpha> else \<beta>)" if "i \<in> B" "j \<in> B" for i j
  proof -
    have "real (card (B \<inter> -{i,j})) = real (card (B - {i,j}))"
      by (intro arg_cong[where f="\<lambda>x. real (card x)"]) auto
    also have "... = real (card B - card {i,j})"
      using that by (subst card_Diff_subset)  auto
    also have "... = real (card B) - real (card {i,j})"
      using assms(2) that by (intro of_nat_diff card_mono) auto
    finally have c: "real (card (B \<inter> -{i,j})) = real (card B) - card {i,j}"
      by simp

    have "(\<integral>\<omega>. Z i \<omega> * Z j \<omega> \<partial>p) = (\<integral>\<omega>. of_bool(\<omega> ` R \<subseteq> - {i,j}) \<partial>p)"
      unfolding Z_def of_bool_conj[symmetric]
      by (intro arg_cong[where f="measure_pmf.expectation p"] ext) auto
    also have "... = (real (card (B \<inter> -{i,j})) / real (card B))^card R"
      by (intro b)
    also have "... = ((real (card B) - card {i,j}) / real (card B))^card R"
      by (subst c) simp
    also have "... = (if i = j then \<alpha> else \<beta>)" 
      unfolding \<alpha>_def \<beta>_def using assms(3)
      by (simp add:divide_eq_eq diff_divide_distrib)
    finally show ?thesis by simp
  qed

  have Y_eq: "Y \<omega> = (\<Sum>i \<in> B. 1 - Z i \<omega>)" if "\<omega> \<in> set_pmf p" for \<omega> 
  proof -
    have "set_pmf p \<subseteq> Pi R (\<lambda>_. B)"
      using set_pmf_p by (simp add:PiE_def)
    hence "\<omega> ` R \<subseteq> B"
      using that by auto
    hence "Y \<omega> = card (B \<inter> \<omega> ` R)"
      unfolding Y_def using Int_absorb1 by metis
    also have "... = (\<Sum> i \<in> B. of_bool(i \<in> \<omega> ` R))"
      unfolding of_bool_def sum.If_cases[OF assms(2)] by(simp)
    also have "... = (\<Sum> i \<in> B. 1 - Z i \<omega>)"
      unfolding Z_def by (intro sum.cong) (auto simp add:of_bool_def)
    finally show "Y \<omega> = (\<Sum>i \<in> B. 1 - Z i \<omega>)" by simp
  qed

  have Y_sq_eq: "(Y \<omega>)\<^sup>2 = (\<Sum>(i,j) \<in> B \<times> B. 1 - Z i \<omega> - Z j \<omega> + Z i \<omega> * Z j \<omega>)"
    if "\<omega> \<in> set_pmf p" for \<omega>
    unfolding Y_eq[OF that] power2_eq_square sum_product sum.cartesian_product
    by (intro sum.cong) (auto simp add:algebra_simps)

  have "measure_pmf.expectation p Y = (\<integral>\<omega>. (\<Sum>i \<in> B. 1 - Z i \<omega>) \<partial> p)"
    using Y_eq by (intro Bochner_Integration.integral_cong_AE AE_pmfI) auto
  also have "... = (\<Sum>i \<in> B. 1 - (\<integral>\<omega>. Z i \<omega> \<partial>p))"
    using int by simp
  also have "... = ?b * (1 - \<alpha>)"
    using Z_exp by simp
  also have "... = ?AR"
    unfolding \<alpha>_def by simp
  finally show "?AL = ?AR" by simp

  have "measure_pmf.variance p Y = (\<integral>\<omega>. Y \<omega>^2 \<partial>p) - (\<integral>\<omega>. Y \<omega> \<partial>p)^2"
    using int by (subst measure_pmf.variance_eq) auto
  also have "... = 
    (\<integral>\<omega>. (\<Sum>i \<in> B \<times> B. 1 - Z (fst i) \<omega> - Z (snd i) \<omega> + Z (fst i) \<omega> * Z (snd i) \<omega>) \<partial> p) - 
    (\<integral>\<omega>. (\<Sum>i \<in> B. 1 - Z i \<omega>) \<partial>p)^2"
    using Y_eq Y_sq_eq
    by (intro arg_cong2[where f="(-)"] arg_cong[where f="(\<lambda>x. x^2)"] 
        Bochner_Integration.integral_cong_AE AE_pmfI) (auto simp add:case_prod_beta)
  also have "... = 
    (\<Sum>i \<in> B \<times> B. (\<integral>\<omega>. (1 - Z (fst i) \<omega> - Z (snd i) \<omega> + Z (fst i) \<omega> * Z (snd i) \<omega>) \<partial> p)) -
    (\<Sum>i \<in> B. (\<integral>\<omega>. (1 - Z i \<omega>) \<partial> p))^2"
    by (intro arg_cong2[where f="(-)"] arg_cong[where f="(\<lambda>x. x^2)"] 
        Bochner_Integration.integral_sum int)
  also have "... = 
    (\<Sum>i \<in> B \<times> B. (\<integral>\<omega>. (1 - Z (fst i) \<omega> - Z (snd i) \<omega> + Z (fst i) \<omega> * Z (snd i) \<omega>) \<partial> p)) -
    (\<Sum>i \<in> B \<times> B. (\<integral>\<omega>. (1 - Z (fst i) \<omega>) \<partial> p) * (\<integral>\<omega>. (1 - Z (snd i) \<omega>) \<partial> p))"
    unfolding power2_eq_square sum_product sum.cartesian_product
    by (simp add:case_prod_beta)
  also have "... = (\<Sum>(i,j) \<in> B \<times> B. (\<integral>\<omega>. (1 - Z i \<omega> - Z j \<omega> + Z i \<omega> * Z j \<omega>) \<partial> p) -
    (\<integral>\<omega>. (1 - Z i \<omega>) \<partial> p) * (\<integral>\<omega>. (1 - Z j \<omega>) \<partial> p))"
    by (subst sum_subtractf[symmetric], simp add:case_prod_beta)
  also have "... = (\<Sum>(i,j) \<in> B \<times> B. (\<integral>\<omega>. Z i \<omega> * Z j \<omega> \<partial> p) -(\<integral>\<omega>. Z i \<omega> \<partial> p) * (\<integral> \<omega>. Z j \<omega> \<partial>p))"
    using int by (intro sum.cong refl) (simp add:algebra_simps case_prod_beta)
  also have "... = (\<Sum>i \<in> B \<times> B. (if fst i = snd i then \<alpha> - \<alpha>^2 else \<beta> - \<alpha>^2))"
    by (intro sum.cong refl) (simp add:Z_exp Z_prod_exp mem_Times_iff case_prod_beta power2_eq_square)
  also have "... = ?b * (\<alpha> - \<alpha>\<^sup>2) + (?b^2 - card B) * (\<beta> - \<alpha>\<^sup>2)"
    using count_1 count_2 finite_cartesian_product assms(2) by (subst sum.If_cases) auto
  also have "... = ?b^2 * (\<beta> - \<alpha>\<^sup>2) + ?b * (\<alpha> - \<beta>)"
    by (simp add:algebra_simps)
  also have "... = ?b * ((1 - 1 /?b)^?r - (1-2 /?b)^?r) - ?b^2 * (((1-1 /?b)^2)^?r - (1 - 2 /?b)^?r)"
    unfolding \<beta>_def \<alpha>_def
    by (simp add: power_mult[symmetric] algebra_simps)
  also have "... \<le> card R * (real (card R) - 1)/ card B" (is "?L \<le> ?R")
  proof (cases "?b \<ge> 2")
    case True
    have "?L \<le>
    ?b * (((1 - 1 /?b) - (1-2 /?b)) * ?r * (1-1/?b)^(?r - 1)) - 
    ?b^2 * ((((1-1 /?b)^2) - ((1 - 2 /?b))) * ?r * ((1-2/?b))^(?r - 1))"
    using True
    by (intro diff_mono mult_left_mono power_diff_est_2 power_diff_est divide_right_mono)
      (auto simp add:power2_eq_square algebra_simps)
    also have "... = ?b * ((1/?b) * ?r * (1-1/?b)^(?r - 1)) - ?b^2 * ((1/?b^2)* ?r * ((1-2/?b))^(?r - 1))"
      by (intro arg_cong2[where f="(-)"] arg_cong2[where f="(*)"] refl)
        (auto simp add:algebra_simps power2_eq_square)
    also have "... = ?r * ((1-1/?b)^(?r - 1) - ((1-2/?b))^(?r - 1))"
      by (simp add:algebra_simps)
    also have "... \<le> ?r * (((1-1/?b) - (1-2/?b)) * (?r - 1) * (1-1/?b)^(?r -1 -1))"
      using True by (intro mult_left_mono power_diff_est) (auto simp add:algebra_simps)
    also have "... \<le> ?r * ((1/?b) * (?r - 1) * 1^(?r - 1-1))"
      using True by (intro mult_left_mono mult_mono power_mono) auto
    also have "... =  ?R"
      using assms(2) by auto 
    finally show "?L \<le> ?R" by simp
  next
    case False
    hence "?b = 1" using assms(3) by simp
    thus "?L \<le> ?R" 
      by (cases "card R =0") auto
  qed
  finally show "measure_pmf.variance p Y \<le> card R * (real (card R) - 1)/ card B"
    by simp

qed


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
  assumes fin_R: "finite R"
  assumes fin_B: "finite B"
  assumes indep: "prob_space.k_wise_indep_vars (measure_pmf p) k (\<lambda>_. discrete) (\<lambda>x \<omega>. \<omega> x) R"
  assumes ran: "\<And>x. x \<in> R \<Longrightarrow> map_pmf (\<lambda>\<omega>. \<omega> x) p = pmf_of_set B"
  (* Random variable counting the number of times bin j was hit *)
  defines "Z j \<omega> \<equiv> real (card {i. i \<in> R \<and> \<omega> i = (j::'b)})"
begin

lemma hit_count_prod_exp:
  assumes "j1 \<in> B" "j2 \<in> B" "s+t \<le> k"
  defines "L \<equiv> {(xs,ys). set xs \<subseteq> R \<and> set ys \<subseteq> R \<and> (set xs \<inter> set ys = {} \<or> j1 = j2) \<and> length xs = s \<and> length ys = t}"
  shows "(\<integral>\<omega>. Z j1 \<omega>^s * Z j2 \<omega>^t \<partial>p) = (\<Sum>(xs,ys) \<in> L. (1/real (card B))^(card (set xs \<union> set ys)))"
    (is "?L = ?R")
proof -
  define W1 :: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> real" where "W1 = (\<lambda>i \<omega>. of_bool (\<omega> i = j1) :: real)"
  define W2 :: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> real" where "W2 = (\<lambda>i \<omega>. of_bool (\<omega> i = j2) :: real)"
  define \<tau> :: "'a list \<times> 'a list \<Rightarrow> 'a \<Rightarrow> 'b" where "\<tau> = (\<lambda>l x. if x \<in> set (fst l) then j1 else j2)"

  have \<tau>_check_1: "\<tau> l x = j1" if "x \<in> set (fst l)" and "l \<in> L" for x l 
    using that unfolding \<tau>_def L_def by auto
  have \<tau>_check_2: "\<tau> l x = j2" if "x \<in> set (snd l)" and "l \<in> L" for x l 
    using that unfolding \<tau>_def L_def by auto
  have \<tau>_check_3: "\<tau> l x \<in> B" for x l
    using assms(1,2) unfolding \<tau>_def by simp

  have Z1_eq: "Z j1 \<omega> = (\<Sum>i \<in> R. W1 i \<omega>)" for \<omega>
    using fin_R unfolding Z_def W1_def
    by (simp add:of_bool_def sum.If_cases Int_def)

  have Z2_eq: "Z j2 \<omega> = (\<Sum>i \<in> R. W2 i \<omega>)" for \<omega>
    using fin_R unfolding Z_def W2_def
    by (simp add:of_bool_def sum.If_cases Int_def)

  define \<alpha> where "\<alpha> = 1 / real (card B)"

  have a: "measure_pmf.expectation p (\<lambda>\<omega>. (\<Prod>x\<leftarrow>a. W1 x \<omega>) * (\<Prod>y\<leftarrow>b. W2 y \<omega>)) = 0" (is "?L1 = 0")
    if "x \<in> set a \<inter> set b" "j1 \<noteq> j2" "length a = s" "length b = t" for x a b
  proof -
    have  "(\<Prod>x\<leftarrow>a. W1 x \<omega>) * (\<Prod>y\<leftarrow>b. W2 y \<omega>) = 0" for \<omega>
    proof -
      have "W1 x \<omega> = 0 \<or> W2 x \<omega> = 0" 
        unfolding W1_def W2_def using that by simp
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

  have b: "prob_space.indep_vars p (\<lambda>_. discrete) (\<lambda>i \<omega>. \<omega> i) (set (fst x) \<union> set (snd x))"
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
      by (intro prob_space.k_wise_indep_vars_subset[OF prob_space_measure_pmf indep])
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
      using that by (subst ran) auto
    also have "... = 1/card B"
      using fin_B that by (subst measure_pmf_of_set) auto
    also have "... = \<alpha>"
      unfolding \<alpha>_def by simp
    finally show ?thesis by simp
  qed

  have d: "abs x \<le> 1 \<Longrightarrow> abs y \<le> 1 \<Longrightarrow> abs (x*y) \<le> 1" for x y :: real 
    by (simp add:abs_mult mult_le_one) 
  have e:"(\<And>x. x \<in> set xs \<Longrightarrow> abs x \<le>1) \<Longrightarrow> abs(prod_list xs) \<le> 1 " for xs :: "real list"
    using d by (induction xs, simp, simp)

  have "?L = (\<integral>\<omega>. (\<Sum>j \<in> R. W1 j \<omega>)^s * (\<Sum>j \<in> R. W2 j \<omega>)^t \<partial>p)"
    unfolding Z1_eq Z2_eq by simp
  also have "... = (\<integral>\<omega>. (\<Sum>xs | set xs \<subseteq> R \<and> length xs = s. (\<Prod>x \<leftarrow> xs. W1 x \<omega>)) *
                        (\<Sum>ys | set ys \<subseteq> R \<and> length ys = t. (\<Prod>y \<leftarrow> ys. W2 y \<omega>)) \<partial>p)"
    unfolding sum_power_distrib[OF fin_R] by simp
  also have "... = (\<integral>\<omega>. 
    (\<Sum>l\<in>{xs. set xs \<subseteq> R \<and> length xs = s} \<times> {ys. set ys \<subseteq> R \<and> length ys = t}. 
      (\<Prod>x\<leftarrow>fst l. W1 x \<omega>) * (\<Prod>y\<leftarrow>snd l. W2 y \<omega>)) \<partial>p)"
    by (intro arg_cong[where f="integral\<^sup>L p"]) 
      (simp add: sum_product sum.cartesian_product case_prod_beta) 
  also have "... = (\<Sum>l\<in>{xs. set xs \<subseteq> R \<and> length xs = s} \<times> {ys. set ys \<subseteq> R \<and> length ys = t}.
    (\<integral>\<omega>. (\<Prod>x\<leftarrow>fst l. W1 x \<omega>) * (\<Prod>y\<leftarrow>snd l. W2 y \<omega>) \<partial>p))"
    unfolding W1_def W2_def
    by (intro Bochner_Integration.integral_sum integrable_pmf_iff_bounded[where C="1"] d e) auto 
  also have "... = (\<Sum>l\<in> L. (\<integral>\<omega>. (\<Prod>x\<leftarrow>fst l. W1 x \<omega>) * (\<Prod>y\<leftarrow>snd l. W2 y \<omega>) \<partial>p))"
    unfolding L_def using a by (intro sum.mono_neutral_right finite_cartesian_product 
        finite_lists_length_eq fin_R) auto 
  also have "... = (\<Sum>l\<in> L. (\<integral>\<omega>. (\<Prod>x\<leftarrow>fst l. of_bool(\<omega> x = \<tau> l x)) * (\<Prod>y\<leftarrow>snd l. of_bool(\<omega> y = \<tau> l y)) \<partial>p))"
    unfolding W1_def W2_def using \<tau>_check_1 \<tau>_check_2
    by (intro sum.cong arg_cong[where f="integral\<^sup>L p"] ext arg_cong2[where f="(*)"] 
        arg_cong[where f="prod_list"]) auto
  also have "... = (\<Sum>l\<in> L. (\<integral>\<omega>. (\<Prod>x\<leftarrow>(fst l@snd l). of_bool(\<omega> x = \<tau> l x))\<partial> p))"
    by simp
  also have "... = (\<Sum>l\<in> L. (\<integral>\<omega>. (\<Prod>x \<in> set (fst l@snd l). of_bool(\<omega> x = \<tau> l x)^count_list (fst l@snd l) x) \<partial> p))"
    unfolding prod_list_eval by simp
  also have "... = (\<Sum>l\<in> L. (\<integral>\<omega>. (\<Prod>x \<in> set (fst l) \<union> set (snd l). of_bool(\<omega> x = \<tau> l x)^count_list (fst l@snd l) x) \<partial> p))"
    by simp
  also have "... = (\<Sum>l\<in> L. (\<integral>\<omega>. (\<Prod>x \<in> set (fst l) \<union> set (snd l). of_bool(\<omega> x = \<tau> l x)) \<partial> p))"
    using count_list_gr_1 by (intro sum.cong arg_cong[where f="integral\<^sup>L p"] ext prod.cong) force+
  also have "... = (\<Sum>l\<in> L. (\<Prod>x \<in> set (fst l) \<union> set (snd l). (\<integral>\<omega>. of_bool(\<omega> x = \<tau> l x) \<partial> p)))"
    by (intro sum.cong prob_space.indep_vars_lebesgue_integral[OF prob_space_measure_pmf] 
        integrable_pmf_iff_bounded[where C="1"] prob_space.indep_vars_compose2[OF prob_space_measure_pmf b])
      auto 
  also have "... = (\<Sum>l\<in> L. (\<Prod>x \<in> set (fst l) \<union> set (snd l). \<alpha>))"
    using \<tau>_check_3 unfolding L_def by (intro sum.cong prod.cong c) auto 
  also have "... = (\<Sum>l \<in> L. \<alpha>^(card (set (fst l) \<union> set (snd l))))"
    by simp
  also have "... = ?R" 
    unfolding L_def \<alpha>_def by (simp add:case_prod_beta)
  finally show ?thesis by simp
qed

lemma hit_count_moments:
  assumes "j \<in> B" "s \<le> k"
  defines "L \<equiv> {xs. set xs \<subseteq> R \<and> length xs = s}"
  shows "(\<integral>\<omega>. Z j \<omega>^s  \<partial>p) = (\<Sum>xs \<in> L. (1/real (card B))^(card (set xs)))"
    (is "?L = ?R")
proof -
  let ?M = "{(xs,ys). set xs \<subseteq> R \<and> set ys \<subseteq> R \<and> (set xs \<inter> set ys = {} \<or> j = j) \<and> length xs = s \<and> length ys = 0}"

  have "?L = (\<integral>\<omega>. Z j \<omega>^s * Z j \<omega>^0 \<partial>p)"
    by simp
  also have "... = (\<Sum>(xs,ys) \<in> ?M. (1/real (card B))^(card (set xs \<union> set ys)))"
     using assms(1,2) by (intro hit_count_prod_exp) auto
  also have "... = (\<Sum>(xs,ys) \<in> ?M. (1/real (card B))^(card (set xs)))"
    by (intro sum.cong) auto
  also have "... = (\<Sum>xs \<in> fst ` ?M. (1/real (card B))^(card (set xs)))"
    by (subst sum.reindex) (auto simp add:inj_on_def case_prod_beta)
  also have "... = ?R"
    unfolding L_def by (intro sum.cong) (auto simp add:image_iff)
  finally show ?thesis by simp
qed

lemma hit_count_prod_approx':
  assumes "j1 \<in> B" "j2 \<in> B" "s+t \<le> k"
  shows "(\<integral>\<omega>. Z j1 \<omega>^s * Z j2 \<omega>^t \<partial>p) \<le> 
  (\<Sum>i\<le>s+t. real (Stirling (s+t) i) * (1 / real (card B))^i * ffact i (card R))" (is "?L \<le> ?R")
proof -
  define \<alpha> where "\<alpha> = 1 / real (card B)"

  define L where 
    "L = {(xs,ys). set xs \<subseteq> R \<and> set ys \<subseteq> R \<and> (set xs \<inter> set ys = {} \<or> j1 = j2) \<and> length xs = s \<and> length ys = t}"
  define L' where 
    "L' = {(xs,ys). set xs \<subseteq> R \<and> set ys \<subseteq> R \<and> length xs = s \<and> length ys = t}"
  define L'' where "L'' = {xs. set xs \<subseteq> R \<and> length xs = (s+t)}" 

  have "set x \<subseteq> R \<Longrightarrow> y \<in> set (take s x) \<Longrightarrow> y \<in> R" for x y 
    using set_take_subset in_mono by force
  moreover have "set x \<subseteq> R \<Longrightarrow> y \<in> set (drop s x) \<Longrightarrow> y \<in> R" for x y 
    using set_drop_subset in_mono by force
  ultimately have bij: "bij_betw (\<lambda>x. fst x @ snd x) L' L''"
    unfolding L'_def L''_def using in_mono[OF set_take_subset]
    by (intro bij_betwI[where g="\<lambda>x. (take s x, drop s x)"]) auto

  have "finite L''" 
    unfolding L''_def using fin_R finite_lists_length_eq by auto
  hence a:"finite L'" 
    using bij_betw_finite[OF bij] by simp

  have b: "inj_on (\<lambda>x. fst x @ snd x) L'" 
    using bij unfolding bij_betw_def by simp

  have c:"finite {xs. set xs \<subseteq> R \<and> length xs = s+t \<and> card (set xs) = i}" for i
    by (intro finite_subset[OF _ finite_lists_length_eq[OF fin_R, where n="s+t"]]) auto  

  have card_set_leI: "length x \<le> q \<Longrightarrow> card (set x) \<le> q" for x :: "'a list" and q
    using card_length order_trans by auto

  have "?L = (\<Sum>(xs,ys) \<in> L. \<alpha>^(card (set xs \<union> set ys)))"
    unfolding L_def \<alpha>_def using assms
    by (intro hit_count_prod_exp arg_cong[where f="abs"]) auto
  also have "... = (\<Sum>x \<in> L. \<alpha>^(card (set (fst x) \<union> set (snd x))))"
    by (intro arg_cong[where f="abs"] sum.cong)  (auto simp add:case_prod_beta)
  also have "... \<le> (\<Sum>x \<in> L'. \<alpha>^(card (set (fst x) \<union> set (snd x))))"
    using a unfolding L_def L'_def \<alpha>_def by (intro sum_mono2) auto
  also have "... = (\<Sum>xs \<in> (\<lambda>x. fst x @ snd x) ` L'. \<alpha>^(card (set xs)))"
    using b by (subst sum.reindex) auto
  also have "... = (\<Sum>xs | set xs \<subseteq> R \<and> length xs = s+t. \<alpha>^(card (set xs)))"
    using bij unfolding bij_betw_def L''_def
    by (intro sum.cong refl) auto
  also have "... = (\<Sum>xs \<in> (\<Union>i \<in> {0..s+t}. 
    {xs. set xs \<subseteq> R \<and> length xs = s+t \<and> card (set xs) = i}). \<alpha>^ card (set xs))"
    by (intro sum.cong) (auto intro!:card_set_leI) 
  also have "... = (\<Sum>i=0..s+t. 
    (\<Sum>xs | set xs \<subseteq> R \<and> length xs = s+t \<and> card(set xs) = i. \<alpha>^ card (set xs)))"
    using c by (subst sum.UNION_disjoint[symmetric]) auto 
  also have "... = (\<Sum>i=0..s+t. (\<Sum>xs | set xs \<subseteq> R \<and> length xs = s+t \<and> card(set xs) = i. \<alpha>^i))"
    unfolding \<alpha>_def by auto
  also have "... = (\<Sum>i\<le>s+t. \<alpha>^i * card {xs. set xs \<subseteq> R \<and> length xs = s+t \<and> card(set xs) = i})"
    by (intro sum.cong) auto
  also have "... = (\<Sum>i\<le>s+t. real (Stirling (s+t) i) * (1 / real (card B))^i * ffact i (card R))"
    unfolding \<alpha>_def
    by (subst card_lists_with_image_size[OF fin_R]) (simp add:algebra_simps)
  finally show "?L \<le> ?R" by simp
qed

lemma hit_count_prod_approx:
  assumes "j1 \<in> B" "j2 \<in> B" "s+t \<le> k" "card R \<le> card B"
  shows "(\<integral>\<omega>. Z j1 \<omega>^s * Z j2 \<omega>^t \<partial>p) \<le> real (Bell (s+t))" (is "?L \<le> ?R")
proof -
  have card_B_gt_0: "card B > 0"
    using assms fin_B card_gt_0_iff by blast

  have "?L \<le> (\<Sum>i\<le>s+t. real (Stirling (s+t) i) * (1 / real (card B))^i * ffact i (card R))"
    by (intro hit_count_prod_approx' assms)
  also have "... \<le> (\<Sum>i\<le>s+t. real (Stirling (s+t) i) * (1 / real (card B)) ^ i * real (card R^i))" 
    by (intro sum_mono mult_left_mono ffact_le_pow of_nat_mono) simp
  also have "... = (\<Sum>i\<le>s+t. real (Stirling (s+t) i) * (real (card R) / real (card B)) ^ i)" 
    by (simp add:algebra_simps power_divide)
  also have "... \<le> (\<Sum>i\<le>s+t. real (Stirling (s+t) i) * 1 ^ i)"
    using assms card_B_gt_0 by (intro sum_mono mult_left_mono power_mono) auto
  also have "... = real (\<Sum>i\<le>s+t. Stirling (s+t) i)"
    by simp
  also have "... = ?R"
    by (subst Bell_Stirling_eq) simp
  finally show ?thesis by simp
qed

lemma hit_count_approx:
  assumes "card R \<le> card B" "s > 0" "j \<in> B" "s \<le> k"
  shows "(\<integral>\<omega>. Z j \<omega>^s \<partial> p) \<le> real (Bell s) * real (card R) / real (card B)" (is "?L \<le> ?R")
proof -
  have card_B_gt_0: "card B > 0"
    using assms fin_B card_gt_0_iff by blast

  have "?L = (\<integral>\<omega>. Z j \<omega> ^ s * Z j \<omega> ^ 0 \<partial> p)"
    by simp
  also have "... \<le> (\<Sum>i\<le>s+0. real (Stirling (s+0) i) * (1 / real (card B))^i * ffact i (card R))"
    using assms by (intro hit_count_prod_approx') auto
  also have "... = (\<Sum>i\<le>s. real (Stirling s i) * (1 / real (card B))^i * ffact i (card R))"
    by simp
  also have "... \<le> (\<Sum>i\<le>s. real (Stirling s i) * (1 / real (card B)) ^ i * real (card R^i))" 
    by (intro sum_mono mult_left_mono ffact_le_pow of_nat_mono) simp
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
      moreover have "real (card B) > 0" using card_B_gt_0 by simp 
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

end

lemma lim_balls_and_bins_from_ind_balls_and_bins:
  assumes "finite R"
  assumes "finite B"
  defines "p \<equiv> prod_pmf R (\<lambda>_. pmf_of_set B)"
  shows "lim_balls_and_bins R B k p"
proof -
  have "prob_space.indep_vars (measure_pmf p) (\<lambda>_. discrete) (\<lambda>x \<omega>. \<omega> x) R" 
    unfolding p_def using indep_vars_Pi_pmf[OF assms(1)] by metis
  hence "prob_space.indep_vars (measure_pmf p) (\<lambda>_. discrete) (\<lambda>x \<omega>. \<omega> x) J" if "J \<subseteq> R" for J
    using prob_space.indep_vars_subset[OF prob_space_measure_pmf _ that] by auto
  hence a:"prob_space.k_wise_indep_vars (measure_pmf p) k (\<lambda>_. discrete) (\<lambda>x \<omega>. \<omega> x) R"
    by (simp add:prob_space.k_wise_indep_vars_def[OF prob_space_measure_pmf])

  have b: "map_pmf (\<lambda>\<omega>. \<omega> x) p = pmf_of_set B" if "x \<in> R" for x
    using that unfolding p_def Pi_pmf_component[OF assms(1)] by simp

  show ?thesis
    using a b assms by unfold_locales auto
qed

lemma
  fixes R :: "'a set"
  fixes B :: "'b set"
  fixes p :: "bool \<Rightarrow> ('a \<Rightarrow> 'b) pmf"
  assumes "card R \<le> card B"
  assumes "\<And>c. lim_balls_and_bins R B (k+1) (p c)"
  defines "Y \<equiv> (\<lambda>\<omega>. real (card (\<omega> ` R)))"
  shows 
    exp_approx: "\<bar>measure_pmf.expectation (p True) Y - measure_pmf.expectation (p False) Y\<bar> \<le> 
      \<epsilon> * real (card R)" (is "?A") and
    var_approx: "\<bar>measure_pmf.variance (p True) Y - measure_pmf.variance (p False) Y\<bar> \<le> \<epsilon>\<^sup>2" 
      (is "?B")
proof -
  define \<gamma> where "\<gamma> = Bell (k+1) / real (fact k)"
  have \<gamma>_nonneg: "\<gamma> \<ge> 0"
    unfolding \<gamma>_def by simp

  let ?p1 = "p False"
  let ?p2 = "p True"

  define Z :: "'b \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> real" 
    where "Z = (\<lambda>i \<omega>. real (card { j . j \<in> R \<and> \<omega> j = i}))"

  interpret H: lim_balls_and_bins R B "k+1" "p c" "Z" for c
    using assms(2) unfolding Z_def by auto

  interpret H2: lim_balls_and_bins R B "k+1" "?p2" "Z"
    using assms(2) unfolding Z_def by auto

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
    "(\<integral>\<omega>. Z i \<omega>^s \<partial>?p1) = (\<integral>\<omega>. Z i \<omega>^s \<partial>?p2)"  (is "?L = ?R")
    if "s \<le> k+1" "i \<in> B" for s i
    using that H.hit_count_moments  by simp

  have z_moment_prod_eq:
    "(\<integral>\<omega>. Z i \<omega>^s * Z j \<omega>^t  \<partial>?p1) = (\<integral>\<omega>. Z i \<omega>^s * Z j \<omega>^t  \<partial>?p2)" 
    (is "?L = ?R") if "s+t \<le> k+1" "i \<in> B" "j\<in> B" for s t i j
    using assms that H.hit_count_prod_exp by simp

  have q2: "\<bar>Z i x ^ l * Z j x ^ (s - l)\<bar> \<le> real (card R ^ s)"  if "l \<in> {..s}" for s i j l x
  proof -
    have "\<bar>Z i x ^ l * Z j x ^ (s - l)\<bar> \<le> Z i x ^ l * Z j x ^ (s - l)" 
      unfolding Z_def by auto
    also have "... \<le> real (card R) ^ l * real (card R) ^ (s-l)"
      unfolding Z_def 
      by (intro mult_mono power_mono of_nat_mono card_mono H.fin_R) auto
    also have "... = real (card R)^s" using that 
      by (subst power_add[symmetric]) simp
    also have "... = real (card R^s)"
      by simp
    finally show ?thesis by simp
  qed

  have z_sum_moment_eq:
    "(\<integral>\<omega>. (Z i \<omega> + Z j \<omega>)^s \<partial>?p1) = (\<integral>\<omega>. (Z i \<omega> + Z j \<omega>)^s \<partial>?p2)"  
    (is "?L = ?R") if "s \<le> k+1" "i \<in> B" "j \<in> B" for s i j
  proof -
    have "?L = (\<integral>\<omega>. (\<Sum>l\<le>s. real (s choose l) * (Z i \<omega>^l * Z j \<omega>^(s-l))) \<partial>?p1)"
      by (subst binomial_ring) (simp add:algebra_simps)
    also have "... = (\<Sum>l\<le>s. (\<integral>\<omega>. real (s choose l) * (Z i \<omega>^l * Z j \<omega>^(s-l)) \<partial>?p1))"
       by (intro Bochner_Integration.integral_sum integrable_mult_right 
          integrable_pmf_iff_bounded[where C="card R^s"] q2) auto
    also have "... = (\<Sum>l\<le>s. real (s choose l) * (\<integral>\<omega>. (Z i \<omega>^l * Z j \<omega>^(s-l)) \<partial>?p1))"
       by (intro sum.cong integral_mult_right integrable_pmf_iff_bounded[where C="card R^s"] q2) auto
    also have "... = (\<Sum>l\<le>s. real (s choose l) * (\<integral>\<omega>. (Z i \<omega>^l * Z j \<omega>^(s-l)) \<partial>?p2))"
      using that by (intro sum.cong arg_cong2[where f="(*)"] z_moment_prod_eq) auto
    also have "... = (\<Sum>l\<le>s. (\<integral>\<omega>. real (s choose l) * (Z i \<omega>^l * Z j \<omega>^(s-l)) \<partial>?p2))"
      by (intro sum.cong integral_mult_right[symmetric] integrable_pmf_iff_bounded[where C="card R^s"] q2) auto
    also have "... = (\<integral>\<omega>. (\<Sum>l\<le>s. real (s choose l) * (Z i \<omega>^l * Z j \<omega>^(s-l))) \<partial>?p2)"
      by (intro Bochner_Integration.integral_sum[symmetric] integrable_mult_right 
          integrable_pmf_iff_bounded[where C="card R^s"] q2) auto
    also have "... = ?R"
      by (subst binomial_ring) (simp add:algebra_simps)
    finally show ?thesis by simp
  qed

  have Z_any_integrable:
    "integrable (p c) (\<lambda>\<omega>. f (Z i \<omega>))" for i c and f :: "real \<Rightarrow> real" 
    unfolding Z_def using H.fin_R card_mono
    by (intro integrable_pmf_iff_bounded[where C="Max (abs ` f ` real ` {..card R})"])
     fastforce+ 

  have q:"real (card A) + real (card B) \<in> real ` {..2 * card R}" if "A \<subseteq> R" "B \<subseteq> R" for A B
  proof -
    have "card A + card B \<le> card R + card R"
      by (intro add_mono card_mono H.fin_R that)
    also have "... = 2 * card R" by simp
    finally show ?thesis by force
  qed

  hence Z_any_integrable':
    "integrable (p c) (\<lambda>\<omega>. f (Z i \<omega> + Z j \<omega>))" for i j c and f :: "real \<Rightarrow> real" 
    unfolding Z_def using assms(1) card_mono abs_triangle_ineq
    by (intro integrable_pmf_iff_bounded[where C="Max (abs ` f ` real ` {..2*card R})"] Max_ge 
        finite_imageI imageI) auto
  
  have Z_poly_eq: "(\<integral>\<omega>. poly f (Z i \<omega>) \<partial>?p1) = (\<integral>\<omega>. poly f (Z i \<omega>) \<partial>?p2)"
    (is "?L = ?R") if "i \<in> B" "degree f \<le> k+1" for f i
  proof -
    have "?L = (\<Sum>j\<le>degree f. (\<integral>\<omega>. poly.coeff f j * Z i \<omega> ^ j \<partial>?p1))"
      unfolding poly_altdef
      by (intro Bochner_Integration.integral_sum integrable_mult_right Z_any_integrable)
    also have "... = (\<Sum>j\<le>degree f. poly.coeff f j * (\<integral>\<omega>. Z i \<omega> ^ j \<partial>?p1))"
      by (intro sum.cong z_moment_eq Bochner_Integration.integral_mult_right Z_any_integrable)
       simp 
    also have "... = (\<Sum>j\<le>degree f. poly.coeff f j * (\<integral>\<omega>. Z i \<omega> ^ j \<partial>?p2))"
      using that by (intro sum.cong arg_cong2[where f="(*)"] z_moment_eq) auto
    also have "... = (\<Sum>j\<le>degree f. (\<integral>\<omega>. poly.coeff f j * Z i \<omega> ^ j \<partial>?p2))"
      by (intro sum.cong) auto 
    also have "... = ?R"
      unfolding poly_altdef by (intro Bochner_Integration.integral_sum[symmetric] 
          integrable_mult_right Z_any_integrable) 
    finally show ?thesis by simp
  qed

  have Z_poly_eq_2: "(\<integral>\<omega>. poly f (Z i \<omega> + Z j \<omega>) \<partial>?p1) = (\<integral>\<omega>. poly f (Z i \<omega> + Z j \<omega>) \<partial>?p2)"
    (is "?L = ?R") if "i \<in> B" "j \<in> B" "degree f \<le> k+1" for f i j 
  proof -
    have "?L = (\<Sum>d\<le>degree f. (\<integral>\<omega>. poly.coeff f d * (Z i \<omega> + Z j \<omega>) ^ d \<partial>?p1))"
      unfolding poly_altdef
      by (intro Bochner_Integration.integral_sum integrable_mult_right Z_any_integrable')
    also have "... = (\<Sum>d\<le>degree f. poly.coeff f d * (\<integral>\<omega>. (Z i \<omega> + Z j \<omega>) ^ d \<partial>?p1))"
      by (intro sum.cong z_moment_eq Bochner_Integration.integral_mult_right Z_any_integrable')
       simp 
    also have "... = (\<Sum>d\<le>degree f. poly.coeff f d *(\<integral>\<omega>. (Z i \<omega> + Z j \<omega>) ^ d \<partial>?p2))"
      using that by (intro sum.cong arg_cong2[where f="(*)"] z_sum_moment_eq) auto
    also have "... = (\<Sum>d\<le>degree f. (\<integral>\<omega>. poly.coeff f d * (Z i \<omega> + Z j \<omega>) ^ d \<partial>?p2))"
      by (intro sum.cong) auto 
    also have "... = ?R"
      unfolding poly_altdef by (intro Bochner_Integration.integral_sum[symmetric] 
          integrable_mult_right Z_any_integrable') 
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

  have z1_g_bound: "\<bar>(\<integral>\<omega>. g (Z i \<omega>) \<partial>(p c))\<bar> \<le> (real (card R) / real (card B)) * \<gamma>" 
    (is "?L1 \<le> ?R1") if "i \<in> B" for i c
  proof -
    have card_B_gt_0: "card B > 0" 
      using that card_gt_0_iff H.fin_B by auto

    have "(\<integral>\<omega>. Z i \<omega>^(k+1) \<partial>(p c)) \<le> real (Bell (k+1)) * real (card R) / real (card B)"
      using assms by (intro H.hit_count_approx[OF _ _ that]) auto
    also have "... = real (card R) / real (card B) * Bell (k+1)" by simp
    finally have Z_pow_exp_bound: "(\<integral>\<omega>. Z i \<omega>^(k+1) \<partial>(p c)) \<le> 
      real (card R) / real (card B) * Bell (k+1)"
      by simp

    have "?L1 \<le> measure_pmf.expectation (p c) (\<lambda>\<omega>. Z i \<omega> ^ (k + 1)) / real (fact k)"
      unfolding Z_def using H.fin_R
      by (intro g_bound_abs[where m="card R"]) (auto intro!:imageI card_mono)
    also have "... \<le> real (card R) / real (card B) * Bell (k+1) / real (fact k)"
      by (intro divide_right_mono Z_pow_exp_bound) auto
    finally show ?thesis by (simp add:\<gamma>_def)
  qed

  have g_add_bound: "\<bar>integral\<^sup>L (p c) (\<lambda>\<omega>. g (Z i \<omega> + Z j \<omega>))\<bar> \<le> 2^(k+1) * \<gamma>" 
    (is "?L1 \<le> ?R1") if ij_in_B: "i \<in> B" "j \<in> B" for i j c
  proof -
    have a:"(\<integral>\<omega>. (Z i \<omega>^d * Z j \<omega>^(k+1-d)) \<partial>(p c)) \<le> Bell (k+1)" (is "?L c \<le> ?R") if "d \<in> {..k+1}" for d
    proof -
      have "?L False \<le> Bell (d + (k+1-d))"
        using that by (intro H.hit_count_prod_approx ij_in_B assms) auto
      moreover have "?L True \<le> Bell (d + (k+1-d))"
        using that by (intro H.hit_count_prod_approx ij_in_B assms) auto
      ultimately have "?L c \<le> Bell (d + (k+1-d))"
        by (cases c) auto
      also have "... = Bell (k+1)"
        using that by auto
      finally show ?thesis by simp
    qed

    have "?L1 \<le> measure_pmf.expectation (p c) (\<lambda>\<omega>. (Z i \<omega> + Z j \<omega>) ^ (k + 1)) / real (fact k)"
      unfolding Z_def using assms(1)
      by (intro g_bound_abs[where m="2*card R"]) (auto intro!:imageI q)
    also have "... = (\<integral>\<omega>. (\<Sum>d \<le> k+1. real (k+1 choose d) * (Z i \<omega>^d * Z j \<omega>^(k+1-d))) \<partial>(p c)) / real (fact k)"
      by (subst binomial_ring) (simp add:algebra_simps)
    also have "... = (\<Sum>d \<le> k+1. (\<integral>\<omega>. real (k+1 choose d) * (Z i \<omega>^d * Z j \<omega>^((k+1)-d)) \<partial>(p c))) / real (fact k)"
      by (intro Bochner_Integration.integral_sum arg_cong2[where f="(/)"] 
          integrable_mult_right integrable_pmf_iff_bounded[where C="real (card R^(k+1))"] q2) auto
    also have "... = (\<Sum>d \<le> k+1. real (k+1 choose d) * (\<integral>\<omega>. (Z i \<omega>^d * Z j \<omega>^(k+1-d)) \<partial>(p c))) / real (fact k)"
      by (simp del:power_Suc)
    also have "... \<le> (\<Sum>d \<le> k+1. real (k+1 choose d) * Bell (k+1)) / real (fact k)"
      by (intro divide_right_mono sum_mono mult_left_mono a) auto
    also have "... = (\<Sum>d \<le> k+1. (k+1 choose d)) * Bell (k+1) / real (fact k)"
      by (subst sum_distrib_right) simp
    also have "... = ?R1"
      by (subst choose_row_sum) (simp add:\<gamma>_def)
    finally show ?thesis by simp
  qed

  have Z_poly_diff: 
    "\<bar>(\<integral>\<omega>. \<phi> (Z i \<omega>) \<partial>?p1) - (\<integral>\<omega>. \<phi> (Z i \<omega>) \<partial>?p2)\<bar> \<le> 2 * ((real (card R) / real (card B)) * \<gamma>)" 
    (is "?L \<le> 2 * ?R") if "i \<in> B" for i
  proof -
    have "?L = \<bar>(\<integral>\<omega>. f (Z i \<omega>) \<partial>?p1) + (\<integral>\<omega>. g (Z i \<omega>) \<partial>?p1) - (\<integral>\<omega>. f (Z i \<omega>) \<partial>?p2) - (\<integral>\<omega>. g (Z i \<omega>) \<partial>?p2)\<bar>"
      using Z_any_integrable unfolding \<phi>_exp by simp
    also have "... = \<bar>(\<integral>\<omega>. g (Z i \<omega>) \<partial>?p1) + (- (\<integral>\<omega>. g (Z i \<omega>) \<partial>?p2))\<bar>"
      unfolding f_def using that deg_fp by (subst Z_poly_eq) auto
    also have "... \<le> \<bar>(\<integral>\<omega>. g (Z i \<omega>) \<partial>?p1)\<bar> + \<bar>(\<integral>\<omega>. g (Z i \<omega>) \<partial>?p2)\<bar>"
      by simp
    also have "... \<le> ?R + ?R"
      by (intro add_mono z1_g_bound that)
    also have "... = 2 * ?R" 
      by (simp add:algebra_simps)
    finally show ?thesis by simp
  qed

  have Z_poly_diff_2: "\<bar>(\<integral>\<omega>. \<phi> (Z i \<omega>) \<partial>?p1) - (\<integral>\<omega>. \<phi> (Z i \<omega>) \<partial>?p2)\<bar> \<le> 2 * \<gamma>" 
    (is "?L \<le> ?R") if "i \<in> B" for i
  proof -
    have "?L \<le> 2 * ((real (card R) / real (card B)) * \<gamma>)"
      by (intro Z_poly_diff that)
    also have "... \<le> 2 * (1 * \<gamma>)"
      using assms H.fin_B that card_gt_0_iff
      by (intro mult_right_mono mult_left_mono \<gamma>_nonneg that iffD2[OF pos_divide_le_eq]) auto
    also have "... = ?R" by simp
    finally show ?thesis by simp
  qed

  have Z_poly_diff_3: "\<bar>(\<integral>\<omega>. \<phi> (Z i \<omega> + Z j \<omega>) \<partial>?p2) - (\<integral>\<omega>. \<phi> (Z i \<omega> + Z j \<omega>) \<partial>?p1)\<bar> \<le> 2^(k+2) * \<gamma>" 
    (is "?L \<le> ?R") if "i \<in> B" "j \<in> B" for i j
  proof -
    have "?L = \<bar>(\<integral>\<omega>. f (Z i \<omega> + Z j \<omega>) \<partial>?p2) + (\<integral>\<omega>. g (Z i \<omega> + Z j \<omega>) \<partial>?p2) -
      (\<integral>\<omega>. f (Z i \<omega> + Z j \<omega>) \<partial>?p1) - (\<integral>\<omega>. g (Z i \<omega> + Z j \<omega>) \<partial>?p1)\<bar>" 
      using Z_any_integrable' unfolding \<phi>_exp by simp
    also have "... = \<bar>(\<integral>\<omega>. g (Z i \<omega> + Z j \<omega>) \<partial>?p2) + (- (\<integral>\<omega>. g (Z i \<omega> + Z j \<omega>) \<partial>?p1))\<bar>"
      unfolding f_def using that deg_fp by (subst Z_poly_eq_2) auto
    also have "... \<le> \<bar>(\<integral>\<omega>. g (Z i \<omega> + Z j \<omega>) \<partial>?p1)\<bar> + \<bar>(\<integral>\<omega>. g (Z i \<omega> + Z j \<omega>) \<partial>?p2)\<bar>"
      by simp
    also have "... \<le> 2^(k+1) * \<gamma> + 2^(k+1) * \<gamma>"
      by (intro add_mono g_add_bound that)
    also have "... = ?R" 
      by (simp add:algebra_simps)
    finally show ?thesis by simp
  qed

  have B_nonempty: "B \<noteq> {}" if "x \<in> R" for x 
  proof  -
    have "R \<noteq> {}" using that by auto
    hence "card R > 0" using H.fin_R by auto
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
        by (intro arg_cong[where f="set_pmf"] assms H.ran a)
      also have "... = B"
        by (intro set_pmf_of_set H.fin_B B_nonempty[OF a])
      finally show "\<omega> x \<in> B" by simp
    qed
    hence "(\<omega> ` R) = B \<inter> \<omega> ` R"
      by auto
    hence "Y \<omega> = card (B \<inter> \<omega> ` R)"
      unfolding Y_def by auto
    also have  "... = (\<Sum>i \<in> B. of_bool (i \<in> \<omega> ` R))"
      unfolding of_bool_def using H.fin_B by (subst sum.If_cases) auto
    also have  "... = (\<Sum>i \<in> B. of_bool (card {r \<in> R.  \<omega> r = i} > 0))"
      using H.fin_R by (intro sum.cong arg_cong[where f="of_bool"]) 
        (auto simp add:card_gt_0_iff) 
    also have "... = (\<Sum>i \<in> B. \<phi>(Z i \<omega>))"
      unfolding \<phi>_def Z_def by (intro sum.cong) (auto simp add:of_bool_def) 
    finally show ?thesis by simp
  qed

  have Y_sq_eq: "Y \<omega>^ 2 = 
    (\<Sum>i \<in> B \<times> B. \<phi>(Z (fst i) \<omega>) + \<phi>(Z (snd i) \<omega>) - \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>))" (is "?L = ?R")
    if "\<omega> \<in> set_pmf (p c)" for c \<omega>
  proof -

    have a: "\<phi> (Z x \<omega>) = of_bool(card {r \<in> R. \<omega> r = x} > 0)" for x 
      unfolding \<phi>_def Z_def by auto
    have b: "\<phi> (Z x \<omega> + Z y \<omega>) = 
      of_bool( card {r \<in> R. \<omega> r = x} > 0 \<or> card {r \<in> R. \<omega> r = y} > 0)" for x y 
      unfolding \<phi>_def Z_def by auto

    have "?L = (\<Sum>i\<in>B \<times> B. \<phi> (Z (fst i) \<omega>) * \<phi> (Z (snd i) \<omega>))" 
      unfolding Y_eq[OF that] power2_eq_square sum_product sum.cartesian_product 
      by (simp add:case_prod_beta)
    also have "... = ?R"
      unfolding a b of_bool_def
      by (intro sum.cong) auto 
    finally show ?thesis by simp
  qed

  have "\<bar>integral\<^sup>L ?p1 Y - integral\<^sup>L ?p2 Y\<bar> = 
    \<bar>(\<integral>\<omega>. (\<Sum>i \<in> B. \<phi>(Z i \<omega>)) \<partial>?p1) - (\<integral>\<omega>. (\<Sum>i \<in> B. \<phi>(Z i \<omega>)) \<partial>?p2)\<bar>"
    by (intro arg_cong[where f="abs"] arg_cong2[where f="(-)"] integral_cong_AE AE_pmfI Y_eq) auto
  also have "... = 
    \<bar>(\<Sum>i \<in> B. (\<integral>\<omega>. \<phi>(Z i \<omega>) \<partial>?p1)) - (\<Sum>i \<in> B. (\<integral>\<omega>. \<phi>(Z i \<omega>) \<partial>?p2))\<bar>"
    by (intro arg_cong[where f="abs"] arg_cong2[where f="(-)"] 
        Bochner_Integration.integral_sum Z_any_integrable)
  also have "... = \<bar>(\<Sum>i \<in> B. (\<integral>\<omega>. \<phi>(Z i \<omega>) \<partial>?p1) - (\<integral>\<omega>. \<phi>(Z i \<omega>) \<partial>?p2))\<bar>"
    by (subst sum_subtractf) simp
  also have "... \<le> (\<Sum>i \<in> B. \<bar>(\<integral>\<omega>. \<phi>(Z i \<omega>) \<partial>?p1) - (\<integral>\<omega>. \<phi>(Z i \<omega>) \<partial>?p2)\<bar>)"
    by simp
  also have "... \<le> (\<Sum>i \<in> B. 2 * ((real (card R) / real (card B)) * \<gamma>))"
    by (intro sum_mono Z_poly_diff)
  also have "... \<le> 2 * real (card R) * \<gamma>"
    using \<gamma>_nonneg by simp
  finally have Y_exp_diff_1: "\<bar>integral\<^sup>L ?p1 Y - integral\<^sup>L ?p2 Y\<bar> \<le>  2 * real (card R) * \<gamma>" by simp

  have "\<bar>integral\<^sup>L ?p1 Y - integral\<^sup>L ?p2 Y\<bar> \<le>  2 * real (card R) * \<gamma>"
    using Y_exp_diff_1 by simp
  also have "... \<le> \<epsilon> * card R" sorry
  finally show ?A
    by simp

  have "\<bar>integral\<^sup>L ?p1 Y - integral\<^sup>L ?p2 Y\<bar> \<le>  2 * real (card R) * \<gamma>"
    using Y_exp_diff_1 by simp
  also have "... \<le> 2 * real (card B) * \<gamma>" 
    by (intro mult_right_mono mult_left_mono \<gamma>_nonneg of_nat_mono assms)auto
  finally have Y_exp_diff_2: "\<bar>integral\<^sup>L ?p1 Y - integral\<^sup>L ?p2 Y\<bar> \<le> 2 * \<gamma> * real (card B)"
    by (simp add:algebra_simps)

  have int_Y: "integrable (measure_pmf (p c)) Y" for c
    using H.fin_R card_image_le unfolding Y_def
    by (intro integrable_pmf_iff_bounded[where C="card R"])  auto

  have int_Y_sq: "integrable (measure_pmf (p c)) (\<lambda>\<omega>. Y \<omega>^2)" for c
    using H.fin_R card_image_le unfolding Y_def
    by (intro integrable_pmf_iff_bounded[where C="real (card R)^2"]) auto

  have "\<bar>(\<integral>\<omega>. Y \<omega> ^2 \<partial>?p1) - (\<integral>\<omega>. Y \<omega>^2 \<partial>?p2)\<bar> =
    \<bar>(\<integral>\<omega>. (\<Sum>i \<in> B \<times> B. \<phi>(Z (fst i) \<omega>) + \<phi>(Z (snd i) \<omega>) - \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>)) \<partial>?p1) - 
     (\<integral>\<omega>. (\<Sum>i \<in> B \<times> B. \<phi>(Z (fst i) \<omega>) + \<phi>(Z (snd i) \<omega>) - \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>)) \<partial>?p2)\<bar>" 
    by (intro arg_cong[where f="abs"] arg_cong2[where f="(-)"] 
       Bochner_Integration.integral_cong_AE AE_pmfI Y_sq_eq) auto
  also have "... = \<bar>(\<Sum>i \<in> B \<times> B. 
    (\<integral>\<omega>. \<phi>(Z (fst i) \<omega>) \<partial>?p1) + (\<integral>\<omega>. \<phi>(Z (snd i) \<omega>) \<partial>?p1) - 
    (\<integral>\<omega>. \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>) \<partial>?p1) - ( (\<integral>\<omega>. \<phi>(Z (fst i) \<omega>) \<partial>?p2) + 
    (\<integral>\<omega>. \<phi>(Z (snd i) \<omega>) \<partial>?p2) - (\<integral>\<omega>. \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>) \<partial>?p2)))\<bar>"
    using Z_any_integrable Z_any_integrable' by (simp add:Bochner_Integration.integral_sum sum_subtractf)
  also have "... = \<bar>(\<Sum>i \<in> B \<times> B. 
    ((\<integral>\<omega>. \<phi>(Z (fst i) \<omega>) \<partial>?p1) - (\<integral>\<omega>. \<phi>(Z (fst i) \<omega>) \<partial>?p2)) + 
    ((\<integral>\<omega>. \<phi>(Z (snd i) \<omega>) \<partial>?p1) - (\<integral>\<omega>. \<phi>(Z (snd i) \<omega>) \<partial>?p2)) + 
    ((\<integral>\<omega>. \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>) \<partial>?p2) - (\<integral>\<omega>. \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>) \<partial>?p1)))\<bar>"
    by (intro arg_cong[where f="abs"] sum.cong) auto
  also have "... \<le> (\<Sum>i \<in> B \<times> B. \<bar>
    ((\<integral>\<omega>. \<phi>(Z (fst i) \<omega>) \<partial>?p1) - (\<integral>\<omega>. \<phi>(Z (fst i) \<omega>) \<partial>?p2)) + 
    ((\<integral>\<omega>. \<phi>(Z (snd i) \<omega>) \<partial>?p1) - (\<integral>\<omega>. \<phi>(Z (snd i) \<omega>) \<partial>?p2)) + 
    ((\<integral>\<omega>. \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>) \<partial>?p2) - (\<integral>\<omega>. \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>) \<partial>?p1))\<bar>)"
    by (intro sum_abs)
  also have "... \<le> (\<Sum>i \<in> B \<times> B.
    \<bar>(\<integral>\<omega>. \<phi>(Z (fst i) \<omega>) \<partial>?p1) - (\<integral>\<omega>. \<phi>(Z (fst i) \<omega>) \<partial>?p2)\<bar> + 
    \<bar>(\<integral>\<omega>. \<phi>(Z (snd i) \<omega>) \<partial>?p1) - (\<integral>\<omega>. \<phi>(Z (snd i) \<omega>) \<partial>?p2)\<bar> + 
    \<bar>(\<integral>\<omega>. \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>) \<partial>?p2) - (\<integral>\<omega>. \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>) \<partial>?p1)\<bar>)"
    by (intro sum_mono) auto
  also have "... \<le> (\<Sum>i \<in> B \<times> B. 2*\<gamma> + 2 * \<gamma> + 2^(k+2)*\<gamma>)"
    by (intro sum_mono add_mono Z_poly_diff_2 Z_poly_diff_3) auto 
  also have "... = (2^(k+2)+4) * \<gamma> * card B^2"
    by (simp add:card_cartesian_product power2_eq_square algebra_simps)
  finally have Y_sq_exp_diff: "\<bar>(\<integral>\<omega>. Y \<omega> ^2 \<partial>?p1) - (\<integral>\<omega>. Y \<omega>^2 \<partial>?p2)\<bar> \<le> (2^(k+2)+4) * \<gamma> * card B^2" 
    by simp

  have Y_exp_rough_bound: "\<bar>integral\<^sup>L (p c) Y\<bar> \<le> card B" (is "?L \<le> ?R") for c 
  proof -
    have "?L \<le> (\<integral>\<omega>. \<bar>Y \<omega>\<bar> \<partial>(p c))"
      by (intro Bochner_Integration.integral_abs_bound)
    also have "... \<le> (\<integral>\<omega>. real (card R)  \<partial>(p c))"
      unfolding Y_def using card_image_le[OF H.fin_R]
      by (intro Bochner_Integration.integral_mono integrable_pmf_iff_bounded[where C="card R"])
       auto
    also have "... = card R" by simp
    also have "... \<le> card B" using assms by simp
    finally show ?thesis by simp
  qed

  have "\<bar>measure_pmf.variance ?p1 Y - measure_pmf.variance ?p2 Y\<bar> = 
    \<bar>(\<integral>\<omega>. Y \<omega> ^2 \<partial>?p1) - (\<integral>\<omega>. Y \<omega> \<partial> ?p1)^2 - ((\<integral>\<omega>. Y \<omega> ^2 \<partial>?p2) - (\<integral>\<omega>. Y \<omega> \<partial> ?p2)^2)\<bar>"
    by (intro arg_cong[where f="abs"] arg_cong2[where f="(-)"] measure_pmf.variance_eq
        int_Y int_Y_sq)
  also have "... \<le> \<bar>(\<integral>\<omega>. Y \<omega>^2 \<partial>?p1) - (\<integral>\<omega>. Y \<omega>^2 \<partial>?p2)\<bar> + \<bar>(\<integral>\<omega>. Y \<omega> \<partial> ?p1)\<^sup>2 - (\<integral>\<omega>. Y \<omega> \<partial> ?p2)\<^sup>2\<bar>"
    by simp
  also have "... = \<bar>(\<integral>\<omega>. Y \<omega>^2 \<partial>?p1) - (\<integral>\<omega>. Y \<omega>^2 \<partial>?p2)\<bar> + 
    \<bar>(\<integral>\<omega>. Y \<omega> \<partial> ?p1) - (\<integral>\<omega>. Y \<omega> \<partial> ?p2)\<bar>*\<bar>(\<integral>\<omega>. Y \<omega> \<partial> ?p1) + (\<integral>\<omega>. Y \<omega> \<partial> ?p2)\<bar>"
    by (simp add:power2_eq_square algebra_simps abs_mult[symmetric])
  also have "... \<le> (2^(k+2)+4) * \<gamma> * card B^2 + (2 * \<gamma> * card B) * (\<bar>\<integral>\<omega>. Y \<omega> \<partial>?p1\<bar> + \<bar>\<integral>\<omega>. Y \<omega> \<partial> ?p2\<bar>)"
    using \<gamma>_nonneg
    by (intro add_mono mult_mono Y_sq_exp_diff Y_exp_diff_2) auto
  also have "... \<le> (2^(k+2)+4) * \<gamma> * card B^2 + (2 * \<gamma> * card B) * (real (card B) + real (card B))"
    using \<gamma>_nonneg
    by (intro add_mono mult_left_mono Y_exp_rough_bound) auto
  also have "... = (2^(k+2)+8) * \<gamma> * card B^2"
    by (simp add:algebra_simps power2_eq_square)
  also have "... \<le> \<epsilon>^2" sorry
  finally show ?B 
    by simp
qed

lemma
  fixes R :: "'a set"
  fixes B :: "'b set"
  fixes p :: "('a \<Rightarrow> 'b) pmf"
  assumes "finite R" "finite B" "card R \<le> card B" "card B \<ge> 1"
  assumes "prob_space.k_wise_indep_vars (measure_pmf p) (k+1) (\<lambda>_. discrete) (\<lambda>x \<omega>. \<omega> x) R"
  assumes "\<And>c x. x \<in> R \<Longrightarrow> map_pmf (\<lambda>\<omega>. \<omega> x) p = pmf_of_set B"
  defines "Y \<equiv> (\<lambda>\<omega>. real (card (\<omega> ` R)))"
  defines "\<rho> \<equiv> real (card B) * (1 - (1-1/real (card B))^card R)"
  shows 
    exp_approx_2: "\<bar>measure_pmf.expectation p Y - \<rho>\<bar> \<le> card R / sqrt (card B)" (is "?AL \<le> ?AR") and
    var_approx_2: "measure_pmf.variance p Y  \<le> real (card R)^2 / card B"  (is "?BL \<le> ?BR")
proof -
  define q where "q = (\<lambda>c. if c then prod_pmf R (\<lambda>_. pmf_of_set B) else p)"

  have q_altdef: "q True = prod_pmf R (\<lambda>_. pmf_of_set B)" "q False = p"
    unfolding q_def by auto

  have a:"lim_balls_and_bins R B (k+1) (q c)" for c
  proof (cases c)
    case False
    then show ?thesis
      unfolding q_def using assms by unfold_locales auto
  next
    case True
    then show ?thesis
      using lim_balls_and_bins_from_ind_balls_and_bins[OF assms(1,2)] 
      unfolding q_def by simp
  qed

  have "?AL = \<bar>(\<integral>\<omega>. Y \<omega> \<partial>(q True)) - (\<integral>\<omega>. Y \<omega> \<partial>(q False))\<bar>"
    using exp_balls_and_bins[OF assms(1,2,4)]
    unfolding q_def Y_def \<rho>_def by simp
  also have "... \<le> sqrt (1 / card B) * card R"
    unfolding Y_def
    by (intro exp_approx[OF assms(3) a]) 
  also have "... = ?AR" using real_sqrt_divide by simp
  finally show "?AL \<le> ?AR" by simp

  show "?BL \<le> ?BR"
  proof (cases "R= {}")
    case True
    then show ?thesis unfolding Y_def by simp
  next
    case "False"
    hence "card R > 0" using assms(1) by auto
    hence card_R_ge_1: "real (card R) \<ge> 1" by simp
  
    have "?BL \<le> measure_pmf.variance (q True) Y + 
      \<bar>measure_pmf.variance (q True) Y - measure_pmf.variance (q False) Y\<bar>"
      unfolding q_def by auto
    also have "... \<le> measure_pmf.variance (q True) Y + sqrt(1 / card B)^2"
      unfolding Y_def 
      by (intro add_mono var_approx[OF assms(3) a]) auto 
    also have "... \<le> card R * (real (card R) - 1)/ card B + sqrt(1 / card B)^2"
      unfolding q_altdef Y_def by (intro add_mono var_balls_and_bins[OF assms(1,2,4)]) auto
    also have "... = card R * (real (card R) - 1)/ card B + 1 / card B"
      by (auto simp add:power_divide real_sqrt_divide)
    also have "... \<le> card R * (real (card R) - 1)/ card B + card R / card B"
      by (intro add_mono divide_right_mono card_R_ge_1) auto
    also have "... = (card R * (real (card R) - 1) + card R) / card B"
      by argo
    also have "... = ?BR" 
      by (simp add:algebra_simps power2_eq_square)
    finally show "?BL \<le> ?BR" by simp
  qed
qed

end