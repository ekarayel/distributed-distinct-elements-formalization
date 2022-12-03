subsection "Uniform k-independent Hash Family"

theory Pseudorandom_Combinators_Hash
  imports Pseudorandom_Combinators
    "Finite_Fields.Card_Irreducible_Polynomials" 
    "Universal_Hash_Families.Carter_Wegman_Hash_Family"
    "Frequency_Moments.Product_PMF_Ext"
begin

lemma indep_vars_map_pmf:
  assumes "prob_space.indep_vars (measure_pmf p) (\<lambda>_. discrete) (\<lambda>i \<omega>. X' i (f \<omega>)) I"
  shows "prob_space.indep_vars (measure_pmf (map_pmf f p)) (\<lambda>_. discrete) X' I"
proof -
  have "prob_space.indep_vars (measure_pmf p) (\<lambda>_. discrete) (\<lambda>i. X' i \<circ> f) I" 
    using assms by (simp add:comp_def)  
  hence "prob_space.indep_vars (distr (measure_pmf p) discrete f) (\<lambda>_. discrete) X' I" 
    by (intro prob_space.indep_vars_distr prob_space_measure_pmf) auto
  thus ?thesis
    using map_pmf_rep_eq by metis
qed

lemma k_wise_indep_vars_map_pmf:
  assumes "prob_space.k_wise_indep_vars (measure_pmf p) k (\<lambda>_. discrete) (\<lambda>i \<omega>. X' i (f \<omega>)) I"
  shows "prob_space.k_wise_indep_vars (measure_pmf (map_pmf f p)) k (\<lambda>_. discrete) X' I"
  using assms indep_vars_map_pmf 
  unfolding prob_space.k_wise_indep_vars_def[OF prob_space_measure_pmf]
  by blast

lemma (in prob_space) k_wise_indep_subset:
  assumes "J \<subseteq> I"
  assumes "k_wise_indep_vars k M' X' I"
  shows "k_wise_indep_vars k M' X' J"
  using assms unfolding k_wise_indep_vars_def by simp

lemma (in prob_space) k_wise_indep_vars_reindex:
  assumes "inj_on f I"
  assumes "k_wise_indep_vars k M' X' (f ` I)"
  shows "k_wise_indep_vars k (M' \<circ> f) (\<lambda>k \<omega>. X' (f k) \<omega>) I"
proof -
  have "indep_vars (M' \<circ> f) (\<lambda>k. X' (f k)) J" if "finite J" "card J \<le> k" "J \<subseteq> I" for J
  proof -
    have "f ` J \<subseteq> f ` I" using that by auto
    moreover have "card (f ` J) \<le> k" 
      using card_image_le[OF that(1)] that(2) order.trans by auto
    moreover have "finite (f ` J)" using that by auto
    ultimately have "indep_vars M' X' (f ` J)" 
      using assms(2) unfolding k_wise_indep_vars_def by simp
    thus ?thesis
      using that assms(1) inj_on_subset
      by (intro indep_vars_reindex) 
  qed
  thus ?thesis
    unfolding k_wise_indep_vars_def by simp
qed

definition GF :: "nat \<Rightarrow> int set list set ring"
  where "GF n = (SOME F. finite_field F \<and> order F = n)"

definition some_bij :: "'a set \<Rightarrow> (nat \<Rightarrow> 'a)"
  where "some_bij A = (SOME f. inj_on f {..<card A} \<and> f ` {..<card A} = A)"

lemma some_bij:
  assumes "finite A" "x = card A"
  shows "bij_betw (some_bij A) {..<x} A"
proof -
  obtain n :: nat and f where a:"A = f ` {i. i < n}" and b:"inj_on f {i. i < n}"
    using finite_imp_nat_seg_image_inj_on[OF assms(1)] by auto

  let ?g = "some_bij A"

  have "n = card {i. i < n}" by simp
  also have "... = card (f ` {i. i < n})" using card_image[OF b] by simp
  also have "... = card A"  using a by simp
  finally have "n = card A" by simp
  hence c:"inj_on f {..<card A} \<and> f ` {..<card A} = A"
    using a b by (auto simp add:lessThan_def)
  have "inj_on ?g {..<card A} \<and> ?g ` {..<card A} = A"
    unfolding some_bij_def
    using someI[where P="\<lambda>f. inj_on f {..<card A} \<and> f ` {..<card A} = A", OF c]
    by simp
  thus ?thesis 
    unfolding bij_betw_def assms(2) by simp
qed

definition is_prime_power :: "nat \<Rightarrow> bool"
  where "is_prime_power n \<longleftrightarrow> (\<exists>p k. Factorial_Ring.prime p \<and> k > 0 \<and> n = p^k)"

lemma 
  assumes "is_prime_power n"
  shows GF: "finite_field (GF n)" "order (GF n) = n"
proof -
  obtain p k where p_k: "Factorial_Ring.prime p" "k > 0" "n = p^k"
    using assms unfolding is_prime_power_def by blast
  have a:"\<exists>(F :: int set list set ring). finite_field F \<and> order F = n"
    using existence[OF p_k(2,1)] p_k(3) by simp
  show  "finite_field (GF n)" "order (GF n) = n"
    unfolding GF_def
    using someI_ex[OF a]
    by auto 
qed


lemma is_prime_power: "Factorial_Ring.prime p \<Longrightarrow> k > 0 \<Longrightarrow> is_prime_power (p^k)" 
  unfolding is_prime_power_def by auto

definition split_prime_power :: "nat \<Rightarrow> (nat \<times> nat)"
  where "split_prime_power n = (THE (p, k). p^k = n \<and> Factorial_Ring.prime p \<and> k > 0)" 

lemma split_prime_power:
  assumes "Factorial_Ring.prime p"
  assumes "k > 0"
  shows "split_prime_power (p^k) = (p,k)"
proof -
  have "q = p \<and> l = k" if "q^l = p^k" "Factorial_Ring.prime q" "l > 0" for q l
  proof -
    have "q dvd p^k" using that by (metis dvd_power)
    hence "q dvd p" using prime_dvd_power that by auto
    moreover have "p dvd q^l" using that assms(2) by (metis dvd_power)
    hence "p dvd q" using prime_dvd_power that assms by blast
    ultimately have a:"p = q" by auto
    hence "l = k" using that prime_power_inj by auto
    thus ?thesis using a by simp
  qed
  thus ?thesis
    unfolding split_prime_power_def using assms
    by (intro the_equality) auto
qed

definition \<H> :: "nat \<Rightarrow> nat \<Rightarrow> 'a sample_space \<Rightarrow> (nat \<Rightarrow> 'a) sample_space"
  where "\<H> k d R = (
    let (p,n) = split_prime_power (size R);
        m = (LEAST j. d \<le> p^j \<and> j \<ge> n);
        f = some_bij (carrier (GF (p^m)));
        f' = the_inv_into {..<(p^m)} f;
        g = some_bij (bounded_degree_polynomials (GF (p^m)) k) in
    \<lparr> size = p^(m*k), select = (\<lambda>i x. select R ((f' (ring.hash (GF (p^m)) (f x) (g i))) mod p^n))\<rparr>)"

locale \<H>_locale =
  fixes k d R S
  assumes size_R_assm: "is_prime_power (size R)"
  assumes k_gt_0: "k > 0"
  defines "S \<equiv> \<H> k d R"
begin

definition p where "p = fst (split_prime_power (size R))"
definition n where "n = snd (split_prime_power (size R))"

lemma p_n_def: "(p,n) = split_prime_power (size R)"
  unfolding p_def n_def by simp

lemma 
  n_gt_0: "n > 0" and 
  p_prime: "Factorial_Ring.prime p" and
  size_R: "size R = p^n"
proof -
  obtain p' n' where a: "n' > 0" "Factorial_Ring.prime p'" and b:"size R = p'^n'"
    using size_R_assm unfolding is_prime_power_def by auto
  have "(p,n) = split_prime_power (p'^n')"
    unfolding p_n_def b by simp
  also have "... = (p',n')"
    by (intro split_prime_power a)
  finally have c:"p= p'" "n = n'"
    by auto
  show "n >0"  "Factorial_Ring.prime p" "size R = p^n" using a b c by auto
qed


definition m where "m = (LEAST j. d \<le> p^j \<and> j \<ge> n)"
definition f where "f = some_bij (carrier (GF (p^m)))"
definition f' where "f' = the_inv_into {..<(p^m)} f"


lemma n_lt_m: "n \<le> m" and d_lt_p_m: "d \<le> p^m" 
proof -
  define j :: nat where "j = max n d"
  have "d \<le> 2^d" by simp
  also have "... \<le> 2^j"
    unfolding j_def
    by (intro iffD2[OF power_increasing_iff]) auto
  also have "... \<le> p^j" 
    using p_prime prime_ge_2_nat
    by (intro power_mono) auto
  finally have "d \<le> p^j" by simp
  moreover have "n \<le> j" unfolding j_def by simp
  ultimately have "d \<le> p^m \<and> m \<ge> n"
    unfolding m_def 
    by (intro LeastI[where P="\<lambda>x. d \<le> p^ x \<and> x \<ge> n" and k="j"]) auto
  thus "n \<le> m" "d \<le> p^m" 
    by auto
qed

lemma 
  is_field: "finite_field (GF (p^m))" (is "?A") and 
  field_order: "order (GF(p^m)) = p^m"  (is "?B")
proof -
  have "is_prime_power (p^m)" 
    using n_gt_0 n_lt_m
    by (intro is_prime_power p_prime) auto
  
  thus "?A" "?B"
    using GF by auto
qed

interpretation cw: carter_wegman_hash_family "GF (p^m)" "k"
  using finite_field_def is_field finite_field_axioms_def
  by (intro carter_wegman_hash_familyI k_gt_0) auto

lemma field_size: "cw.field_size = p^m"
  using field_order unfolding Coset.order_def by simp

lemma f_bij: "bij_betw f {..<p^m} (carrier (GF (p^m)))"
  unfolding f_def using field_size
  by (intro some_bij) auto

definition g where "g = some_bij cw.space"

lemma p_n_gt_0: "p^n > 0" 
  by (metis p_prime gr0I not_prime_0 power_not_zero)

lemma p_m_gt_0: "p^m > 0"
  by (metis p_prime gr0I not_prime_0 power_not_zero)


lemma S_eq: "S = \<lparr> size = p^(m*k), select = (\<lambda> i x. select R (f' (cw.hash (f x) (g i)) mod p^n )) \<rparr>"
  unfolding S_def \<H>_def 
  by (simp add:p_n_def[symmetric] m_def[symmetric] f_def[symmetric] g_def f'_def Let_def cw.space_def)

lemma \<H>_size: "size S > 0" 
  unfolding S_eq using p_m_gt_0 k_gt_0 by simp

sublocale sample_space "S"
  unfolding sample_space_def using \<H>_size by simp

lemma \<H>_range: "range (select S i) \<subseteq> (sample_set R)"
proof -
  have "select S i x \<in> (sample_set R)" for x
  proof -
    have "f' (cw.hash (f x) (g i)) mod p^n < p^n" using p_n_gt_0 by simp
    hence "select R (f' (cw.hash (f x) (g i)) mod p^n) \<in> sample_set R" 
      unfolding sample_set_def size_R by simp
    thus ?thesis by (simp add:S_eq)
  qed
  thus "range (select S i) \<subseteq> sample_set R" by auto
qed


lemma cw_space: "map_pmf g (pmf_of_set {..<p^(m*k)}) = pmf_of_set cw.space"
proof-
  have card_cw_space: "p ^ (m * k) = card (cw.space)" 
    unfolding cw.space_def cw.bounded_degree_polynomials_card  field_size
    by (simp add:power_mult)
  have card_cw_space_gt_0: "card (cw.space) > 0" 
    using card_gt_0_iff cw.finite_space cw.non_empty_bounded_degree_polynomials by blast

  show ?thesis
    unfolding g_def using card_cw_space card_cw_space_gt_0
    by (intro map_pmf_of_set_bij_betw some_bij cw.finite_space)
     auto
qed

lemma \<H>_single:
  assumes "x < d"
  shows "map_pmf (\<lambda>\<omega>. \<omega> x) (sample_pmf S) = sample_pmf R" (is "?L = ?R")
proof -

  have f_x_carr: "f x \<in> carrier (GF (p^m))"
    using assms d_lt_p_m
    by (intro bij_betw_apply[OF f_bij]) auto

  have "pmf (map_pmf (cw.hash (f x)) (pmf_of_set cw.space)) i = 
    pmf (pmf_of_set (carrier (GF (p ^ m)))) i" (is "?L1 = ?R1") for i
  proof -
    have "?L1 = cw.prob (cw.hash (f x) -` {i})"
      unfolding cw.M_def by (simp add:pmf_map)
    also have "... = real (card ({i} \<inter> carrier (GF (p ^ m)))) / real cw.field_size"
      using cw.prob_range[OF f_x_carr, where A="{i}" ] by (simp add:vimage_def)
    also have "... = ?R1"
      by (cases "i \<in> carrier (GF (p^m))", auto)
    finally  show ?thesis by simp
  qed

  hence b: "map_pmf (cw.hash (f x)) (pmf_of_set cw.space) = pmf_of_set (carrier (GF (p^m)))" 
    by (intro pmf_eqI) simp

  have c: "map_pmf f' (pmf_of_set (carrier (GF (p^m)))) = pmf_of_set {..<p^m}"
    unfolding f'_def  
    by (intro map_pmf_of_set_bij_betw bij_betw_the_inv_into f_bij) auto 

  have "n \<le> m" "p > 0" 
    using n_lt_m p_prime prime_gt_0_nat by auto
  hence d: "map_pmf (\<lambda>x. x mod p^n) (pmf_of_set {..<p^m}) = pmf_of_set {..<p^n}" 
    using split_pmf_mod[where a = "p^n" and b="p^(m-n)"] 
    by (simp add:power_add[symmetric])

  have "?L = map_pmf ((\<lambda>\<omega>. \<omega> x) \<circ> (select S)) (pmf_of_set {..<size S})"
    unfolding sample_pmf_def by (simp add:map_pmf_compose)
  also have "... = map_pmf (\<lambda>\<omega>. select S \<omega> x) (pmf_of_set {..<size S})"
    by (simp add:comp_def)
  also have "... = map_pmf (select R \<circ> (\<lambda>x. x mod p^n) \<circ> f' \<circ> (cw.hash (f x)) \<circ> g) (pmf_of_set {..<p^(m*k)})"
    unfolding S_eq by (simp add:comp_def)
  also have "... = map_pmf (select R) (pmf_of_set {..<p^n})"
    by (simp add:map_pmf_compose cw_space b c d)
  also have "... = ?R"
    unfolding sample_pmf_def size_R by simp
  finally show ?thesis by simp
qed

lemma \<H>_indep:
  "k_wise_indep_vars  k (\<lambda>_. discrete) (\<lambda>i \<omega>. \<omega> i) {..<d}" 
proof -
  let ?p = "map_pmf g (pmf_of_set {..<p ^ (m * k)})"
  let ?h = "(\<lambda>i x. select R (f' (cw.hash (f x) i) mod p ^ n))"

  have a:"cw.k_wise_indep_vars k (\<lambda>_. discrete) cw.hash (f ` {..<d})"
    using d_lt_p_m
    by (intro cw.k_wise_indep_subset[OF _ cw.k_wise_indep] image_subsetI bij_betw_apply[OF f_bij])
    auto

  have "cw.k_wise_indep_vars k (\<lambda>_. discrete) (\<lambda>i \<omega>. select R (f' (cw.hash i \<omega>) mod p^n)) (f ` {..<d})"
    by (intro cw.k_wise_indep_vars_compose[OF a]) auto
  moreover 
  have "inj_on f {..<p^m}" 
    using f_bij bij_betw_def by auto
  hence "inj_on f {..<d}" 
    using inj_on_subset d_lt_p_m by blast
  ultimately have "cw.k_wise_indep_vars k (\<lambda>_. discrete) (\<lambda>i \<omega>. select R (f' (cw.hash (f i) \<omega>) mod p ^ n)) {..<d}"
    using cw.k_wise_indep_vars_reindex[where f="f"] unfolding comp_def by auto

  hence "prob_space.k_wise_indep_vars (measure_pmf ((map_pmf ?h \<circ> map_pmf g) (pmf_of_set {..<p^(m*k)}))) k
     (\<lambda>_. discrete) (\<lambda>i \<omega>. \<omega> i) {..<d}"
    unfolding cw.M_def cw_space[symmetric] comp_def by (intro k_wise_indep_vars_map_pmf[where p="?p"]) auto

  hence "prob_space.k_wise_indep_vars (measure_pmf (map_pmf (\<lambda>i x. ?h (g i) x) (pmf_of_set {..<p^(m*k)}))) k
     (\<lambda>_. discrete) (\<lambda>i \<omega>. \<omega> i) {..<d}"
    unfolding map_pmf_compose[symmetric] by (simp add:comp_def)

  thus ?thesis
    unfolding M_def
    unfolding sample_pmf_def  S_eq by simp
qed
end

subsection "Geometric k-independent Hash Family"

fun count_zeros :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
  "count_zeros 0 k = 0" |
  "count_zeros (Suc n) k = (if odd k then 0 else 1 + count_zeros n (k div 2))"

lemma count_zeros_iff: "j \<le> n \<Longrightarrow> count_zeros n k \<ge> j \<longleftrightarrow> 2^j dvd k"
proof (induction j arbitrary: n k)
  case 0
  then show ?case by simp
next
  case (Suc j)
  then obtain n' where n_def: "n = Suc n'" using Suc_le_D by presburger
  show ?case using Suc unfolding n_def by auto 
qed

lemma count_zeros_max:
  "count_zeros n k \<le> n"
  by (induction n arbitrary: k) auto

definition \<G>' :: "nat \<Rightarrow> nat sample_space" where 
  "\<G>' n = \<lparr> size = 2^n, select = count_zeros n \<rparr>"

lemma \<G>'_range: "sample_set (\<G>' n) \<subseteq> {..n}"
  using count_zeros_max
  unfolding sample_set_def \<G>'_def by auto

lemma \<G>'_prob:
  "\<P>(\<omega> in sample_pmf (\<G>' n). \<omega> \<ge> j) = of_bool (j \<le> n) / 2^j" (is "?L = ?R")
proof (cases "j \<le> n")
  case True
  have a:"{..<(2^n)::nat} \<noteq> {}" 
    by (simp add: lessThan_empty_iff)
  have b:"finite {..<(2^n)::nat}" by simp

  define f :: "nat \<Rightarrow> nat" where "f = (\<lambda>x. x * 2^j)" 
  have d:"inj_on  f {..<2^(n-j)}" unfolding f_def by (intro inj_onI) simp

  have e:"2^j > (0::nat)" by simp

  have "y \<in> f ` {..< 2^(n-j)} \<longleftrightarrow> y \<in> {x. x < 2^n \<and> 2^j dvd x}" for y :: nat
  proof -
    have "y \<in> f ` {..< 2^(n-j)} \<longleftrightarrow> (\<exists>x. x < 2 ^ (n - j) \<and> y = 2 ^ j * x)"
      unfolding f_def by auto
    also have "... \<longleftrightarrow> (\<exists>x. 2^j * x < 2^j * 2 ^ (n-j) \<and> y = 2 ^ j * x)"
      using e by simp
    also have "... \<longleftrightarrow> (\<exists>x. 2^j * x < 2^n \<and> y = 2 ^ j * x)"
      using True by (subst power_add[symmetric]) simp
    also have "... \<longleftrightarrow> (\<exists>x. y < 2^n \<and> y = x * 2 ^ j)" 
      by (metis Groups.mult_ac(2))
    also have "... \<longleftrightarrow> y \<in> {x. x < 2^n \<and> 2^j dvd x}" by auto
    finally show ?thesis by simp
  qed

  hence c:"f ` {..< 2^(n-j)} = {x. x < 2^n \<and> 2^j dvd x}" by auto

  have "?L = measure (sample_pmf (\<G>' n)) {\<omega>. \<omega> \<ge> j}" by simp
  also have "... = measure (pmf_of_set {..<2^n}) {\<omega>. count_zeros n \<omega> \<ge> j}" 
    unfolding sample_pmf_def \<G>'_def by simp
  also have "... = real (card {x::nat. x < 2^n \<and> 2^j dvd x}) / 2^n"
    by (simp add: measure_pmf_of_set[OF a b] count_zeros_iff[OF True])
     (simp add:lessThan_def Collect_conj_eq) 
  also have "... = real (card (f ` {..<2^(n-j)})) / 2^n"
    by (simp add:c)
  also have "... = real (card ({..<(2^(n-j)::nat)})) / 2^n"
    by (simp add: card_image[OF d]) 
  also have "... = ?R"
    using True by (simp add:frac_eq_eq power_add[symmetric]) 
  finally show ?thesis by simp
next
  case False
  have "size (\<G>' n) > 0" unfolding \<G>'_def by simp
  hence "sample_space (\<G>' n)" unfolding sample_space_def by simp
  hence a: "set_pmf (sample_pmf (\<G>' n)) \<subseteq> {..n}"
    using sample_space.set_pmf_sample_pmf \<G>'_range by auto
  have "?L = measure (sample_pmf (\<G>' n)) {\<omega>. \<omega> \<ge> j}" by simp
  also have "... \<le> measure (sample_pmf (\<G>' n)) {}" 
    using a False
    by (intro measure_pmf.pmf_mono[where p="sample_pmf (\<G>' n)"])  auto
  also have "... = 0"
    by simp
  finally have "?L \<le> 0" by simp
  moreover have "?L \<ge>0 " by simp
  ultimately have "?L = 0" using order.antisym by blast
  then show ?thesis using False by simp
qed


definition \<G> :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) sample_space"
  where "\<G> k n = \<H> k n (\<G>' (max (nat \<lceil>log 2 n\<rceil>) 1))"

locale \<G>_locale = 
  fixes k n S
  assumes k_gt_0: "k > 0"
  assumes n_gt_0: "n > 0"
  defines "S \<equiv> \<G> k n"
begin

definition m where "m = max (nat \<lceil>log 2 n\<rceil>) 1"
definition R where "R = \<G>' m"

lemma size_R: "size R = 2^m" 
  unfolding R_def \<G>'_def by simp 

interpretation e: \<H>_locale "k" "n" "R" "\<G> k n"
proof -
  have "is_prime_power (size R)"
    unfolding size_R m_def by (intro is_prime_power) auto
  thus "\<H>_locale k R"
    using k_gt_0 by (simp add:\<H>_locale_def)
  show "\<G> k n \<equiv> \<H> k n R"
    unfolding \<G>_def R_def m_def by simp
qed

lemma \<G>_range: "select S i j \<le> max (nat \<lceil>log 2 n\<rceil>) 1"
proof -
  have "range (select (\<G> k n) i) \<subseteq> sample_set R" 
    using e.\<H>_range by simp
  also have "... \<subseteq> {..m}"
    unfolding R_def using \<G>'_range by simp
  finally have "range (select (\<G> k n) i) \<subseteq> {..m}" by simp
  thus "select S i j \<le> max (nat \<lceil>log 2 n\<rceil>) 1"
    unfolding S_def m_def by auto 
qed

lemma \<G>_size: "size (\<G> k n) > 0"
  using e.\<H>_size by simp

sublocale sample_space "S"
  unfolding S_def sample_space_def using  \<G>_size by simp

lemma \<G>_prob:
  assumes "x < n"
  shows "prob {f.  f x \<ge> j} = of_bool (j \<le> (max (nat \<lceil>log 2 n\<rceil>) 1)) / 2^j" (is "?L = ?R")
proof -
  have "?L = measure (map_pmf (\<lambda>f. f x) (sample_pmf S)) {x. x \<ge> j}"
    unfolding M_def by simp
  also have "... = measure (sample_pmf R) {x. x \<ge> j}"
    unfolding S_def 
    by (intro arg_cong2[where f="measure"] arg_cong[where f="measure_pmf"] e.\<H>_single assms) auto
  also have "... = of_bool (j \<le> m) /2^j" 
    unfolding R_def
    using \<G>'_prob by simp
  also have "... = ?R" unfolding m_def by simp
  finally show ?thesis by simp
qed

lemma \<G>_indep:
  "k_wise_indep_vars k (\<lambda>_. discrete) (\<lambda>i \<omega>. \<omega> i) {..<n}" 
  unfolding S_def using e.\<H>_indep by simp

end


end