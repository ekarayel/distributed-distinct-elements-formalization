subsection "Uniform k-independent Hash Family"

theory Pseudorandom_Combinators_Hash
  imports Pseudorandom_Combinators
    "Finite_Fields.Card_Irreducible_Polynomials" 
    "Universal_Hash_Families.Carter_Wegman_Hash_Family"
    "Frequency_Moments.Product_PMF_Ext"
begin

definition GF :: "nat \<Rightarrow> int set list set ring"
  where "GF n = (SOME F. finite_field F \<and> order F = n)"

definition some_bij :: "'a set \<Rightarrow> (nat \<Rightarrow> 'a)"
  where "some_bij A = (SOME f. inj_on f {..<card A} \<and> f ` {..<card A} = A \<and> f ` {card A..} = {f 0})"

lemma some_bij:
  assumes "finite A"
  shows "bij_betw (some_bij f) {..<card A} A"
  sorry

definition is_prime_power :: "nat \<Rightarrow> bool"
  where "is_prime_power n \<longleftrightarrow> (\<exists>p k. Factorial_Ring.prime p \<and> k > 0 \<and> n = p^k)"

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
    \<lparr> size = p^m, select = (\<lambda>i x. select R ((f' (ring.hash (GF (p^m)) (f x) (g i))) mod p^n))\<rparr>)"

(* TODO: size = p^(m*k) *)

locale \<H>_locale =
  fixes k d R S
  assumes size_R_assm: "is_prime_power (size R)"
  assumes k_gt_0: "k > 0"
  defines "S \<equiv> (\<H> k d R)"
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
definition g where "g = some_bij (bounded_degree_polynomials (GF (p^m)) k)"

interpretation cw: carter_wegman_hash_family "GF (p^m)" "k"
  apply (intro carter_wegman_hash_familyI k_gt_0)
  sorry

lemma p_n_gt_0: "p^n > 0" 
  by (metis p_prime gr0I not_prime_0 power_not_zero)

lemma p_m_gt_0: "p^m > 0"
  by (metis p_prime gr0I not_prime_0 power_not_zero)

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

lemma S_eq: "S = \<lparr> size = p^m, select = (\<lambda> i x. select R (f' (cw.hash (f x) (g i)) mod p^n )) \<rparr>"
  unfolding S_def \<H>_def 
  by (simp add:p_n_def[symmetric] m_def[symmetric] f_def[symmetric] g_def f'_def Let_def)

lemma \<H>_size: "size S > 0" 
  unfolding S_eq using p_m_gt_0 by simp

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


lemma \<H>_single:
  assumes "x < d"
  shows "map_pmf (\<lambda>\<omega>. \<omega> x) (sample_pmf S) = sample_pmf R" (is "?L = ?R")
proof -
  have a: "map_pmf g (pmf_of_set {..<p^m}) = pmf_of_set cw.space"
    apply (intro map_pmf_of_set_bij_betw)
    sorry

  have f_x_carr: "f x \<in> carrier (GF (p^m))"
    sorry

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
    apply (intro map_pmf_of_set_bij_betw)
    sorry

  have "n \<le> m" "p > 0" 
    using n_lt_m p_prime prime_gt_0_nat by auto
  hence d: "map_pmf (\<lambda>x. x mod p^n) (pmf_of_set {..<p^m}) = pmf_of_set {..<p^n}" 
    using split_pmf_mod[where a = "p^n" and b="p^(m-n)"] 
    by (simp add:power_add[symmetric])

  have "?L = map_pmf ((\<lambda>\<omega>. \<omega> x) \<circ> (select S)) (pmf_of_set {..<size S})"
    unfolding sample_pmf_def by (simp add:map_pmf_compose)
  also have "... = map_pmf (\<lambda>\<omega>. select S \<omega> x) (pmf_of_set {..<size S})"
    by (simp add:comp_def)
  also have "... = map_pmf (select R \<circ> (\<lambda>x. x mod p^n) \<circ> f' \<circ> (cw.hash (f x)) \<circ> g) (pmf_of_set {..<p^m})"
    unfolding S_eq by (simp add:comp_def)
  also have "... = map_pmf (select R) (pmf_of_set {..<p^n})"
    by (simp add:map_pmf_compose a b c d)
  also have "... = ?R"
    unfolding sample_pmf_def size_R by simp
  finally show ?thesis by simp
qed


lemma \<H>_indep:
  "prob_space.k_wise_indep_vars (sample_pmf S) k (\<lambda>_. discrete) (\<lambda>i \<omega>. \<omega> i) {..<d}" 
  sorry
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

lemma sample_set_\<G>': "sample_set (\<G>' n) \<subseteq> {..n}"
  using count_zeros_max
  unfolding sample_set_def \<G>'_def by auto

lemma \<G>'_prob:
  assumes "j \<le> n" 
  shows "\<P>(\<omega> in sample_pmf (\<G>' n). \<omega> \<ge> j) = 1 / 2^j" (is "?L = ?R")
proof -
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
      using assms by (subst power_add[symmetric]) simp
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
    by (simp add: measure_pmf_of_set[OF a b] count_zeros_iff[OF assms])
     (simp add:lessThan_def Collect_conj_eq) 
  also have "... = real (card (f ` {..<2^(n-j)})) / 2^n"
    by (simp add:c)
  also have "... = real (card ({..<(2^(n-j)::nat)})) / 2^n"
    by (simp add: card_image[OF d]) 
  also have "... = ?R"
    using assms by (simp add:frac_eq_eq power_add[symmetric]) 
  finally show ?thesis by simp
qed


definition \<G> :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) sample_space"
  where "\<G> k n = \<H> k n (\<G>' (max (nat \<lceil>log 2 n\<rceil>) 1))"

locale \<G>_locale =
  fixes k n  S
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
    unfolding R_def using sample_set_\<G>' by simp
  finally have "range (select (\<G> k n) i) \<subseteq> {..m}" by simp
  thus "select S i j \<le> max (nat \<lceil>log 2 n\<rceil>) 1"
    unfolding S_def m_def by auto 
qed

lemma \<G>_size: "size (\<G> k n) > 0"
  using e.\<H>_size by simp

lemma
  assumes "x < n"
  shows "\<P>(f in sample_pmf S. f x \<ge> j) = 1/2^j" (is "?L = ?R")
proof -
  have "?L = measure (map_pmf (\<lambda>f. f x) (sample_pmf S)) {x. x \<ge> j}"
    by simp
  also have "... = measure (sample_pmf R) {x. x \<ge> j}"
    unfolding S_def 
    by (intro arg_cong2[where f="measure"] arg_cong[where f="measure_pmf"] e.\<H>_single assms) auto
  also have "... = ?R" 
    unfolding R_def
    using \<G>'_prob sorry
  finally show ?thesis by simp
qed

end


end