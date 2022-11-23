theory Pseudorandom_Combinators
  imports 
    HOL.Rat 
    "Finite_Fields.Card_Irreducible_Polynomials" 
    "Universal_Hash_Families.Carter_Wegman_Hash_Family"
    "Frequency_Moments.Product_PMF_Ext"
begin

definition GF :: "nat \<Rightarrow> int set list set ring"
  where "GF n = (SOME F. finite_field F \<and> order F = n)"


definition some_bij :: "'a set \<Rightarrow> (nat \<Rightarrow> 'a)"
  where "some_bij A = (SOME f. inj_on f {..<card A} \<and> f ` {..<card A} = A \<and> f ` {card A..} = {f 0})"

definition is_prime_power :: "nat \<Rightarrow> bool"
  where "is_prime_power n \<longleftrightarrow> (\<exists>p k. Factorial_Ring.prime p \<and> k > 0 \<and> n = p^k)"
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

record 'a sample_space = 
  size :: "nat"
  select :: "nat \<Rightarrow> 'a"

definition "sample_set S = (select S) ` {..<(size S)}"

definition nat_sample_space :: "nat \<Rightarrow> nat sample_space" ("[_]\<^sub>S")
  where "nat_sample_space n = \<lparr> size = n, select = id \<rparr>"

definition prod_sample_space :: 
  "'a sample_space \<Rightarrow> 'b sample_space \<Rightarrow> ('a \<times> 'b) sample_space" (infixr "\<times>\<^sub>S" 65)
  where 
    "prod_sample_space s t = 
      \<lparr> size = size s * size t, 
        select = (\<lambda>i. (select s (i mod (size s)), select t ((i div (size s)) mod (size t)))) \<rparr>"

lemma prod_select:
  assumes "size S > 0"
  assumes "size T > 0" 
  shows "select (S \<times>\<^sub>S T) x \<in> sample_set S \<times> sample_set T"
  using assms
  by (simp add:prod_sample_space_def sample_set_def)

lemma prod_sample_set:  "sample_set (S \<times>\<^sub>S T) \<subseteq> sample_set S \<times> sample_set T" 
proof 
  fix x
  assume "x \<in> sample_set (S \<times>\<^sub>S T)"
  then obtain j where j_def: "j < size (S \<times>\<^sub>S T)" and x_def:"x = select (S \<times>\<^sub>S T) j"
    unfolding sample_set_def by auto
  have "size (S \<times>\<^sub>S T) > 0" using j_def by simp
  hence "size S > 0 \<and> size T > 0" 
    unfolding prod_sample_space_def by simp
  thus "x \<in> sample_set S \<times> sample_set T"
    unfolding x_def  by (intro prod_select) auto
qed

definition \<E> :: "nat \<Rightarrow> rat \<Rightarrow> 'a sample_space \<Rightarrow> (nat \<Rightarrow> 'a) sample_space"
  where "\<E> l \<Lambda> S = undefined"

lemma \<E>_range:
  assumes "size S > 0"
  shows "select (\<E> l \<Lambda> S) i j \<in> sample_set S"
  sorry

definition \<H> :: "nat \<Rightarrow> nat \<Rightarrow> 'a sample_space \<Rightarrow> (nat \<Rightarrow> 'a) sample_space"
  where "\<H> k d R = (
    let (p,n) = split_prime_power (size R);
        m = (LEAST j. d \<le> p^j \<and> j \<ge> n);
        f = some_bij (carrier (GF (p^m)));
        f' = the_inv_into {..<(p^m)} f;
        g = some_bij (bounded_degree_polynomials (GF (p^m)) k) in
    \<lparr> size = p^m, select = (\<lambda>i x. select R ((f' (ring.hash (GF (p^m)) (f i) (g i))) mod p^n))\<rparr>)"

lemma 
  fixes d :: nat
  assumes "is_prime_power (size R)"
  assumes "k > 0"
  defines "S \<equiv> (\<H> k d R)"
  shows 
    \<H>_size: "size S > 0" and
    \<H>_range: "range (select S i) \<subseteq> (sample_set R)" and
(*    unif: "\<And>x. x < d \<Longrightarrow> y \<in> sample_set R \<Longrightarrow> \<P>(\<omega> in pmf_of_set {..< size S}. select S \<omega> x = y) = 1/(real (size R))" and
    unif': "\<And>x. x < d \<Longrightarrow> map_pmf (\<lambda>\<omega>. select S \<omega> x) (pmf_of_set {..<size S}) = map_pmf (select R) (pmf_of_set {..<size R})" and *)
    unif'': 
      "\<And>D. D \<subseteq> {..<d} \<Longrightarrow> card D \<le> k \<Longrightarrow> map_pmf (\<lambda>\<omega>. (\<lambda>x \<in> D. select S \<omega> x)) (pmf_of_set {..<size S}) = 
      map_pmf (\<lambda>\<omega>. (\<lambda>x \<in> D. select R (\<omega> x))) (prod_pmf D (\<lambda>_. pmf_of_set {..<size R}))" (is "\<And>D. ?A D \<Longrightarrow> ?B D \<Longrightarrow> ?C D") (* and   
    indep: "prob_space.k_wise_indep_vars (pmf_of_set {..<size S}) k (\<lambda>_. discrete) (\<lambda>i \<omega>. select S \<omega> i) {..<d}" *)
proof -
  obtain p n where p_n_altdef: "n > 0" "Factorial_Ring.prime p" and size_R:"size R = p^n"
    using assms(1) unfolding is_prime_power_def by auto
  have p_n_def: "(p,n) = split_prime_power (size R)"
    unfolding size_R
    by (intro split_prime_power[symmetric] p_n_altdef)
  define m where "m = (LEAST j. d \<le> p^j \<and> j \<ge> n)"
  define f where "f = some_bij (carrier (GF (p^m)))"
  define f' where "f' = the_inv_into {..<(p^m)} f"
  define g where "g = some_bij (bounded_degree_polynomials (GF (p^m)) k)"

  have p_n_gt_0: "p^n > 0" 
    by (metis p_n_altdef(2) gr0I not_prime_0 power_not_zero)

  have S_eq: "S = \<lparr> size = p^m, select = (\<lambda> i x. select R ((f' (ring.hash (GF (p^m)) (f i) (g i))) mod p^n )) \<rparr>"
    unfolding S_def \<H>_def 
    by (simp add:p_n_def[symmetric] m_def[symmetric] f_def[symmetric] g_def f'_def)

  have "p^m > 0"
    by (metis p_n_altdef(2) gr0I not_prime_0 power_not_zero)
  thus "size S > 0" 
    unfolding S_eq by simp

  have "select S i x \<in> (sample_set R)" for x
  proof -
    have "f' (ring.hash (GF (p ^ m)) (f i) (g i)) mod p^n < p^n" using p_n_gt_0 by simp
    hence "select R (f' ((ring.hash (GF (p ^ m)) (f i) (g i))) mod p^n) \<in> sample_set R" 
      unfolding sample_set_def size_R by simp
    thus ?thesis by (simp add:S_eq)
  qed
  thus "range (select S i) \<subseteq> (sample_set R)" by auto

  show "\<And>D. ?A D \<Longrightarrow> ?B D \<Longrightarrow> ?C D" sorry
qed

fun count_zeros :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
  "count_zeros 0 k = 0" |
  "count_zeros (Suc n) k = (if odd k then 0 else 1 + count_zeros n (k div 2))"

lemma count_zeros_max:
  "count_zeros n k \<le> n"
  by (induction n arbitrary: k) auto

lemma is_prime_power: "Factorial_Ring.prime p \<Longrightarrow> k > 0 \<Longrightarrow> is_prime_power (p^k)" 
  unfolding is_prime_power_def by auto

definition \<G>' where 
  "\<G>' n = \<lparr> size = 2^n, select = count_zeros n \<rparr>"

lemma sample_set_\<G>': "sample_set (\<G>' n) \<subseteq> {..n}"
  using count_zeros_max
  unfolding sample_set_def \<G>'_def by auto

definition \<G> :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) sample_space"
  where "\<G> k n = \<H> k n (\<G>' (max (nat \<lceil>log 2 n\<rceil>) 1))"

lemma  
  assumes "k > 0"
  assumes "n > 0"
  shows 
    \<G>_range: "select (\<G> k n) i j \<le> max (nat \<lceil>log 2 n\<rceil>) 1" and
    \<G>_size: "size (\<G> k n) > 0"
proof -
  let ?p = "max (nat \<lceil>log 2 n\<rceil>) 1"
  let ?R = "\<G>' ?p"
  have size_R: "size ?R = 2^?p" 
    unfolding \<G>'_def by simp 
  have a:"is_prime_power (size ?R)" 
    unfolding size_R by (intro is_prime_power) auto 

  hence "range (select (\<H> k n ?R) i) \<subseteq> sample_set ?R" 
    by (intro \<H>_range assms(1)) auto
  also have "... \<subseteq> {..?p}"
    using sample_set_\<G>' by simp
  finally have "range (select (\<H> k n ?R) i) \<subseteq> {..?p}" by simp
  thus "select (\<G> k n) i j \<le> max (nat \<lceil>log 2 n\<rceil>) 1"
    by (auto simp add:\<G>_def) 
  show "size (\<G> k n) > 0"
    unfolding \<G>_def by (intro \<H>_size a assms)
qed




end