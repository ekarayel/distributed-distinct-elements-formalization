theory Pseudorandom_Combinators
  imports 
    HOL.Rat 
    "Finite_Fields.Card_Irreducible_Polynomials" 
    "Universal_Hash_Families.Carter_Wegman_Hash_Family"
    "Frequency_Moments.Product_PMF_Ext"
begin

record 'a sample_space = 
  size :: "nat"
  select :: "nat \<Rightarrow> 'a"

definition "sample_set S = select S ` {..<size S}"

definition "sample_pmf S = map_pmf (select S) (pmf_of_set {..<size S})"

locale sample_space =
  fixes S
  assumes size_S: "size S > 0"
begin

definition M where "M = measure_pmf (sample_pmf S)"

sublocale prob_space "M"
  unfolding M_def using prob_space_measure_pmf by auto

lemma set_pmf_sample_pmf:
  "set_pmf (sample_pmf S) = sample_set S"
proof -
  have "set_pmf (pmf_of_set {..<size S}) = {..<size S}"
    using size_S by (intro set_pmf_of_set) auto
  thus ?thesis
    unfolding sample_pmf_def sample_set_def by simp
qed

lemma integrable_M[simp]:
  fixes f :: "'a \<Rightarrow> 'c::{banach, second_countable_topology}"
  shows "integrable M f"
proof -
  have " finite (set_pmf (sample_pmf S))" 
    unfolding set_pmf_sample_pmf sample_set_def 
    by (intro finite_imageI) simp
  thus ?thesis
    unfolding M_def 
    by (intro integrable_measure_pmf_finite)
qed

end

definition nat_sample_space :: "nat \<Rightarrow> nat sample_space" ("[_]\<^sub>S")
  where "nat_sample_space n = \<lparr> size = n, select = id \<rparr>"

lemma nat_sample_pmf: "sample_pmf ([x]\<^sub>S) = pmf_of_set {..<x}"
  unfolding nat_sample_space_def sample_pmf_def by simp

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

lemma split_pmf_mod_div': 
  assumes "a > (0::nat)"
  assumes "b > 0"
  shows "map_pmf (\<lambda>x. (x mod a, x div a)) (pmf_of_set {..<a * b}) = pmf_of_set ({..<a} \<times> {..<b})"
proof -
  have "x + a * y < a * b" if "x < a" "y < b" for x y
  proof -
    have a:"y+1 \<le> b" using that by simp
    have "x + a * y < a + a * y"
      using that by simp
    also have "... = a * (y+1)"
      by simp
    also have "... \<le> a * b"
      by (intro mult_left_mono a) auto
    finally show ?thesis by simp
  qed

  hence "bij_betw (\<lambda>x. (x mod a, x div a)) {..<a * b} ({..<a} \<times> {..<b})"
    using assms less_mult_imp_div_less
    by (intro bij_betwI[where g="(\<lambda>x. fst x + a * snd x)"])
     (auto simp add:mult.commute) 

  moreover have "a * b > 0" using assms by simp
  hence "{..<a * b} \<noteq> {}" by blast
  ultimately show "?thesis"
    by (intro map_pmf_of_set_bij_betw) auto 
qed

lemma pmf_of_set_prod_eq:
  assumes "A \<noteq> {}" "finite A"
  assumes "B \<noteq> {}" "finite B"
  shows  "pmf_of_set (A \<times> B) = pair_pmf (pmf_of_set A) (pmf_of_set B)"
proof -
  have "indicat_real (A \<times> B) (i, j) = indicat_real A i * indicat_real B j" for i j
    by (case_tac[!] "i \<in> A", case_tac[!] "j \<in> B") auto
  hence "pmf (pmf_of_set (A \<times> B)) (i,j) = pmf (pair_pmf (pmf_of_set A) (pmf_of_set B)) (i,j)" 
    for i j using assms by (simp add:pmf_pair)
  thus ?thesis
    by (intro pmf_eqI) auto
qed

lemma split_pmf_mod_div: 
  assumes "a > (0::nat)"
  assumes "b > 0"
  shows "map_pmf (\<lambda>x. (x mod a, x div a)) (pmf_of_set {..<a * b}) = 
    pair_pmf (pmf_of_set {..<a}) (pmf_of_set {..<b})"
  using assms 
  by (auto intro!: pmf_of_set_prod_eq simp add:split_pmf_mod_div') 

lemma split_pmf_mod: 
  assumes "a > (0::nat)"
  assumes "b > 0"
  shows "map_pmf (\<lambda>x. x mod a) (pmf_of_set {..<a * b}) = pmf_of_set {..<a}"
proof -
  have "map_pmf (\<lambda>x. x mod a) (pmf_of_set {..<a * b}) =
   map_pmf (fst \<circ> (\<lambda>x. (x mod a, x div a))) (pmf_of_set {..<a * b})"
    by (simp add:comp_def)
  also have "... = map_pmf fst (pair_pmf (pmf_of_set {..<a}) (pmf_of_set {..<b}))"
    by (simp add:map_pmf_compose split_pmf_mod_div[OF assms])
  also have "... = pmf_of_set {..<a}"
    by (simp add:map_fst_pair_pmf)
  finally show ?thesis by simp
qed

lemma prod_sample_pmf: 
  assumes "sample_space S"
  assumes "sample_space T"
  shows "sample_pmf (S \<times>\<^sub>S T) = pair_pmf (sample_pmf S) (sample_pmf T)" (is "?L = ?R")
proof -
  have size: "size S * size T > 0"
    using assms sample_space_def by (metis nat_0_less_mult_iff)
  hence a:"{..<size S * size T} \<noteq> {}" "finite {..<size S * size T}"
    using lessThan_empty_iff by auto
  have b:"x div size S mod size T = x div size S" if "x < size S * size T" for x
    by (simp add: algebra_simps less_mult_imp_div_less that)
  have "?L = map_pmf (\<lambda>i. (select S (i mod size S), select T (i div size S mod size T))) (pmf_of_set {..<size S * size T})"
    unfolding sample_pmf_def prod_sample_space_def by simp
  also have "... = map_pmf (\<lambda>i. (select S (i mod size S), select T (i div size S))) (pmf_of_set {..<size S * size T})"
    using b
    by (intro map_pmf_cong) (auto simp add: set_pmf_of_set[OF a])
  also have "... = map_pmf ((\<lambda>(x,y). (select S x, select T y)) \<circ> (\<lambda>i. (i mod size S, i div size S))) (pmf_of_set {..<size S * size T})"
    by (simp add:comp_def)
  also have "... = map_pmf (\<lambda>(x,y). (select S x, select T y)) (map_pmf (\<lambda>i. (i mod size S, i div size S)) (pmf_of_set {..<size S * size T}))"
    by (subst map_pmf_compose)  simp
  also have "... = map_pmf (\<lambda>(x,y). (select S x, select T y)) (pair_pmf (pmf_of_set {..<size S}) (pmf_of_set {..<size T}))"
    using size by (subst split_pmf_mod_div) auto
  also have "... = ?R"
    unfolding sample_pmf_def map_pair by simp
  finally show ?thesis
    by simp
qed

lemma prod_sample_space:
  assumes "sample_space S"
  assumes "sample_space T"
  shows "sample_space (S \<times>\<^sub>S T)"
proof -
  have "size (S \<times>\<^sub>S T) > 0"
    using assms sample_space.size_S sample_space_def
    by (simp add:prod_sample_space_def) blast
  thus ?thesis
    by (unfold_locales) simp
qed

definition \<E> :: "nat \<Rightarrow> rat \<Rightarrow> 'a sample_space \<Rightarrow> (nat \<Rightarrow> 'a) sample_space"
  where "\<E> l \<Lambda> S = undefined"

lemma \<E>_range:
  assumes "size S > 0"
  shows "select (\<E> l \<Lambda> S) i j \<in> sample_set S"
  sorry


end