theory Pseudorandom_Combinators
  imports
    HOL.Rat 
    "Finite_Fields.Card_Irreducible_Polynomials" 
    "Universal_Hash_Families.Carter_Wegman_Hash_Family"
    "Frequency_Moments.Product_PMF_Ext"
begin

record 'a sample_space = 
  size :: "nat"
  sample_space_select :: "nat \<Rightarrow> 'a"

definition sample_pmf
  where "sample_pmf S = map_pmf (sample_space_select S) (pmf_of_set {..<size S})"

definition "sample_space S \<equiv> size S > 0" 

definition "select S k = (sample_space_select S (if k < size S then k else 0))" 

definition "sample_set S = select S ` {..<size S}"

lemma sample_space_imp_ne:
  assumes "sample_space S"
  shows "{..<size S} \<noteq> {}"
  using assms unfolding sample_space_def by auto

lemma sample_pmf_alt:
  assumes "sample_space S"
  shows "sample_pmf S = map_pmf (select S) (pmf_of_set {..<size S})"
  using sample_space_imp_ne[OF assms] unfolding sample_pmf_def select_def
  by (intro map_pmf_cong refl) simp

lemma sample_space_alt:
  assumes "sample_space S"
  shows "sample_set S = set_pmf (sample_pmf S)"
  using sample_space_imp_ne[OF assms]
  unfolding sample_set_def sample_pmf_alt[OF assms]
  by simp

lemma sample_set_alt:
  assumes "sample_space S"
  shows "sample_set S = sample_space_select S ` {..<size S}"
  unfolding sample_set_def select_def
  by (intro image_cong) auto

lemma select_range:
  assumes "sample_space S"
  shows "select S i \<in> sample_set S"
  using assms unfolding sample_space_def select_def sample_set_def by auto

definition nat_sample_space :: "nat \<Rightarrow> nat sample_space" ("[_]\<^sub>S")
  where "nat_sample_space n = \<lparr> size = n, select = id \<rparr>"

lemma nat_sample_pmf: 
  "sample_pmf ([x]\<^sub>S) = pmf_of_set {..<x}"
  unfolding nat_sample_space_def sample_pmf_def by simp

definition prod_sample_space :: 
  "'a sample_space \<Rightarrow> 'b sample_space \<Rightarrow> ('a \<times> 'b) sample_space" (infixr "\<times>\<^sub>S" 65)
  where 
    "prod_sample_space s t = 
      \<lparr> size = size s * size t, 
        select = (\<lambda>i. (select s (i mod (size s)), select t (i div (size s)))) \<rparr>"

lemma nat_sample_space[simp]:
  assumes "n > 0"
  shows "sample_space [n]\<^sub>S"
  using assms
  unfolding sample_space_def nat_sample_space_def by simp

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
  using assms by (auto intro!: pmf_of_set_prod_eq simp add:split_pmf_mod_div') 

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

  have "?L = map_pmf (\<lambda>i. (select S (i mod size S), select T (i div size S))) 
    (pmf_of_set {..<size S * size T})"
    unfolding sample_pmf_def prod_sample_space_def by simp
  also have "... = map_pmf ((\<lambda>(x,y). (select S x, select T y)) \<circ> (\<lambda>i. (i mod size S, i div size S))) 
    (pmf_of_set {..<size S * size T})"
    by (simp add:comp_def)
  also have "... = map_pmf (\<lambda>(x,y). (select S x, select T y)) 
    (map_pmf (\<lambda>i. (i mod size S, i div size S)) (pmf_of_set {..<size S * size T}))"
    by (subst map_pmf_compose)  simp
  also have "... = map_pmf (\<lambda>(x,y). (select S x, select T y)) 
    (pair_pmf (pmf_of_set {..<size S}) (pmf_of_set {..<size T}))"
    using size by (subst split_pmf_mod_div) auto
  also have "... = ?R"
    unfolding sample_pmf_alt[OF assms(1)] sample_pmf_alt[OF assms(2)] map_pair by simp
  finally show ?thesis
    by simp
qed

lemma prod_sample_space[simp]:
  assumes "sample_space S" "sample_space T"
  shows "sample_space (S \<times>\<^sub>S T)"
  using assms
  unfolding sample_space_def prod_sample_space_def by simp

lemma prod_sample_set: 
  assumes "sample_space S"
  assumes "sample_space T"
  shows "sample_set (S \<times>\<^sub>S T) = sample_set S \<times> sample_set T" (is "?L = ?R")
  using assms by (simp add:sample_space_alt prod_sample_pmf)


declare [[coercion sample_pmf]]

lemma integrable_sample_pmf[simp]:
  fixes f :: "'a \<Rightarrow> 'c::{banach, second_countable_topology}"
  assumes "sample_space S"
  shows "integrable (measure_pmf (sample_pmf S)) f"
proof -
  have "finite (set_pmf (pmf_of_set {..<size S}))"
    using assms sample_space_def
    by (subst set_pmf_of_set) auto
  hence "finite (set_pmf (sample_pmf S))"
    unfolding sample_pmf_def by simp
  thus ?thesis
    by (intro integrable_measure_pmf_finite)
qed


end