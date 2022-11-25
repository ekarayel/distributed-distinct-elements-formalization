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

definition "sample_set S = (select S) ` {..<(size S)}"

definition "sample_pmf S = map_pmf (select S) (pmf_of_set {..<(size S)})"

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


definition \<E> :: "nat \<Rightarrow> rat \<Rightarrow> 'a sample_space \<Rightarrow> (nat \<Rightarrow> 'a) sample_space"
  where "\<E> l \<Lambda> S = undefined"

lemma \<E>_range:
  assumes "size S > 0"
  shows "select (\<E> l \<Lambda> S) i j \<in> sample_set S"
  sorry





end