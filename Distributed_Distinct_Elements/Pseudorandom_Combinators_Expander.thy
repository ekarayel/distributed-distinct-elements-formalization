theory Pseudorandom_Combinators_Expander
  imports 
    Pseudorandom_Combinators
    Expander_Graphs.Expander_Graphs_Strongly_Explicit
    Distributed_Distinct_Elements_Tail_Bounds
begin

unbundle intro_cong_syntax

definition \<E> :: "nat \<Rightarrow> real \<Rightarrow> 'a sample_space \<Rightarrow> (nat \<Rightarrow> 'a) sample_space"
  where "\<E> l \<Lambda> S = (let e = see_standard (size S) \<Lambda> in 
    \<lparr> size = see_size e * see_degree e^(l-1), 
      sample_space_select = (\<lambda>i j. select S (see_sample_walk e (l-1) i ! j)) \<rparr>) "

locale expander_sample_space =
  fixes l :: nat
  fixes \<Lambda> :: real
  fixes S :: "'a sample_space"
  assumes l_gt_0: "l > 0"
  assumes \<Lambda>_gt_0: "\<Lambda> > 0"
  assumes sample_space_S: "sample_space S"
begin

definition e where "e = see_standard (size S) \<Lambda>"

lemma size_S_gt_0: "size S > 0" 
  using sample_space_S unfolding sample_space_def by simp

lemma \<E>_alt: "(\<E> l \<Lambda> S) = 
  \<lparr> size = see_size e * see_degree e^(l-1), 
    sample_space_select = (\<lambda>i j. select S (see_sample_walk e (l-1) i ! j)) \<rparr>"
  unfolding \<E>_def e_def[symmetric] by (simp add:Let_def)

lemmas see_standard = see_standard[OF size_S_gt_0 \<Lambda>_gt_0]

sublocale E: regular_graph "graph_of e"
  using see_standard(1) unfolding is_expander_def e_def by auto

lemma e_deg_gt_0: "see_degree e > 0"
  unfolding e_def see_standard by simp

lemma e_size_gt_0: "see_size e > 0"
  unfolding e_def see_standard using size_S_gt_0 by simp

lemma sample_space: "sample_space (\<E> l \<Lambda> S)"
  unfolding sample_space_def \<E>_alt using e_size_gt_0 e_deg_gt_0 by simp

lemma range: "select (\<E> l \<Lambda> S) i j \<in> sample_set S"
proof -
  define \<alpha> where "\<alpha> = select (\<E> l \<Lambda> S) i" 
  have "\<alpha> \<in> sample_set (\<E> l \<Lambda> S)"
    unfolding \<alpha>_def by (intro select_range sample_space)
  then obtain k where "\<alpha> = sample_space_select  (\<E> l \<Lambda> S) k"
    using sample_set_alt[OF sample_space] by auto
  hence "\<alpha> j \<in> sample_set S" 
    unfolding \<E>_alt using select_range[OF sample_space_S] by simp
  thus ?thesis
    unfolding \<alpha>_def by simp
qed

lemma walks: 
  defines "R \<equiv> map_pmf (\<lambda>xs i. select S (xs ! i)) (pmf_of_multiset (walks (graph_of e) l))"
  shows "sample_pmf (\<E> l \<Lambda> S) = R"
proof -
  let ?S = "{..<see_size e * see_degree e ^ (l-1)}"
  let ?T = "(map_pmf (see_sample_walk e (l-1)) (pmf_of_set ?S))"

  have "0 \<in> ?S" 
    using e_size_gt_0 e_deg_gt_0 l_gt_0 by auto
  hence "?S \<noteq> {}" 
    by blast
  hence "?T = pmf_of_multiset {#see_sample_walk e (l-1) i. i \<in># mset_set ?S#}"
    by (subst map_pmf_of_set) simp_all
  also have "... = pmf_of_multiset (walks' (graph_of e) (l-1))"
    by (subst see_sample_walk) auto
  also have "... = pmf_of_multiset (walks (graph_of e) l)"
    unfolding walks_def using l_gt_0 by (cases l, simp_all)
  finally have 0:"?T = pmf_of_multiset (walks (graph_of e) l)" 
    by simp

  have "sample_pmf (\<E> l \<Lambda> S) = map_pmf (\<lambda>xs j. select S (xs ! j)) ?T"
    unfolding map_pmf_comp sample_pmf_def \<E>_alt by simp
  also have "... = R"
    unfolding 0 R_def by simp
  finally show ?thesis by simp
qed

lemma deviation_bound:
  fixes f :: "'a \<Rightarrow> real"
  assumes "l > 0"
  assumes "\<Lambda> \<le> exp (-real l * ln (real l)^3)"
  assumes "\<And>x. x \<ge> 20 \<Longrightarrow> measure (sample_pmf S) {v. f v \<ge> x} \<le> exp (-x * ln x^3)"
  shows "measure (\<E> l \<Lambda> S) {\<omega>. (\<Sum>i<l. f (\<omega> i)) \<ge> C\<^sub>1 * l} \<le> exp (- real l)"  (is "?L \<le> ?R")
proof -
  let ?w = "pmf_of_multiset (walks (graph_of e) l)"

  have "E.\<Lambda>\<^sub>a \<le> \<Lambda>"
    using see_standard(1) unfolding is_expander_def e_def by simp
  also have "... \<le>  exp (- real l * ln (real l) ^ 3)"
    using assms(2) by simp
  finally have 0: "E.\<Lambda>\<^sub>a \<le> exp (- real l * ln (real l) ^ 3)"
    by simp

  have 1: "measure (pmf_of_set (verts (graph_of e))) {v. x \<le> f (select S v)} \<le> exp (- x*ln x^3)"
    (is "?L1 \<le> ?R1") if "x \<ge> 20" for x
  proof -
    have "?L1 = measure (map_pmf (select S) (pmf_of_set {..<size S})) {v. x \<le> f v}"
      using see_standard(2) unfolding e_def graph_of_def by simp
    also have "... = measure (sample_pmf S) {v. x \<le> f v}"
      unfolding sample_pmf_alt[OF sample_space_S] by simp
    also have "... \<le> ?R1"
      by (intro assms(3) that)
    finally show ?thesis 
      by simp
  qed

  have "?L = measure ?w {w. C\<^sub>1 * real l \<le> (\<Sum>i<l. f (select S (w ! i)))}"
    unfolding walks by simp
  also have "... = measure ?w {ws. C\<^sub>1 * real l \<le> (\<Sum>w\<leftarrow>ws. f (select S w))}"
    using E.walks_nonempty E.set_walks_3 atLeast0LessThan
    unfolding sum_list_sum_nth by (intro measure_pmf_cong) simp
  also have "... \<le> ?R"
    by (intro E.deviation_bound assms(1) 0 1)
  finally show ?thesis by simp
qed

lemma tail_bound:
  fixes T
  assumes "l > 0" "\<Lambda> > 0"
  defines "\<mu> \<equiv> measure (sample_pmf S) {w. T w}"
  assumes "\<gamma> < 1" "\<mu> + \<Lambda> \<le> \<gamma>"
  shows "measure (\<E> l \<Lambda> S) {w. real (card {i \<in> {..<l}. T (w i)}) \<ge> \<gamma>*l} 
    \<le> exp (- real l * (\<gamma> * ln (1/(\<mu>+\<Lambda>)) - 2 * exp(-1)))" (is "?L \<le> ?R")
proof -
  let ?w = "pmf_of_multiset (walks (graph_of e) l)"
  define V where "V = {v\<in> verts (graph_of e). T (select S v)} "

  have 0: "card {i \<in> {..<l}. T (select S (w ! i))} = card {i \<in> {..<l}. w ! i \<in> V}" 
    if "w  \<in> set_pmf (pmf_of_multiset (walks (graph_of e) l))" for w
  proof -
    have a0: "w \<in># walks (graph_of e) l" using that E.walks_nonempty by simp
    have "w ! i \<in> verts (graph_of e)" if "i < l" for i
      using that E.set_walks_3[OF a0] by auto
    thus ?thesis
      unfolding V_def
      by (intro arg_cong[where f="card"] restr_Collect_cong) auto
  qed

  have 1:"E.\<Lambda>\<^sub>a \<le> \<Lambda>"
    using see_standard(1) unfolding is_expander_def e_def by simp

  have 2: "V \<subseteq> verts (graph_of e)"
    unfolding V_def by simp

  have "\<mu> = measure (pmf_of_set {..<size S}) ({v. T (select S v)})"
    unfolding \<mu>_def sample_pmf_alt[OF sample_space_S] 
    by simp
  also have "... = real (card ({v\<in>{..<size S}. T (select S v)})) / real (size S)"
    using size_S_gt_0 by (subst measure_pmf_of_set) (auto simp add:Int_def)
  also have "... = real (card V) / card (verts (graph_of e))"
    unfolding V_def graph_of_def e_def using see_standard by (simp add:Int_commute)
  finally have \<mu>_eq: "\<mu> = real (card V) / card (verts (graph_of e))" 
    by simp

  have "?L = measure ?w {y. \<gamma> * real l \<le> real (card {i \<in> {..<l}. T (select S (y ! i))})}"
    unfolding walks by simp
  also have "... = measure ?w {y. \<gamma> * real l \<le> real (card {i \<in> {..<l}. y ! i \<in> V})}"
    using 0 by (intro measure_pmf_cong) (simp)
  also have "... \<le> ?R"
    using assms(5) unfolding \<mu>_eq
    by (intro E.walk_tail_bound_2 assms(1,2,4) 1 2) auto
  finally show ?thesis
    by simp
qed

end

unbundle no_intro_cong_syntax

end