theory Expander_Graphs_2
  imports  
    "HOL-Library.Multiset" 
    "HOL-Probability.Probability_Mass_Function"
    "Expander_Graphs"
    "Frequency_Moments.Frequency_Moments_Preliminary_Results"
    "Balls_and_Bins"
begin

lemma count_mset_exp: "count A x = size (filter_mset (\<lambda>y. y = x) A)"
  by (induction A, simp, simp)

lemma count_image_mset_inj:
  assumes "inj f"
  shows "count (image_mset f A) (f x) = count A x"
proof (cases "x \<in> set_mset A")
  case True
  hence "f -` {f x} \<inter> set_mset A = {x}" 
    using assms by (auto simp add:vimage_def inj_def) 
  then show ?thesis by (simp add:count_image_mset)
next
  case False
  hence "f -` {f x} \<inter> set_mset A = {}" 
    using assms by (auto simp add:vimage_def inj_def) 
  thus ?thesis  using False by (simp add:count_image_mset count_eq_zero_iff)
qed

lemma count_image_mset_0_triv:
  assumes "x \<notin> range f"
  shows "count (image_mset f A) x = 0" 
proof -
  have "x \<notin> set_mset (image_mset f A)" 
    using assms by auto
  thus ?thesis 
    by (meson count_inI)
qed

lemma last_in: "set x \<subseteq> A \<Longrightarrow> x \<noteq> [] \<Longrightarrow> last x \<in> A"
  by auto

lemma filter_mset_ex_predicates:
  assumes "\<And>x. \<not> P x \<or> \<not> Q x"
  shows "filter_mset P M + filter_mset Q M = filter_mset (\<lambda>x. P x \<or> Q x) M"
  using assms by (induction M, auto)

lemma sum_count_2: 
  assumes "finite F"
  shows "sum (count M) F = size (filter_mset (\<lambda>x. x \<in> F) M)"
  using assms
proof (induction F rule:finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  have "sum (count M) (insert x F) = size ({#y \<in># M. y = x#} + {#x \<in># M. x \<in> F#})"
    using insert(1,2,3) by (simp add:count_mset_exp)
  also have "... = size ({#y \<in># M. y = x \<or> y \<in> F#})"
    using insert(2)
    by (intro arg_cong[where f="size"] filter_mset_ex_predicates) simp
  also have "... = size (filter_mset (\<lambda>y. y \<in> insert x F) M)"
    by simp
  finally show ?case by simp
qed

lemma sum_mset_conv: 
  fixes f :: "'a \<Rightarrow> 'b::{semiring_1}"
  shows "sum_mset (image_mset f A) = sum (\<lambda>x. of_nat (count A x) * f x) (set_mset A)"
proof (induction A rule: disj_induct_mset)
  case 1
  then show ?case by simp
next
  case (2 n M x)
  moreover have "count M x = 0" using 2 by (simp add: count_eq_zero_iff)
  moreover have "\<And>y. y \<in> set_mset M \<Longrightarrow> y \<noteq> x" using 2 by blast
  ultimately show ?case by (simp add:algebra_simps) 
qed

lemma sum_mset_conv_2: 
  fixes f :: "'a \<Rightarrow> 'b::{semiring_1}"
  assumes "set_mset A \<subseteq> B" "finite B"
  shows "sum_mset (image_mset f A) = sum (\<lambda>x. of_nat (count A x) * f x) B" (is "?L = ?R")
proof -
  have "?L = sum (\<lambda>x. of_nat (count A x) * f x) (set_mset A)"
    unfolding sum_mset_conv by simp
  also have "... = ?R"
    by (intro sum.mono_neutral_left assms) (simp_all add: iffD2[OF count_eq_zero_iff])
  finally show ?thesis by simp
qed

lemma size_filter_mset_conv:
  "size (filter_mset f A) = sum_mset (image_mset (\<lambda>x. of_bool (f x) :: nat) A)"
  by (induction A, auto)


definition concat_mset :: "('a multiset) multiset \<Rightarrow> 'a multiset"
  where "concat_mset xss = fold_mset (\<lambda>xs ys. xs + ys) {#} xss"

lemma image_concat_mset:
  "image_mset f (concat_mset xss) = concat_mset (image_mset (image_mset f) xss)"
  unfolding concat_mset_def by (induction xss, auto)

lemma size_concat_mset:
  "size (concat_mset xss) = sum_mset (image_mset size xss)"
  unfolding concat_mset_def by (induction xss, auto)

lemma count_concat_mset:
  "count (concat_mset xss) xs = sum_mset (image_mset (\<lambda>x. count x xs) xss)"
  unfolding concat_mset_def by (induction xss, auto)

lemma set_mset_concat_mset:
  "set_mset (concat_mset xss) = \<Union> (set_mset ` (set_mset xss))"
  unfolding concat_mset_def by (induction xss, auto)

lemma measure_pmf_of_multiset:
  assumes "A \<noteq> {#}"
  shows "measure (pmf_of_multiset A) S = real (size (filter_mset (\<lambda>x. x \<in> S) A)) / size A" 
    (is "?L = ?R")
proof -
  have "sum (count A) (S \<inter> set_mset A) = size (filter_mset (\<lambda>x. x \<in> S \<inter> set_mset A) A)"
    by (intro sum_count_2) simp
  also have "... = size (filter_mset (\<lambda>x. x \<in> S) A)"
    by (intro arg_cong[where f="size"] filter_mset_cong) auto
  finally have a: "sum (count A) (S \<inter> set_mset A) = size (filter_mset (\<lambda>x. x \<in> S) A)" 
    by simp

  have "?L = measure (pmf_of_multiset A) (S \<inter> set_mset A)"
    using assms by (intro measure_eq_AE AE_pmfI) auto
  also have "... = sum (pmf (pmf_of_multiset A)) (S \<inter> set_mset A)"
    by (intro measure_measure_pmf_finite) simp
  also have "... = (\<Sum>x \<in> S \<inter> set_mset A. count A x / size A)"
    using assms by (intro sum.cong, auto)
  also have "... = (\<Sum>x \<in> S \<inter> set_mset A. count A x) / size A"
    by (simp add:sum_divide_distrib)
  also have "... = ?R" 
    using a by simp
  finally show ?thesis
    by simp
qed

lemma pmf_of_multiset_image_mset:
  assumes "A \<noteq> {#}"
  shows "pmf_of_multiset (image_mset f A) = map_pmf f (pmf_of_multiset A)"
  using assms by (intro pmf_eqI) (simp add:pmf_map measure_pmf_of_multiset count_mset_exp 
      image_mset_filter_mset_swap[symmetric])

lemma foldl_matrix_mult_expand:
  fixes Ms :: "(('r::{semiring_1,comm_monoid_mult})^'a^'a) list"
  shows "(foldl (\<lambda>x M. M *v x) a Ms) $ k = (\<Sum>x | length x = length Ms+1 \<and> x! length Ms = k. 
  (\<Prod> i< length Ms. (Ms ! i) $ (x ! (i+1)) $ (x ! i)) * a $ (x ! 0))"
proof (induction Ms arbitrary: k rule:rev_induct)
  case Nil
  have "length x = Suc 0 \<Longrightarrow> x = [x!0]" for x :: "'a list"
    by (cases x, auto)
  hence "{x. length x = Suc 0 \<and> x ! 0 = k} = {[k]}" 
    by auto 
  thus ?case by auto
next
  case (snoc M Ms)
  let ?l = "length Ms"

  have 0: "finite {w. length w = Suc (length Ms) \<and> w ! length Ms = i}" for i :: 'a
    using finite_lists_length_eq[where A="UNIV::'a set" and n="?l +1"] by simp

  have "take (?l+1) x @ [x ! (?l+1)] = x" if "length x = ?l+2" for x :: "'a list"
  proof -
    have "take (?l+1) x @ [x ! (?l+1)] = take (Suc (?l+1)) x"
      using that by (intro take_Suc_conv_app_nth[symmetric], simp)
    also have "... = x" 
      using that by simp
    finally show ?thesis by simp
  qed
  hence 1: "bij_betw  (take (?l+1)) {w. length w=?l+2 \<and> w!(?l+1) =k} {w. length w = ?l+1}"
    by (intro bij_betwI[where g="\<lambda>x. x@[k]"]) (auto simp add:nth_append)

  have "foldl (\<lambda>x M. M *v x) a (Ms @ [M]) $ k = (\<Sum>j\<in>UNIV. M$k$j *(foldl (\<lambda>x M. M *v x) a Ms $ j))"
    by (simp add:matrix_vector_mult_def)
  also have "... = 
    (\<Sum>j\<in>UNIV. M$k$j * (\<Sum>w|length w=?l+1\<and>w!?l=j. (\<Prod>i<?l. Ms!i $ w!(i+1) $ w!i) * a $ w!0))"
    unfolding snoc by simp
  also have "... = 
    (\<Sum>j\<in>UNIV. (\<Sum>w|length w=?l+1\<and>w!?l=j. M$k$w!?l * (\<Prod>i<?l. Ms!i $ w!(i+1) $ w!i) * a $ w!0))"
    by (intro sum.cong refl) (simp add: sum_distrib_left algebra_simps)
  also have "... = (\<Sum>w\<in> (\<Union>j \<in> UNIV. {w. length w=?l+1 \<and> w!?l =j}). 
    M$k$w!?l*(\<Prod>i<?l. Ms!i $ w!(i+1) $ w!i) * a $ w!0)"
    using 0 by (subst sum.UNION_disjoint, simp, simp) auto 
  also have "... = (\<Sum>w | length w=?l+1. M$k$(w!?l)*(\<Prod>i<?l. Ms!i $ w!(i+1) $ w!i) * a $ w!0)"
    by (intro sum.cong arg_cong2[where f="(*)"] refl) auto
  also have "... = (\<Sum>w \<in> take (?l+1) ` {w. length w=?l+2 \<and> w!(?l+1) =k}. 
    M$k$w!?l*(\<Prod>i<?l. Ms!i $ w!(i+1) $ w!i) * a $ w!0)"
    using 1 unfolding bij_betw_def by (intro sum.cong refl, auto) 
  also have "... = (\<Sum>w|length w=?l+2\<and>w!(?l+1)=k. M$k$w!?l*(\<Prod>i<?l. Ms!i $ w!(i+1) $ w!i)* a$w!0)"
    using 1 unfolding bij_betw_def by (subst sum.reindex, auto)
  also have "... = (\<Sum>w|length w=?l+2\<and>w!(?l+1)=k. 
    (Ms@[M])!?l$k$w!?l*(\<Prod>i<?l. (Ms@[M])!i $ w!(i+1) $ w!i)* a$w!0)"
    by (intro sum.cong arg_cong2[where f="(*)"] prod.cong refl) (auto simp add:nth_append)
  also have "... = (\<Sum>w|length w=?l+2\<and>w!(?l+1)=k. (\<Prod>i<(?l+1). (Ms@[M])!i $ w!(i+1) $ w!i)* a$w!0)"
    by (intro sum.cong, auto simp add:algebra_simps)
  finally have "foldl (\<lambda>x M. M *v x) a (Ms @ [M]) $ k = 
    (\<Sum> w | length w = ?l+2 \<and> w ! (?l+1) = k. (\<Prod>i<(?l+1). (Ms@[M])!i $ w!(i+1) $ w!i)* a$w!0)"
    by simp
  then show ?case by simp
qed

lemma foldl_matrix_mult_expand_2:
  fixes Ms :: "(real^'a^'a) list"
  shows "(foldl (\<lambda>x M. M *v x) a Ms) \<bullet> 1= (\<Sum>x | length x = length Ms+1. 
          (\<Prod> i< length Ms. (Ms ! i) $ (x ! (i+1)) $ (x ! i)) * a $ (x ! 0))"
  (is "?L = ?R")
proof -
  let ?l = "length Ms"
  have "?L = (\<Sum>j \<in> UNIV. (foldl (\<lambda>x M. M *v x) a Ms) $ j)"
    by (simp add:inner_vec_def)
  also have "... = (\<Sum>j\<in>UNIV. \<Sum>x|length x=?l+1 \<and> x!?l=j.(\<Prod>i<?l. Ms!i $ x!(i+1) $ x!i) * a $ x!0)"
    unfolding foldl_matrix_mult_expand by simp
  also have "... = (\<Sum>x \<in> (\<Union>j\<in> UNIV.{w. length w = length Ms+1 \<and> w ! length Ms = j}).
          (\<Prod> i< length Ms. (Ms ! i) $ (x ! (i+1)) $ (x ! i)) * a $ (x ! 0))"
    using finite_lists_length_eq[where A="UNIV::'a set" and n="?l +1"]
    by (intro sum.UNION_disjoint[symmetric]) auto
  also have "... = ?R"
    by (intro sum.cong, auto)
  finally show ?thesis by simp
qed


record 'a multi_graph =
  vertices :: "'a set"
  edges :: "('a \<times> 'a) multiset"

definition "graph G = 
  (finite (vertices G) \<and> (vertices G) \<noteq> {} \<and> set_mset (edges G) \<subseteq> (vertices G) \<times> (vertices G))"

lemma graphD:
  assumes "graph G"
  shows "finite (vertices G)" "vertices G \<noteq> {}"
  using assms unfolding graph_def by auto

lemma graph_edgeD: 
  assumes "graph G"
  assumes "x \<in># edges G"
  shows "fst x \<in> vertices G" "snd x \<in> vertices G"
  using assms unfolding graph_def by auto

definition "vertices_from G v = {# snd e | e \<in># edges G . fst e = v #}"
definition "vertices_to G v = {# fst e | e \<in># edges G . snd e = v #}"

lemma set_mset_vertices_from:
  assumes "graph G"
  shows "set_mset (vertices_from G x) \<subseteq> vertices G"
  using graph_edgeD[OF assms] unfolding vertices_from_def by auto

definition "in_degree G v = size (vertices_to G v)"
definition "out_degree G v = size (vertices_from G v)"

definition "regular G d = (graph G \<and> d > 0 \<and> (\<forall>v \<in> vertices G. in_degree G v = d \<and> out_degree G v = d))"

lemma regularD: 
  assumes "regular G d"
  shows "graph G" "d > 0"
  using assms unfolding regular_def by auto

definition step_distr :: "'a multi_graph \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow>real)"
  where
    "step_distr G f v = (\<Sum>\<^sub># {# f w / out_degree G w . w \<in># vertices_to G v #})"

definition norm_distr :: "'a multi_graph \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real"
  where "norm_distr G f = sqrt (\<Sum>v \<in> vertices G. (f v)^2)"

definition sum_distr :: "'a multi_graph \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real"
  where "sum_distr G f = (\<Sum>v \<in> vertices G. (f v))"

definition distr_on :: "'a multi_graph \<Rightarrow> ('a \<Rightarrow> real) set"
  where "distr_on G = {f. f ` (UNIV - vertices G) \<subseteq> {0}}"

lemma distr_onD: "f \<in> distr_on G \<Longrightarrow> x \<notin> vertices G \<Longrightarrow> f x = 0"
  unfolding distr_on_def by auto

lemma distr_onI: "(\<And>x. x \<notin> vertices G \<Longrightarrow> f x = 0) \<Longrightarrow> f \<in> distr_on G"
  unfolding distr_on_def by auto

definition spectral_expansion :: "'a multi_graph \<Rightarrow> real \<Rightarrow> bool" where 
  "spectral_expansion G \<alpha> = (\<alpha> \<in> {0..1} \<and> 
  (\<forall>f \<in> distr_on G. sum_distr G f = 0 \<longrightarrow> norm_distr G (step_distr G f) \<le> \<alpha> * norm_distr G f))"


fun walks' :: "'a multi_graph \<Rightarrow> nat \<Rightarrow> ('a list) multiset"
  where 
    "walks' G 0 = image_mset (\<lambda>x. [x]) (mset_set (vertices G))" |
    "walks' G (Suc n) = concat_mset {#{#w @[z].z\<in># vertices_from G (last w)#}. w \<in># walks' G n#}" 

definition "walks G l = (case l of 0 \<Rightarrow> {#[]#} | Suc pl \<Rightarrow> walks' G pl)"

lemma Union_image_mono: "(\<And>x. x \<in> A \<Longrightarrow> f x \<subseteq> g x) \<Longrightarrow> \<Union> (f ` A) \<subseteq> \<Union> (g ` A)"
  by auto

lemma set_walks':
  assumes "graph G"
  shows  "set_mset (walks' G l) \<subseteq> {xs. set xs \<subseteq> vertices G \<and> length xs = (l+1)}"
proof (induction l)
  case 0
  then show ?case using graphD[OF assms(1)] by auto 
next
  case (Suc l)
  have "set_mset (walks' G (Suc l)) =  
    (\<Union>x\<in>set_mset (walks' G l). (\<lambda>z. x @ [z]) ` set_mset (vertices_from G (last x)))"
    by (simp add:set_mset_concat_mset)
  also have "... \<subseteq> (\<Union>x\<in>{xs. set xs \<subseteq> vertices G \<and> length xs = l + 1}. 
    (\<lambda>z. x @ [z]) ` set_mset (vertices_from G (last x)))"
    by (intro Union_mono image_mono Suc)
  also have "... \<subseteq> (\<Union>x\<in>{xs. set xs \<subseteq> vertices G \<and> length xs = l + 1}. (\<lambda>z. x @ [z]) ` vertices G)"
    by (intro Union_image_mono image_mono set_mset_vertices_from[OF assms])
  also have "... \<subseteq> {xs. set xs \<subseteq> vertices G \<and> length xs = (Suc l + 1)}"
    by (intro subsetI) auto
  finally show ?case by simp
qed

lemma set_walks:
  assumes "graph G"
  shows  "set_mset (walks G l) \<subseteq> {xs. set xs \<subseteq> vertices G \<and> length xs = l}"
  unfolding walks_def using set_walks'[OF assms] by (cases l, auto)

lemma set_walks_2:
  assumes "graph G"
  assumes  "xs \<in># walks' G l"
  shows "set xs \<subseteq> vertices G" "xs \<noteq> []"
proof -
  have a:"xs \<in> set_mset (walks' G l)"
    using assms(2) by simp
  thus "set xs \<subseteq> vertices G"
    using set_walks'[OF assms(1)] by auto
  have "length xs \<noteq> 0"
    using set_walks'[OF assms(1)] a by fastforce
  thus "xs \<noteq> []" by simp
qed

lemma set_walks_3:
  assumes "graph G" "xs \<in># walks G l"
  shows  "set xs \<subseteq> vertices G" "length xs = l"
  using set_walks[OF assms(1)]  assms(2) by auto

lemma size_walks':
  assumes "regular G d"
  shows "size (walks' G l) = card (vertices G) * d^l"
proof (induction l)
  case 0
  then show ?case by simp
next
  case (Suc l)

  have a:"out_degree G (last x) = d" if "x \<in># walks' G l" for x
  proof -
    have "graph G" using regularD[OF assms] by simp
    hence "last x \<in> vertices G" 
      using last_in set_walks_2 that by metis
    thus ?thesis
      using assms unfolding regular_def by simp
  qed

  have "size (walks' G (Suc l)) = (\<Sum>x\<in>#walks' G l. out_degree G (last x))"
    by (simp add:size_concat_mset image_mset.compositionality comp_def out_degree_def)
  also have "... = (\<Sum>x\<in>#walks' G l. d)"
    by (intro arg_cong[where f="sum_mset"] image_mset_cong a) simp
  also have "... = size (walks' G l) * d" by simp
  also have "... = card (vertices G) * d^(Suc l)" using Suc by simp
  finally show ?case by simp
qed

lemma size_walks:
  assumes "regular G d"
  shows "size (walks G l) = (if l > 0 then card (vertices G) * d^(l-1) else 1)"
  using size_walks'[OF assms] unfolding walks_def by (cases l, auto)

lemma count_walks':
  assumes "graph G"
  assumes "set xs \<subseteq> vertices G"
  assumes "length xs = l+1"
  shows "count (walks' G l) xs = (\<Prod>i \<in> {..<l}. count (edges G)  (xs ! i, xs ! (i+1)))"
proof -
  have a:"xs \<noteq> []" using assms(3) by auto

  have "count (walks' G (length xs-1)) xs = (\<Prod>i<length xs -1. count (edges G) (xs ! i, xs ! (i + 1)))"
    using a assms(2)
  proof (induction xs rule:rev_nonempty_induct)
    case (single x)
    hence "x \<in> vertices G" by simp
    moreover have "finite (vertices G)" 
      using assms(1) unfolding graph_def by simp
    ultimately have "count {#[x]. x \<in># mset_set (vertices G)#} [x] = 1" 
      by (subst count_image_mset_inj, auto simp add:inj_def) 
    then show ?case by simp 
  next
    case (snoc x xs)
    have set_xs: "set xs \<subseteq> vertices G" using snoc by simp

    define l where "l = length xs - 1" 
    have l_xs: "length xs = l + 1" unfolding l_def using snoc by simp
    have "count (walks' G (length (xs @ [x]) - 1)) (xs @ [x]) =
      (\<Sum>ys\<in>#walks' G l. count {#ys @ [z]. z \<in># vertices_from G (last ys)#} (xs @ [x]))"
      by (simp add:l_xs count_concat_mset image_mset.compositionality comp_def)
    also have "... = 
      (\<Sum>ys\<in>#walks' G l. (if ys = xs then count {#xs @ [z]. z \<in># vertices_from G (last xs)#} (xs @ [x]) else 0))"
      by (intro arg_cong[where f="sum_mset"] image_mset_cong) (auto intro!: count_image_mset_0_triv) 
    also have "... = (\<Sum>ys\<in>#walks' G l.(if ys=xs then count (vertices_from G (last xs)) x else 0))"
      by (subst count_image_mset_inj, auto simp add:inj_def)
    also have "... = count (walks' G l) xs * count (vertices_from G (last xs)) x"
      by (subst sum_mset_delta, simp)
    also have "... = count (walks' G l) xs * count (edges G) (last xs, x)"
      unfolding vertices_from_def count_mset_exp image_mset_filter_mset_swap[symmetric] 
        filter_filter_mset by (simp add:prod_eq_iff)
    also have "... = count (walks' G l) xs * count (edges G) ((xs@[x])!l, (xs@[x])!(l+1))"
      using snoc(1) unfolding l_def nth_append last_conv_nth[OF snoc(1)] by simp 
    also have "... = (\<Prod>i<l+1. count (edges G) ((xs@[x])!i, (xs@[x])!(i+1)))"
      unfolding l_def snoc(2)[OF set_xs] by (simp add:nth_append)
    finally have "count (walks' G (length (xs @ [x]) - 1)) (xs @ [x]) =
       (\<Prod>i<length (xs@[x]) - 1. count (edges G) ((xs@[x])!i, (xs@[x])!(i+1)))"
      unfolding l_def using snoc(1) by simp
    then show ?case by simp 
  qed
  moreover have "l = length xs - 1" using a assms by simp
  ultimately show ?thesis by simp
qed

lemma count_walks:
  assumes "graph G"
  assumes "set xs \<subseteq> vertices G"
  assumes "length xs = l" "l > 0"
  shows "count (walks G l) xs = (\<Prod>i \<in> {..<l-1}. count (edges G)  (xs ! i, xs ! (i+1)))"
  using assms unfolding walks_def by (cases l, auto simp add:count_walks')

locale univ_regular_graph = 
  fixes G :: "('a :: finite) multi_graph" 
  fixes d
  assumes regular: "regular G d"
  assumes vertices_univ: "vertices G = UNIV"
begin

(* The stochastic matrix associated to the graph *)
definition A :: "real^'a^'a" where 
  "A = (\<chi> i j. count (edges G) (j,i)/real d)"

lemma graph: "graph G"
  using regularD[OF regular] by simp

lemma d_gt_0: "d > 0"
  using regularD[OF regular] by simp

lemma markov: "markov A"
proof -
  have "(\<Sum>j\<in>UNIV. count (edges G) (i, j)) = d" for i 
  proof -
    have "(\<Sum>j\<in>UNIV. count (edges G) (i, j)) = sum (count (edges G)) ((\<lambda>x. (i,x)) ` UNIV)"
      by (subst sum.reindex) (auto simp add:inj_on_def comp_def)
    also have "... = size {# e \<in># edges G. e \<in> (\<lambda>x. (i,x)) ` UNIV #}"
      by (subst sum_count_2) auto
    also have "... =  size {# e \<in># edges G. fst e = i #}"
      by (intro arg_cong[where f="size"] filter_mset_cong) auto
    also have "... = out_degree G i"
      unfolding out_degree_def vertices_from_def by simp
    also have "... = d" 
      using regular unfolding regular_def vertices_univ by simp
    finally show ?thesis by simp
  qed
  hence "1 v* A = 1" 
    unfolding A_def vector_matrix_mult_def 
    using d_gt_0 by (vector sum_divide_distrib[symmetric] of_nat_sum[symmetric])

  moreover have "(\<Sum>i\<in>UNIV. count (edges G) (i, j)) = d" for j
  proof -
    have "(\<Sum>i\<in>UNIV. count (edges G) (i, j)) = sum (count (edges G)) ((\<lambda>x. (x,j)) ` UNIV)"
      by (subst sum.reindex) (auto simp add:inj_on_def comp_def)
    also have "... = size {# e \<in># edges G. e \<in> (\<lambda>x. (x,j)) ` UNIV #}"
      by (subst sum_count_2) auto
    also have "... =  size {# e \<in># edges G. snd e = j #}"
      by (intro arg_cong[where f="size"] filter_mset_cong) auto
    also have "... = in_degree G j"
      unfolding in_degree_def vertices_to_def by simp
    also have "... = d" 
      using regular unfolding regular_def vertices_univ by simp
    finally show ?thesis by simp
  qed
  hence "A *v 1 = 1" 
    unfolding A_def matrix_vector_mult_def 
    using d_gt_0 by (vector sum_divide_distrib[symmetric] of_nat_sum[symmetric])

  moreover have "nonneg_mat A" 
    unfolding nonneg_mat_def A_def by simp

  ultimately show ?thesis
    unfolding markov_def by simp
qed

definition distr_vec :: "('a \<Rightarrow> real) \<Rightarrow> (real^'a)"
  where "distr_vec f = (\<chi> i. f i)"

lemma step_distr: 
  "A *v (distr_vec f) = distr_vec (step_distr G f)"
proof -
  have "(\<Sum>j\<in>UNIV. real (count (edges G) (j, i)) * f j / real d) = 
        (\<Sum>j\<in>#vertices_to G i. f j / real (out_degree G j))" (is "?L = ?R") for i
  proof -
    have "?L =  (\<Sum>j\<in>UNIV. f j * size {#e \<in># edges G. snd e = i \<and> fst e = j#} / d)"
      unfolding count_mset_exp prod_eq_iff by (simp add:conj_commute algebra_simps)
    also have "... = (\<Sum>j\<in>UNIV. f j * (count (image_mset fst {#e \<in># edges G. snd e = i#}) j) / d)"
      by (simp add: count_mset_exp image_mset_filter_mset_swap[symmetric] filter_filter_mset)
    also have "... = (\<Sum>j\<in>#vertices_to G i. f j / real d)"
      unfolding vertices_to_def by (simp add: sum_mset_conv_2[where B="UNIV"] algebra_simps)
    also have "... = ?R" 
      using regular unfolding regular_def vertices_univ by simp
    finally show ?thesis by simp
  qed
  thus ?thesis
    unfolding matrix_vector_mult_def distr_vec_def step_distr_def A_def by vector
qed

lemma norm_distr:
  "norm_distr G f = norm (distr_vec f)"
  unfolding norm_distr_def distr_vec_def vertices_univ norm_vec_def L2_set_def by simp

lemma sum_distr:
  "sum_distr G f = inner (distr_vec f) 1"
  unfolding sum_distr_def distr_vec_def vertices_univ inner_vec_def by simp

lemma spec_bound:
  assumes "spectral_expansion G \<alpha>"
  shows "spec_bound A \<alpha>"
proof -
  have "norm (A *v v) \<le> \<alpha> * norm v" if "v \<bullet> 1 = 0" for v
  proof -
    define w where "w = (\<lambda>i. v $ i)"
    have v_def: "v = distr_vec w" unfolding distr_vec_def w_def by simp
    have "sum_distr G w = 0"
      unfolding sum_distr v_def[symmetric] using that by simp
    moreover have "w \<in> distr_on G"
      unfolding distr_on_def vertices_univ by simp
    ultimately have "norm_distr G (step_distr G w) \<le> \<alpha> * norm_distr G w"
      using assms unfolding spectral_expansion_def by simp
    thus ?thesis
      unfolding norm_distr step_distr[symmetric] v_def by simp
  qed
  moreover have "\<alpha> \<ge> 0"
    using assms unfolding spectral_expansion_def by simp
  ultimately show ?thesis 
    unfolding spec_bound_def by auto
qed

lemma walks_nonempty: "walks G l \<noteq> {#}"
proof -
  have "size (walks G l) > 0"
    using graphD[OF graph] d_gt_0
    unfolding size_walks[OF regular] by auto 
  thus "walks G l \<noteq> {#}"
    by auto
qed

lemma walk_distr:
  "measure (pmf_of_multiset (walks G l)) {\<omega>. (\<forall>i<l. \<omega> ! i \<in> S i)} =
  foldl (\<lambda>x M. M *v x) stat (intersperse A (map (\<lambda>i. diag (ind_vec (S i))) [0..<l])) \<bullet> 1" 
  (is "?L = ?R")
proof (cases "l > 0")
  case True
  let ?n = "real (card (vertices G))"
  let ?d = "real d"
  let ?W = "{(w::'a list). length w = l}"

  have a: "set_mset (walks G l) \<subseteq> ?W"
    using set_walks[OF graph] by auto
  have b: "finite ?W"
    by (intro finite_subset[OF _ finite_lists_length_eq[where A="UNIV" and n="l"]])
     auto

  define lp where "lp = l - 1"

  define xs where "xs = map (\<lambda>i. diag (ind_vec (S i))) [0..<l]"
  have "xs \<noteq> []" unfolding xs_def using True by simp
  then obtain xh xt where xh_xt: "xh#xt=xs" by (cases xs, auto)

  have "length xs = l"
    unfolding xs_def by simp
  hence len_xt: "length xt = lp" 
    using True unfolding xh_xt[symmetric] lp_def by simp

  have "xh = xs ! 0" 
    unfolding xh_xt[symmetric] by simp
  also have "... = diag (ind_vec (S 0))"
    using True unfolding xs_def by simp
  finally have xh_eq: "xh = diag (ind_vec (S 0))" 
    by simp

  have "?L = size {# w \<in># walks G l. \<forall>i<l. w ! i \<in> S i #} / (?n * ?d^(l-1))"
    using True unfolding size_walks[OF regular] measure_pmf_of_multiset[OF walks_nonempty] by simp
  also have "... = (\<Sum>w\<in>?W. real (count (walks G l) w) * of_bool (\<forall>i<l. w!i \<in> S i))/(?n*?d^(l-1))"
    unfolding size_filter_mset_conv sum_mset_conv_2[OF a b] by simp
  also have "... = (\<Sum>w\<in>?W. (\<Prod>i<l-1. real (count (edges G) (w!i,w!(i+1)))) * 
                            (\<Prod>i<l. of_bool(w!i \<in> S i)))/(?n*?d^(l-1))"
    using True vertices_univ by (intro sum.cong arg_cong2[where f="(/)"]) 
      (auto simp add: count_walks[OF graph])
  also have "... = (\<Sum>w\<in>?W. (\<Prod>i<l-1. real (count (edges G) (w!i,w!(i+1))) / ?d) * 
                            (\<Prod>i<l. of_bool(w!i \<in> S i)))/?n"
    using True unfolding prod_dividef by (simp add:sum_divide_distrib algebra_simps)
  also have "... = (\<Sum>w\<in>?W. (\<Prod>i<lp. A $ w!(i+1) $ w!i) * (\<Prod>i<Suc lp. of_bool(w!i \<in> S i)))/?n"
    unfolding A_def lp_def using True by simp
  also have "... = (\<Sum>w\<in>?W. (\<Prod>i<lp. A $ w!(i+1) $ w!i) * 
    (\<Prod>i\<in>insert 0 (Suc ` {..<lp}). of_bool(w!i \<in> S i)))/?n"
    using lessThan_Suc_eq_insert_0
    by (intro sum.cong arg_cong2[where f="(/)"] arg_cong2[where f="(*)"] prod.cong) auto
  also have "... = 
    (\<Sum>w\<in>?W. (\<Prod>i<lp. of_bool(w!(i+1)\<in>S(i+1))* A $ w!(i+1) $ w!i) * of_bool(w!0\<in>S 0))/?n"
    by (simp add:prod.reindex algebra_simps prod.distrib)
  also have "... = 
    (\<Sum>w\<in>?W. (\<Prod>i<lp. (diag (ind_vec (S (i+1)))**A) $ w!(i+1) $ w!i) * of_bool(w!0\<in>S 0))/?n"
    unfolding diag_def ind_vec_def matrix_matrix_mult_def
    by (intro sum.cong arg_cong2[where f="(/)"] arg_cong2[where f="(*)"] prod.cong refl) 
      (simp add:if_distrib if_distribR sum.If_cases)
  also have "... = (\<Sum>w\<in>?W. (\<Prod>i<lp. (xs ! (i+1) **A) $ w!(i+1) $ w!i) * of_bool(w!0\<in>S 0))/?n"
    unfolding xs_def lp_def True
    by (intro sum.cong arg_cong2[where f="(/)"] arg_cong2[where f="(*)"] prod.cong refl) auto 
  also have "... = (\<Sum>w\<in>?W. (\<Prod>i<lp. (xt ! i ** A) $ w!(i+1) $ w!i) * of_bool(w!0\<in>S 0))/?n"
    unfolding xh_xt[symmetric] by auto
  also have "... = (\<Sum>w\<in>?W. (\<Prod>i<lp. (xt!i**A)$ w!(i+1) $ w!i)*(diag (ind_vec (S 0))*v stat) $w!0)"
    unfolding matrix_vector_mult_def diag_def stat_def vertices_univ ind_vec_def 
    by (simp add:sum.If_cases if_distrib if_distribR sum_divide_distrib)
  also have "... = (\<Sum>w\<in>?W. (\<Prod>i<lp. (xt ! i ** A) $ w!(i+1) $ w!i) * (xh *v stat) $ w ! 0)"
    unfolding xh_eq by simp
  also have "... = foldl (\<lambda>x M. M *v x) (xh *v stat) (map (\<lambda>x. x ** A) xt) \<bullet> 1" 
    using True unfolding foldl_matrix_mult_expand_2 by (simp add:len_xt lp_def)
  also have "... = foldl (\<lambda>x M. M *v (A *v x)) (xh *v stat) xt \<bullet> 1" 
    by (simp add: matrix_vector_mul_assoc foldl_map)
  also have "... = foldl (\<lambda>x M. M *v x) stat (intersperse A (xh#xt)) \<bullet> 1" 
    by (subst foldl_intersperse_2, simp)
  also have "... = ?R"  unfolding xh_xt xs_def by simp
  finally show ?thesis by simp
next
  case False
  hence "l = 0" by simp
  thus ?thesis unfolding stat_def by (simp add: inner_1_1)
qed

end

definition map_graph :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a multi_graph \<Rightarrow> 'b multi_graph"
  where "map_graph f G = \<lparr> vertices = f ` vertices G, edges = image_mset (map_prod f f) (edges G) \<rparr>"

locale graph_iso =
  fixes G :: "'a multi_graph"
  fixes f :: "'a \<Rightarrow> 'b"
  assumes graph: "graph G"
  assumes inj_f: "inj_on f (vertices G)"
begin

context 
  includes lifting_syntax
begin

abbreviation H where "H \<equiv> map_graph f G"

lemma graph_H: "graph H"
  using graph unfolding graph_def map_graph_def map_prod_def by auto

lemma vertices_H: "f ` vertices G = vertices H"
  unfolding map_graph_def by simp

lemma vert_transfer: "S \<subseteq> vertices G \<Longrightarrow> f ` S \<subseteq> vertices H"
  using image_mono unfolding vertices_H[symmetric] by auto

abbreviation rel_vertex where "rel_vertex x y \<equiv> (x \<in> vertices G \<and> f x = y)"

abbreviation rel_mset where "rel_mset x y \<equiv> (set_mset x \<subseteq> vertices G \<and> image_mset f x = y)"

lemma vertices_from_rel[transfer_rule]: "(rel_vertex ===> rel_mset) (vertices_from G) (vertices_from H)"
proof -
  have a:"{#e \<in># edges G. f (fst e) = f x#} = {#e \<in># edges G. fst e = x#}" 
    if "x \<in> vertices G" for x
    by (intro filter_mset_cong inj_on_eq_iff[OF inj_f] that graph_edgeD[OF graph]) auto

  moreover have "snd ` {a. a \<in># edges G \<and> fst a = x} \<subseteq> vertices G" if "x \<in> vertices G" for x
    by (intro image_subsetI graph_edgeD[OF graph]) auto

  ultimately show ?thesis
    unfolding vertices_from_def map_graph_def rel_fun_def rel_mset_def
    by (simp add:image_mset_filter_mset_swap[symmetric] image_mset.compositionality)
qed

lemma vertices_from_comm: 
  assumes "x \<in> vertices G"
  shows "image_mset f (vertices_from G x) = vertices_from H (f x)"
  using vertices_from_rel assms unfolding rel_fun_def by simp

lemma [transfer_rule]: "(rel_vertex ===> rel_mset) (vertices_to G) (vertices_to H)"
proof -
  have a:"{#e \<in># edges G. f (snd e) = f x#} = {#e \<in># edges G. snd e = x#}" 
    if "x \<in> vertices G" for x
    by (intro filter_mset_cong inj_on_eq_iff[OF inj_f] that graph_edgeD[OF graph]) auto

  moreover have "fst ` {a. a \<in># edges G \<and> snd a = x} \<subseteq> vertices G" if "x \<in> vertices G" for x
    by (intro image_subsetI graph_edgeD[OF graph]) auto

  ultimately show ?thesis
    unfolding vertices_to_def map_graph_def rel_fun_def rel_mset_def
    by (simp add:image_mset_filter_mset_swap[symmetric] image_mset.compositionality)
qed

lemma [transfer_rule]: "(rel_mset ===> ((=))) size size"
  unfolding rel_mset_def rel_fun_def by simp

lemma [transfer_rule]: "(rel_vertex ===> ((=))) (out_degree G) (out_degree H)"
  unfolding out_degree_def by (transfer_prover)

lemma [transfer_rule]: "(rel_vertex ===> ((=))) (in_degree G) (in_degree H)"
  unfolding in_degree_def by (transfer_prover)

lemma [transfer_rule]: "((rel_vertex ===> ((=))) ===> ((=))) (Ball (vertices G)) (Ball (vertices H))"
  unfolding rel_fun_def using vertices_H by force 

lemma [transfer_rule]: "(((=)) ===> ((=))) (regular G) (regular H)"
  unfolding regular_def by (simp add:graph graph_H) transfer_prover

lemma [transfer_rule]: "((rel_vertex ===> ((=))) ===> rel_mset ===> ((=))) 
  (\<lambda>f A. image_mset f A)  (\<lambda>f A. image_mset f A)"
  unfolding rel_fun_def
  by (auto intro!: image_mset_cong simp add:image_mset.compositionality)

lemma [transfer_rule]: "((rel_vertex ===> ((=))) ===> rel_vertex ===> ((=))) (step_distr G) (step_distr H)"
  unfolding step_distr_def 
  by transfer_prover

lemma [transfer_rule]: "((rel_vertex ===> ((=))) ===> ((=))) (norm_distr G) (norm_distr H)"
  unfolding norm_distr_def rel_fun_def vertices_H[symmetric]
  by (subst sum.reindex[OF inj_f]) auto

lemma [transfer_rule]: "((rel_vertex ===> ((=))) ===> ((=))) (sum_distr G) (sum_distr H)"
  unfolding sum_distr_def rel_fun_def vertices_H[symmetric]
  by (subst sum.reindex[OF inj_f]) auto

lemma distr_bij: "bij_betw (\<lambda>g x. (if x\<in> vertices G then (g (f x)) else 0)) (distr_on H) (distr_on G)"
proof -
  let ?inv = "\<lambda>h x. (if x \<in> vertices H then h (the_inv_into (vertices G) f x) else 0)"

  have "x \<in> vertices G \<Longrightarrow> f x \<in> vertices H" for x 
    using vertices_H by auto
  thus ?thesis
    using the_inv_into_f_f[OF inj_f]  f_the_inv_into_f[OF inj_f] 
      the_inv_into_into[OF inj_f _ order.refl] vertices_H
    by (intro bij_betwI[where g="?inv"]) (auto intro!:ext distr_onI simp add:distr_onD cong:if_cong)
qed

lemma distr_G_eq: 
  "distr_on G = (\<lambda>g x. (if x \<in> vertices G then (g (f x)) else 0)) ` distr_on H"
  using distr_bij unfolding bij_betw_def by simp

lemma [transfer_rule]: 
  "(((rel_vertex ===> ((=))) ===> ((=))) ===> ((=))) (Ball (distr_on G)) (Ball (distr_on H))"
  unfolding  rel_fun_def distr_G_eq Ball_image_comp 
  by (intro impI allI ball_cong) (simp_all add:comp_def distr_on_def)

lemma [transfer_rule]: "(((=)) ===> ((=))) (spectral_expansion G) (spectral_expansion H)"
  unfolding spectral_expansion_def
  by transfer_prover

lemma walks'_map: "image_mset (map f) (walks' G l) = walks' H l"
proof (induction l)
  case 0
  have "walks' H 0 = {#[x]. x \<in># mset_set (f ` vertices G)#}"
    by (simp add:vertices_H)
  also have "... = {#[x]. x \<in># image_mset f (mset_set (vertices G))#}"
    by (subst image_mset_mset_set[OF inj_f], simp)
  also have "... = image_mset (map f) (walks' G 0)"
    by (simp add:image_mset.compositionality comp_def)
  finally show ?case by simp
next
  case (Suc l)
  have comm_ver: "image_mset f (vertices_from G (last x)) = vertices_from H (last (map f x))"
    if "x \<in># walks' G l" for x 
    using last_map vertices_from_comm last_in set_walks_2[OF graph] that by metis

  have "image_mset (map f) (walks' G (Suc l)) = 
    concat_mset {#{#map f x @ [f y]. y \<in># vertices_from G (last x)#}. x \<in># walks' G l#}"
    by (simp add:image_concat_mset image_mset.compositionality comp_def)
  also have "... = 
    concat_mset {#{#map f x@[y]. y \<in># image_mset f (vertices_from G (last x))#}. x \<in># walks' G l#}"
    by (simp add:image_mset.compositionality comp_def)
  also have "... = 
    concat_mset {#{#map f x@[y]. y \<in># vertices_from H (last (map f x))#}. x \<in># walks' G l#}"
    by (intro arg_cong[where f="concat_mset"] image_mset_cong) (simp add:comm_ver)
  also have "... = concat_mset {#{#x@[y]. y \<in># vertices_from H (last x)#}. x \<in># (walks' H l)#}"
    unfolding Suc[symmetric] by (simp add:image_mset.compositionality comp_def)
  also have "... = walks' H (Suc l)"
    by simp
  finally show ?case by simp 
qed

lemma walks_map: "walks H l = image_mset (map f) (walks G l)"
  unfolding walks_def using walks'_map by (cases l, auto)

end
end



lemma hitting_property_gen_aux:
  fixes S :: "('a :: finite) set"
  assumes "vertices G = UNIV"
  assumes "regular G d" "spectral_expansion G \<alpha>"
  assumes "S \<subseteq> vertices G" "I \<subseteq> {..<l}"
  defines "\<mu> \<equiv> real (card S) / card (vertices G)"
  shows "measure (pmf_of_multiset (walks G l)) {w. set (nths w I) \<subseteq> S} \<le> (\<mu>+\<alpha>*(1-\<mu>))^card I"
    (is "?L \<le> ?R")
proof -
  interpret univ_regular_graph G d
    using assms(1,2) by unfold_locales auto

  define T where "T = (\<lambda>i. if i \<in> I then S else UNIV)" 

  have 0: "diag (ind_vec (UNIV::'a set)) = mat 1"
    unfolding diag_def ind_vec_def mat_def by vector

  have spec: "spec_bound A \<alpha>" using spec_bound[OF assms(3)] by simp
  note x = hitting_property_alg_2[OF _ _ spec markov]
  have \<alpha>_range: "\<alpha> \<in> {0..1}" 
    using assms(3) unfolding spectral_expansion_def by simp

  have "?L = measure (pmf_of_multiset (walks G l)) {w. \<forall>i<l. w ! i \<in> T i}"
    using walks_nonempty set_walks_3[OF graph] unfolding T_def set_nths
    by (intro measure_eq_AE AE_pmfI) auto
  also have "... = foldl (\<lambda>x M. M *v x) stat 
    (intersperse A (map (\<lambda>i. (if i \<in> I then diag (ind_vec S) else mat 1)) [0..<l])) \<bullet> 1"
    unfolding walk_distr T_def by (simp add:if_distrib if_distribR 0 cong:if_cong)
  also have "... \<le> ?R"
    unfolding \<mu>_def vertices_univ
    by (intro hitting_property_alg_2[OF \<alpha>_range assms(5) spec markov])
  finally show ?thesis by simp
qed

lemmas hitting_property_gen_aux_internalized = 
  hitting_property_gen_aux[internalize_sort "'a :: finite"]

lemma hitting_property_gen:
  fixes S :: "'a set"
  assumes "regular G d" "spectral_expansion G \<alpha>"
  assumes "S \<subseteq> vertices G" "I \<subseteq> {..<l}"
  defines "\<mu> \<equiv> real (card S) / card (vertices G)"
  shows "measure (pmf_of_multiset (walks G l)) {w. set (nths w I) \<subseteq> S} \<le> (\<mu>+\<alpha>*(1-\<mu>))^card I" 
    (is "?L \<le> ?R")
proof -
  have graph_G: "graph G" 
    using assms(1) unfolding regular_def by auto

  have "size (walks G l) > 0"
    using assms(1) graphD[OF graph_G]
    unfolding size_walks[OF assms(1)] regular_def by auto 
  hence walks_ne: "walks G l \<noteq> {#}"
    by auto

  have t:?thesis if a:"\<exists>Rep Abs. type_definition Rep Abs (vertices G)"
  proof -
    obtain Rep :: "'b \<Rightarrow> 'a" and Abs where d:"type_definition Rep Abs (vertices G)"
      using a by auto
    interpret type_definition Rep Abs "vertices G"
      using d by simp
                                
    have "finite (vertices G)" using assms(1) regular_def graph_def by metis
    hence cf: "class.finite TYPE('b)"
      using d by (simp add:class.finite_def univ)

    have inj_on_Abs: "inj_on Abs (vertices G)" 
      using Abs_inject unfolding inj_on_def by auto

    interpret graph_iso G Abs
      using graph_G inj_on_Abs by unfold_locales auto

    have " real (card (Abs ` S)) = real (card S)" 
      using inj_on_subset[OF inj_on_Abs assms(3)] by (simp add: card_image)
    moreover have "real (card (vertices H)) = real (card (vertices G))"
      unfolding vertices_H[symmetric] using inj_on_Abs by (simp add:card_image)
    ultimately have \<mu>_def': "\<mu> = real (card (Abs ` S)) / real (card (vertices H))"
      unfolding \<mu>_def by simp

    have hp_0: "vertices H = UNIV"
      unfolding vertices_H[symmetric] Abs_image by simp
    have hp_1: "regular H d" "spectral_expansion H \<alpha>" "Abs ` S \<subseteq> vertices H"
      using assms(1,2)[transferred] vert_transfer[OF assms(3)] by auto

    have "set (nths y I) \<subseteq> S \<longleftrightarrow> Abs ` set (nths y I) \<subseteq> Abs ` S"
      if "y \<in> set_pmf (pmf_of_multiset (walks G l))" for y
    proof -
      have "set (nths y I) \<subseteq> set y" 
        by (intro set_nths_subset)
      also have "... \<subseteq> vertices G" 
        using that walks_ne set_walks[OF graph_G] by auto
      finally have "set (nths y I) \<subseteq> vertices G" by simp  
      thus ?thesis
        by (intro inj_on_image_subset_iff[OF inj_on_Abs, symmetric] assms(3)) simp
    qed

    hence "?L = measure (pmf_of_multiset (walks G l)) {w. Abs ` set (nths w I) \<subseteq> Abs ` S}" 
      by (intro measure_eq_AE AE_pmfI, simp_all)
    also have "... = measure (pmf_of_multiset (walks H l)) {w. set (nths w I) \<subseteq> Abs ` S}" 
      unfolding walks_map by (subst pmf_of_multiset_image_mset[OF walks_ne]) (simp add:nths_map)
    also have "... \<le> (\<mu>+\<alpha>*(1-\<mu>))^card I"
      unfolding \<mu>_def' using assms(4) 
        hitting_property_gen_aux_internalized[OF cf hp_0] hp_1 by simp
    finally show ?thesis by simp
  qed

  show ?thesis 
    using t[cancel_type_definition] graphD[OF graph_G] by simp
qed

lemma hitting_property:
  assumes "regular G d" "spectral_expansion G \<alpha>"
  assumes "S \<subseteq> vertices G"  "d > 0"
  defines "\<mu> \<equiv> real (card S) / card (vertices G)"
  shows "measure (pmf_of_multiset (walks G l)) {w. set w \<subseteq> S} \<le> (\<mu>+\<alpha>*(1-\<mu>))^l" (is "?L \<le> ?R")
proof -
  have graph_G: "graph G" 
    using assms(1) unfolding regular_def by auto

  have "size (walks G l) > 0"
    unfolding size_walks[OF assms(1)] using assms(4,5) graphD[OF graph_G] by auto 
  hence walks_ne: "walks G l \<noteq> {#}"
    by auto

  have a: "y \<in># walks G l \<Longrightarrow> take l y = y" for y
    using set_walks_3[OF graph_G] by auto

  have "?L = measure (pmf_of_multiset (walks G l)) {w. set (nths w {..<l}) \<subseteq> S}"
    using walks_ne a by (intro measure_eq_AE AE_pmfI, auto)
  also have "... \<le>  (\<mu>+\<alpha>*(1-\<mu>))^(card {..<l})"
    unfolding \<mu>_def by (intro hitting_property_gen[OF assms(1)] assms) simp
  also have "... = ?R" by simp
  finally show ?thesis by simp
qed

lemma uniform_property_gen:
  fixes S :: "'a set"
  assumes "regular G d"
  assumes "S \<subseteq> vertices G" "i < l"
  defines "\<mu> \<equiv> real (card S) / card (vertices G)"
  shows "measure (pmf_of_multiset (walks G l)) {w. w ! i \<in> S} = \<mu>" (is "?L = ?R")
proof -

  show ?thesis sorry
qed

lemma uniform_property_gen_2:
  fixes S :: "'a set"
  assumes "regular G d"  "i < l"
  shows "map_pmf (\<lambda>w. w ! i) (pmf_of_multiset (walks G l)) = pmf_of_set (vertices G)" (is "?L = ?R")
proof -
  show ?thesis 
    apply (intro pmf_eqI)
    apply (simp add:pmf_map) sorry

qed


lemma kl_chernoff_property:
  assumes "regular G d" "spectral_expansion G \<alpha>"
  assumes "S \<subseteq> vertices G"
  defines "\<mu> \<equiv> real (card S) / card (vertices G)"
  shows "measure (pmf_of_multiset (walks G l)) {w. set w \<subseteq> S} \<le> (\<mu>+\<alpha>*(1-\<mu>))^(l+1)"
  sorry




end