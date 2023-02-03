theory Expander_Walks
  imports 
    Expander_Graphs 
    Expander_Graphs_3
    "HOL-Types_To_Sets.Types_To_Sets"
    Constructive_Chernoff_Bound
begin

hide_const Matrix_Legacy.transpose
no_notation Matrix.vec_index (infixl "$" 100)
hide_const Matrix.vec_index
hide_fact Matrix.vec_eq_iff
hide_const Matrix.vec
hide_const Matrix.mat
no_notation Matrix.scalar_prod  (infix "\<bullet>" 70)

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

lemma size_filter_mset_conv:
  "size (filter_mset f A) = sum_mset (image_mset (\<lambda>x. of_bool (f x) :: nat) A)"
  by (induction A, auto)

definition "vertices_from G v = {# snd e | e \<in># edges G. fst e = v #}"
definition "vertices_to G v = {# fst e | e \<in># edges G. snd e = v #}"

fun walks' :: "('a,'b) pre_digraph \<Rightarrow> nat \<Rightarrow> ('a list) multiset"
  where 
    "walks' G 0 = image_mset (\<lambda>x. [x]) (mset_set (verts G))" |
    "walks' G (Suc n) = concat_mset {#{#w @[z].z\<in># vertices_from G (last w)#}. w \<in># walks' G n#}" 

definition "walks G l = (case l of 0 \<Rightarrow> {#[]#} | Suc pl \<Rightarrow> walks' G pl)"

lemma Union_image_mono: "(\<And>x. x \<in> A \<Longrightarrow> f x \<subseteq> g x) \<Longrightarrow> \<Union> (f ` A) \<subseteq> \<Union> (g ` A)"
  by auto

context fin_digraph
begin

lemma verts_from_alt:
  "vertices_from G v = image_mset (head G) (mset_set (out_arcs G v))"
proof -
  have "{#x \<in># mset_set (arcs G). tail G x = v#} = mset_set {a \<in> arcs G. tail G a = v}"
    by (intro filter_mset_mset_set) simp
  thus ?thesis
    unfolding vertices_from_def out_arcs_def edges_def arc_to_ends_def
    by (simp add:image_mset.compositionality image_mset_filter_mset_swap[symmetric] comp_def)
qed

lemma verts_to_alt:
  "vertices_to G v = image_mset (tail G) (mset_set (in_arcs G v))"
proof -
  have "{#x \<in># mset_set (arcs G). head G x = v#} = mset_set {a \<in> arcs G. head G a = v}"
    by (intro filter_mset_mset_set) simp
  thus ?thesis
    unfolding vertices_to_def in_arcs_def edges_def arc_to_ends_def
    by (simp add:image_mset.compositionality image_mset_filter_mset_swap[symmetric] comp_def)
qed


lemma count_walks':
  assumes "set xs \<subseteq> verts G"
  assumes "length xs = l+1"
  shows "count (walks' G l) xs = (\<Prod>i \<in> {..<l}. count (edges G) (xs ! i, xs ! (i+1)))"
proof -
  have a:"xs \<noteq> []" using assms(2) by auto

  have "count (walks' G (length xs-1)) xs = (\<Prod>i<length xs -1. count (edges G) (xs ! i, xs ! (i + 1)))"
    using a assms(1)
  proof (induction xs rule:rev_nonempty_induct)
    case (single x)
    hence "x \<in> verts G" by simp
    hence "count {#[x]. x \<in># mset_set (verts G)#} [x] = 1" 
      by (subst count_image_mset_inj, auto simp add:inj_def) 
    then show ?case by simp 
  next
    case (snoc x xs)
    have set_xs: "set xs \<subseteq> verts G" using snoc by simp

    define l where "l = length xs - 1" 
    have l_xs: "length xs = l + 1" unfolding l_def using snoc by simp
    have "count (walks' G (length (xs @ [x]) - 1)) (xs @ [x]) =
      (\<Sum>ys\<in>#walks' G l. count {#ys @ [z]. z \<in># vertices_from G (last ys)#} (xs @ [x]))"
      by (simp add:l_xs count_concat_mset image_mset.compositionality comp_def)
    also have "... = (\<Sum>ys\<in>#walks' G l. 
      (if ys = xs then count {#xs @ [z]. z \<in># vertices_from G (last xs)#} (xs @ [x]) else 0))"
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
  assumes "set xs \<subseteq> verts G"
  assumes "length xs = l" "l > 0"
  shows "count (walks G l) xs = (\<Prod>i \<in> {..<l-1}. count (edges G)  (xs ! i, xs ! (i+1)))"
  using assms unfolding walks_def by (cases l, auto simp add:count_walks')

lemma edge_set: 
  assumes "x \<in># edges G"
  shows "fst x \<in> verts G" "snd x \<in> verts G"
  using assms unfolding edges_def arc_to_ends_def by auto

lemma set_mset_vertices_from:
  "set_mset (vertices_from G x) \<subseteq> verts G"
  unfolding vertices_from_def using edge_set by auto

lemma set_mset_vertices_to:
  "set_mset (vertices_to G x) \<subseteq> verts G"
  unfolding vertices_to_def using edge_set by auto

lemma set_walks':
  "set_mset (walks' G l) \<subseteq> {xs. set xs \<subseteq> verts G \<and> length xs = (l+1)}"
proof (induction l)
  case 0
  then show ?case by auto 
next
  case (Suc l)

  have "set_mset (walks' G (Suc l)) =
    (\<Union>x\<in>set_mset (walks' G l). (\<lambda>z. x @ [z]) ` set_mset (vertices_from G (last x)))"
    by (simp add:set_mset_concat_mset)
  also have "... \<subseteq> (\<Union>x\<in>{xs. set xs \<subseteq> verts G \<and> length xs = l + 1}. 
    (\<lambda>z. x @ [z]) ` set_mset (vertices_from G (last x)))"
    by (intro Union_mono image_mono Suc)
  also have "... \<subseteq> (\<Union>x\<in>{xs. set xs \<subseteq> verts G \<and> length xs = l + 1}. (\<lambda>z. x @ [z]) ` verts G)"
    by (intro Union_image_mono image_mono set_mset_vertices_from)
  also have "... \<subseteq> {xs. set xs \<subseteq> verts G \<and> length xs = (Suc l + 1)}"
    by (intro subsetI) auto
  finally show ?case by simp
qed

lemma set_walks:
  "set_mset (walks G l) \<subseteq> {xs. set xs \<subseteq> verts G \<and> length xs = l}"
  unfolding walks_def using set_walks' by (cases l, auto)

lemma set_walks_2:
  assumes  "xs \<in># walks' G l"
  shows "set xs \<subseteq> verts G" "xs \<noteq> []"
proof -
  have a:"xs \<in> set_mset (walks' G l)"
    using assms by simp
  thus "set xs \<subseteq> verts G"
    using set_walks' by auto
  have "length xs \<noteq> 0"
    using set_walks' a by fastforce
  thus "xs \<noteq> []" by simp
qed

lemma set_walks_3:
  assumes "xs \<in># walks G l"
  shows  "set xs \<subseteq> verts G" "length xs = l"
  using set_walks assms by auto
end

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


context pre_expander_graph 
begin

lemma size_walks':
  "size (walks' G l) = card (verts G) * d^l"
proof (induction l)
  case 0
  then show ?case by simp
next
  case (Suc l)
  have a:"out_degree G (last x) = d" if "x \<in># walks' G l" for x
  proof -
    have "last x \<in> verts G" 
      using set_walks_2 that by fastforce
    thus ?thesis
      using reg by simp
  qed

  have "size (walks' G (Suc l)) = (\<Sum>x\<in>#walks' G l. out_degree G (last x))"
    by (simp add:size_concat_mset image_mset.compositionality comp_def verts_from_alt out_degree_def)
  also have "... = (\<Sum>x\<in>#walks' G l. d)"
    by (intro arg_cong[where f="sum_mset"] image_mset_cong a) simp
  also have "... = size (walks' G l) * d" by simp
  also have "... = card (verts G) * d^(Suc l)" using Suc by simp
  finally show ?case by simp
qed

lemma size_walks:
  "size (walks G l) = (if l > 0 then card (verts G) * d^(l-1) else 1)" (* TODO Use n = card (verts G) *)
  using size_walks' unfolding walks_def by (cases l, auto)

lemma walks_nonempty: 
  "walks G l \<noteq> {#}"
proof -
  have "size (walks G l) > 0"
    unfolding size_walks using d_gt_0 verts_non_empty by auto 
  thus "walks G l \<noteq> {#}"
    by auto
qed

context 
  assumes td: "\<exists>(Rep :: ('n :: finite)  \<Rightarrow> 'a) Abs. type_definition Rep Abs (verts G)"
begin

definition td_components :: "('n \<Rightarrow> 'a) \<times> ('a \<Rightarrow> 'n)" 
  where "td_components = (SOME q. type_definition (fst q) (snd q) (verts G))"

interpretation type_definition "(fst td_components)" "(snd td_components)" "verts G"
proof -
  have 0:"\<exists>q'. type_definition ((fst q')::(('n :: finite) \<Rightarrow> 'a)) (snd q') (verts G)"
    using td by simp
  show "type_definition (fst td_components) (snd td_components) (verts G)"
    unfolding td_components_def using someI_ex[OF 0] by simp
qed

definition enum_verts where "enum_verts = fst td_components"

lemma enum_verts: "bij_betw enum_verts UNIV (verts G)"
  unfolding bij_betw_def  by (simp add: Rep_inject Rep_range enum_verts_def inj_on_def)

(* The stochastic matrix associated to the graph *)
definition A :: "real^'n^'n" where 
  "A = (\<chi> i j. count (edges G) (enum_verts j,enum_verts i)/real d)"

lemma nonneg_A: "nonneg_mat A"
  unfolding nonneg_mat_def A_def by auto

lemma symmetric_A: "transpose A = A"
proof -
  have "A $ i $ j = A $ j $ i" for i j
    unfolding A_def count_edges arcs_betw_def using symmetric_multi_graphD[OF sym]
    by auto
  thus ?thesis
    unfolding transpose_def
    by (intro iffD2[OF vec_eq_iff] allI) auto
qed

lemma g_step_1:
  assumes "v \<in> verts G"
  shows "g_step (\<lambda>_. 1) v = 1" (is "?L = ?R")
proof -
  have "?L = (\<Sum>x\<in>in_arcs G v. 1 / real (out_degree G (tail G x)))"
    unfolding g_step_def by simp
  also have "... = (\<Sum>x\<in>in_arcs G v. 1 / d)"
    using assms by (intro sum.cong arg_cong2[where f="(/)"] arg_cong[where f="real"] reg) auto
  also have "... = in_degree G v / d"
    unfolding in_degree_def by simp
  also have "... = 1"
    unfolding reg(2)[OF assms] using d_gt_0 by simp
  finally show ?thesis by simp
qed

lemma g_step_conv: 
  "(\<chi> i. g_step f (enum_verts i)) = A *v (\<chi> i. f (enum_verts i))"
proof -
  have "g_step f (enum_verts i) = (\<Sum>j\<in>UNIV. A $ i $ j * f (enum_verts j))" (is "?L = ?R") for i
  proof -
    have "?L = (\<Sum>x\<in>in_arcs G (enum_verts i). f (tail G x) / real (out_degree G (tail G x)))"
      unfolding g_step_def by simp
    also have "... = (\<Sum>x\<in>in_arcs G (enum_verts i). f (tail G x) / real d)"
      by (intro sum.cong arg_cong2[where f="(/)"] arg_cong[where f="real"] reg) auto
    also have "... = (\<Sum>x\<in>#vertices_to G (enum_verts i). f x/d)"
      unfolding verts_to_alt  sum_unfold_sum_mset by (simp add:image_mset.compositionality comp_def)
    also have "... = (\<Sum>j\<in>verts G. (count (vertices_to G (enum_verts i)) j) * (f j / real d))"
      by (intro sum_mset_conv_2 set_mset_vertices_to) auto
    also have "... = (\<Sum>j\<in>verts G. (count (edges G) (j,enum_verts i)) * (f j / real d))"
      unfolding vertices_to_def count_mset_exp 
      by (intro sum.cong arg_cong[where f="real"] arg_cong2[where f="(*)"])
       (auto simp add:filter_filter_mset image_mset_filter_mset_swap[symmetric] prod_eq_iff ac_simps)
    also have "...=(\<Sum>j\<in>UNIV.(count(edges G)(enum_verts j,enum_verts i))*(f(enum_verts j)/real d))"
      by (intro sum.reindex_bij_betw[symmetric] enum_verts)
    also have "... = ?R"
      unfolding A_def by simp
    finally show ?thesis by simp
  qed
  thus ?thesis
    unfolding matrix_vector_mult_def by (intro iffD2[OF vec_eq_iff] allI) simp
qed

lemma markov: "markov A"
proof -
  have "A *v 1 = 1"
  proof -
    have "A *v 1 = (\<chi> i. g_step (\<lambda>_. 1) (enum_verts i))"
      unfolding g_step_conv one_vec_def by simp
    also have "... = (\<chi> i. 1)"
      using bij_betw_apply[OF enum_verts] by (subst g_step_1) auto
    also have "... = 1" unfolding one_vec_def by simp
    finally show ?thesis by simp
  qed
  thus ?thesis
    by (intro markov_symI nonneg_A symmetric_A)
qed

lemma g_inner_conv: 
  "g_inner f g = (\<chi> i. f (enum_verts i)) \<bullet> (\<chi> i. g (enum_verts i))"
  unfolding inner_vec_def g_inner_def vec_lambda_beta inner_real_def
  by (intro sum.reindex_bij_betw[symmetric] enum_verts)

lemma g_norm_conv: 
  "g_norm f = norm (\<chi> i. f (enum_verts i))"
proof -
  have "g_norm f^2 = norm (\<chi> i. f (enum_verts i))^2"
    unfolding g_norm_sq power2_norm_eq_inner g_inner_conv by simp
  thus ?thesis
    using g_norm_nonneg norm_ge_zero by simp
qed

lemma spec_bound:
  "spec_bound A \<Lambda>"
proof -
  have "norm (A *v v) \<le> \<Lambda> * norm v" if "v \<bullet> 1 = 0" for v
  proof -
    define f where "f i = v $ (snd (td_components) i)" for i
    have v_def: "v = (\<chi> i. f (enum_verts i))"
      unfolding f_def enum_verts_def Rep_inverse by simp

    have "g_inner f (\<lambda>_. 1) = v \<bullet> (\<chi> i. 1)"
      unfolding g_inner_conv v_def by simp
    also have "... = v \<bullet> 1" 
      by (simp add: one_vec_def)
    also have "... = 0" using that by simp
    finally have 0: "g_inner f (\<lambda>_. 1) = 0" by simp
    have "norm (A *v v) = g_norm (g_step f)"
      unfolding v_def g_step_conv g_norm_conv by simp
    also have "... \<le> \<Lambda> * g_norm  f"
      by (intro expansionD2 0)
    also have "... = \<Lambda> * norm v"
      unfolding v_def g_norm_conv by simp
    finally show ?thesis by simp
  qed
  thus ?thesis
    unfolding spec_bound_def using \<Lambda>_ge_0 by auto
qed

definition ind_mat where "ind_mat S = diag (ind_vec (enum_verts -` S))"

lemma walk_distr:
  "measure (pmf_of_multiset (walks G l)) {\<omega>. (\<forall>i<l. \<omega> ! i \<in> S i)} =
  foldl (\<lambda>x M. M *v x) stat (intersperse A (map (\<lambda>i. ind_mat (S i)) [0..<l]))\<bullet>1" 
  (is "?L = ?R")
proof (cases "l > 0")
  case True
  let ?n = "real (card (verts G))"
  let ?d = "real d"
  let ?W = "{(w::'a list). set w \<subseteq> verts G \<and> length w = l}"
  let ?V = "{(w::'n list). length w = l}"

  have a: "set_mset (walks G l) \<subseteq> ?W"
    using set_walks by auto
  have b: "finite ?W"
    by (intro finite_lists_length_eq) auto

  define lp where "lp = l - 1"

  define xs where "xs = map (\<lambda>i. ind_mat (S i)) [0..<l]"
  have "xs \<noteq> []" unfolding xs_def using True by simp
  then obtain xh xt where xh_xt: "xh#xt=xs" by (cases xs, auto)

  have "length xs = l"
    unfolding xs_def by simp
  hence len_xt: "length xt = lp" 
    using True unfolding xh_xt[symmetric] lp_def by simp

  have "xh = xs ! 0" 
    unfolding xh_xt[symmetric] by simp
  also have "... = ind_mat (S 0)"
    using True unfolding xs_def by simp
  finally have xh_eq: "xh = ind_mat (S 0)" 
    by simp

  have inj_map_enum_verts: "inj_on (map enum_verts) ?V"
    using bij_betw_imp_inj_on[OF enum_verts] inj_on_subset
    by (intro inj_on_mapI) auto

  have "card ?W = card (verts G)^l"
    by (intro card_lists_length_eq) simp
  also have "... = card {w. set w \<subseteq> (UNIV :: 'n set) \<and> length w  = l}"
    unfolding card[symmetric] by (intro card_lists_length_eq[symmetric]) simp
  also have "... = card ?V"
    by (intro arg_cong[where f="card"]) auto
  also have "... = card (map enum_verts ` ?V)"
    by (intro card_image[symmetric] inj_map_enum_verts)
  finally have "card ?W = card (map enum_verts ` ?V)"
    by simp
  hence "map enum_verts ` ?V = ?W"
    using bij_betw_apply[OF enum_verts]
    by (intro card_subset_eq b image_subsetI) auto

  hence bij_map_enum_verts: "bij_betw (map enum_verts) ?V ?W"
    using inj_map_enum_verts unfolding bij_betw_def by auto

  have "?L = size {# w \<in># walks G l. \<forall>i<l. w ! i \<in> S i #} / (?n * ?d^(l-1))"
    using True unfolding size_walks measure_pmf_of_multiset[OF walks_nonempty] by simp
  also have "... = (\<Sum>w\<in>?W. real (count (walks G l) w) * of_bool (\<forall>i<l. w!i \<in> S i))/(?n*?d^(l-1))"
    unfolding size_filter_mset_conv sum_mset_conv_2[OF a b] by simp
  also have "... = (\<Sum>w\<in>?W. (\<Prod>i<l-1. real (count (edges G) (w!i,w!(i+1)))) * 
                            (\<Prod>i<l. of_bool (w!i \<in> S i)))/(?n*?d^(l-1))"
    using True by (intro sum.cong arg_cong2[where f="(/)"]) (auto simp add: count_walks)
  also have "... = 
    (\<Sum>w\<in>?W. (\<Prod>i<l-1. real (count (edges G) (w!i,w!(i+1)))/?d)*(\<Prod>i<l. of_bool (w!i \<in> S i)))/?n"
    using True unfolding prod_dividef by (simp add:sum_divide_distrib algebra_simps)
  also have "... = 
    (\<Sum>w\<in>?V. (\<Prod>i<l-1. count (edges G) (map enum_verts w!i,map enum_verts w!(i+1)) / ?d) * 
    (\<Prod>i<l. of_bool (map enum_verts w!i \<in> S i)))/?n"
    by (intro sum.reindex_bij_betw[symmetric] arg_cong2[where f="(/)"] refl bij_map_enum_verts)
  also have "... = 
    (\<Sum>w\<in>?V. (\<Prod>i<lp. A $ w!(i+1) $ w!i) * (\<Prod>i<Suc lp. of_bool(enum_verts (w!i) \<in> S i)))/?n"
    unfolding A_def lp_def using True by simp
  also have "... = (\<Sum>w\<in>?V. (\<Prod>i<lp. A $ w!(i+1) $ w!i) * 
    (\<Prod>i\<in>insert 0 (Suc ` {..<lp}). of_bool(enum_verts (w!i) \<in> S i)))/?n"
    using lessThan_Suc_eq_insert_0
    by (intro sum.cong arg_cong2[where f="(/)"] arg_cong2[where f="(*)"] prod.cong) auto
  also have "... = (\<Sum>w\<in>?V. (\<Prod>i<lp. of_bool(enum_verts (w!(i+1))\<in>S(i+1))* A$ w!(i+1) $ w!i) 
    * of_bool(enum_verts(w!0)\<in>S 0))/?n"
    by (simp add:prod.reindex algebra_simps prod.distrib)
  also have "... = 
    (\<Sum>w\<in>?V. (\<Prod>i<lp. (ind_mat (S (i+1))**A) $ w!(i+1) $ w!i) * of_bool(enum_verts (w!0)\<in>S 0))/?n"
    unfolding diag_def ind_vec_def matrix_matrix_mult_def ind_mat_def
    by (intro sum.cong arg_cong2[where f="(/)"] arg_cong2[where f="(*)"] prod.cong refl) 
      (simp add:if_distrib if_distribR sum.If_cases)
  also have "... = 
    (\<Sum>w\<in>?V. (\<Prod>i<lp. (xs!(i+1)**A) $ w!(i+1) $ w!i) * of_bool(enum_verts (w!0)\<in>S 0))/?n"
    unfolding xs_def lp_def True
    by (intro sum.cong arg_cong2[where f="(/)"] arg_cong2[where f="(*)"] prod.cong refl) auto 
  also have "... = 
    (\<Sum>w\<in>?V. (\<Prod>i<lp. (xt ! i ** A) $ w!(i+1) $ w!i) * of_bool(enum_verts (w!0)\<in>S 0))/?n"
    unfolding xh_xt[symmetric] by auto
  also have "... = (\<Sum>w\<in>?V. (\<Prod>i<lp. (xt!i**A)$ w!(i+1) $ w!i)*(ind_mat(S 0)*v stat) $w!0)"
    unfolding matrix_vector_mult_def diag_def stat_def ind_vec_def ind_mat_def card
    by (simp add:sum.If_cases if_distrib if_distribR sum_divide_distrib)
  also have "... = (\<Sum>w\<in>?V. (\<Prod>i<lp. (xt ! i ** A) $ w!(i+1) $ w!i) * (xh *v stat) $ w ! 0)"
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

lemma hitting_property_1:
  assumes "S \<subseteq> verts G" 
  assumes "I \<subseteq> {..<l}"
  defines "\<mu> \<equiv> real (card S) / card (verts G)"
  shows "measure (pmf_of_multiset (walks G l)) {w. set (nths w I) \<subseteq> S} \<le> (\<mu>+\<Lambda>*(1-\<mu>))^card I" 
    (is "?L \<le> ?R")
proof -
  define T where "T = (\<lambda>i. if i \<in> I then S else UNIV)" 

  have 0: "ind_mat UNIV = mat 1"
    unfolding ind_mat_def diag_def ind_vec_def Finite_Cartesian_Product.mat_def by vector

  have \<Lambda>_range: "\<Lambda> \<in> {0..1}"
    using \<Lambda>_ge_0 \<Lambda>_le_1 by simp

  have "S \<subseteq> range enum_verts" 
    using assms(1) enum_verts unfolding bij_betw_def by simp
  moreover have "inj enum_verts" 
    using bij_betw_imp_inj_on[OF enum_verts] by simp
  ultimately have \<mu>_alt: "\<mu> = real (card (enum_verts -` S)) / CARD ('n)"
    unfolding \<mu>_def card by (subst card_vimage_inj) auto

  have "?L = measure (pmf_of_multiset (walks G l)) {w. \<forall>i<l. w ! i \<in> T i}"
    using walks_nonempty set_walks_3 unfolding T_def set_nths
    by (intro measure_eq_AE AE_pmfI) auto
  also have "... = foldl (\<lambda>x M. M *v x) stat 
    (intersperse A (map (\<lambda>i. (if i \<in> I then ind_mat S else mat 1)) [0..<l])) \<bullet> 1"
    unfolding walk_distr T_def by (simp add:if_distrib if_distribR 0 cong:if_cong)
  also have "... \<le> ?R"
    unfolding \<mu>_alt ind_mat_def
    by (intro hitting_property_alg_2[OF \<Lambda>_range assms(2) spec_bound markov])
  finally show ?thesis by simp
qed

lemma uniform_property_1:
  assumes  "i < l" "x \<in> verts G"
  shows "measure (pmf_of_multiset (walks G l)) {w. w ! i = x} = 1/real (card (verts G))" 
    (is "?L = ?R")
proof -
  obtain xi where xi_def: "enum_verts xi = x" 
    using assms(2) bij_betw_imp_surj_on[OF enum_verts] by force

  define T where "T = (\<lambda>j. if j = i then {x} else UNIV)"

  have "diag (ind_vec UNIV) = mat 1"
    unfolding diag_def ind_vec_def Finite_Cartesian_Product.mat_def by vector
  moreover have "enum_verts -` {x} = {xi}"
    using bij_betw_imp_inj_on[OF enum_verts]
    unfolding vimage_def xi_def[symmetric] by (auto simp add:inj_on_def)
  ultimately have 0: "ind_mat (T j) = (if j = i then diag (ind_vec {xi}) else mat 1)" for j
    unfolding T_def ind_mat_def by (cases "j = i", auto)

  have "?L = measure (pmf_of_multiset (walks G l)) {w. \<forall>j < l. w ! j \<in> T j}"
    unfolding T_def using assms(1) by simp
  also have "... = foldl (\<lambda>x M. M *v x) stat (intersperse A (map (\<lambda>j. ind_mat (T j)) [0..<l])) \<bullet> 1"
    unfolding walk_distr by simp
  also have "... = 1/CARD('n)"
    unfolding 0 uniform_property_alg[OF assms(1) markov] by simp
  also have "... = ?R" 
    unfolding card by simp
  finally show ?thesis  by simp
qed

end

lemma remove_finite_premise_aux:
  assumes "\<exists>(Rep :: 'n  \<Rightarrow> 'a) Abs. type_definition Rep Abs (verts G)"
  shows "class.finite TYPE('n)"
proof -
  obtain Rep :: "'n \<Rightarrow> 'a" and Abs where d:"type_definition Rep Abs (verts G)"
    using assms by auto
  interpret type_definition Rep Abs "verts G"
    using d by simp
                              
  have "finite (verts G)" by simp 
  thus ?thesis
    unfolding class.finite_def univ by auto
qed

lemma remove_finite_premise: 
  "(class.finite TYPE('n) \<Longrightarrow> \<exists>(Rep :: 'n  \<Rightarrow> 'a) Abs. type_definition Rep Abs (verts G) \<Longrightarrow> PROP Q) 
  \<equiv> (\<exists>(Rep :: 'n  \<Rightarrow> 'a) Abs. type_definition Rep Abs (verts G) \<Longrightarrow> PROP Q)" 
  (is "?L \<equiv> ?R")
proof (intro Pure.equal_intr_rule)
  assume e:"\<exists>(Rep :: 'n  \<Rightarrow> 'a) Abs. type_definition Rep Abs (verts G)" and l:"PROP ?L"
  hence f: "class.finite TYPE('n)" 
    using remove_finite_premise_aux[OF e] by simp

  show "PROP ?R"
    using l[OF f] by auto
next
  assume "\<exists>(Rep :: 'n  \<Rightarrow> 'a) Abs. type_definition Rep Abs (verts G)" and l:"PROP ?R"
  show "PROP ?L"
    using l by auto
qed

lemmas hitting_property =  
  pre_expander_graph.hitting_property_1[
    internalize_sort "'n :: finite", OF _ pre_expander_graph_axioms, 
    unfolded remove_finite_premise, cancel_type_definition, OF verts_non_empty]

lemmas uniform_property_2 =  
  pre_expander_graph.uniform_property_1[
    internalize_sort "'n :: finite", OF _ pre_expander_graph_axioms, 
    unfolded remove_finite_premise, cancel_type_definition, OF verts_non_empty]

lemma uniform_property:
  assumes "i < l"
  shows "map_pmf (\<lambda>w. w ! i) (pmf_of_multiset (walks G l)) = pmf_of_set (verts G)" (is "?L = ?R")
proof (rule pmf_eqI)
  fix x :: "'a"
  have a:"measure (pmf_of_multiset (walks G l)) {w. w ! i = x} = 0" (is "?L1 = ?R1")
    if "x \<notin> verts G"
  proof -
    have "?L1 \<le> measure (pmf_of_multiset (walks G l)) {w. set w \<subseteq> verts G \<and> x \<in> set w}"
      using walks_nonempty set_walks_3 assms(1)
      by (intro measure_pmf.pmf_mono[OF refl]) auto
    also have "... \<le> measure (pmf_of_multiset (walks G l)) {}"
      using that by (intro measure_pmf.pmf_mono[OF refl]) auto
    also have "... = 0" by simp
    finally have "?L1 \<le> 0" by simp
    thus ?thesis using measure_le_0_iff by blast
  qed

  have "pmf ?L x = measure (pmf_of_multiset (walks G l)) {w. w ! i = x}"
    unfolding pmf_map by (simp add:vimage_def)
  also have "... = indicator (verts G) x/real (card (verts G))"
    using uniform_property_2[OF assms(1)] a
    by (cases "x \<in> verts G", auto)
  also have "... = pmf ?R x"
    using verts_non_empty by (intro pmf_of_set[symmetric]) auto 
  finally show "pmf ?L x = pmf ?R x" by simp
qed

lemma uniform_property_gen:
  fixes S :: "'a set"
  assumes "S \<subseteq> verts G" "i < l"
  defines "\<mu> \<equiv> real (card S) / card (verts G)"
  shows "measure (pmf_of_multiset (walks G l)) {w. w ! i \<in> S} = \<mu>" (is "?L = ?R")
proof -

  have "?L = measure (map_pmf (\<lambda>w. w ! i) (pmf_of_multiset (walks G l))) S"
    unfolding measure_map_pmf by (simp add:vimage_def)
  also have "... = measure (pmf_of_set (verts G)) S"
    unfolding uniform_property[OF assms(2)] by simp
  also have "... = ?R"
    using verts_non_empty Int_absorb1[OF assms(1)] 
    unfolding \<mu>_def by (subst measure_pmf_of_set) auto 
  finally show ?thesis by simp
qed

lemma kl_chernoff_property:
  assumes "l > 0"
  assumes "S \<subseteq> verts G" 
  defines "\<mu> \<equiv> real (card S) / card (verts G)"
  assumes "\<gamma> \<le> 1" "\<mu> + \<Lambda> * (1-\<mu>) \<in> {0<..\<gamma>}"
  shows "measure (pmf_of_multiset (walks G l)) {w. real (card {i \<in> {..<l}. w ! i \<in> S}) \<ge> \<gamma>*real l} 
    \<le> exp (- real l * KL_div \<gamma> (\<mu>+\<Lambda>*(1-\<mu>)))" (is "?L \<le> ?R")
proof -
  let ?\<delta> = "(\<Sum>i<l. \<mu>+\<Lambda>*(1-\<mu>))/l"

  have a: "measure (pmf_of_multiset (walks G l)) {w. \<forall>i\<in>T. w ! i \<in> S} \<le> (\<mu> + \<Lambda>*(1-\<mu>)) ^ card T"
    (is "?L1 \<le> ?R1") if "T \<subseteq> {..<l}" for T 
  proof -
    have "?L1 = measure (pmf_of_multiset (walks G l)) {w. set (nths w T) \<subseteq> S}"
      unfolding set_nths setcompr_eq_image using that set_walks_3 walks_nonempty
      by (intro measure_eq_AE AE_pmfI) (auto simp add:image_subset_iff)
    also have "... \<le> ?R1"
      unfolding \<mu>_def by (intro hitting_property[OF assms(2) that])
    finally show ?thesis by simp
  qed
 
  have "?L \<le> exp ( - real l * KL_div \<gamma> ?\<delta>)"
    using assms(1,4,5) a by (intro impagliazzo_kabanets_pmf) simp_all
  also have "... = ?R" by simp
  finally show ?thesis by simp
qed

end


end

