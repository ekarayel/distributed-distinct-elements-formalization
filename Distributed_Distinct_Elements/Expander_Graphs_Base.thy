theory Expander_Graphs_Base
  imports 
    Graph_Theory.Digraph
    Graph_Theory.Digraph_Isomorphism
    "HOL-Library.Multiset" 
    "HOL-Analysis.L2_Norm" 
    "Extra_Congruence_Rules"
begin

unbundle intro_cong_syntax

lemma count_mset_exp: "count A x = size (filter_mset (\<lambda>y. y = x) A)"
  by (induction A, simp, simp)

definition arcs_betw where "arcs_betw G u v = {a. a \<in> arcs G \<and> head G a = v \<and> tail G a = u}"

text \<open>The following is a stronger notion than the notion of symmetry defined in 
@{theory "Graph_Theory.Digraph"}, it requires that the number of edges from @{term "v"} to 
@{term "w"} must be equal to the number of edges from @{term "w"} to @{term "v"} for any pair of 
vertices @{term "v"} @{term "w \<in> verts G"}.\<close>

definition symmetric_multi_graph where "symmetric_multi_graph G =
  (fin_digraph G \<and> (\<forall>v w. {v, w} \<subseteq> verts G \<longrightarrow> card (arcs_betw G w v) = card (arcs_betw G v w)))"

lemma symmetric_multi_graphI:
  assumes "fin_digraph G"
  assumes "bij_betw f (arcs G) (arcs G)"
  assumes "\<And>e. e \<in> arcs G \<Longrightarrow> head G (f e) = tail G e \<and> tail G (f e) = head G e"
  shows "symmetric_multi_graph G"
proof -
  have "card (arcs_betw G w v) = card (arcs_betw G v w)"
    (is "?L = ?R") if "v \<in> verts G" "w \<in> verts G" for v w
  proof -
    have a:"f x \<in> arcs G" if "x \<in> arcs G" for x
      using assms(2) that unfolding bij_betw_def by auto
    have b:"\<exists>y. y \<in> arcs G \<and> f y = x" if "x \<in> arcs G" for x
      using bij_betw_imp_surj_on[OF assms(2)] that by force

    have "inj_on f (arcs G)" 
      using assms(2) unfolding bij_betw_def by simp
    hence "inj_on f {e \<in> arcs G. head G e = v \<and> tail G e = w}"
      by (rule inj_on_subset, auto)
    hence "?L = card (f ` {e \<in> arcs G. head G e = v \<and> tail G e = w})"
      unfolding arcs_betw_def
      by (intro card_image[symmetric])
    also have "... = ?R"
      unfolding arcs_betw_def using a b assms(3)
      by (intro arg_cong[where f="card"] order_antisym image_subsetI subsetI) fastforce+ 
    finally show ?thesis by simp
  qed
  thus ?thesis 
    using assms(1) unfolding symmetric_multi_graph_def by simp
qed

lemma symmetric_multi_graphD2:
  assumes "symmetric_multi_graph G"
  shows "fin_digraph G"
  using assms unfolding symmetric_multi_graph_def by simp 

lemma symmetric_multi_graphD:
  assumes "symmetric_multi_graph G"
  shows "card {e \<in> arcs G. head G e=v \<and> tail G e=w} = card {e \<in> arcs G. head G e=w \<and> tail G e=v}" 
    (is "card ?L = card ?R")
proof (cases "v \<in> verts G \<and> w \<in> verts G")
  case True
  then show ?thesis 
  using assms unfolding symmetric_multi_graph_def arcs_betw_def by simp 
next
  case False
  interpret fin_digraph G
    using symmetric_multi_graphD2[OF assms(1)] by simp
  have 0:"?L = {}" "?R = {}"
    using False wellformed by auto
  show ?thesis unfolding 0 by simp
qed

lemma symmetric_multi_graphD3:
  assumes "symmetric_multi_graph G"
  shows "card {e \<in> arcs G. tail G e=v \<and> head G e=w} = card {e \<in> arcs G. tail G e=w \<and> head G e=v}" 
  using symmetric_multi_graphD[OF assms] by (simp add:conj.commute)

lemma symmetric_multi_graphD4:
  assumes "symmetric_multi_graph G"
  shows "card (arcs_betw G v w) = card (arcs_betw G w v)" 
  using symmetric_multi_graphD[OF assms] unfolding arcs_betw_def by simp

lemma symmetric_degree_eq:
  assumes "symmetric_multi_graph G"
  assumes "v \<in> verts G"
  shows "out_degree G v = in_degree G v" (is "?L = ?R")
proof -
  interpret fin_digraph "G" 
    using assms(1) symmetric_multi_graph_def by auto

  have "?L = card {e \<in> arcs G. tail G e = v}"
    unfolding out_degree_def out_arcs_def by simp
  also have "... = card (\<Union>w \<in> verts G. {e \<in> arcs G. head G e = w \<and> tail G e = v})"
    using wellformed 
    by (intro arg_cong[where f="card"]) (auto simp add:set_eq_iff)
  also have "... = (\<Sum>w \<in> verts G. card {e \<in> arcs G. head G e = w \<and> tail G e = v})"
    by (intro card_UN_disjoint) auto
  also have "... = (\<Sum>w \<in> verts G. card {e \<in> arcs G. head G e = v \<and> tail G e = w})"
    by (intro sum.cong refl symmetric_multi_graphD assms)
  also have "... = card (\<Union>w \<in> verts G. {e \<in> arcs G. head G e = v \<and> tail G e = w})"
    by (intro card_UN_disjoint[symmetric]) auto
  also have "... = card (in_arcs G v)"
    using wellformed by (intro arg_cong[where f="card"]) (auto simp add:set_eq_iff) 
  also have "... = ?R" 
    unfolding in_degree_def by simp
  finally show ?thesis by simp
qed

definition edges where "edges G = image_mset (arc_to_ends G) (mset_set (arcs G))"

lemma (in fin_digraph) count_edges:
  "count (edges G) (u,v) = card (arcs_betw G u v)" (is "?L = ?R")
proof -
  have "?L = card {x \<in> arcs G. arc_to_ends G x = (u, v)}"
    unfolding edges_def count_mset_exp image_mset_filter_mset_swap[symmetric] by simp
  also have "... = ?R"
    unfolding arcs_betw_def arc_to_ends_def
    by (intro arg_cong[where f="card"]) auto
  finally show ?thesis by simp
qed

lemma (in fin_digraph) count_edges_sym:
  assumes "symmetric_multi_graph G"
  shows "count (edges G) (v, w) = count (edges G) (w, v)" 
  unfolding count_edges using symmetric_multi_graphD4[OF assms]  by simp

lemma (in fin_digraph) edges_sym:
  assumes "symmetric_multi_graph G"
  shows "{# (y,x). (x,y) \<in># (edges G) #} = edges G" 
proof -
  have "count {#(y, x). (x, y) \<in># edges G#} x = count (edges G) x" (is "?L = ?R") for x
  proof -
    have "?L = count (edges G) (snd x, fst x)"
      unfolding count_mset_exp
      by (simp add:image_mset_filter_mset_swap[symmetric] case_prod_beta prod_eq_iff ac_simps)
    also have "... = count (edges G) (fst x, snd x)"
      unfolding count_edges_sym[OF assms] by simp
    also have "... = count (edges G) x" by simp
    finally show ?thesis by simp
  qed

  thus ?thesis
    by (intro multiset_eqI) simp
qed


locale pre_expander_graph = fin_digraph +
  assumes sym: "symmetric_multi_graph G"
  assumes verts_non_empty: "verts G \<noteq> {}"
  assumes arcs_non_empty: "arcs G \<noteq> {}"
  assumes reg': "\<And>v w. v \<in> verts G \<Longrightarrow> w \<in> verts G \<Longrightarrow> out_degree G v = out_degree G w"
begin

definition d where "d = out_degree G (SOME v. v \<in> verts G)"

lemma reg: 
  assumes "v \<in> verts G"
  shows "out_degree G v = d" "in_degree G v = d"
proof -
  define w where "w = (SOME v. v \<in> verts G)"
  have "w \<in> verts G"
    unfolding w_def using assms(1) by (rule someI)
  hence "out_degree G v = out_degree G w"
    by (intro reg' assms(1))
  also have "... = d"
    unfolding d_def w_def by simp
  finally show a:"out_degree G v = d" by simp

  show "in_degree G v = d"
    using a symmetric_degree_eq[OF sym assms(1)] by simp
qed

definition n where "n = card (verts G)"

lemma n_gt_0: "n > 0"
  unfolding n_def using verts_non_empty by auto

lemma d_gt_0: "d > 0"
proof -
  obtain a where a:"a \<in> arcs G"
    using arcs_non_empty by auto
  hence "a \<in> in_arcs G (head G a) "
    unfolding in_arcs_def by simp
  hence "0 < in_degree G (head G a)"
    unfolding in_degree_def card_gt_0_iff by blast
  also have "... = d"
    using a by (intro reg) simp
  finally show ?thesis by simp
qed

(* should we use conjugatable field here? *)
definition g_inner :: "('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real" 
  where "g_inner f g = (\<Sum>x \<in> verts G. (f x) * (g x))"

lemma g_inner_simps:
  "g_inner (\<lambda>x. 0) g = 0" 
  "g_inner f (\<lambda>x. 0) = 0" 
  "g_inner (\<lambda>x. c * f x) g = c * g_inner f g" 
  "g_inner f (\<lambda>x. c * g x) = c * g_inner f g" 
  "g_inner (\<lambda>x. f x - g x) h = g_inner f h - g_inner g h" 
  "g_inner (\<lambda>x. f x + g x) h = g_inner f h + g_inner g h" 
  "g_inner f (\<lambda>x. g x + h x) = g_inner f g + g_inner f h" 
  "g_inner f (\<lambda>x. g x / c) = g_inner f g / c" 
  "g_inner (\<lambda>x. f x / c) g = g_inner f g / c" 
  unfolding g_inner_def 
  by (auto simp add:sum.distrib algebra_simps sum_distrib_left sum_subtractf sum_divide_distrib)

(* TODO use L2_set *)
definition "g_norm f = sqrt (g_inner f f)"

lemma g_norm_eq: "g_norm f = L2_set f (verts G)"
  unfolding g_norm_def g_inner_def L2_set_def
  by (intro arg_cong[where f="sqrt"] sum.cong refl) (simp add:power2_eq_square)

lemma g_inner_cauchy_schwartz:
  "\<bar>g_inner f g\<bar> \<le> g_norm f * g_norm g"
proof -
  have "\<bar>g_inner f g\<bar> \<le> (\<Sum>v \<in> verts G. \<bar>f v * g v\<bar>)" 
    unfolding g_inner_def by (intro sum_abs)
  also have "... \<le> g_norm f * g_norm g"
    unfolding g_norm_eq abs_mult by (intro L2_set_mult_ineq)
  finally show ?thesis by simp
qed

lemma g_inner_cong:
  assumes "\<And>x. x \<in> verts G \<Longrightarrow> f1 x = f2 x"
  assumes "\<And>x. x \<in> verts G \<Longrightarrow> g1 x = g2 x"
  shows "g_inner f1 g1 = g_inner f2 g2"
  unfolding g_inner_def using assms
  by (intro sum.cong refl) auto

lemma g_norm_cong:
  assumes "\<And>x. x \<in> verts G \<Longrightarrow> f x = g x"
  shows "g_norm f = g_norm g"
  unfolding g_norm_def 
  by (intro arg_cong[where f="sqrt"] g_inner_cong assms)

lemma g_norm_nonneg: "g_norm f \<ge> 0" 
  unfolding g_norm_def g_inner_def
  by (intro real_sqrt_ge_zero sum_nonneg) auto

lemma g_norm_sq:
  "g_norm f^2 = g_inner f f" 
  using g_norm_nonneg g_norm_def by simp

definition g_step :: "('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real)"
  where "g_step f v = (\<Sum>x \<in> in_arcs G v. f (tail G x) / real (out_degree G (tail G x)))"

lemma g_step_altdef:
  "g_step f v = (\<Sum>x \<in> in_arcs G v. f (tail G x) / real d)"
  unfolding g_step_def by (intro_cong "[\<sigma>\<^sub>2 (/), \<sigma>\<^sub>1 real]" more: sum.cong reg) auto


lemma g_step_simps:
  "g_step (\<lambda>x. f x  + g x) y = g_step f y + g_step g y"
  "g_step (\<lambda>x. f x / c) y = g_step f y / c"
  unfolding g_step_altdef  sum_divide_distrib[symmetric] using finite_in_arcs d_gt_0
  by (auto intro:sum.cong simp add:sum.distrib field_simps sum_distrib_left sum_subtractf)

lemma g_inner_step_eq:
  "g_inner f (g_step f) = (\<Sum>a \<in> arcs G. f (head G a) * f (tail G a)) / d" (is "?L = ?R")
proof -
  have "?L = (\<Sum>v\<in>verts G. f v * (\<Sum>a\<in>in_arcs G v. f (tail G a) / d))"
    unfolding g_inner_def g_step_altdef by simp
  also have "... = (\<Sum>v\<in>verts G. (\<Sum>a\<in>in_arcs G v. f v * f (tail G a) / d))"
    by (subst sum_distrib_left) simp
  also have "... =  (\<Sum>v\<in>verts G. (\<Sum>a\<in>in_arcs G v. f (head G a) * f (tail G a) / d))"
    unfolding in_arcs_def by (intro sum.cong refl) simp
  also have "... = (\<Sum>a \<in> (\<Union> (in_arcs G ` verts G)). f (head G a) * f (tail G a) / d)"
    using finite_verts by (intro sum.UNION_disjoint[symmetric] ballI) 
      (auto simp add:in_arcs_def)
  also have "... = (\<Sum>a \<in> arcs G. f (head G a) * f (tail G a) / d)"
    unfolding in_arcs_def using wellformed by (intro sum.cong) auto
  also have "... = ?R"
    by (intro sum_divide_distrib[symmetric])
  finally show ?thesis by simp
qed

definition \<Lambda>_test 
  where "\<Lambda>_test = {f. g_norm f^2 \<le> 1 \<and> g_inner f (\<lambda>_. 1) = 0}"

lemma \<Lambda>_test_ne: "\<Lambda>_test \<noteq> {}"
proof -
  have "(\<lambda>_. 0) \<in> \<Lambda>_test"
    unfolding \<Lambda>_test_def g_norm_sq g_inner_def by simp
  thus ?thesis by auto
qed

text \<open>The following is a variational definition for the second largest absolute eigenvalue of the
stochastic matrix (using the supremum of the Rayleigh-Quotient for vectors orthogonal to the
stationary distribution). In Section~\ref{sec:expander_spectral_theory}, the equivalence of this
definition and the more common definition will be shown. The definition here has the advantage
that it is (obviously) independent of the matrix representation (ordering of the vertices) used.\<close>

definition \<Lambda> :: real 
  where "\<Lambda> = (SUP f \<in> \<Lambda>_test. \<bar>\<Sum>a \<in> arcs G. f (head G a) * f (tail G a)\<bar>/d)"

lemma 
  shows bdd_above_\<Lambda>: "bdd_above ((\<lambda>f.\<bar>\<Sum>a\<in>arcs G. f(head G a)*f(tail G a)\<bar>/d)`\<Lambda>_test)" (is "?A")
    and \<Lambda>_le_1: "\<Lambda> \<le> 1" (is "?B")
proof -
  have 2:"\<bar>\<Sum>a\<in>arcs G. f (head G a) * f (tail G a)\<bar>/d \<le> 1" (is "?L \<le> ?R") if "f \<in> \<Lambda>_test" for f
  proof -
    have "(\<Sum>a\<in>arcs G. f (head G a)^2) = (\<Sum>a\<in>(\<Union>v \<in> verts G. in_arcs G v). f (head G a)^2)"
      unfolding in_arcs_def by (intro sum.cong) auto
    also have "... = (\<Sum>v \<in> verts G. (\<Sum>a \<in> in_arcs G v. f (head G a)^2))"
      by (intro sum.UNION_disjoint) auto
    also have "... = (\<Sum>v \<in> verts G. (\<Sum>a \<in> in_arcs G v. f v^2))"
      unfolding in_arcs_def by (intro sum.cong refl) auto
    also have "... = (\<Sum>v \<in> verts G. in_degree G v * f v^2)"
      unfolding in_degree_def by simp
    also have "... = (\<Sum>v \<in> verts G. d * f v^2)"
      by (intro sum.cong arg_cong2[where f="(*)"] arg_cong[where f="real"] reg) auto
    also have "... = d * g_norm f^2"
      unfolding sum_distrib_left[symmetric] g_norm_sq g_inner_def
      by (simp add:power2_eq_square)
    also have "... \<le> real d * 1"
      using that \<Lambda>_test_def by (intro mult_left_mono) auto
    finally have "(\<Sum>a\<in>arcs G. f (head G a)^2) \<le> d" by simp
    hence 0:"L2_set (\<lambda>a. f (head G a)) (arcs G) \<le> sqrt d" 
      unfolding L2_set_def by simp

    have "(\<Sum>a\<in>arcs G. f (tail G a)^2) = (\<Sum>a\<in>(\<Union>v \<in> verts G. out_arcs G v). f (tail G a)^2)"
      unfolding out_arcs_def by (intro sum.cong) auto
    also have "... = (\<Sum>v \<in> verts G. (\<Sum>a \<in> out_arcs G v. f (tail G a)^2))"
      by (intro sum.UNION_disjoint) auto
    also have "... = (\<Sum>v \<in> verts G. (\<Sum>a \<in> out_arcs G v. f v^2))"
      by (intro sum.cong refl) auto
    also have "... = (\<Sum>v \<in> verts G. out_degree G v * f v^2)"
      unfolding out_degree_def by simp
    also have "... = (\<Sum>v \<in> verts G. d * f v^2)"
      by (intro sum.cong arg_cong2[where f="(*)"] arg_cong[where f="real"] reg) auto
    also have "... = d * g_norm f^2"
      unfolding sum_distrib_left[symmetric] g_norm_sq g_inner_def
      by (simp add:power2_eq_square)
    also have "... \<le> real d * 1"
      using that \<Lambda>_test_def by (intro mult_left_mono) auto
    finally have "(\<Sum>a\<in>arcs G. f (tail G a)^2) \<le> d" by simp
    hence 1:"L2_set (\<lambda>a. f (tail G a)) (arcs G) \<le> sqrt d" 
      unfolding L2_set_def by simp

    have "?L \<le> (\<Sum>a \<in> arcs G. \<bar>f (head G a)\<bar> * \<bar>f(tail G a)\<bar>)/d"
      unfolding abs_mult[symmetric] by (intro divide_right_mono sum_abs) auto
    also have "... \<le> (L2_set (\<lambda>a. f (head G a)) (arcs G) * L2_set (\<lambda>a. f (tail G a)) (arcs G)) / d"
      by (intro L2_set_mult_ineq divide_right_mono) auto
    also have "... \<le> (sqrt d * sqrt d) / d"
      by (intro divide_right_mono mult_mono 0 1) auto
    also have "... = 1"
      using d_gt_0 by simp
    finally show ?thesis by simp
  qed
  thus ?A
    by (intro bdd_aboveI[where M="1"]) auto
  show ?B
    unfolding \<Lambda>_def using 2 \<Lambda>_test_ne
    by (intro cSup_least) auto
qed

lemma \<Lambda>_ge_0: "\<Lambda> \<ge> 0"
proof -
  have 0:"(\<lambda>_. 0) \<in> \<Lambda>_test" 
    unfolding \<Lambda>_test_def g_norm_sq g_inner_def by simp
  thus ?thesis
    unfolding \<Lambda>_def 
    by (intro cSup_upper bdd_above_\<Lambda> image_eqI[OF _ 0]) auto
qed

lemma expander_intro_1:
  assumes "C \<ge> 0"
  assumes "\<And>f. g_inner f (\<lambda>_. 1)=0 \<Longrightarrow> \<bar>g_inner f (g_step f)\<bar> \<le> C*g_norm f^2" 
  shows "\<Lambda> \<le> C"
proof -
  have "\<bar>\<Sum>a\<in>arcs G. f (head G a) * f (tail G a)\<bar>/d \<le> C" (is "?L \<le> ?R") if "f \<in> \<Lambda>_test" for f
  proof -
    have "?L = \<bar>(\<Sum>a\<in>arcs G. f (head G a) * f (tail G a))/d\<bar>"
      using d_gt_0 by simp
    also have "... = \<bar>g_inner f (g_step f)\<bar> "
      unfolding g_inner_step_eq by simp
    also have "... \<le> C*g_norm f^2"
      using that unfolding \<Lambda>_test_def 
      by (intro divide_right_mono assms(2)) auto
    also have "... \<le> C * 1"
      using that assms(1) unfolding \<Lambda>_test_def
      by (intro mult_left_mono) auto
    also have "... = ?R" by simp
    finally show ?thesis by simp
  qed
  thus ?thesis
    unfolding \<Lambda>_def using \<Lambda>_test_ne
    by (intro cSup_least) auto
qed

lemma expander_intro:
  assumes "C \<ge> 0"
  assumes "\<And>f. g_inner f (\<lambda>_. 1)=0 \<Longrightarrow> \<bar>\<Sum>a \<in> arcs G. f(head G a) * f(tail G a)\<bar> \<le> C*g_norm f^2" 
  shows "\<Lambda> \<le> C/d"
proof -
  have "\<bar>\<Sum>a\<in>arcs G. f (head G a) * f (tail G a)\<bar>/d \<le> C/d" (is "?L \<le> ?R") if "f \<in> \<Lambda>_test" for f
  proof -
    have "?L \<le> C*g_norm f^2/d"
      using that unfolding \<Lambda>_test_def
      by (intro divide_right_mono assms(2)) auto
    also have "... = (C /d) * g_norm f^2"
      by simp
    also have "... \<le> (C/d) * 1"
      using that assms(1) unfolding \<Lambda>_test_def
      by (intro mult_left_mono) auto
    also have "... = ?R" by simp
    finally show ?thesis by simp
  qed

  thus ?thesis
    unfolding \<Lambda>_def using \<Lambda>_test_ne
    by (intro cSup_least) auto
qed

lemma expansionD1:
  assumes "g_inner f (\<lambda>_. 1) = 0"
  shows "\<bar>g_inner f (g_step f)\<bar> \<le> \<Lambda> * g_norm f^2"  (is "?L \<le> ?R")
proof (cases "g_norm f \<noteq> 0")
  case True
  define g where "g x = f x / g_norm f" for x 
  have "g_norm g^2 = g_inner g g"
    unfolding g_norm_sq by simp
  also have "... = g_inner f f / (g_norm f^2)"
    unfolding g_def by (simp add:g_inner_simps power2_eq_square)
  also have "... = 1"
    using True unfolding g_norm_sq[symmetric] by simp
  finally have 1:"g_norm g^2 = 1" by simp

  have 2: "g_inner g (\<lambda>_. 1) = 0" 
    unfolding g_def g_inner_simps assms(1) by simp

  have 0:"g \<in> \<Lambda>_test"
    unfolding \<Lambda>_test_def using 1 2 by auto

  have "?L = \<bar>g_inner g (g_step g) * g_norm f^2\<bar>"
    unfolding g_def g_inner_simps g_step_simps using True by (simp add:power2_eq_square) 
  also have "... = g_norm f^2 * (\<bar>\<Sum>a \<in> arcs G. g (head G a) * g (tail G a)\<bar>/d)"
    unfolding g_inner_step_eq by (simp add:abs_mult)
  also have "... \<le> g_norm f^2 * \<Lambda>"
    unfolding \<Lambda>_def by (intro mult_left_mono cSup_upper imageI 0 bdd_above_\<Lambda>) auto
  also have "... = ?R" by simp
  finally show ?thesis by simp
next
  case False
  hence "g_inner f f = 0"
    unfolding g_norm_sq[symmetric] by simp
  hence 0:"\<And>v. v \<in> verts G \<Longrightarrow> f v = 0"
    unfolding g_inner_def by (subst (asm) sum_nonneg_eq_0_iff) auto
  hence "?L = 0"
    unfolding g_step_altdef g_inner_def by simp 
  also have "... \<le> \<Lambda> * g_norm f^2"
    using False by simp
  finally show ?thesis by simp
qed


lemma expansionD:
  assumes "g_inner f (\<lambda>_. 1) = 0"
  shows "\<bar>\<Sum>a \<in> arcs G. f (head G a) * f (tail G a)\<bar> \<le> d * \<Lambda> * g_norm f^2"  (is "?L \<le> ?R")
proof -
  have "?L = \<bar>g_inner f (g_step f) * d\<bar>"
    unfolding g_inner_step_eq using d_gt_0 by simp
  also have "... \<le> \<bar>g_inner f (g_step f)\<bar> * d"
    by (simp add:abs_mult)
  also have "... \<le> (\<Lambda> * g_norm f^2) * d"
    by (intro expansionD1 mult_right_mono assms(1)) auto
  also have "... = ?R" by simp
  finally show ?thesis by simp
qed

end

lemma pre_expander_graphI:
  assumes "symmetric_multi_graph G"
  assumes "verts G \<noteq> {}" "d > 0"
  assumes "\<And>v. v \<in> verts G \<Longrightarrow> out_degree G v = d"
  shows "pre_expander_graph G"
proof -
  obtain v where v_def: "v \<in> verts G"
    using assms(2) by auto
  have "arcs G \<noteq> {}" 
  proof (rule ccontr)
    assume "\<not>arcs G \<noteq> {}"
    hence "arcs G = {}" by simp
    hence "out_degree G v = 0"
      unfolding out_degree_def out_arcs_def by simp
    hence "d = 0"
      using v_def assms(4) by simp
    thus False
      using assms(3) by simp
  qed

  thus ?thesis
    using assms symmetric_multi_graphD2[OF assms(1)]
    unfolding pre_expander_graph_def pre_expander_graph_axioms_def
    by simp
qed

lemma (in fin_digraph) symmetric_graph_iso:
  assumes "digraph_iso G H"
  assumes "symmetric_multi_graph G"
  shows "symmetric_multi_graph H"
proof -
  obtain h where hom_iso: "digraph_isomorphism h" and H_alt: "H = app_iso h G"
    using assms unfolding digraph_iso_def by auto

  have 0:"fin_digraph H"
    unfolding H_alt
    by (intro fin_digraphI_app_iso hom_iso)

  interpret H:fin_digraph H
    using 0 by auto

  have 1:"arcs_betw H (iso_verts h v) (iso_verts h w) = iso_arcs h ` arcs_betw G v w"
    (is "?L = ?R") if "v \<in> verts G" "w \<in> verts G" for v w
  proof -
    have "?L = {a \<in> iso_arcs h ` arcs G. iso_head h a=iso_verts h w \<and> iso_tail h a=iso_verts h v}"
      unfolding arcs_betw_def H_alt arcs_app_iso head_app_iso tail_app_iso by simp
    also have "... = {a. (\<exists>b \<in> arcs G. a = iso_arcs h b \<and> iso_verts h (head G b) = iso_verts h w \<and> 
      iso_verts h (tail G b) = iso_verts h v)}"
      using iso_verts_head[OF hom_iso] iso_verts_tail[OF hom_iso] by auto
    also have "... = {a. (\<exists>b \<in> arcs G. a = iso_arcs h b \<and> head G b = w \<and> tail G b = v)}" 
      using that iso_verts_eq_iff[OF hom_iso] by auto
    also have "... = ?R"
      unfolding arcs_betw_def by (auto simp add:image_iff set_eq_iff)
    finally show ?thesis by simp
  qed

  have "card (arcs_betw H w v) = card (arcs_betw H v w)" (is "?L = ?R") 
    if v_range: "v \<in> verts H" and w_range: "w \<in> verts H" for v w
  proof -
    obtain v' where v': "v = iso_verts h v'" "v' \<in> verts G"
      using that v_range verts_app_iso unfolding H_alt by auto
    obtain w' where w': "w = iso_verts h w'" "w' \<in> verts G"
      using that w_range verts_app_iso unfolding H_alt by auto
    have "?L = card (arcs_betw H (iso_verts h w') (iso_verts h v'))"
      unfolding v' w' by simp
    also have "... = card (iso_arcs h ` arcs_betw G w' v')"
      by (intro arg_cong[where f="card"] 1 v' w')
    also have "... = card (arcs_betw G w' v')"
      using iso_arcs_eq_iff[OF hom_iso] unfolding arcs_betw_def
      by (intro card_image inj_onI) auto
    also have "... = card (arcs_betw G v' w')"
      by (intro symmetric_multi_graphD4 assms(2)) 
    also have "... = card (iso_arcs h ` arcs_betw G v' w')"
      using iso_arcs_eq_iff[OF hom_iso] unfolding arcs_betw_def
      by (intro card_image[symmetric] inj_onI) auto
    also have "... = card (arcs_betw H (iso_verts h v') (iso_verts h w'))"
      by (intro arg_cong[where f="card"] 1[symmetric] v' w')
    also have "... = ?R"
      unfolding v' w' by simp
    finally show ?thesis by simp
  qed

  thus ?thesis
    using 0 unfolding symmetric_multi_graph_def by auto
qed

lemma (in pre_expander_graph)
  assumes "digraph_iso G H"
  shows pre_expander_graph_iso: "pre_expander_graph H" 
    and pre_expander_graph_iso_degree: "pre_expander_graph.d H = d"
    and pre_expander_graph_iso_expansion_le:  "pre_expander_graph.\<Lambda> H \<le> \<Lambda>"
proof -
  obtain h where hom_iso: "digraph_isomorphism h" and H_alt: "H = app_iso h G"
    using assms unfolding digraph_iso_def by auto

  have 0:"symmetric_multi_graph H"
    by (intro symmetric_graph_iso[OF assms(1)] sym)

  have 1:"verts H \<noteq> {}" 
    unfolding H_alt verts_app_iso using verts_non_empty by simp

  then obtain h_wit where h_wit: "h_wit \<in> verts H"
    by auto

  have 3:"out_degree H v = d" if v_range: "v \<in> verts H" for v
  proof -
    obtain v' where v': "v = iso_verts h v'" "v' \<in> verts G"
      using that v_range verts_app_iso unfolding H_alt by auto
    have "out_degree H v = out_degree G v'"
      unfolding v' H_alt by (intro out_degree_app_iso_eq[OF hom_iso] v')
    also have "... = d"
      by (intro reg v')
    finally  show ?thesis by simp
  qed

  thus 2:"pre_expander_graph H"
    by (intro pre_expander_graphI[where d="d"] 0 d_gt_0 1) auto
  interpret H:"pre_expander_graph" H
    using 2 by auto

  have "H.d = out_degree H h_wit"
    by (intro H.reg[symmetric] h_wit)
  also have "... = d"
    by (intro 3 h_wit)
  finally show 4:"H.d = d" by simp

  have "bij_betw (iso_verts h) (verts G) (verts H)" 
    unfolding H_alt using hom_iso 
    by (simp add: bij_betw_def digraph_isomorphism_inj_on_verts)

  hence g_inner_conv: 
    "g_inner (\<lambda>x. f (iso_verts h x)) (\<lambda>x. g (iso_verts h x)) = H.g_inner f g" for f g
    unfolding g_inner_def H.g_inner_def by (intro sum.reindex_bij_betw)

  have "\<bar>\<Sum>a\<in>arcs H. f (head H a) * f (tail H a)\<bar> \<le> \<Lambda> * real d * (H.g_norm f)\<^sup>2" (is "?L \<le> ?R")
    if "H.g_inner f (\<lambda>_. 1) = 0" for f
  proof -
    have "g_inner (\<lambda>x. f (iso_verts h x)) (\<lambda>_. 1) = H.g_inner f (\<lambda>_. 1)"
      by (intro g_inner_conv)
    also have "... = 0" using that by simp
    finally have 5:"g_inner (\<lambda>x. f (iso_verts h x)) (\<lambda>_. 1) = 0" by simp


    have "?L = \<bar>\<Sum>a\<in>iso_arcs h ` arcs G. f (head H a) * f (tail H a)\<bar>"
      unfolding H_alt arcs_app_iso by simp
    also have "... = \<bar>\<Sum>a\<in>arcs G. f (head H (iso_arcs h a)) * f (tail H (iso_arcs h a))\<bar>"
      using iso_arcs_eq_iff[OF hom_iso]
      by (intro arg_cong[where f="abs"] sum.reindex_cong[where l="iso_arcs h"] inj_onI) auto
    also have "... = \<bar>\<Sum>a\<in>arcs G. f (iso_verts h (head G a)) * f (iso_verts h (tail G a))\<bar>"
      unfolding H_alt head_app_iso tail_app_iso using iso_verts_head[OF hom_iso]
      using  iso_verts_tail[OF hom_iso] by (intro arg_cong[where f="abs"] sum.cong) auto
    also have "... \<le> real d * \<Lambda> * (g_norm (\<lambda>x. f (iso_verts h x)))\<^sup>2"
      by (intro expansionD 5)
    also have "...  =real d * \<Lambda> * (H.g_norm f)^2"
      unfolding g_norm_sq H.g_norm_sq g_inner_conv by simp
    also have "... = ?R" by simp
    finally show ?thesis by simp
  qed

  hence "H.\<Lambda> \<le> \<Lambda> * d/H.d"
    by (intro H.expander_intro mult_nonneg_nonneg \<Lambda>_ge_0) auto
  also have "... = \<Lambda>"
    unfolding 4 using d_gt_0 by simp
  finally show "H.\<Lambda> \<le> \<Lambda>"
    by simp
qed

lemma (in pre_expander_graph)
  assumes "digraph_iso G H"
  shows pre_expander_graph_iso_expansion: "pre_expander_graph.\<Lambda> H = \<Lambda>"
proof -
  interpret H:"pre_expander_graph" "H"
    by (intro pre_expander_graph_iso assms)

  have "digraph_iso H G"
    using digraph_iso_swap assms wf_digraph_axioms by blast

  hence "\<Lambda> \<le> H.\<Lambda>"
    by (intro H.pre_expander_graph_iso_expansion_le)
  moreover have "H.\<Lambda> \<le> \<Lambda>"
    using pre_expander_graph_iso_expansion_le[OF assms] by auto
  ultimately show "H.\<Lambda> = \<Lambda>"
    by auto
qed

unbundle no_intro_cong_syntax

end