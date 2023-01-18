theory Margulis_Gaber_Galil
  imports 
    "Graph_Theory.Digraph"
    "HOL-Analysis.Complex_Transcendental"
begin

definition "locally_finite_graph G = 
  (wf_digraph G \<and> (\<forall>v \<in> verts G. finite (in_arcs G v) \<and> finite (out_arcs G v)))"

lemma locally_finite_graphD:
  assumes "locally_finite_graph G"
  assumes "v \<in> verts G" 
  shows "finite (in_arcs G v)" " finite (out_arcs G v)"
  using assms unfolding locally_finite_graph_def by auto

lemma finite_imp_locally_finite:
  assumes "fin_digraph G"
  shows "locally_finite_graph G"
proof -
  have a:"finite (arcs G)" "wf_digraph G" 
    using assms unfolding fin_digraph_def fin_digraph_axioms_def by auto
  have "finite (in_arcs G v)" "finite (out_arcs G v)" for v
    using a(1) unfolding in_arcs_def out_arcs_def finite_subset by auto
  thus ?thesis
    using a(2) unfolding locally_finite_graph_def by auto
qed

text \<open>The following is a stronger notion than classic symmetry for multi-graphs, where the number
of edges from @{term "v"} to @{term "w"} must be equal to the number of edges from @{term "w"} to 
@{term "v"} for any pair of vertices @{term "v"} @{term "w \<in> verts G"}.\<close>

definition "symmetric_multi_graph G =
  (locally_finite_graph G \<and> (\<forall>v w. {v, w} \<subseteq> verts G \<longrightarrow> 
    card {e \<in> arcs G. head G e=v \<and> tail G e=w} = card {e \<in> arcs G. head G e=w \<and> tail G e=v}))"

lemma symmetric_multi_graphI:
  assumes "locally_finite_graph G"
  assumes "bij_betw f (arcs G) (arcs G)"
  assumes "\<And>e. e \<in> arcs G \<Longrightarrow> head G (f e) = tail G e \<and> tail G (f e) = head G e"
  shows "symmetric_multi_graph G"
proof -
  have "card {e \<in> arcs G. head G e=v \<and> tail G e=w} = card {e \<in> arcs G. head G e=w \<and> tail G e=v}"
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
      by (intro card_image[symmetric])
    also have "... = ?R"
      using a b assms(3)
      by (intro arg_cong[where f="card"] order_antisym image_subsetI subsetI) fastforce+ 
    finally show ?thesis by simp
  qed
  thus ?thesis 
    using assms(1) unfolding symmetric_multi_graph_def by simp
qed

lemma symmetric_multi_graphD:
  assumes "symmetric_multi_graph G" "v \<in> verts G" "w \<in> verts G"
  shows "card {e \<in> arcs G. head G e=v \<and> tail G e=w} = card {e \<in> arcs G. head G e=w \<and> tail G e=v}"
  using assms unfolding symmetric_multi_graph_def by simp 

locale regular_graph = wf_digraph +
  fixes d :: nat
  assumes lf: "locally_finite_graph G"
  assumes reg: "\<And>v. v \<in> verts G \<Longrightarrow> in_degree G v = d \<and> out_degree G v = d"
begin

lemma regD: 
  assumes "v \<in> verts G"
  shows "out_degree G v = d" "in_degree G v = d"
  using reg assms by auto

definition g_inner :: "('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> real" 
  where "g_inner f g = (\<Sum>x \<in> verts G. (f x) * (g x))"

definition "g_norm f = sqrt (g_inner f f)"


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

text \<open>Numerical radius - maximum absolute value of the rayleigh quotient of vectors orthogonal
to the one vector (corresponding to the stationary distribution).\<close>

definition 
  "numerical_rad = (Sup {\<bar>g_inner x (g_step x)\<bar> | x. g_norm x \<le> 1 \<and> g_inner x (\<lambda>_. 1) = 0})"

text \<open>Spectral radius - maximum norm of  value of the rayleigh quotient\<close>

definition 
  "spectral_rad = (Sup {\<bar>g_norm (g_step x)\<bar> | x. g_norm x \<le> 1 \<and> g_inner x (\<lambda>_. 1) = 0})"

text \<open>For finite symmetric multi-graphs the concepts of spectral and numerical radius are equivalent.\<close>

lemma inner_step_eq:
  assumes "fin_digraph G"
  shows "g_inner f (g_step f) = (\<Sum>a \<in> arcs G. f (head G a) * f (tail G a)) / d" (is "?L = ?R")
proof -
  have "?L = (\<Sum>v\<in>verts G. f v * (\<Sum>a\<in>in_arcs G v. f (tail G a) / out_degree G (tail G a)))"
    unfolding g_inner_def g_step_def by simp
  also have "... = (\<Sum>v\<in>verts G. f v * (\<Sum>a\<in>in_arcs G v. f (tail G a) / d))"
    unfolding in_arcs_def using regD 
    by (intro sum.cong arg_cong2[where f="(*)"] wellformed refl) simp
  also have "... = (\<Sum>v\<in>verts G. (\<Sum>a\<in>in_arcs G v. f v * f (tail G a) / d))"
    by (subst sum_distrib_left) simp
  also have "... =  (\<Sum>v\<in>verts G. (\<Sum>a\<in>in_arcs G v. f (head G a) * f (tail G a) / d))"
    unfolding in_arcs_def by (intro sum.cong refl) simp
  also have "... = (\<Sum>a \<in> (\<Union> (in_arcs G ` verts G)). f (head G a) * f (tail G a) / d)"
    using fin_digraph.finite_verts[OF assms]
    by (intro sum.UNION_disjoint[symmetric] ballI locally_finite_graphD lf) 
      (auto simp add:in_arcs_def)
  also have "... = (\<Sum>a \<in> arcs G. f (head G a) * f (tail G a) / d)"
    unfolding in_arcs_def using wellformed by (intro sum.cong) auto
  also have "... = ?R"
    by (intro sum_divide_distrib[symmetric])
  finally show ?thesis by simp
qed

lemma numerical_radI:
  assumes "fin_digraph G" "C \<ge> 0"
  assumes "\<And>f. g_inner f (\<lambda>_. 1)=0 \<Longrightarrow> \<bar>\<Sum>a \<in> arcs G. f(head G a) * f(tail G a)\<bar> \<le> C*g_norm f^2" 
  shows "numerical_rad \<le> C/d"
proof -
  have "\<exists>x. g_norm x \<le> 1 \<and> g_inner x (\<lambda>_. 1) = 0"
    unfolding g_norm_def g_inner_def
    by (intro exI[where x="\<lambda>_. 0"], simp)
  moreover have "\<bar>g_inner f (g_step f)\<bar> \<le> C /d" if "g_norm f \<le> 1" "g_inner f (\<lambda>_. 1) = 0" for f 
  proof -
    have "\<bar>g_inner f (g_step f)\<bar> = \<bar>(\<Sum>a \<in> arcs G. f (head G a) * f (tail G a))\<bar>/d"
      unfolding inner_step_eq[OF assms(1)] by simp
    also have "... \<le> C * g_norm f^2 /d"
      by (intro divide_right_mono assms(3) that(2)) simp
    also have "... \<le> C * 1^2 / d"
      by (intro divide_right_mono mult_left_mono power_mono that(1) g_norm_nonneg assms(2)) simp
    also have "... = C/d" by simp
    finally show ?thesis by simp
  qed
  ultimately show ?thesis
    unfolding numerical_rad_def
    by (intro cSup_least) auto
qed

lemma spectral_eq_numerical_radius:
  assumes "symmetric_multi_graph G" "fin_digraph G"
  shows "spectral_rad = numerical_rad"
  sorry


end

lemma symmetric_degree_eq:
  assumes "symmetric_multi_graph G"
  assumes "v \<in> verts G"
  shows "out_degree G v = in_degree G v" (is "?L = ?R")
proof -
  have lf: "locally_finite_graph G" 
    using assms(1) unfolding symmetric_multi_graph_def by simp

  interpret wf_digraph "G" 
    using lf locally_finite_graph_def by auto

  have a: "finite {e \<in> arcs G. head G e = v \<and> tail G e = w}" (is "finite ?X") for v w 
  proof (cases "v \<in> verts G")
    case True
    hence "?X \<subseteq> in_arcs G v"
      unfolding in_arcs_def by auto
    then show ?thesis 
      using finite_subset locally_finite_graphD(1)[OF lf True] by blast
  next
    case False
    hence "?X \<subseteq> {}"
      using wellformed by (intro subsetI) auto
    then show ?thesis 
      using finite_subset by blast
  qed

  let ?N = "tail G ` in_arcs G v \<union> head G ` out_arcs G v"

  have b:"finite ?N" 
    using lf assms(2) unfolding locally_finite_graph_def
    by (intro finite_UnI finite_imageI) auto

  have c: "?N \<subseteq> verts G"
    by (intro Un_least image_subsetI wellformed)
    (auto simp add:in_arcs_def out_arcs_def)

  have "?L = card {e \<in> arcs G. tail G e = v}"
    unfolding out_degree_def out_arcs_def by simp
  also have "... = card (\<Union>w \<in> ?N. {e \<in> arcs G. head G e = w \<and> tail G e = v})"
    using wellformed 
    by (intro arg_cong[where f="card"]) (auto simp add:set_eq_iff)
  also have "... = (\<Sum>w \<in> ?N. card {e \<in> arcs G. head G e = w \<and> tail G e = v})"
    by (intro card_UN_disjoint ballI b a) auto
  also have "... = (\<Sum>w \<in> ?N. card {e \<in> arcs G. head G e = v \<and> tail G e = w})"
    using c by (intro sum.cong refl symmetric_multi_graphD[symmetric] assms(1,2)) auto
  also have "... = card (\<Union>w \<in> ?N. {e \<in> arcs G. head G e = v \<and> tail G e = w})"
    by (intro card_UN_disjoint[symmetric] ballI a b) auto
  also have "... = card (in_arcs G v)"
    using wellformed 
    by (intro arg_cong[where f="card"]) (auto simp add:set_eq_iff) 
  also have "... = ?R" 
    unfolding in_degree_def by simp
  finally show ?thesis by simp
qed


lemma regular_symmetric_graphI:
  assumes "symmetric_multi_graph G"
  assumes "\<And>v. v \<in> verts G \<Longrightarrow> out_degree G v = d"
  shows "regular_graph G d"
  using symmetric_degree_eq[OF assms(1)] assms
  unfolding regular_graph_def regular_graph_axioms_def symmetric_multi_graph_def
    locally_finite_graph_def by simp

(*
  MGG
*)

datatype ('a, 'b) arc = Arc (arc_tail: 'a)  (arc_head: 'a) (arc_label: 'b)  

fun mgg_graph_step :: "nat \<Rightarrow> (int \<times> int) \<Rightarrow> (nat \<times> int) \<Rightarrow> (int \<times> int)"
  where "mgg_graph_step n (i,j) (l,\<sigma>) = 
  [ ((i+\<sigma>*(2*j+0)) mod int n, j), (i, (j+\<sigma>*(2*i+0)) mod int n)
  , ((i+\<sigma>*(2*j+1)) mod int n, j), (i, (j+\<sigma>*(2*i+1)) mod int n) ] ! l"

definition mgg_graph :: "nat \<Rightarrow> (int \<times> int, (int \<times> int, nat \<times> int) arc) pre_digraph" where 
  "mgg_graph n =
    \<lparr> verts = {0..<n} \<times> {0..<n}, 
      arcs = (\<lambda>(t,l). (Arc t (mgg_graph_step n t l) l))`(({0..<int n}\<times>{0..<int n})\<times>({..<4}\<times>{-1,1})), 
      tail = arc_tail,
      head = arc_head \<rparr>"


locale margulis_gaber_galil =
  fixes n :: nat
  assumes n_gt_0: "n > 0"
begin

abbreviation G where "G \<equiv> mgg_graph n"

lemma wf_digraph: "wf_digraph (mgg_graph n)"
proof -
  have 
    "tail (mgg_graph n) e \<in> verts (mgg_graph n)" (is "?A") 
    "head (mgg_graph n) e \<in> verts (mgg_graph n)" (is "?B")
    if a:"e \<in> arcs (mgg_graph n)" for e
  proof -
    obtain t l \<sigma> where tl_def: 
      "t \<in> {0..<int n} \<times> {0..<int n}" "l \<in> {..<4}" "\<sigma> \<in> {-1,1}" 
      "e = Arc t (mgg_graph_step n t (l,\<sigma>)) (l,\<sigma>)"
      using a mgg_graph_def by auto 
    thus ?A
      unfolding mgg_graph_def by auto
    have "mgg_graph_step n (fst t, snd t) (l,\<sigma>) \<in> {0..<int n} \<times> {0..<int n}" 
      unfolding mgg_graph_step.simps using tl_def(1,2) n_gt_0
      by (intro set_mp[OF _ nth_mem])  auto
    hence "arc_head e \<in> {0..<int n} \<times> {0..<int n}" 
      unfolding tl_def(4) by simp
    thus ?B
      unfolding mgg_graph_def by simp
  qed
  thus ?thesis
    by unfold_locales auto
qed

lemma mgg_finite: "fin_digraph (mgg_graph n)"
proof -
  have "finite (verts (mgg_graph n))" "finite (arcs (mgg_graph n))"
    unfolding mgg_graph_def by auto
  thus ?thesis
    using wf_digraph
    unfolding fin_digraph_def fin_digraph_axioms_def by auto
qed

interpretation fin_digraph "mgg_graph n"
  using mgg_finite by simp

lemma locally_finite: "locally_finite_graph (mgg_graph n)" 
  by (intro finite_imp_locally_finite mgg_finite)

definition arcs_pos :: "(int \<times> int, nat \<times> int) arc set" 
    where "arcs_pos = (\<lambda>(t,l). (Arc t (mgg_graph_step n t (l,1)) (l, 1)))`(verts G\<times>{..<4})"
definition arcs_neg :: "(int \<times> int, nat \<times> int) arc set" 
    where "arcs_neg = (\<lambda>(h,l). (Arc (mgg_graph_step n h (l,1)) h (l,-1)))`(verts G\<times>{..<4})"

lemma arcs_sym:
  "arcs G = arcs_pos \<union> arcs_neg"
proof -
  have 0: "x \<in> arcs G" if "x \<in> arcs_pos" for x 
    using that unfolding arcs_pos_def mgg_graph_def by auto 
  have 1: "a \<in> arcs G" if t:"a \<in> arcs_neg" for a 
  proof -
    obtain h l where hl_def: "h \<in> verts G" "l \<in> {..<4}" "a = Arc (mgg_graph_step n h (l,1)) h (l,-1)"
      using t unfolding arcs_neg_def by auto

    define t where "t = mgg_graph_step n h (l,1)"

    have h_ran: "h \<in> {0..<int n} \<times> {0..<int n}" 
      using hl_def(1) unfolding mgg_graph_def by simp
    have l_ran: "l \<in> set [0,1,2,3]" 
      using hl_def(2) by auto

    have "t \<in> {0..<int n} \<times> {0..<int n}" 
      using h_ran l_ran
      unfolding t_def by (cases h, auto simp add:mod_simps)
    hence t_ran: "t \<in> verts G" 
      unfolding mgg_graph_def by simp

    have "h = mgg_graph_step n t (l,-1)" 
      using h_ran l_ran unfolding t_def by (cases h, auto simp add:mod_simps)
    hence "a = Arc t (mgg_graph_step n t (l,-1)) (l,-1)"
      unfolding t_def hl_def(3) by simp
    thus ?thesis 
      using t_ran hl_def(2) mgg_graph_def by (simp add:image_iff)
  qed

  have "card (arcs_pos \<union> arcs_neg) = card arcs_pos + card arcs_neg"
    unfolding arcs_pos_def arcs_neg_def by (intro card_Un_disjoint finite_imageI) auto
  also have "... = card (verts G\<times>{..<4::nat}) + card (verts G\<times>{..<4::nat})"
    unfolding arcs_pos_def arcs_neg_def
    by (intro arg_cong2[where f="(+)"] card_image inj_onI) auto
  also have "... = card (verts G\<times>{..<4::nat}\<times>{-1,1::int})"
    by simp
  also have "... = card ((\<lambda>(t, l). Arc t (mgg_graph_step n t l) l) ` (verts G \<times>{..<4}\<times>{-1,1}))"
    by (intro card_image[symmetric] inj_onI) auto
  also have "... = card (arcs G)"
    unfolding mgg_graph_def by simp
  finally have "card (arcs_pos \<union> arcs_neg) = card (arcs G)" 
    by simp
  hence "arcs_pos \<union> arcs_neg = arcs G"
    using 0 1 by (intro card_subset_eq, auto) 
  thus ?thesis by simp
qed

lemma sym: "symmetric_multi_graph (mgg_graph n)"
proof -
  define f :: "(int \<times> int, nat \<times> int) arc \<Rightarrow> (int \<times> int, nat \<times> int) arc"  
    where "f a = Arc (arc_head a) (arc_tail a) (apsnd (\<lambda>x. (-1) * x) (arc_label a))" for a 

  have a: "bij_betw f arcs_pos arcs_neg"
    by (intro bij_betwI[where g="f"])
     (auto simp add:f_def image_iff arcs_pos_def arcs_neg_def)

  have b: "bij_betw f arcs_neg arcs_pos"
    by (intro bij_betwI[where g="f"])
     (auto simp add:f_def image_iff  arcs_pos_def arcs_neg_def)

  have c:"bij_betw f (arcs_pos \<union> arcs_neg) (arcs_neg \<union> arcs_pos)"
    by (intro bij_betw_combine[OF a b])  (auto simp add:arcs_pos_def arcs_neg_def)

  hence c:"bij_betw f (arcs G) (arcs G)"
    unfolding arcs_sym by (subst (2) sup_commute, simp)
  show ?thesis
    by (intro symmetric_multi_graphI[where f="f"] c locally_finite) 
      (simp add:f_def mgg_graph_def)
qed

sublocale regular_graph "mgg_graph n" "8"
proof -
  have "out_degree (mgg_graph n) v = 8" if "v \<in> verts (mgg_graph n)" for v
  proof -
    have "out_degree (mgg_graph n) v = card (out_arcs (mgg_graph n) v)"
      unfolding out_degree_def by simp
    also have "... = card {e. (\<exists>w \<in> verts (mgg_graph n). \<exists>l \<in> {..<4} \<times> {-1,1}. 
      e = Arc w (mgg_graph_step n w l) l \<and> arc_tail e = v)}" 
      unfolding mgg_graph_def out_arcs_def by (simp add:image_iff)
    also have "... = card {e. (\<exists>l \<in> {..<4} \<times> {-1,1}. e = Arc v (mgg_graph_step n v l) l)}"
      using that by (intro arg_cong[where f="card"] iffD2[OF set_eq_iff] allI)  auto
    also have "... = card ((\<lambda>l. Arc v (mgg_graph_step n v l) l) ` ({..<4} \<times> {-1,1}))"
      by (intro arg_cong[where f="card"]) (auto simp add:image_iff)
    also have "... = card ({..<4::nat} \<times> {-1,1::int})"
      by (intro card_image inj_onI) simp
    also have "... = 8" by simp
    finally show ?thesis by simp
  qed
  thus "regular_graph (mgg_graph n) 8"
    by (intro regular_symmetric_graphI sym)
qed

definition c_inner :: "(int \<times> int \<Rightarrow> complex) \<Rightarrow> (int \<times> int \<Rightarrow> complex) \<Rightarrow> complex"
  where "c_inner f g = (\<Sum>v \<in> verts G. f v * cnj (g v))" 

lemma c_inner_simps:
  "c_inner (\<lambda>x. 0) g = 0" 
  "c_inner f (\<lambda>x. 0) = 0" 
  "c_inner (\<lambda>x. c * f x) g = c * c_inner f g" 
  "c_inner f (\<lambda>x. c * g x) = cnj c * c_inner f g" 
  "c_inner (\<lambda>x. f x + g x) h = c_inner f h + c_inner g h" 
  "c_inner f (\<lambda>x. g x + h x) = c_inner f g + c_inner f h" 
  "c_inner f (\<lambda>x. g x / c) = c_inner f g / cnj c" 
  "c_inner (\<lambda>x. f x / c) g = c_inner f g / c" 
  unfolding c_inner_def 
  by (auto simp add:sum.distrib algebra_simps sum_distrib_left sum_divide_distrib)

lemma c_inner_sum_left:
  assumes "finite I"
  shows "c_inner (\<lambda>x. (\<Sum>i \<in> I. f i x)) g = (\<Sum>i\<in> I. c_inner (f i) g)"
  using assms by (induction I rule:finite_induct) (auto simp add:c_inner_simps)

lemma c_inner_sum_right:
  assumes "finite I"
  shows "c_inner f (\<lambda>x. (\<Sum>i \<in> I. g i x)) = (\<Sum>i\<in> I. c_inner f (g i))"
  using assms by (induction I rule:finite_induct) (auto simp add:c_inner_simps)

lemma c_inner_reindex:
  assumes "bij_betw h (verts G) (verts G)"
  shows "c_inner f g = c_inner (\<lambda>x. (f (h x))) (\<lambda>x. (g (h x)))"
  unfolding c_inner_def
  by (subst sum.reindex_bij_betw[OF assms,symmetric]) simp

lemma c_inner_self:
  "c_inner f f = (\<Sum>v \<in> verts G. norm (f v)^2)"
  unfolding c_inner_def using complex_norm_square by simp 

lemma c_inner_cong:
  assumes "\<And>x. x \<in> verts G \<Longrightarrow> f1 x = f2 x"
  assumes "\<And>x. x \<in> verts G \<Longrightarrow> g1 x = g2 x"
  shows "c_inner f1 g1 = c_inner f2 g2"
  unfolding c_inner_def using assms by (intro sum.cong) auto

definition \<omega>\<^sub>F :: "real \<Rightarrow> complex" where "\<omega>\<^sub>F x = cis (2*pi*x/n)"

lemma \<omega>\<^sub>F_simps:
  "\<omega>\<^sub>F (x + y) = \<omega>\<^sub>F x * \<omega>\<^sub>F y"
  "\<omega>\<^sub>F (x - y) = \<omega>\<^sub>F x * \<omega>\<^sub>F (-y)"
  "cnj (\<omega>\<^sub>F x) = \<omega>\<^sub>F (-x)"
  unfolding \<omega>\<^sub>F_def by (auto simp add:algebra_simps diff_divide_distrib 
      add_divide_distrib cis_mult cis_divide cis_cnj)

lemma \<omega>\<^sub>F_cong:
  fixes x y :: int
  assumes "x mod n = y mod n" 
  shows "\<omega>\<^sub>F (of_int x) = \<omega>\<^sub>F (of_int y)"
proof -
  obtain z :: int where "y = x + n*z" using mod_eqE[OF assms] by auto
  hence "\<omega>\<^sub>F (of_int y) = \<omega>\<^sub>F (of_int x + of_int (n*z))"
    by simp
  also have "... = \<omega>\<^sub>F (of_int x) * \<omega>\<^sub>F (of_int (n*z))"
    by (simp add:\<omega>\<^sub>F_simps)
  also have "... = \<omega>\<^sub>F (of_int x) * cis (2 * pi * of_int (z))"
    unfolding \<omega>\<^sub>F_def  using n_gt_0 
    by (intro arg_cong2[where f="(*)"] arg_cong[where f="cis"]) auto
  also have "... = \<omega>\<^sub>F (of_int x) * 1"
    by (intro arg_cong2[where f="(*)"] cis_multiple_2pi) auto
  finally show ?thesis by simp
qed

lemma cis_eq_1_imp:
  assumes "cis (2 * pi * x) = 1"
  shows "x \<in> \<int>"
proof -
  have "cos (2 * pi * x) = Re (cis (2*pi*x))" 
    using cis.simps by simp
  also have "... = 1" 
    unfolding assms by simp
  finally have "cos (2 * pi * x) = 1" by simp
  then obtain y where "2 * pi * x = of_int y * 2 * pi"
    using cos_one_2pi_int by auto
  hence "y = x" by simp
  thus ?thesis by auto
qed

lemma \<omega>\<^sub>F_eq_1_iff:
  fixes x :: int
  shows "\<omega>\<^sub>F x = 1 \<longleftrightarrow> x mod n = 0"
proof
  assume "\<omega>\<^sub>F (real_of_int x) = 1"
  hence "cis (2 * pi * real_of_int x / real n) = 1"
    unfolding \<omega>\<^sub>F_def by simp
  hence "real_of_int x / real n \<in> \<int>"
    using cis_eq_1_imp by simp
  then obtain z :: int where "of_int x / real n = z"
    using Ints_cases by auto
  hence "x = z * real n"
    using n_gt_0 by (simp add: nonzero_divide_eq_eq)
  hence "x = z * n" using of_int_eq_iff by fastforce
  thus "x mod n = 0" by simp
next
  assume "x mod n = 0"
  hence "\<omega>\<^sub>F x = \<omega>\<^sub>F (of_int 0)"
    by (intro \<omega>\<^sub>F_cong) auto
  also have "... = 1" unfolding \<omega>\<^sub>F_def by simp
  finally show "\<omega>\<^sub>F x= 1" by simp
qed

definition FT :: "(int \<times> int \<Rightarrow> complex) \<Rightarrow> (int \<times> int \<Rightarrow> complex)"
  where "FT f v = c_inner f (\<lambda>x. \<omega>\<^sub>F (fst x * fst v + snd x * snd v))"

lemma FT_altdef: "FT f (u,v) = c_inner f (\<lambda>x. \<omega>\<^sub>F (fst x * u + snd x * v))"
  unfolding FT_def by (simp add:case_prod_beta)

lemma FT_add: "FT (\<lambda>x. f x + g x) v = FT f v + FT g v"
  unfolding FT_def by (simp add:c_inner_simps algebra_simps)

lemma FT_zero: "FT (\<lambda>x. 0) v = 0"
  unfolding FT_def c_inner_def by simp

lemma FT_sum: 
  assumes "finite I" 
  shows "FT (\<lambda>x. (\<Sum>i \<in> I. f i x)) v = (\<Sum>i \<in> I. FT (f i) v)"
  using assms by (induction rule: finite_induct, auto simp add:FT_zero FT_add)

lemma FT_scale: "FT (\<lambda>x. c * f x) v = c * FT f v"
  unfolding FT_def by (simp add: c_inner_simps)

lemma FT_cong:
  assumes "\<And>x. x \<in> verts G \<Longrightarrow> f x = g x"
  shows "FT f = FT g"
  unfolding FT_def by (intro ext c_inner_cong assms refl)

lemma parseval:
  "c_inner f g = c_inner (FT f) (FT g)/n^2" (is "?L = ?R")
proof -
  define \<delta> :: "(int \<times> int) \<Rightarrow> (int \<times> int) \<Rightarrow> complex" where "\<delta> x y = of_bool (x = y)" for x y

  have FT_\<delta>: "FT (\<delta> v) x = \<omega>\<^sub>F (-(fst v *fst x +snd v * snd x))" if "v \<in> verts G" for v x
    using that by (simp add:FT_def c_inner_def \<delta>_def \<omega>\<^sub>F_simps)

  have 1: "(\<Sum>x=0..<int n. \<omega>\<^sub>F (z*x)) = n * of_bool(z mod n = 0)" (is "?L1 = ?R1") for z :: int
  proof (cases "z mod n = 0")
    case True
    have "(\<Sum>x=0..<int n. \<omega>\<^sub>F (z*x)) = (\<Sum>x=0..<int n. \<omega>\<^sub>F (of_int 0))"
      using True by (intro sum.cong \<omega>\<^sub>F_cong refl) auto
    also have "... = n * of_bool(z mod n = 0)"
      unfolding \<omega>\<^sub>F_def True by simp
    finally show ?thesis by simp
  next
    case False
    have "(1-\<omega>\<^sub>F z) * ?L1 = (1-\<omega>\<^sub>F z) * (\<Sum>x \<in> int ` {..<n}. \<omega>\<^sub>F(z*x))"
      by (intro arg_cong2[where f="(*)"] sum.cong refl)
       (simp add: image_atLeastZeroLessThan_int)
    also have "... = (\<Sum>x<n. \<omega>\<^sub>F(z*real x) - \<omega>\<^sub>F(z*(real (Suc x))))"
      by (subst sum.reindex, auto simp add:algebra_simps sum_distrib_left \<omega>\<^sub>F_simps)
    also have "... = \<omega>\<^sub>F(z * 0) -\<omega>\<^sub>F (z*n)"
      by (subst sum_lessThan_telescope') simp
    also have "... = \<omega>\<^sub>F (of_int 0) - \<omega>\<^sub>F (of_int 0)"
      by (intro arg_cong2[where f="(-)"] \<omega>\<^sub>F_cong) auto
    also have "... = 0"
      by simp
    finally have "(1- \<omega>\<^sub>F z) * ?L1 = 0" by simp
    moreover have "\<omega>\<^sub>F z \<noteq> 1" using \<omega>\<^sub>F_eq_1_iff False by simp
    hence "(1- \<omega>\<^sub>F z) \<noteq> 0" by simp
    ultimately have "?L1 = 0" by simp
    then show ?thesis using False by simp
  qed

  have 0:"c_inner (\<delta> v) (\<delta> w) = c_inner (FT (\<delta> v)) (FT (\<delta> w))/n^2" (is "?L1 = ?R1/_")
    if "v \<in> verts G" "w \<in> verts G" for v w
  proof -
    have "?R1=c_inner(\<lambda>x. \<omega>\<^sub>F(-(fst v *fst x +snd v * snd x)))(\<lambda>x. \<omega>\<^sub>F(-(fst w *fst x +snd w * snd x)))"
      using that by (intro c_inner_cong, auto simp add:FT_\<delta>)
    also have "...=(\<Sum>(x,y)\<in>{0..<int n}\<times>{0..<int n}. \<omega>\<^sub>F((fst w-fst v)*x)*\<omega>\<^sub>F((snd w - snd v)* y))"
      unfolding mgg_graph_def c_inner_def by (simp add:\<omega>\<^sub>F_simps algebra_simps case_prod_beta)
    also have "...=(\<Sum>x=0..<int n. \<Sum>y = 0..<int n. \<omega>\<^sub>F((fst w - fst v)*x)*\<omega>\<^sub>F((snd w - snd v) * y))"
      by (subst sum.cartesian_product[symmetric]) simp
    also have "...=(\<Sum>x=0..<int n. \<omega>\<^sub>F((fst w - fst v)*x))*(\<Sum>y = 0..<int n. \<omega>\<^sub>F((snd w - snd v) * y))"
      by (subst sum.swap) (simp add:sum_distrib_left sum_distrib_right)
    also have "... = 
      of_nat (n* of_bool(fst v mod n = fst w mod n)) * 
      of_nat (n * of_bool(snd v mod n = snd w mod n))"
      unfolding 1 by (intro arg_cong2[where f="(*)"] arg_cong[where f="of_bool"] 
          arg_cong[where f="of_nat"] iffI refl) (algebra)+
    also have "... = n^2 * of_bool(v = w)"
      using that by (auto simp add:prod_eq_iff mgg_graph_def power2_eq_square)
    also have "... = n^2 * ?L1" 
      using that unfolding c_inner_def \<delta>_def by simp
    finally have "?R1 = n^2 * ?L1" by simp
    thus ?thesis using n_gt_0 by simp
  qed

  have "?L = c_inner (\<lambda>x. (\<Sum>v \<in> verts G. (f v) * \<delta> v x)) (\<lambda>x. (\<Sum>v \<in> verts G. (g v) * \<delta> v x))"
    unfolding \<delta>_def by (intro c_inner_cong) auto
  also have "... = (\<Sum>v\<in>verts G. (f v) * (\<Sum>w\<in>verts G. cnj (g w) * c_inner (\<delta> v) (\<delta> w)))"
    by (simp add:c_inner_simps c_inner_sum_left c_inner_sum_right)
  also have "... = (\<Sum>v\<in>verts G. (f v) * (\<Sum>w\<in>verts G. cnj (g w) * c_inner(FT (\<delta> v)) (FT (\<delta> w))))/n^2"
    by (simp add:0 sum_divide_distrib sum_distrib_left algebra_simps)
  also have "...=c_inner(\<lambda>x.(\<Sum>v\<in>verts G. (f v)*FT (\<delta> v) x))(\<lambda>x.(\<Sum>v\<in>verts G. (g v)*FT (\<delta> v) x))/n\<^sup>2"
    by (simp add:c_inner_simps c_inner_sum_left c_inner_sum_right)
  also have "...=c_inner(FT(\<lambda>x.(\<Sum>v\<in>verts G.(f v)*\<delta> v x)))(FT(\<lambda>x.(\<Sum>v\<in>verts G.(g v)*\<delta> v x)))/n\<^sup>2"
    by (intro c_inner_cong arg_cong2[where f="(/)"]) (simp_all add: FT_sum FT_scale)
  also have "... = c_inner (FT f) (FT g)/n^2 "
    unfolding \<delta>_def comp_def
    by (intro c_inner_cong arg_cong2[where f="(/)"] fun_cong[OF FT_cong]) auto
  finally show ?thesis by simp
qed

lemma plancharel:
  "(\<Sum>v \<in> verts G. norm (f v)^2) = (\<Sum>v \<in> verts G. norm (FT f v)^2)/n^2" (is "?L = ?R")
proof -
  have "complex_of_real ?L = c_inner f f"
    by (simp flip:of_real_power add:complex_norm_square c_inner_def algebra_simps)
  also have "... = c_inner (FT f) (FT f) / n^2"
    by (subst parseval) simp
  also have "... = complex_of_real ?R"
    by (simp flip:of_real_power add:complex_norm_square c_inner_def algebra_simps) simp
  finally have "complex_of_real ?L = complex_of_real ?R" by simp
  thus ?thesis 
    using of_real_eq_iff by blast
qed

lemma FT_swap:
  "FT (\<lambda>x. f (snd x, fst x)) (u,v) = FT f (v,u)"
proof -
  have 0:"bij_betw (\<lambda>(x::int \<times> int). (snd x, fst x)) (verts G) (verts G)"
    by (intro bij_betwI[where g="(\<lambda>(x::int \<times> int). (snd x, fst x))"])
     (auto simp add:mgg_graph_def)
  show ?thesis
    unfolding FT_def
    by (subst c_inner_reindex[OF 0]) (simp add:algebra_simps)
qed


lemma mod_add_mult_eq:
  fixes a x y :: int
  shows "(a + x * (y mod n)) mod n = (a+x*y) mod n"
  using mod_add_cong mod_mult_right_eq by blast

definition periodic where "periodic f = (\<forall>x y. f (x,y) = f (x mod int n, y mod int n))"

lemma periodicD:
  assumes "periodic f"
  shows "f (x,y) = f (x mod n, y mod n)"
  using assms unfolding periodic_def by simp

lemma periodic_comp:
  assumes "periodic f"
  shows "periodic (\<lambda>x. g (f x))"
  using assms unfolding periodic_def by simp

lemma periodic_cong:
  fixes x y u v :: int
  assumes "periodic f"
  assumes "x mod n = u mod n" "y mod n = v mod n" 
  shows "f (x,y) = f (u, v)"
  using periodicD[OF assms(1)] assms(2,3) by metis

lemma periodic_FT: "periodic (FT f)"
proof -
  have "FT f (x,y) = FT f (x mod n,y mod n)" for x y
    unfolding FT_altdef by (intro  arg_cong2[where f="c_inner"] \<omega>\<^sub>F_cong ext) 
     (auto simp add:mod_simps cong:mod_add_cong)
  thus ?thesis 
    unfolding periodic_def by simp
qed

lemma FT_sheer_aux:
  fixes u v c d :: int
  assumes "periodic f" 
  shows  "FT (\<lambda>x. f (fst x,snd x+c*fst x+d)) (u,v) = \<omega>\<^sub>F (d* v) * FT f (u-c* v,v)" 
    (is "?L = ?R")
proof -
  define s where "s = (\<lambda>(x,y). (x, (y - c * x-d) mod n))"
  define s0 where "s0 = (\<lambda>(x,y). (x, (y-c*x) mod n))"
  define s1 where "s1 = (\<lambda>(x::int,y). (x, (y-d) mod n))"

  have 0:"bij_betw s0 (verts G) (verts G)"
    by (intro bij_betwI[where g="\<lambda>(x,y). (x,(y+c*x) mod n)"])
     (auto simp add:mgg_graph_def s0_def Pi_def mod_simps)
  have 1:"bij_betw s1 (verts G) (verts G)"
    by (intro bij_betwI[where g="\<lambda>(x,y). (x,(y+d) mod n)"])
     (auto simp add:mgg_graph_def s1_def Pi_def mod_simps)
  have 2: "s = (s1 \<circ> s0)"
    by (simp add:s1_def s0_def s_def comp_def mod_simps case_prod_beta ext)
  have 3:"bij_betw s (verts G) (verts G)"
    unfolding 2 using bij_betw_trans[OF 0 1] by simp

  have 4:"(snd (s x) + c * fst x + d) mod int n = snd x mod n" for x
    unfolding s_def by (simp add:case_prod_beta cong:mod_add_cong) (simp add:algebra_simps)
  have 5: "fst (s x) = fst x" for x
    unfolding s_def by (cases x, simp)

  have "?L = c_inner (\<lambda>x. f (fst x, snd x + c*fst x+d)) (\<lambda>x. \<omega>\<^sub>F (fst x*u + snd x* v))"
    unfolding FT_altdef by simp
  also have "... = c_inner (\<lambda>x. f (fst x, (snd x + c*fst x+d) mod n)) (\<lambda>x. \<omega>\<^sub>F (fst x*u + snd x* v))"
    by (intro c_inner_cong  periodic_cong[OF assms]) (auto simp add:algebra_simps)
  also have "... = c_inner (\<lambda>x. f (fst x, snd x mod n)) (\<lambda>x. \<omega>\<^sub>F (fst x*u+ snd (s x)* v))"
    by (subst c_inner_reindex[OF 3]) (simp add:4 5)
  also have "... =
    c_inner (\<lambda>x. f (fst x, snd x mod n)) (\<lambda>x. \<omega>\<^sub>F (fst x*u+ ((snd x-c*fst x-d) mod n)* v))"
    by (simp add:s_def case_prod_beta)
  also have "... = c_inner f (\<lambda>x. \<omega>\<^sub>F (fst x* (u-c * v) + snd x * v-d * v))"
    by (intro c_inner_cong \<omega>\<^sub>F_cong) (auto simp add:mgg_graph_def algebra_simps mod_add_mult_eq) 
  also have "... = c_inner f (\<lambda>x. \<omega>\<^sub>F (-d* v)*\<omega>\<^sub>F (fst x*(u-c* v) + snd x * v))"
    by (simp add: \<omega>\<^sub>F_simps   algebra_simps)
  also have "... = \<omega>\<^sub>F (d* v)*c_inner f (\<lambda>x. \<omega>\<^sub>F (fst x*(u-c* v) + snd x * v))"
    by (simp add:c_inner_simps \<omega>\<^sub>F_simps)
  also have "... = ?R"
    unfolding FT_altdef by simp 
  finally show ?thesis by simp
qed

lemma FT_sheer:
  fixes u v c d :: int
  assumes "periodic f" 
  shows 
    "FT (\<lambda>x. f (fst x,snd x+c*fst x+d)) (u,v) = \<omega>\<^sub>F (d* v) * FT f (u-c* v,v)" (is "?A")
    "FT (\<lambda>x. f (fst x,snd x+c*fst x)) (u,v) = FT f (u-c* v,v)" (is "?B")
    "FT (\<lambda>x. f (fst x+c* snd x+d,snd x)) (u,v) = \<omega>\<^sub>F (d* u) * FT f (u,v-c*u)" (is "?C")
    "FT (\<lambda>x. f (fst x+c* snd x,snd x)) (u,v) = FT f (u,v-c*u)" (is "?D")
proof -
  have 1: "periodic (\<lambda>x. f (snd x, fst x))" 
    using assms unfolding periodic_def by simp

  have 0:"\<omega>\<^sub>F 0 = 1"
    unfolding \<omega>\<^sub>F_def by simp
  show ?A
    using FT_sheer_aux[OF assms] by simp
  show ?B
    using 0 FT_sheer_aux[OF assms, where d="0"] by simp
  show ?C
    using FT_sheer_aux[OF 1] by (subst (1 2) FT_swap[symmetric], simp)
  show ?D
    using 0 FT_sheer_aux[OF 1, where d="0"] by (subst (1 2) FT_swap[symmetric], simp)
qed

definition S\<^sub>2 :: "int \<times> int \<Rightarrow> int \<times> int" where "S\<^sub>2 x = (fst x, snd x - 2 * fst x)"
definition S\<^sub>1 :: "int \<times> int \<Rightarrow> int \<times> int" where "S\<^sub>1 x = (fst x - 2 * snd x, snd x)"

lemma hoory_8_8':
  fixes f :: "int \<times> int \<Rightarrow> real"
  assumes "\<And>x. f x \<ge> 0"
  assumes "f (0,0) = 0"
  shows "g_inner f (\<lambda>x. f(S\<^sub>2 x)*\<bar>cos(pi*fst x/n)\<bar>+f(S\<^sub>1 x)*\<bar>cos(pi* snd x/n)\<bar>)\<le>1.25* sqrt 2*g_norm f^2"
  sorry

lemma hoory_8_8:
  fixes f :: "int \<times> int \<Rightarrow> real"
  assumes "\<And>x. f x \<ge> 0"
  assumes "f (0,0) = 0"
  shows "g_inner f (\<lambda>(x,y). f(x,y-2*x)*\<bar>cos(pi*x/n)\<bar>+f(x-2*y,y)*\<bar>cos(pi*y/n)\<bar>)
    \<le>1.25* sqrt 2*g_norm f^2"
  sorry

lemma hoory_8_7:
  fixes f :: "int\<times>int \<Rightarrow> complex"
  assumes "f (0,0) = 0"
  assumes "periodic f"
  shows "norm(c_inner f (\<lambda>(x,y). f(x,y-2*x)*(1+\<omega>\<^sub>F x)+f(x-2*y,y)*(1+\<omega>\<^sub>F y)))
    \<le> (2.5 * sqrt 2) * (\<Sum>v \<in> verts G. norm (f v)^2)" (is "?L \<le> ?R")
proof -
  define g :: "int\<times>int \<Rightarrow> real" where "g x = norm (f x)" for x

  have g_zero: "g (0,0) = 0"
    using assms(1) unfolding g_def by simp
  have g_nonneg: "g x \<ge> 0" for x
    unfolding g_def by simp

  have 0: "norm(1+\<omega>\<^sub>F x) = 2*\<bar>cos(pi*x/n)\<bar>" for x :: real
  proof -
    have "norm(1+\<omega>\<^sub>F x) = norm(\<omega>\<^sub>F (-x/2)*(\<omega>\<^sub>F 0 + \<omega>\<^sub>F x))"
      unfolding \<omega>\<^sub>F_def norm_mult by simp
    also have "... = norm (\<omega>\<^sub>F (0-x/2) + \<omega>\<^sub>F (x-x/2))"
      unfolding \<omega>\<^sub>F_simps by (simp add: algebra_simps)
    also have "... = norm (\<omega>\<^sub>F (x/2) + cnj (\<omega>\<^sub>F (x/2)))"
      unfolding \<omega>\<^sub>F_simps(3) by (simp add:algebra_simps)
    also have "... = \<bar>2*Re (\<omega>\<^sub>F (x/2))\<bar>"
      unfolding complex_add_cnj norm_of_real by simp
    also have "... =  2*\<bar>cos(pi*x/n)\<bar>"
      unfolding \<omega>\<^sub>F_def cis.simps by simp
    finally show ?thesis by simp
  qed

  have "?L\<le>norm(\<Sum>v\<in>verts G. f v *
    cnj(f(fst v,snd v-2*fst v)*(1+\<omega>\<^sub>F (fst v))+f(fst v-2* snd v,snd v)*(1+\<omega>\<^sub>F (snd v))))"
    unfolding c_inner_def by (simp add:case_prod_beta)
  also have "...\<le>(\<Sum>v\<in>verts G. norm(f v *
    cnj(f(fst v,snd v-2*fst v)*(1+\<omega>\<^sub>F (fst v))+f(fst v-2* snd v,snd v)*(1+\<omega>\<^sub>F (snd v)))))"
    by (intro norm_sum)
  also have "...=(\<Sum>v\<in>verts G. g v *
    norm(f(fst v,snd v-2*fst v)*(1+\<omega>\<^sub>F (fst v))+f(fst v-2* snd v,snd v)*(1+\<omega>\<^sub>F (snd v))))"
    unfolding norm_mult g_def complex_mod_cnj by simp
  also have "...\<le>(\<Sum>v\<in>verts G. g v *
    (norm (f(fst v,snd v-2*fst v) *(1+\<omega>\<^sub>F (fst v)))+norm ( f(fst v-2* snd v,snd v)*(1+\<omega>\<^sub>F(snd v)))))"
    by (intro sum_mono norm_triangle_ineq mult_left_mono g_nonneg)
  also have "...=2*g_inner g (\<lambda>(x,y). g(x,y-2*x)*\<bar>cos(pi*x/n)\<bar>+g(x-2*y,y)*\<bar>cos(pi*y/n)\<bar>)"
    unfolding g_def g_inner_def norm_mult 0 
    by (simp add:sum_distrib_left algebra_simps case_prod_beta)
  also have "... \<le>2*(1.25* sqrt 2*g_norm g^2)"
    by (intro mult_left_mono hoory_8_8 g_nonneg g_zero) auto
  also have "... = ?R"
    unfolding g_norm_sq g_def g_inner_def by (simp add:power2_eq_square)
  finally show ?thesis by simp
qed

lemma hoory_8_3:
  assumes "g_inner f (\<lambda>_. 1) = 0"
  assumes "periodic f"
  shows "\<bar>(\<Sum>(x,y)\<in>verts G. f(x,y)*(f(x+2*y,y)+f(x+2*y+1,y)+f(x,y+2*x)+f(x,y+2*x+1)))\<bar> 
    \<le> (2.5 * sqrt 2) * g_norm f^2" (is "\<bar>?L\<bar> \<le> ?R")
proof -
  define Ts :: "(int \<times> int \<Rightarrow> int \<times> int) list" where 
    "Ts = [(\<lambda>(x,y).(x+2*y,y)),(\<lambda>(x,y).(x+2*y+1,y)),(\<lambda>(x,y).(x,y+2*x)),(\<lambda>(x,y).(x,y+2*x+1))]"
  have p: "periodic (\<lambda>x. complex_of_real (f x))" 
    by (intro periodic_comp[OF assms(2)])

  have 0: "(\<Sum>T\<leftarrow>Ts. FT (f\<circ>T) (x,y))= FT f (x,y-2*x)*(1+\<omega>\<^sub>F x)+FT f (x-2*y,y)*(1+\<omega>\<^sub>F y)" 
    (is "?L1 = ?R1") for x y :: int
    unfolding Ts_def by (simp add:case_prod_beta FT_sheer[OF p]) (simp add:algebra_simps)

  have "cmod ((of_nat n)^2) = cmod (of_real (of_nat n^2))" by simp
  also have "... = abs (of_nat n^2)" by (intro norm_of_real)
  also have "... = real n^2" by simp
  finally have 1: "cmod ((of_nat n)\<^sup>2) = (real n)\<^sup>2" by simp

  have "FT (\<lambda>x. complex_of_real (f x)) (0, 0) = complex_of_real (g_inner f (\<lambda>_ . 1))"
    unfolding FT_def g_inner_def c_inner_def \<omega>\<^sub>F_def by simp
  also have "... = 0"
    unfolding assms by simp
  finally have 2: "FT (\<lambda>x. complex_of_real (f x)) (0, 0) = 0"
    by simp

  have "abs ?L = norm (complex_of_real ?L)" 
    unfolding norm_of_real by simp
  also have "... = norm (\<Sum>T \<leftarrow> Ts. (c_inner f (f \<circ> T)))"
    unfolding Ts_def by (simp add:algebra_simps c_inner_def sum.distrib comp_def case_prod_beta)
  also have "... = norm (\<Sum>T \<leftarrow> Ts. (c_inner (FT f) (FT (f \<circ> T)))/n^2)" 
    by (subst parseval) simp
  also have "... = norm (c_inner (FT f) (\<lambda>x. (\<Sum>T \<leftarrow> Ts. (FT (f \<circ> T) x)))/n^2)"
    unfolding Ts_def by (simp add:c_inner_simps case_prod_beta add_divide_distrib)
  also have "... = norm (c_inner (FT f) (\<lambda>(x,y). (\<Sum>T \<leftarrow> Ts. (FT (f \<circ> T) (x,y))))/n^2)"
    by (simp add: cond_case_prod_eta) 
  also have "...=norm(c_inner(FT f)(\<lambda>(x,y).(FT f(x,y-2*x)*(1+\<omega>\<^sub>F x)+FT f (x-2*y,y)*(1+\<omega>\<^sub>F y))))/n^2"
    by (subst 0) (simp add:norm_divide 1)
  also have "... \<le> (2.5 * sqrt 2) * (\<Sum>v \<in> verts G. norm (FT f v)^2) / n^2"
    by (intro divide_right_mono hoory_8_7[where f="FT f"] 2 periodic_FT) auto 
  also have "... = (2.5 * sqrt 2) * (\<Sum>v \<in> verts G. cmod (f v)^2)"
    by (subst (2) plancharel) simp
  also have "... = (2.5 * sqrt 2) * (g_inner f f)"
    unfolding g_inner_def norm_of_real by (simp add: power2_eq_square)
  also have "... = ?R" 
    using g_norm_sq by auto
  finally show ?thesis by simp
qed


text \<open>Inequality stated before Theorem 8.3 in Hoory.\<close> 

lemma mgg_numerical_radius_aux:
  assumes "g_inner f (\<lambda>_. 1) = 0"
  shows "\<bar>(\<Sum>a \<in> arcs G. f (head G a) * f (tail G a))\<bar> \<le> (5 * sqrt 2) * g_norm f^2"  (is "?L \<le> ?R")
proof -
  define g where "g x = f (fst x mod n, snd x mod n)" for x :: "int \<times> int"
  have 0:"g x = f x" if "x \<in> verts G" for x 
    unfolding g_def using that
    by (auto simp add:mgg_graph_def mem_Times_iff)

  have g_mod_simps[simp]: "g (x, y mod n) = g (x, y)" "g (x mod n, y) = g (x, y)" for x y :: int
    unfolding g_def by auto

  have periodic_g: "periodic g"
    unfolding periodic_def by simp

  have "g_inner g (\<lambda>_. 1) = g_inner f (\<lambda>_. 1)"
    by (intro g_inner_cong 0) auto
  also have "... = 0"
    using assms by simp
  finally have 1:"g_inner g (\<lambda>_. 1) = 0" by simp

  have 2:"g_norm g = g_norm f"
    by (intro g_norm_cong 0) (auto)

  have "?L = \<bar>(\<Sum>a \<in> arcs G. g (head G a) * g (tail G a))\<bar>"
    using wellformed
    by (intro arg_cong[where f="abs"] sum.cong arg_cong2[where f="(*)"] 0[symmetric]) auto
  also have "...=\<bar>(\<Sum>a\<in>arcs_pos. g(head G a)*g(tail G a))+(\<Sum>a\<in>arcs_neg. g(head G a)*g(tail G a))\<bar>"
    unfolding arcs_sym arcs_pos_def arcs_neg_def
    by (intro arg_cong[where f="abs"] sum.union_disjoint) auto
  also have "... = \<bar>2 * (\<Sum>(v,l)\<in>verts G \<times> {..<4}. g v * g (mgg_graph_step n v (l, 1)))\<bar>"
    unfolding arcs_pos_def arcs_neg_def
    by (simp add:inj_on_def sum.reindex case_prod_beta mgg_graph_def algebra_simps)
  also have "... = 2 * \<bar>(\<Sum>v \<in> verts G. (\<Sum>l \<in> {..<4}. g v * g (mgg_graph_step n v (l, 1))))\<bar>"
    by (subst sum.cartesian_product)  (simp add:abs_mult)
  also have "... = 2*\<bar>(\<Sum>(x,y)\<in>verts G. (\<Sum>l\<leftarrow>[0..<4]. g(x,y)* g (mgg_graph_step n (x,y) (l,1))))\<bar>"
    by (subst interv_sum_list_conv_sum_set_nat)
      (auto simp add:atLeast0LessThan case_prod_beta simp del:mgg_graph_step.simps) 
  also have "... =2*\<bar>\<Sum>(x,y)\<in>verts G. g (x,y)* (g(x+2*y,y)+g(x+2*y+1,y)+g(x,y+2*x)+g(x,y+2*x+1))\<bar>"
    by (simp add:case_prod_beta numeral_eq_Suc algebra_simps) 
  also have "... \<le> 2* ((2.5 * sqrt 2) * g_norm g^2)"
    by (intro mult_left_mono hoory_8_3 1 periodic_g) auto
  also have "... \<le> ?R" unfolding 2 by simp
  finally show ?thesis by simp
qed

definition MGG_bound :: real where "MGG_bound = 5 * sqrt 2 / 8"

text \<open>Main result: Theorem 8.2 in Hoory.\<close> 

lemma mgg_numerical_radius: "numerical_rad \<le> MGG_bound"
proof -
  have "numerical_rad \<le> (5 * sqrt 2)/real 8"
    by (intro numerical_radI[OF mgg_finite] mgg_numerical_radius_aux) auto
  also have "... = MGG_bound"
    unfolding MGG_bound_def by simp
  finally show ?thesis by simp
qed


end

end