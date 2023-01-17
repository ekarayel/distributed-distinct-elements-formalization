theory Margulis_Gaber_Galil
  imports 
    "Graph_Theory.Digraph"
    "HOL-Analysis.Complex_Transcendental"
    "HOL-Analysis.Set_Integral" 
    "HOL-Analysis.Lebesgue_Measure"
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
  where "c_inner f g = (\<Sum>v \<in> verts G. cnj (f v) * g v)" 

lemma c_inner_simps:
  "c_inner (\<lambda>x. c * f x) g = cnj c * c_inner f g" 
  "c_inner f (\<lambda>x. c * g x) = c * c_inner f g" 
  "c_inner (\<lambda>x. f x + g x) h = c_inner f h + c_inner g h" 
  "c_inner f (\<lambda>x. g x + h x) = c_inner f g + c_inner f h" 
  unfolding c_inner_def by (auto simp add:sum.distrib algebra_simps sum_distrib_left)

definition \<omega>\<^sub>F :: complex where "\<omega>\<^sub>F = exp(2*pi*\<i>/n)"

definition FT :: "(int \<times> int \<Rightarrow> complex) \<Rightarrow> (int \<times> int \<Rightarrow> complex)"
  where "FT f = (\<lambda>(u,v). \<Sum>(x,y) \<in> verts G. cnj (f (x,y)) * \<omega>\<^sub>F powr (x * u + y * v))"

lemma FT_altdef: "FT f (u,v) = (\<Sum>x \<in> verts G. cnj (f x) * \<omega>\<^sub>F powr (fst x * u + snd x * v))"
  unfolding FT_def by (simp add:case_prod_beta)

lemma FT_add: "FT (\<lambda>x. f x + g x) (u,v) = FT f (u,v) + FT g (u,v)"
  unfolding FT_altdef by (simp add:sum.distrib algebra_simps)

lemma FT_zero: "FT (\<lambda>x. 0) (u,v) = 0"
  unfolding FT_altdef by simp

lemma FT_sum: 
  assumes "finite I" 
  shows "FT (\<lambda>x. (\<Sum>i \<in> I. f i x)) (u,v) = (\<Sum>i \<in> I. FT (f i) (u,v))"
  using assms by (induction rule: finite_induct, auto simp add:FT_zero FT_add)

lemma FT_scale: "FT (\<lambda>x. c * f x) (u,v) = cnj c * FT f (u,v)"
  unfolding FT_altdef by (simp add: algebra_simps  sum_distrib_left)


(* NOT NEEDED ? *)
definition FT_INV :: "(int \<times> int \<Rightarrow> complex) \<Rightarrow> (int \<times> int \<Rightarrow> complex)"
  where "FT_INV f = (\<lambda>(u,v). (\<Sum>(x,y) \<in> verts G. f (x,y) * \<omega>\<^sub>F powr (-(x * u + y * v))/n^2))"

lemma parseval:
  "(\<Sum>v \<in> verts G. cnj (f v) * g v) = (\<Sum>v \<in> verts G. cnj (FT f v) * FT g v)/n^2"
proof -
  have "FT (\<lambda>\<omega>. c * of_bool(\<omega>=x)) (u,v) = cnj c * \<omega>\<^sub>F powr (fst x * u + snd x * v)" 
    if "x \<in> verts G"  for c x u v
    unfolding FT_altdef using that by (simp add:of_bool_def if_distrib if_distribR sum.If_cases)
  hence 0:"FT (\<lambda>\<omega>. c * of_bool(\<omega>=x)) v = cnj c * \<omega>\<^sub>F powr (fst x * fst v + snd x * snd v)" 
    if "x \<in> verts G"  for c x v
    using that by (cases v, simp)


  have "(\<Sum>v \<in> verts G. cnj c * of_bool (v=x) * d * of_bool (v=y)) =
    (\<Sum>v \<in> verts G. cnj (FT (\<lambda>w. c * of_bool (w=x)) v) * FT  (\<lambda>w. d * of_bool (w=y)) v)/n^2"
    if "x \<in> verts G" "y \<in> verts G"
    for c d x y
    unfolding 0[OF that(1)] 0[OF that(2)] using that 
    sorry



  show ?thesis
  sorry
qed

lemma plancharel:
  "(\<Sum>v \<in> verts G. norm (f v)^2) = (\<Sum>v \<in> verts G. norm (FT f v)^2)/n^2" (is "?L = ?R")
proof -
  have "complex_of_real ?L = (\<Sum>v \<in> verts G. cnj (f v) * f v)"
    by (simp flip:of_real_power add:complex_norm_square algebra_simps)
  also have "... = (\<Sum>v \<in> verts G. cnj (FT f v) * FT f v) / n^2"
    by (subst parseval) simp
  also have "... = complex_of_real ?R"
    by (simp flip:of_real_power add:complex_norm_square algebra_simps) simp
  finally have "complex_of_real ?L = complex_of_real ?R" by simp
  thus ?thesis 
    using of_real_eq_iff by blast
qed

lemma FT_swap:
  "FT (\<lambda>x. f (snd x, fst x)) (u,v) = FT f (v,u)" (is "?L = ?R")
proof -
  let ?g = "(\<lambda>(x::int \<times> int). (snd x, fst x))" 
  have 0:"bij_betw (\<lambda>(x::int \<times> int). (snd x, fst x)) (verts G) (verts G)"
    by (intro bij_betwI[where g="(\<lambda>(x::int \<times> int). (snd x, fst x))"])
     (auto simp add:mgg_graph_def)

  have "?L = (\<Sum>x\<in>verts G. cnj (f (snd x, fst x)) * \<omega>\<^sub>F powr (fst x * u + snd x * v))"
    unfolding FT_def by (simp add:case_prod_beta) 
  also have "... = (\<Sum>x\<in>verts G. cnj (f x) * \<omega>\<^sub>F powr ((fst x) * v + (snd x) * u))"
    by (subst sum.reindex_bij_betw[OF 0,symmetric]) (simp add:algebra_simps)
  also have "... = ?R"
    unfolding FT_def by (simp add:case_prod_beta) 
  finally show ?thesis by simp
qed

lemma \<omega>_f_powr_cong:
  fixes x y :: int
  assumes "x mod n = y mod n" 
  shows "\<omega>\<^sub>F powr (of_int x) = \<omega>\<^sub>F powr (of_int y)"
  sorry

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
    unfolding FT_altdef by (intro sum.cong arg_cong2[where f="(*)"] \<omega>_f_powr_cong) 
      (auto simp add:mod_simps cong:mod_add_cong)
  thus ?thesis 
    unfolding periodic_def by simp
qed


lemma FT_sheer_aux:
  fixes u v c d :: int
  assumes "periodic f" 
  shows  "FT (\<lambda>x. f (fst x,snd x+c*fst x+d)) (u,v) = \<omega>\<^sub>F powr (-d* v) * FT f (u-c* v,v)" 
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

  have 4:"(snd (s x) + d + c * fst x) mod int n = snd x mod n" for x
    unfolding s_def by (simp add:case_prod_beta cong:mod_add_cong) (simp add:algebra_simps)
  have 5: "fst (s x) = fst x" for x
    unfolding s_def by (cases x, simp)

  have "?L = (\<Sum>x\<in>verts G. cnj (f (fst x, snd x + c*fst x+d)) * \<omega>\<^sub>F powr (fst x*u + snd x* v))"
    unfolding FT_altdef by simp
  also have "... = (\<Sum>x\<in>verts G. cnj(f(fst x,(snd x+d+c*fst x) mod n))*\<omega>\<^sub>F powr (fst x*u+snd x* v))"
    by (intro sum.cong arg_cong2[where f="(*)"] arg_cong[where f="cnj"] periodic_cong[OF assms])
     (auto simp add:algebra_simps)
  also have "... = (\<Sum>x\<in>verts G. cnj (f (fst x, snd x mod n)) * \<omega>\<^sub>F powr (fst x*u+ snd (s x)* v))"
    by (subst sum.reindex_bij_betw[OF 3,symmetric]) (simp add:4 5)
  also have "... =
    (\<Sum>x\<in>verts G. cnj (f (fst x, snd x mod n)) * \<omega>\<^sub>F powr (fst x*u+ ((snd x-c*fst x-d) mod n)* v))"
    by (simp add:s_def case_prod_beta)
  also have "... = (\<Sum>x\<in>verts G. cnj (f x) * \<omega>\<^sub>F powr (fst x* (u-c * v) + snd x * v-d * v))"
    by (intro sum.cong refl arg_cong2[where f="(*)"] \<omega>_f_powr_cong)
     (auto simp add:mgg_graph_def algebra_simps mod_add_mult_eq) 
  also have "... = \<omega>\<^sub>F powr (-d* v)*(\<Sum>x\<in>verts G. cnj (f x) * \<omega>\<^sub>F powr (fst x*(u-c* v) + snd x * v))"
    by (simp add: powr_diff sum_divide_distrib[symmetric] powr_minus_divide)
  also have "... = ?R"
    unfolding FT_altdef by simp 
  finally show ?thesis by simp
qed

lemma FT_sheer:
  fixes u v c d :: int
  assumes "periodic f" 
  shows 
    "FT (\<lambda>x. f (fst x,snd x+c*fst x+d)) (u,v) = \<omega>\<^sub>F powr (-d* v) * FT f (u-c* v,v)" (is "?A")
    "FT (\<lambda>x. f (fst x,snd x+c*fst x)) (u,v) = FT f (u-c* v,v)" (is "?B")
    "FT (\<lambda>x. f (fst x+c* snd x+d,snd x)) (u,v) = \<omega>\<^sub>F powr (-d* u) * FT f (u,v-c*u)" (is "?C")
    "FT (\<lambda>x. f (fst x+c* snd x,snd x)) (u,v) = FT f (u,v-c*u)" (is "?D")
proof -
  have 1: "periodic (\<lambda>x. f (snd x, fst x))" 
    using assms unfolding periodic_def by simp

  have 0:"\<omega>\<^sub>F \<noteq> 0" 
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


lemma hoory_8_7:
  fixes f :: "int\<times>int \<Rightarrow> complex"
  assumes "f (0,0) = 0"
  assumes "periodic f"
  shows "norm(\<Sum>(x,y)\<in>verts G. cnj(f (x,y))*(f(x,y-2*x)*(1+\<omega>\<^sub>F powr -x)+f(x-2*y,y)*(1+\<omega>\<^sub>F powr -y)))
    \<le> (2.5 * sqrt 2) * (\<Sum>v \<in> verts G. norm (f v)^2)"
  sorry

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

  have 0: "(\<Sum>T\<leftarrow>Ts. FT (f\<circ>T) (x,y))= FT f (x,y-2*x)*(1+\<omega>\<^sub>F powr -x)+FT f (x-2*y,y)*(1+\<omega>\<^sub>F powr -y)" 
    (is "?L1 = ?R1") for x y :: int
    unfolding Ts_def by (simp add:case_prod_beta FT_sheer[OF p]) (simp add:algebra_simps)

  have "cmod ((of_nat n)^2) = cmod (of_real (of_nat n^2))" by simp
  also have "... = abs (of_nat n^2)" by (intro norm_of_real)
  also have "... = real n^2" by simp
  finally have 1: "cmod ((of_nat n)\<^sup>2) = (real n)\<^sup>2" by simp

  have "FT (\<lambda>x. complex_of_real (f x)) (0, 0) = complex_of_real (g_inner f (\<lambda>_ . 1))"
    unfolding FT_def g_inner_def  \<omega>\<^sub>F_def by simp
  also have "... = 0"
    unfolding assms by simp
  finally have 2: "FT (\<lambda>x. complex_of_real (f x)) (0, 0) = 0"
    by simp

  have "abs ?L = norm (complex_of_real ?L)" 
    unfolding norm_of_real by simp
  also have "... = norm (\<Sum>T \<leftarrow> Ts. (\<Sum>v\<in>verts G. cnj (f v)* (f \<circ> T) v))"
    unfolding Ts_def by (simp add:algebra_simps sum.distrib comp_def case_prod_beta)
  also have "... = norm (\<Sum>T \<leftarrow> Ts. (\<Sum>v\<in>verts G. cnj (FT f v) * (FT (f \<circ> T) v))/n^2)" 
    by (subst parseval) simp
  also have "... = norm ((\<Sum>(x,y)\<in>verts G. cnj (FT f (x,y)) * (\<Sum>T \<leftarrow> Ts. (FT (f \<circ> T) (x,y))))/n^2)"
    unfolding Ts_def
    by (simp add:sum.distrib sum_divide_distrib case_prod_beta add_divide_distrib algebra_simps)
  also have "... = norm ((\<Sum>(x,y)\<in>verts G. cnj(FT f(x,y))*
    (FT f (x,y-2*x)*(1+\<omega>\<^sub>F powr -x)+FT f (x-2*y,y)*(1+\<omega>\<^sub>F powr -y))))/n^2"
    by (subst 0) (simp add:norm_divide 1)
  also have "... \<le> (2.5 * sqrt 2) * (\<Sum>v \<in> verts G. norm (FT f v)^2) / n^2"
    by (intro divide_right_mono hoory_8_7[where f="FT f"] 2 periodic_FT) auto 
  also have "... = (2.5 * sqrt 2) * (\<Sum>v \<in> verts G. cmod (f v)^2)"
    by (subst (2) plancharel) simp
  also have "... = (2.5 * sqrt 2) * (g_inner f f)"
    unfolding g_inner_def norm_of_real by (simp add: power2_eq_square)
  also have "... = ?R" 
    using g_norm_def g_norm_nonneg by auto
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