theory Margulis_Gaber_Galil
  imports 
    "Graph_Theory.Digraph"
    "HOL-Analysis.Set_Integral" "HOL-Analysis.Lebesgue_Measure"
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
@{term "v"} for any pair of vertices @{term "v"} @{term "w \<in> vertices G"}.\<close>

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

lemma g_norm_nonneg: "g_norm f \<ge> 0" 
  sorry


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
  assumes "fin_digraph G"
  assumes "g_inner f (\<lambda>_. 1) = 0" "C \<ge> 0"
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
      by (intro divide_right_mono assms(4) that(2)) simp
    also have "... \<le> C * 1^2 / d"
      by (intro divide_right_mono mult_left_mono power_mono that(1) g_norm_nonneg assms(3)) simp
    also have "... = C/d" by simp
    finally show ?thesis by simp
  qed
  ultimately show ?thesis
    unfolding numerical_rad_def
    by (intro cSup_least) auto
qed

(*
  Consider x in <x,1> = 0, <x,x> = 1
  
  f(x) = <Ax,Ax> 

  L(x,s,t) = f(x) + t <x,1> + s (1-<x,x>) 

  [not sure this is even better]

  <Ax,Ax> > <x,Ax><x,Ax>
  <Ax,Ax> - <<x,Ax>x,Ax> > 0

  <Ax - <x,Ax>x, Ax> >0
  

  <x,A^2x> > |<x,Ax>|^2
  


  |f| = 1, <f,1> = 0

  want:
  <f, step f> \<le> 1-C/d 

  1/d [sum v in V (f(v) * sum w in w\<rightarrow>v f(w)  ) ]
  = 1/d [sum v in V, w in w \<rightarrow> v (f(v) * f(w)) ]

  x=sum a_i e_i 
  Ax = sum a_i l_i e_i
  <x,Ax> = sum a_i^2 l_i 
  

  x A x

*)


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

lemma 
  assumes "arc_tail x = arc_tail y" "arc_head x= arc_head y" "arc_label x = arc_label y"
  shows "x = y"
  using assms
  using arc.expand by blast

fun mgg_graph_step :: "nat \<Rightarrow> (int \<times> int) \<Rightarrow> (nat \<times> int) \<Rightarrow> (int \<times> int)"
  where "mgg_graph_step n (i,j) (l,\<sigma>) = 
  [((i+\<sigma>) mod int n, j), (i, (j+\<sigma>) mod int n), ((i+\<sigma>*j) mod int n, j),(i, (j+\<sigma>*i) mod int n)] ! l"

definition mgg_graph :: "nat \<Rightarrow> (int \<times> int, (int \<times> int, nat \<times> int) arc) pre_digraph" where 
  "mgg_graph n =
    \<lparr> verts = {0..<n} \<times> {0..<n}, 
      arcs = (\<lambda>(t,l). (Arc t (mgg_graph_step n t l) l)) ` (({0..<int n} \<times> {0..<int n}) \<times> ({..<4} \<times> {-1,1})), 
      tail = arc_tail,
      head = arc_head \<rparr>"


locale margulis_gaber_galil =
  fixes n :: nat
  assumes n_gt_0: "n > 0"
begin

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

lemma sym: "symmetric_multi_graph (mgg_graph n)"
proof -
  define f :: "(int \<times> int, nat \<times> int) arc \<Rightarrow> (int \<times> int, nat \<times> int) arc"  
    where "f a = Arc (arc_head a) (arc_tail a) (apsnd (\<lambda>x. (-1) * x) (arc_label a))" for a 

  have "f e \<in> arcs (mgg_graph n)" if a_0: "e \<in> arcs (mgg_graph n)" for e
  proof -
    obtain t l \<sigma> where tl_def: 
      "t \<in> {0..<int n} \<times> {0..<int n}" "l < 4" "\<sigma> \<in> {-1,1}" 
      "e = Arc t (mgg_graph_step n t (l,\<sigma>)) (l,\<sigma>)"
      using a_0 mgg_graph_def by auto 
    define h where  "h = mgg_graph_step n t (l,\<sigma>)"

    have "mgg_graph_step n (mgg_graph_step n t (l,\<sigma>)) (l,-\<sigma>) = t" if "l \<in> set [0,1,2,3]" 
      using tl_def(1,4) n_gt_0 that
      by (cases t, auto simp add:mod_simps)
    hence "mgg_graph_step n h (l,(-1)*\<sigma>) = t"
      using tl_def(2) unfolding h_def by fastforce
    hence a_1:"f e = Arc h (mgg_graph_step n h (l,-\<sigma>)) (l,-\<sigma>)" 
      unfolding f_def tl_def(4) h_def by simp
    have "h = head (mgg_graph n) e"
      unfolding h_def tl_def mgg_graph_def by simp
    also have "... \<in> verts (mgg_graph n)" 
      by (intro head_in_verts a_0)
    finally have "h \<in> {0..<int n} \<times> {0..<int n}"
      unfolding mgg_graph_def by simp
    thus ?thesis 
      using a_1 tl_def(2,3) unfolding mgg_graph_def by auto 
  qed
  hence a:"f ` arcs (mgg_graph n) \<subseteq> arcs (mgg_graph n)" 
    by auto
  have "inj f" 
    unfolding f_def by (intro inj_onI arc.expand prod_eqI conjI) 
      (simp_all add:apsnd_def map_prod_def case_prod_beta) 
  hence b:"inj_on f (arcs (mgg_graph n))"
    using inj_on_subset by auto
  hence "f ` arcs (mgg_graph n) = arcs (mgg_graph n)"
    by (intro card_subset_eq a card_image fin_digraph.finite_arcs mgg_finite) 
  hence c:"bij_betw f (arcs (mgg_graph n)) (arcs (mgg_graph n))"
    using b unfolding bij_betw_def by simp

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

definition R2_space :: "(real^2) set" 
  where "R2_space = {x. (\<forall>i. x $ i \<in> {0..<real n})}"

lemma R2_space_measurable: "R2_space \<in> sets lborel"
  unfolding R2_space_def by simp

definition R2_bound :: real where "R2_bound = 0.2"

definition rmod :: "real \<Rightarrow> real"
  where "rmod x = real n * frac (x / real n)" 

definition S :: "real^2 \<Rightarrow> real^2"
  where "S x = (\<chi> i. if i = 1 then x $ 1 else rmod (x $ 1 + x $ 2))"

definition T :: "real^2 \<Rightarrow> real^2"
  where "T x = (\<chi> i. if i = 1 then rmod (x $ 1 + x $ 2) else x $ 2)"

lemma 
  assumes "set_integrable lborel R2_space (\<lambda>x. f x^2)"
  assumes "(\<integral>\<omega>\<in>R2_space. f \<omega> \<partial>lborel) = 0"
  assumes "(\<integral>\<omega>\<in>R2_space. (f \<omega>^2) \<partial>lborel) = 1"
  shows "(\<integral>\<omega>\<in>R2_space. ((f \<omega> - f (S \<omega>))^2 + (f \<omega> - f (T \<omega>))^2) \<partial>lborel) \<le> R2_bound"
  sorry

(*
  (i,j) 


*)

lemma two_d_basis: "Basis = {(axis 1 1):: real^2 , axis 2 1}" (is "?L = ?R")
proof -
  have "v \<in> {axis 2 1, axis 1 1}" if "v \<in> ?L" for v
    using axis_inverse[OF that] 
    by (metis (full_types) exhaust_2 insertCI one_neq_zero)
  moreover have "?R \<subseteq> ?L"
    by (auto simp add:Basis_vec_def) 
  ultimately show ?thesis by auto
qed

lemma inner_axis:
  "v \<bullet> (axis i 1) = v $ i"
  unfolding inner_vec_def axis_def by (vector if_distribR if_distrib sum.If_cases)

lemma axis_distinct: "axis 2 1 \<noteq> (axis 1 1 :: real^2)"
    by (simp add: axis_eq_axis)

definition hsquare :: "(int \<times> int) \<Rightarrow> (real^2) set"
  where "hsquare = (\<lambda>(x,y). {p. p $ 1 \<in> {x..<x+1} \<and> p $ 2 \<in> {y..<y+1}})"

lemma hsquare_measuable: "hsquare (x, y) \<in> sets lborel"
  unfolding hsquare_def by simp

lemma hsquare_emeasure: "emeasure lborel (hsquare x) = 1" (is "?L = ?R")
proof -
  have "1 = emeasure lborel (box ((vector [fst x, snd x]) :: real^2) (vector [fst x+1,snd x+1]))"
    using axis_distinct by (subst emeasure_lborel_box) (auto simp add:two_d_basis inner_axis)
  also have "... \<le> ?L"
    unfolding box_def hsquare_def
    by (intro emeasure_mono subsetI) (auto simp add:two_d_basis inner_axis case_prod_beta)
  finally have 0:"1 \<le> ?L" by simp

  have "?L \<le> emeasure lborel (cbox ((vector [fst x, snd x]) :: real^2) (vector [fst x+1,snd x+1]))"
    unfolding cbox_def hsquare_def
    by (intro emeasure_mono subsetI) (auto simp add:two_d_basis inner_axis case_prod_beta)
  also have "... = 1"
    using axis_distinct by (subst emeasure_lborel_cbox) (auto simp add:two_d_basis inner_axis)
  finally have 1: "?L \<le> 1" by simp

  thus ?thesis using 0 1 by simp
qed

lemma hsquare_measure: "measure lborel (hsquare x) = 1"
  unfolding measure_def hsquare_emeasure by simp

lemma hsquare_mem_iff: 
  fixes x :: "int \<times> int"
  shows "p \<in> hsquare x \<longleftrightarrow> x = (\<lfloor>p $ 1\<rfloor>, \<lfloor>p $ 2\<rfloor>)"
proof -
  have "p \<in> hsquare x \<longleftrightarrow> \<lfloor>p $ 1\<rfloor> = fst x \<and> \<lfloor>p $ 2\<rfloor> = snd x"
    unfolding hsquare_def by (auto simp add: floor_eq_iff case_prod_beta) 
  also have "... \<longleftrightarrow> x = (\<lfloor>p $ 1\<rfloor>, \<lfloor>p $ 2\<rfloor>)"
    by auto
  finally show ?thesis by simp
qed

lemma grid_integral:
  fixes f :: "int \<times> int \<Rightarrow> real"
  shows "set_integrable lborel R2_space (\<lambda>\<omega>. f (\<lfloor>\<omega>$1\<rfloor>,\<lfloor>\<omega>$2\<rfloor>))" (is "?U")
    and "(\<integral>\<omega>\<in>R2_space. f (\<lfloor>\<omega>$1\<rfloor>,\<lfloor>\<omega>$2\<rfloor>) \<partial>lborel) = (\<Sum>v \<in> verts (mgg_graph n). f v)" (is "?L = ?R")
proof -
  have 0: "indicator R2_space x *\<^sub>R f (\<lfloor>x$1\<rfloor>,\<lfloor>x$2\<rfloor>) = 
    (\<Sum>v\<in>verts (mgg_graph n). indicator (hsquare v) x * f v)"
    (is "?L1 = ?R1") for x :: "real^2"
  proof -
    have "(\<lfloor>x $ 1\<rfloor>,\<lfloor>x $ 2\<rfloor>) \<in> {0..<int n} \<times> {0..<int n} \<longleftrightarrow> (\<forall>i. \<lfloor>x $ i\<rfloor> \<in> {0..<int n})"
      unfolding mem_Times_iff forall_2 by auto
    also have "... \<longleftrightarrow> x \<in> R2_space"
      unfolding R2_space_def using floor_less_iff
      by (auto simp add:floor_less_iff) 
    finally have a': "(\<lfloor>x $ 1\<rfloor>,\<lfloor>x $ 2\<rfloor>) \<in> {0..<int n} \<times> {0..<int n} \<longleftrightarrow> x \<in> R2_space"
      by auto 

    have "?R1 = (\<Sum>v | v \<in> {0..<int n} \<times> {0..<int n} \<and> x \<in> hsquare v. f v)"
      unfolding mgg_graph_def by simp
    also have "... = (\<Sum>v | v \<in> {0..<int n} \<times> {0..<int n} \<and> v=(\<lfloor>x $ 1\<rfloor>,\<lfloor>x $ 2\<rfloor>). f v)"
      by (simp add:hsquare_mem_iff) 
    also have "... = sum f ({(\<lfloor>x $ 1\<rfloor>,\<lfloor>x $ 2\<rfloor>)} \<inter> {0..<int n} \<times> {0..<int n})"
      by (intro sum.cong) auto
    also have "... = indicator R2_space x * f (\<lfloor>x$1\<rfloor>,\<lfloor>x$2\<rfloor>)"
      using a' by (simp split:split_indicator)
    finally show ?thesis by simp
  qed

  have "integrable lborel (\<lambda>\<omega>.\<Sum>v\<in>verts (mgg_graph n).indicator(hsquare v)\<omega>*f v)"
    using hsquare_measuable hsquare_emeasure
    by (intro integrable_sum integrable_mult_left integrable_real_indicator) auto
  thus ?U
    unfolding set_integrable_def by (intro iffD2[OF integrable_cong[OF refl 0]] )

  have "?L = (\<integral>\<omega>. (\<Sum>v\<in>verts (mgg_graph n). indicator (hsquare v) \<omega> * f v) \<partial>lborel)"
    unfolding set_lebesgue_integral_def
    by (intro Bochner_Integration.integral_cong 0 refl)
  also have "... = (\<Sum>v\<in>verts (mgg_graph n). (\<integral>\<omega>. (indicator (hsquare v) \<omega> * f v) \<partial>lborel))"
    using hsquare_measuable hsquare_emeasure
    by (intro integral_sum integrable_mult_left integrable_real_indicator) auto
  also have "... = (\<Sum>v\<in>verts (mgg_graph n). f v)"
    using hsquare_measure by simp
  finally show "?L = ?R" by simp
qed

(*
lemma 
  assumes "(i,j) \<in> verts (mgg_graph n)"
  shows "LINT \<omega>:R2_space|lborel. indicator (square i j) \<omega> = (1::real)" (is "?L= ?R")
    "set_integrable lborel R2_space (indicat_real (square i j))" (is "?U")
proof -
  have ij_bounds: "i \<ge> (0::real)" "j \<ge> (0::real)" "i + 1 \<le> real n" "j+1 \<le> real n"
    using assms unfolding mgg_graph_def by auto
  have "x \<in> R2_space" if "x \<in> square i j" for x
  proof -
    have "x $ 2 < n" "x $ 2 > 0" "x $ 1 < n" "x $ 1 > 0"
      using that ij_bounds unfolding square_def box_def two_d_basis 
      by (auto simp add: inner_axis vector_def)
    hence "x $ k < n" "x $ k > 0" for k :: 2 
      using exhaust_2[where x="k"] by auto
    thus "x \<in> R2_space"
      using order_le_less unfolding R2_space_def by auto
  qed
  hence 0: "square i j \<subseteq> R2_space" 
    by auto

  have 1:"axis 2 1 \<noteq> (axis 1 1 :: real^2)"
    by (simp add: axis_eq_axis)

  have 2:"indicator R2_space x *\<^sub>R indicator (square i j) x = indicat_real (square i j) x" 
    (is "?L1 = ?R1") for x :: "real^2"
  proof -
    have "?L1 = indicator (R2_space \<inter> square i j) x"
      unfolding indicator_inter_arith by simp
    also have "... = indicator (square i j) x"
      by (subst Int_absorb1[OF 0]) simp
    finally show ?thesis by simp
  qed

  have "?L = LINT x|lborel. indicator (square i j) x"
    unfolding set_lebesgue_integral_def 2 by simp
  also have "... = measure lborel (square i j)"
    by simp
  also have "... = (\<Prod>b\<in>Basis. ((vector [i + 1, j + 1] - vector [i, j]) \<bullet> (b::real^2)))"
    unfolding square_def 
    by (subst measure_lborel_box)  (auto simp add:two_d_basis vector_inner_axis) 
  also have "... = (\<Prod>b\<in>Basis. ((vector [1,1]) \<bullet> (b::real^2)))"
    by (intro prod.cong refl arg_cong2[where f="(\<bullet>)"]) (vector vector_def)
  also have "... = 1"
    using 1 by (simp add:two_d_basis vector_inner_axis)
  finally show "?L = ?R" by simp
  show "?U"
    unfolding set_integrable_def 2 unfolding square_def
    by (intro integrable_real_indicator emeasure_lborel_box_finite) auto
qed
*)





definition MGG_bound :: real where "MGG_bound = 5 * sqrt 2"

lemma mgg_numerical_radius_aux:
  assumes "g_norm f \<le> 1"
  assumes "g_inner f (\<lambda>_. 1) = 0"
  shows "\<bar>g_inner f (g_step f)\<bar> \<le> MGG_bound" 
proof -
  define f' where "f' x = f (\<lfloor>x $ 1\<rfloor>, \<lfloor>x $ 2\<rfloor>)" for x :: "real^2"

  have "\<integral>\<omega>\<in>R2_space. f' \<omega> \<partial>lborel = 0"
    using assms(2) unfolding g_inner_def
    unfolding f'_def grid_integral by simp

  have "\<integral>\<omega>\<in>R2_space. (f' \<omega>^2) \<partial>lborel = (\<Sum>v\<in>verts (mgg_graph n). f v * f v)"
    unfolding f'_def grid_integral[where f="\<lambda>x. (f x)^2"] by (simp add:power2_eq_square)
  also have "... = sqrt ((\<Sum>v\<in>verts (mgg_graph n). f v * f v))^2"
    by (intro real_sqrt_pow2[symmetric] sum_nonneg) auto
  also have "... \<le> 1^2"
    using assms(1) unfolding g_norm_def g_inner_def
    by (intro power_mono real_sqrt_ge_zero sum_nonneg) auto
  finally have "\<integral>\<omega>\<in>R2_space. (f' \<omega>^2) \<partial>lborel \<le> 1" by simp

  have "set_integrable lborel R2_space (\<lambda>\<omega>. f' \<omega>^2)"
    unfolding f'_def by (intro grid_integral[where f="\<lambda>x. (f x)^2"])




  show ?thesis sorry
qed


lemma mgg_numerical_radius: "numerical_rad \<le> MGG_bound"
proof -
  have "\<exists>x. g_norm x \<le> 1 \<and> g_inner x (\<lambda>_. 1) = 0" 
    unfolding g_norm_def g_inner_def by (intro exI[where x="\<lambda>_. 0"]) simp
  thus ?thesis
    using mgg_numerical_radius_aux
    unfolding numerical_rad_def setcompr_eq_image
    by (intro cSup_least) auto
qed


  (*
    Take a function defined on n



  *)







end

end