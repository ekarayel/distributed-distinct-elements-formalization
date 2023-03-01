theory Expander_Graphs_Cheeger_Inequality
  imports Expander_Graphs_Eigenvalues
begin

unbundle intro_cong_syntax
hide_const Quantum.T

context pre_expander_graph
begin

definition edges_betw where "edges_betw S T = {a \<in> arcs G. tail G a \<in> S \<and> head G a \<in> T}"

definition edge_expansion where "edge_expansion = 
  (MIN S\<in>{S. S\<subseteq>verts G\<and>2*card S\<le>n\<and>S\<noteq>{}}. real (card (edges_betw S (-S)))/card S)"

definition \<Phi> where "\<Phi> = (MIN S \<in> {S. S \<subseteq> verts G \<and> S \<noteq> {} \<and> S \<noteq> verts G}. 
  real (card (edges_betw S (-S))) * n / (real d * card S * (real n - card S)))"

lemma edges_betw_sym:
  "card (edges_betw S T) = card (edges_betw T S)" (is "?L = ?R")
proof -
  have "?L =  (\<Sum>a \<in> arcs G. of_bool (tail G a \<in> S \<and> head G a \<in> T))"
    unfolding edges_betw_def of_bool_def by (simp add:sum.If_cases Int_def)
  also have "... = (\<Sum>e \<in># edges G. of_bool (fst e \<in> S \<and> snd e \<in> T))"
    unfolding sum_unfold_sum_mset edges_def arc_to_ends_def
    by (simp add:image_mset.compositionality comp_def)
  also have "... =  (\<Sum>e \<in># edges G. of_bool (snd e \<in> S \<and> fst e \<in> T))"
    by (subst edges_sym[OF sym, symmetric]) 
        (simp add:image_mset.compositionality comp_def case_prod_beta)
  also have "... = (\<Sum>a \<in> arcs G. of_bool (tail G a \<in> T \<and> head G a \<in> S))"
    unfolding sum_unfold_sum_mset edges_def arc_to_ends_def
    by (simp add:image_mset.compositionality comp_def conj.commute)
  also have "... = ?R"
    unfolding edges_betw_def of_bool_def by (simp add:sum.If_cases Int_def)
  finally show ?thesis by simp
qed

lemma edges_betw_reg:
  assumes "S \<subseteq> verts G"
  shows "card (edges_betw S UNIV) = card S * d" (is "?L = ?R")
proof -
  have "?L = card (\<Union>(out_arcs G ` S))"
    unfolding edges_betw_def out_arcs_def by (intro arg_cong[where f="card"]) auto
  also have "... = (\<Sum>i\<in>S. card (out_arcs G i))"
    using finite_subset[OF assms] unfolding out_arcs_def
    by (intro card_UN_disjoint) auto
  also have "... = (\<Sum>i\<in>S. out_degree G i)"
    unfolding out_degree_def by simp
  also have "... = (\<Sum>i\<in>S. d)"
    using assms by (intro sum.cong reg) auto
  also have "... = ?R"
    by simp
  finally show ?thesis by simp
qed

text \<open>The following proof follows Hoory et al.~@{cite \<open>\S 4.5.1\<close> "hoory2006"}.\<close>

lemma cheeger_aux_2:
  assumes "n > 1"
  shows "edge_expansion \<ge> d*(1-\<Lambda>)/2"
proof -
  define St where "St = {S. S \<subseteq> verts G \<and> 2*card S \<le> n \<and> S \<noteq> {}}"
  have 0: "finite St"
    unfolding St_def
    by (rule finite_subset[where B="Pow (verts G)"]) auto 

  obtain v where v_def: "v \<in> verts G" using verts_non_empty by auto 

  have "{v} \<in> St" 
    using assms v_def unfolding St_def n_def by auto
  hence 1: "St \<noteq> {}" by auto

  have 2: "real (card (edges_betw S (-S))) / real (card S) \<ge> d * (1 - \<Lambda>) / 2" 
    if "S \<in> St" for S
  proof -
    have 3:"S \<subseteq> verts G"
      using that unfolding St_def by simp

    let ?ct = "real (card (verts G - S))" 
    let ?cs = "real (card S)" 

    have "card (edges_betw S S)+card (edges_betw S (-S))=card(edges_betw S S\<union>edges_betw S (-S))"
      unfolding edges_betw_def by (intro card_Un_disjoint[symmetric]) auto
    also have "... = card (edges_betw S UNIV)"
      unfolding edges_betw_def by (intro arg_cong[where f="card"]) auto
    also have "... = d * ?cs"
      using edges_betw_reg[OF 3] by simp
    finally have "card (edges_betw S S) + card (edges_betw S (-S)) = d * ?cs" by simp 
    hence 4: "card (edges_betw S S) = d * ?cs - card (edges_betw S (-S))"
      by simp

    have "card(edges_betw S(-S))+card(edges_betw(-S)(-S))=card(edges_betw S(-S)\<union>edges_betw(-S)(-S))"
      unfolding edges_betw_def by (intro card_Un_disjoint[symmetric]) auto
    also have "... = card (edges_betw UNIV (verts G - S))"
      unfolding edges_betw_def by (intro arg_cong[where f="card"]) auto
    also have "... = card (edges_betw (verts G - S) UNIV)"
      by (intro edges_betw_sym)
    also have "... = d * ?ct"
      using edges_betw_reg by auto
    finally have "card (edges_betw S (-S)) + card (edges_betw (-S) (-S)) = d * ?ct" by simp
    hence 5: "card (edges_betw (-S) (-S)) = d * ?ct - card (edges_betw S (-S))"
      by simp
    have 6: "card (edges_betw (-S) S) = card (edges_betw S (-S))" 
      by (intro edges_betw_sym)

    have "card S > 0" 
      using that finite_subset[OF 3] unfolding St_def by auto
    hence cs_gt_0: "?cs > 0" by simp

    have "?cs + ?ct =real (card (S \<union> (verts G- S)))"
      unfolding of_nat_add[symmetric] using finite_subset[OF 3]
      by (intro_cong "[\<sigma>\<^sub>1 of_nat, \<sigma>\<^sub>1 card]" more:card_Un_disjoint[symmetric]) auto
    also have "... = real n"
      unfolding n_def  using 3 by (intro_cong "[\<sigma>\<^sub>1 of_nat, \<sigma>\<^sub>1 card]") auto 
    finally have 7: "?cs + ?ct = n"  by simp


    define f  where 
      "f x = real (card (verts G - S)) * of_bool (x \<in> S) - card S * of_bool (x \<notin> S)" for x

    have "g_inner f (\<lambda>_. 1) = ?cs * ?ct - real (card (verts G \<inter> {x. x \<notin> S})) * ?cs"
      unfolding g_inner_def f_def using Int_absorb1[OF 3] by (simp add:sum_subtractf)
    also have "... = ?cs * ?ct - ?ct * ?cs"
      by (intro_cong "[\<sigma>\<^sub>2 (-), \<sigma>\<^sub>2 (*), \<sigma>\<^sub>1 of_nat, \<sigma>\<^sub>1 card]") auto
    also have "... = 0" by simp
    finally have 11:" g_inner f (\<lambda>_. 1) = 0" by simp

    have "g_norm f^2 = (\<Sum>v\<in>verts G. f v^2)"
      unfolding g_norm_sq g_inner_def conjugate_real_def by (simp add:power2_eq_square)
    also have "...=(\<Sum>v\<in>verts G. ?ct^2*(of_bool (v \<in> S))\<^sup>2)+(\<Sum>v\<in>verts G. ?cs^2*(of_bool (v \<notin> S))\<^sup>2)"
      unfolding f_def power2_diff by (simp add:sum.distrib sum_subtractf power_mult_distrib)
    also have "... = real (card (verts G \<inter> S))*?ct^2 + real (card (verts G \<inter> {v. v \<notin> S})) * ?cs^2"
      unfolding of_bool_def by (simp add:if_distrib if_distribR sum.If_cases)
    also have "... = real(card S)*(real(card(verts G-S)))\<^sup>2 + real(card(verts G-S))*(real(card S))\<^sup>2"
      using 3 by (intro_cong "[\<sigma>\<^sub>2(+), \<sigma>\<^sub>2 (*), \<sigma>\<^sub>2 power, \<sigma>\<^sub>1 of_nat, \<sigma>\<^sub>1 card]") auto
    also have "...  = real(card S)*real (card (verts G -S))*(?cs + ?ct)"
      by (simp add:power2_eq_square algebra_simps)
    also have "...  = real(card S)*real (card (verts G -S))*n"
      unfolding 7 by simp
    finally have 9:" g_norm f^2 = real(card S)*real (card (verts G -S))*real n" by simp

    have "(\<Sum>a \<in> arcs G. f (head G a) * f (tail G a)) = 
      (card (edges_betw S S) * ?ct*?ct) + (card (edges_betw (-S) (-S)) * ?cs*?cs) - 
      (card (edges_betw S (-S)) * ?ct*?cs) - (card (edges_betw (-S) S) * ?cs*?ct)"
      unfolding f_def by (simp add:of_bool_def algebra_simps Int_def if_distrib if_distribR 
          edges_betw_def sum.If_cases)
    also have "... = d*?cs*?ct*(?cs+?ct) - card (edges_betw S (-S))*(?ct*?ct+2*?ct*?cs+?cs*?cs)"
      unfolding 4 5 6 by (simp add:algebra_simps)
    also have "... = d*?cs*?ct*n - (?ct+?cs)^2 * card (edges_betw S (-S))"
      unfolding power2_diff 7 power2_sum by (simp add:ac_simps power2_eq_square)
    also have "... = d *?cs*?ct*n - n^2 * card (edges_betw S (-S))"
      using 7 by (simp add:algebra_simps)
    finally have 8:"(\<Sum>a \<in> arcs G. f(head G a)*f(tail G a))=d*?cs*?ct*n-n^2*card(edges_betw S (-S))" 
      by simp

    have "d*?cs*?ct*n-n^2*card(edges_betw S (-S)) = (\<Sum>a \<in> arcs G. f (head G a) * f (tail G a))"
      unfolding 8 by simp
    also have "... \<le> \<bar>\<Sum>a \<in> arcs G. f (head G a) * f (tail G a)\<bar>"
      by simp
    also have "... \<le> d * \<Lambda> * g_norm f^2" 
      by (intro expansionD 11)
    also have "... = d * \<Lambda> * ?cs*?ct*n"
      unfolding 9 by simp
    finally have "d*?cs*?ct*n-n^2*card(edges_betw S (-S)) \<le> d * \<Lambda> * ?cs*?ct*n" 
      by simp
    hence "n * n * card (edges_betw S (-S)) \<ge> n * (d * ?cs * ?ct * (1-\<Lambda>))"
      by (simp add:power2_eq_square algebra_simps)
    hence 10:"n * card (edges_betw S (-S)) \<ge> d * ?cs * ?ct * ( 1-\<Lambda>)"
      using n_gt_0 by simp 

    have "d * (1 - \<Lambda>) / 2 = d * (1-\<Lambda>) * (1 - 1 / 2)"
      by simp
    also have "... \<le> d * (1-\<Lambda>) * ((n - ?cs) / n)"
      using that n_gt_0 \<Lambda>_le_1 unfolding St_def
      by (intro mult_left_mono mult_nonneg_nonneg) auto
    also have "... = d * (1-\<Lambda>) * ?ct / n"
      using 7 by simp
    also have "... = d * ?cs * ?ct * (1-\<Lambda>) / (n * ?cs)"
      using cs_gt_0 by simp
    also have "... \<le> n * card (edges_betw S (-S)) / (n * ?cs)"
      by (intro divide_right_mono 10) auto
    also have "... = card (edges_betw S (-S)) / ?cs"
      using n_gt_0 by simp
    finally show ?thesis by simp
  qed

  thus "edge_expansion \<ge> d*(1-\<Lambda>)/2"
    unfolding edge_expansion_def St_def[symmetric] using 0 1 2
    by (intro Min.boundedI) auto
qed

end

context pre_expander_graph_tts
begin

text \<open>Normalized Laplacian of the graph\<close>
definition L where "L = mat 1 - A"

text \<open>The following proof follows Hoory et al.~@{cite \<open>\S 4.5.2\<close> "hoory2006"}.\<close>

lemma cheeger_aux_1:
  assumes "n > 1"
  shows "edge_expansion \<le> d* sqrt (2 * (1-\<Lambda>))"
proof -
  obtain v \<alpha> where v_def: "v \<bullet> 1 = 0" "\<bar>\<alpha>\<bar> = \<Lambda>\<^sub>e TYPE('n)" "v \<noteq> 0" "A *v v = \<alpha> *s v"
    using \<gamma>\<^sub>2_real_ev[OF assms] by auto

  have "False" if "2*card {i. (1 *s v) $h i > 0} > n" "2*card {i. ((-1) *s v) $h i > 0} > n"
  proof -
    have "2 * n = n + n" by simp
    also have "... <2 * card {i.  (1 *s v) $h i > 0} + 2 * card {i. ((-1) *s v) $h i > 0}"
      by (intro add_strict_mono that)
    also have "... = 2 * (card {i.  (1 *s v) $h i > 0} + card {i.  ((-1) *s v) $h i > 0})"
      by simp
    also have "... = 2 * (card ({i.  (1 *s v) $h i > 0} \<union> {i.  ((-1) *s v) $h i > 0}))"
      by (intro arg_cong2[where f="(*)"] card_Un_disjoint[symmetric]) auto
    also have "... \<le> 2 * (card (UNIV :: 'n set))"
      by (intro mult_left_mono card_mono) auto
    finally have "2 * n < 2 * n" 
      unfolding n_def card_n by auto
    thus ?thesis by simp
  qed
  then obtain \<beta>  :: real where \<beta>_def: "\<beta> = 1 \<or> \<beta>=(-1)" "2* card {i. (\<beta> *s v) $h i > 0 } \<le> n"
    unfolding not_le[symmetric] by blast

  define g where "g = \<beta> *s v"

  have g_orth: "g \<bullet> 1 = 0" unfolding g_def using v_def(1) 
    by (simp add: scalar_mult_eq_scaleR)
  have g_nz: "g \<noteq> 0" 
    unfolding g_def using \<beta>_def(1) v_def(3) by auto
  have g_ev: "A *v g = \<alpha> *s g"
    unfolding g_def scalar_mult_eq_scaleR matrix_vector_mult_scaleR v_def(4) by auto
  have g_supp: "2 * card { i. g $h i > 0 } \<le> n"
    unfolding g_def using \<beta>_def(2) by auto

  define f where "f = (\<chi> i. max (g $h i) 0)"


  (* -(L f)_i = A f_i - f_i    *)

  have "(L *v f) $h i \<le> (1-\<Lambda>) * g $h i" (is "?L \<le> ?R") if "g $h i > 0" for i
  proof -
    have "?L = f $h i - (A *v f) $h i"
      unfolding L_def by (simp add:algebra_simps)
    also have "... = g $h i - (\<Sum>j \<in> UNIV. A $h i $h j * f $h j)"
      unfolding matrix_vector_mult_def f_def using that by auto
    also have "... \<le> g $h i - (\<Sum>j \<in> UNIV. A $h i $h j * g $h j)"
      unfolding f_def A_def by (intro diff_mono sum_mono mult_left_mono) auto
    also have "... = g $h i - (A *v g) $h i" 
      unfolding matrix_vector_mult_def by simp
    also have "... = (1-\<alpha>) * g $h i"
      unfolding g_ev by (simp add:algebra_simps)
    show ?thesis
      sorry
  qed


  text \<open>Part (i) in Hoory et al. but the operator L here is normalized.\<close>
  have "f \<bullet> (L *v f) \<le> (1 - \<Lambda>) * norm f^2"
    sorry



  show ?thesis
    sorry
qed


end

unbundle no_intro_cong_syntax

end