theory Expander_Graphs_Eigenvalues
  imports 
    Expander_Graphs_Definition
    Commuting_Hermitian.Commuting_Hermitian
begin

hide_const "Matrix_Legacy.mat"
hide_const "Matrix_Legacy.row"
hide_const "Matrix_Legacy.col"
hide_const "Matrix_Legacy.vec"
hide_const "Matrix_Legacy.scalar_prod"
hide_const "Finite_Cartesian_Product.row"
hide_const "Finite_Cartesian_Product.mat"
hide_const "Finite_Cartesian_Product.vec"
unbundle no_inner_syntax
unbundle no_vec_syntax

lemma to_nat_on_from_nat_into': 
  assumes "n < card A" "finite A"
  shows "to_nat_on A (from_nat_into A n) = n"
  using assms(1) to_nat_on_finite[OF assms(2)] unfolding bij_betw_def
  by (intro to_nat_on_from_nat_into) auto

lemma mult_right_mono': "y \<ge> (0::real) \<Longrightarrow> x \<le> x2 \<or> y = 0  \<Longrightarrow> x * y \<le> x2 * y"  
  by (metis mult_cancel_right mult_right_mono)

text \<open>Counterpart to @{thm [source] col_map_mat}\<close>

lemma row_map_mat[simp]:
  assumes "j < dim_row A" shows "row (map_mat f A) j = map_vec f (row A j)"
  unfolding map_mat_def map_vec_def using assms by auto

definition r_norm_vec where "r_norm_vec v = sqrt (\<Sum>i < dim_vec v. norm (vec_index v i)^2)"

lemma r_norm_vec_nonneg:
  "r_norm_vec v \<ge> 0"
  unfolding r_norm_vec_def
  by (intro real_sqrt_ge_zero sum_nonneg) auto

lemma r_norm_vec_of_real: 
  assumes "v \<in> carrier_vec n"
  shows "r_norm_vec (map_vec complex_of_real v) = r_norm_vec v"
  unfolding r_norm_vec_def using assms
  by (intro arg_cong[where f="sqrt"] sum.cong) auto

lemma r_norm_vec_0_iff:
  assumes "v \<in> carrier_vec n"
  shows "r_norm_vec v = 0 \<longleftrightarrow> v = 0\<^sub>v n"
proof -
  have 0:"r_norm_vec v^2 = (\<Sum>i < dim_vec v. norm (vec_index v i)^2)"
    unfolding r_norm_vec_def by (intro real_sqrt_pow2 sum_nonneg) auto
  have "r_norm_vec v = 0 \<longleftrightarrow> r_norm_vec v^2 = 0"
    by simp 
  also have "... \<longleftrightarrow>(\<Sum>i < n. norm (vec_index v i)^2) = 0"
    unfolding 0 using assms by simp
  also have "... \<longleftrightarrow>(\<forall>i \<in>{..< n}. norm (vec_index v i)^2 = 0)"
    by (intro sum_nonneg_eq_0_iff) auto
  also have "... \<longleftrightarrow>(\<forall>i \<in>{..< n}. vec_index v i = 0)"
    by auto
  also have "... \<longleftrightarrow> v = 0\<^sub>v n"
    using assms by auto
  finally  show ?thesis by simp
qed

lemma norm_vec_sq_complex: 
  fixes v :: "complex  Matrix.vec"
  assumes "v \<in> carrier_vec n"
  shows "r_norm_vec v^2 = v \<bullet>c v"
proof -
  have "complex_of_real (r_norm_vec v^2) = of_real (\<Sum>i < dim_vec v. cmod (vec_index v i)^2)"
    unfolding r_norm_vec_def 
    by (intro real_sqrt_pow2 sum_nonneg arg_cong[where f="complex_of_real"]) auto
  also have "... = (\<Sum>i < n. of_real (cmod (vec_index v i)^2))"
    using assms by simp
  also have "... = v \<bullet>c v"
    using assms unfolding complex_norm_square
    by (simp add:scalar_prod_def atLeast0LessThan)
  finally show ?thesis by simp
qed

lemma unitary_iso:
  fixes v :: "complex Matrix.vec"
  fixes U :: "complex Matrix.mat"
  assumes "unitary U" "U \<in> carrier_mat n n"
  assumes "v \<in> carrier_vec n"
  shows "r_norm_vec (U *\<^sub>v v) = r_norm_vec v"
proof -
  have "of_real (r_norm_vec (U *\<^sub>v v)^2) = (U *\<^sub>v v) \<bullet>c (U *\<^sub>v v)"
    using assms(2,3) by (intro norm_vec_sq_complex mult_mat_vec_carrier) auto
  also have "... = v \<bullet>c v"
    using assms by (intro unitary_inner_prod) auto
  also have "... = r_norm_vec v^2"
    using assms(3) by (intro norm_vec_sq_complex[symmetric]) auto
  finally have "r_norm_vec (U *\<^sub>v v)^2 = r_norm_vec v^2"
    using inj_of_real unfolding inj_on_def  by blast
  thus ?thesis
    using r_norm_vec_nonneg power2_eq_imp_eq by auto
qed

lemma norm_vec_sq_real: 
  fixes v :: "real  Matrix.vec"
  assumes "v \<in> carrier_vec n"
  shows "r_norm_vec v^2 = v \<bullet> v"
proof -
  have "r_norm_vec v^2 = (\<Sum>i < dim_vec v. norm (vec_index v i)^2)"
    unfolding r_norm_vec_def by (intro real_sqrt_pow2 sum_nonneg) auto
  also have "... = (\<Sum>i < dim_vec v. vec_index v i * vec_index v i)"
    by (simp add: power2_eq_square)
  also have "... =  v \<bullet> v"
    using assms by (simp add:scalar_prod_def atLeast0LessThan)
  finally show ?thesis by simp
qed

lemma diag_mat_mult:
  assumes "diagonal_mat A" "A \<in> carrier_mat n n" "v \<in> carrier_vec n"
  shows "A *\<^sub>v v = vec n (\<lambda>k. (diag_mat A) ! k * vec_index v k)" 
    (is "?L = ?R")
proof -
  have "vec_index (A *\<^sub>v v) k = diag_mat A ! k * vec_index v k" if " k< n" for k
  proof -
    have "vec_index (A *\<^sub>v v) k = (\<Sum>i = 0..<n. A $$ (k, i) * vec_index v i)"
      using assms(2,3) that by (simp add:scalar_prod_def)
    also have "... = (\<Sum>i \<in> {k}. A $$ (k, i) * vec_index v i)"
      using that assms(1,2) unfolding diagonal_mat_def
      by (intro sum.mono_neutral_right ballI) auto
    also have "... = A $$ (k, k) * vec_index v k"
      by simp
    also have "... = diag_mat A ! k * vec_index v k"
      using assms(2) that unfolding diag_mat_def by (simp)
    finally show ?thesis by simp
  qed
  thus ?thesis
    using assms by (intro eq_vecI) auto
qed

lemma veq_eq_iff: 
  assumes "v \<in> carrier_vec n" "w \<in> carrier_vec n"
  shows "v = w \<longleftrightarrow> (\<forall>i < n. vec_index v i = vec_index w i)"
  using assms by (intro iffI eq_vecI, auto)

lemma count_mset_exp: "count A x = size (filter_mset (\<lambda>y. y = x) A)"
  by (induction A, simp, simp)

lemma mset_repl: "mset (replicate k x) = replicate_mset k x"
  by (induction k, auto)

lemma mset_nths_union: 
  assumes "I \<inter> J = {}"
  shows "mset (nths xs I) + mset (nths xs J) = mset (nths xs (I \<union> J))"
  using assms by (induction xs rule:rev_induct, auto simp add:nths_append)

lemma nths_single:
  "nths xs {i} = (if i < length xs then [xs ! i] else [])"
proof (induction xs rule:rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  have "nths (xs @ [x]) {i} = nths xs {i} @ nths [x] {j. j + length xs \<in> {i}}"
    unfolding nths_append by simp
  also have "... = (if i < length xs then [xs ! i] else []) @ (if i = length xs then [x] else [])"
    unfolding snoc by (intro arg_cong2[where f="(@)"] refl) simp
  also have "... = (if i < length (xs@[x]) then [(xs@[x]) ! i] else [])"
    by (simp add:nth_append)
  finally show ?case by simp
qed

lemma unitaryI:
  assumes "A \<in> carrier_mat n n"
  assumes "A * mat_adjoint A = 1\<^sub>m n"
  shows "unitary A"
  using assms unfolding unitary_def inverts_mat_def by simp

lemma unitaryI2:
  assumes "A \<in> carrier_mat n n"
  assumes "mat_adjoint A * A = 1\<^sub>m n"
  shows "unitary A"
  using assms(1,2) mat_mult_left_right_inverse adjoint_dim
  by (intro unitaryI[OF assms(1)]) blast

lemma poly_prod_zero:
  fixes x :: "'a :: idom"
  assumes "poly (\<Prod>a\<in>#xs. [:- a, 1:]) x = 0"
  shows "x \<in># xs"
  using assms by (induction xs, auto)

lemma poly_prod_inj_aux_1:
  fixes xs ys :: "('a :: idom) multiset"
  assumes "x \<in># xs"
  assumes "(\<Prod>a\<in>#xs. [:- a, 1:]) = (\<Prod>a\<in>#ys. [:- a, 1:])"
  shows "x \<in># ys"
proof -
  have "poly (\<Prod>a\<in>#ys. [:- a, 1:]) x = poly (\<Prod>a\<in>#xs. [:- a, 1:]) x" using assms(2) by simp
  also have "... = poly (\<Prod>a\<in>#xs - {#x#} + {#x#}. [:- a, 1:]) x"
    using assms(1) by simp
  also have "... = 0"
    by simp
  finally have "poly (\<Prod>a\<in>#ys. [:- a, 1:]) x = 0" by simp
  thus "x \<in># ys" using poly_prod_zero by blast
qed

lemma poly_prod_inj_aux_2:
  fixes xs ys :: "('a :: idom) multiset"
  assumes "x \<in># xs \<union># ys"
  assumes "(\<Prod>a\<in>#xs. [:- a, 1:]) = (\<Prod>a\<in>#ys. [:- a, 1:])"
  shows "x \<in># xs \<inter># ys"
proof (cases "x \<in># xs")
  case True
  then show ?thesis using poly_prod_inj_aux_1[OF True assms(2)] by simp
next
  case False
  hence a:"x \<in># ys"
    using assms(1) by simp
  then show ?thesis 
    using poly_prod_inj_aux_1[OF a assms(2)[symmetric]] by simp
qed

lemma poly_prod_inj:
  fixes xs ys :: "('a :: idom) multiset"
  assumes "(\<Prod>a\<in>#xs. [:- a, 1:]) = (\<Prod>a\<in>#ys. [:- a, 1:])"
  shows "xs = ys"
  using assms
proof (induction "size xs + size ys" arbitrary: xs ys rule:nat_less_induct)
  case 1
  show ?case
  proof (cases "xs \<union># ys = {#}")
    case True
    then show ?thesis by simp
  next
    case False
    then obtain x where "x \<in># xs \<union># ys" by auto
    hence a:"x \<in># xs \<inter># ys"
      by (intro poly_prod_inj_aux_2[OF _ 1(2)])
    have b: "[:- x, 1:] \<noteq> 0" 
      by simp
    have c: "size (xs-{#x#}) + size (ys-{#x#}) < size xs + size ys" 
      using a by (simp add: add_less_le_mono size_Diff1_le size_Diff1_less)

    have "[:- x, 1:] * (\<Prod>a\<in>#xs - {#x#}. [:- a, 1:]) = (\<Prod>a\<in>#xs. [:- a, 1:])"
      using a by (subst prod_mset.insert[symmetric]) simp
    also have "... = (\<Prod>a\<in>#ys. [:- a, 1:])" using 1 by simp
    also have "... = [:- x, 1:] * (\<Prod>a\<in>#ys - {#x#}. [:- a, 1:])"
      using a by (subst prod_mset.insert[symmetric]) simp
    finally have "[:- x, 1:]*(\<Prod>a\<in>#xs-{#x#}. [:- a, 1:])=[:-x, 1:]*(\<Prod>a\<in>#ys-{#x#}. [:- a, 1:])"
      by simp
    hence "(\<Prod>a\<in>#xs-{#x#}. [:- a, 1:]) = (\<Prod>a\<in>#ys-{#x#}. [:- a, 1:])" 
      using mult_left_cancel[OF b] by simp
    hence d:"xs - {#x#} = ys - {#x#}"
      using 1 c by simp
    have "xs = xs - {#x#} + {#x#}"
      using a by simp
    also have "... = ys - {#x#} + {#x#}"
      unfolding d by simp
    also have "... = ys"
      using a by simp
    finally show ?thesis by simp
  qed
qed

lemma char_poly_eigvals:
  fixes A B :: "complex Matrix.mat"
  assumes "A \<in> carrier_mat n n" "B \<in> carrier_mat n n"
  assumes "char_poly A = char_poly B"
  shows "mset (eigvals A) = mset (eigvals B)"
proof -
  have "(\<Prod>a\<leftarrow>eigvals A. [:- a, 1:]) = (\<Prod>a\<leftarrow>eigvals B. [:- a, 1:])"
    using assms eigvals_poly_length by simp
  hence "(\<Prod>a\<in>#mset (eigvals A). [:- a, 1:]) = (\<Prod>a\<in>#mset (eigvals B). [:- a, 1:])"
    unfolding mset_map[symmetric] prod_mset_prod_list by simp
  thus ?thesis
    by (intro poly_prod_inj) simp
qed

(* A = U B U^{-1} *)

lemma similar_mat_eigvals:
  fixes A B :: "complex Matrix.mat"
  assumes  "similar_mat A B"
  shows "mset (eigvals A) = mset (eigvals B)"
  using similar_matD[OF assms(1)]
  by (intro char_poly_eigvals char_poly_similar assms) auto

lemma upper_tri_eigvals:
  fixes A :: "complex Matrix.mat"
  assumes "A \<in> carrier_mat n n"
  assumes "upper_triangular A"
  shows "mset (eigvals A) = mset (diag_mat A)"
proof -
  have "(\<Prod>a\<leftarrow>eigvals A. [:- a, 1:]) = char_poly A"
    using  eigvals_poly_length assms by simp
  also have "... = (\<Prod>a\<leftarrow>diag_mat A. [:- a, 1:])"
    by (intro char_poly_upper_triangular[OF assms(1,2)])
  finally have "(\<Prod>a\<leftarrow>eigvals A. [:- a, 1:]) =  (\<Prod>a\<leftarrow>diag_mat A. [:- a, 1:])"
    by simp
  hence "(\<Prod>a\<in>#mset (eigvals A). [:- a, 1:]) = (\<Prod>a\<in>#mset (diag_mat  A). [:- a, 1:])"
    unfolding mset_map[symmetric] prod_mset_prod_list by simp
  thus ?thesis
    by (intro poly_prod_inj) simp
qed

lemma eigenvalue_in_eigvals:
  fixes A :: "complex Matrix.mat"
  assumes "A \<in> carrier_mat n n"
  assumes "eigenvalue A \<alpha>"
  shows "\<alpha> \<in> set (eigvals A)"
proof -
  have "poly (\<Prod>a\<in>#mset (eigvals A). [:- a, 1:]) \<alpha> = poly (\<Prod>a\<leftarrow>eigvals A. [:- a, 1:]) \<alpha>"
    unfolding mset_map[symmetric] prod_mset_prod_list by simp
  also have "... = poly (char_poly A) \<alpha>"
    using  eigvals_poly_length assms by simp
  also have "... = 0"
    using eigenvalue_root_char_poly[OF assms(1)] assms(2) by simp
  finally have "poly (\<Prod>a\<in>#mset (eigvals A). [:- a, 1:]) \<alpha> = 0"
    by simp
  hence "\<alpha> \<in># mset (eigvals A)"
    using poly_prod_zero by blast
  thus ?thesis
    by simp
qed

locale pre_expander_graph_spectral = pre_expander_graph
begin

definition enum_verts :: "nat \<Rightarrow> 'a" 
  where "enum_verts = from_nat_into (verts G)"

lemma enum_verts:
  "bij_betw enum_verts {..<n} (verts G)"
  unfolding enum_verts_def n_def
  using bij_betw_from_nat_into_finite[OF finite_verts] by blast

definition A :: "('c :: field)  Matrix.mat" where 
  "A = Matrix.mat n n (\<lambda> (i, j). of_nat (count (edges G) (enum_verts j,enum_verts i)) / (of_nat d))"

lemma A_mat: "A \<in> carrier_mat n n"
  unfolding A_def by simp

lemma A_dim[simp]: "dim_row A = n" "dim_col A = n"
  using A_mat by auto

lemma count_sym:
  "count (edges G) (u,v) = count (edges G) (v,u)"
  unfolding count_mset_exp edges_def image_mset_filter_mset_swap[symmetric] arc_to_ends_def
  using symmetric_multi_graphD3[OF sym] by simp

lemma A_sym: "hermitian (A :: complex Matrix.mat)"
  unfolding hermitian_def using A_mat
  by (intro eq_matI)  (auto simp add:adjoint_eval adjoint_dim A_def count_sym) 

text \<open>We set @{term "\<gamma>\<^sub>2"} to the second largest absolute eigenvalue (taking multiplicities into 
account). It should be noted that this is only well-defined if the graph has more than one vertex. 
We define @{term "\<gamma>\<^sub>2"} to be @{term "0"} otherwise.\<close>

definition \<gamma>\<^sub>2 
  where "\<gamma>\<^sub>2 = Max_mset (image_mset norm (mset (eigvals A) - {#(1::complex)#})+{#0#})"

lemma \<gamma>\<^sub>2_nonneg: "\<gamma>\<^sub>2 \<ge> 0" 
  unfolding \<gamma>\<^sub>2_def by simp

definition unit :: "('c :: field) Matrix.vec"
  where "unit = Matrix.vec n (\<lambda>_. 1/of_nat n)"

lemma unit_vec: "unit \<in> carrier_vec n"
  unfolding unit_def by simp

lemma A_row_unit:
  assumes "i < n"
  shows  "(Matrix.row A i) \<bullet> unit = (1::complex)/of_nat n" (is "?L = ?R")
proof -
  have "?L = (\<Sum>j<n. of_nat (count (edges G)(enum_verts j, enum_verts i))/(of_nat d * of_nat n))"
    using assms unfolding A_def unit_def by (simp add:scalar_prod_def atLeast0LessThan)
  also have "...=(\<Sum>j\<in>enum_verts`{..<n}. of_nat(count (edges G)(j,enum_verts i))/(of_nat d* of_nat n))"
    using bij_betw_imp_inj_on[OF enum_verts] by (subst sum.reindex, simp_all add:comp_def)
  also have "... = of_nat (\<Sum>v\<in>verts G. count (edges G) (v,enum_verts i))/(of_nat d* of_nat n)"
    using bij_betw_imp_surj_on[OF enum_verts]
    by (simp add:sum_divide_distrib)
  also have "...= of_nat(\<Sum>v\<in>verts G. card {a \<in> arcs G. tail G a=v \<and> head G a = enum_verts i}) 
    / (of_nat d * of_nat n)"
    unfolding count_mset_exp edges_def image_mset_filter_mset_swap[symmetric] arc_to_ends_def
    by simp
  also have "... = of_nat(card (\<Union>v \<in> verts G.{a \<in> arcs G. tail G a=v \<and> head G a = enum_verts i}))
    / (of_nat d * of_nat n)"
    by (subst card_UN_disjoint) auto
  also have "... = of_nat (in_degree G (enum_verts i)) / (of_nat d * of_nat n)"
    unfolding in_degree_def
    by (intro arg_cong2[where f="(/)"] arg_cong[where f="of_nat"]  arg_cong[where f="card"]) auto
  also have "... = of_nat d  / (of_nat d * of_nat n)"
    using assms by (intro arg_cong2[where f="(/)"] arg_cong[where f="of_nat"] reg 
        bij_betw_apply[OF enum_verts]) auto
  also have "... = ?R" using d_gt_0 by simp 
  finally show ?thesis by simp 
qed

lemma A_markov: 
  "A *\<^sub>v unit = (unit :: complex Matrix.vec)"
  "eigenvector A unit (1::complex)"
  "eigenvalue A (1::complex)"
  "(1::complex) \<in> set (eigvals A)"
proof -
  have [simp]:"dim_row A = n" 
    using A_mat by auto

  have "scalar_prod (Matrix.row A i) unit = (vec_index unit i :: complex)" if "i < n" for i
    unfolding A_row_unit[OF that] using that unfolding unit_def by simp
  thus "A *\<^sub>v unit = (unit :: complex Matrix.vec)"
    using A_mat[where 'c="complex"] unit_vec[where 'c="complex"]
    by (intro eq_vecI) auto
  moreover have "unit \<noteq> (0\<^sub>v n :: complex Matrix.vec)" 
    using n_gt_0 unfolding unit_def by (auto simp add:veq_eq_iff)
  ultimately show "eigenvector A unit (1::complex)"
    using unit_vec A_mat
    unfolding eigenvector_def by simp
  thus "eigenvalue A (1::complex)"
    unfolding eigenvalue_def by blast
  thus "(1::complex) \<in> set (eigvals A)" 
    using eigenvalue_in_eigvals[OF A_mat] by simp
qed

lemma 
  assumes "n > 1"
  shows \<gamma>\<^sub>2_iff_n_gt_1: "\<gamma>\<^sub>2 = Max_mset (image_mset norm (mset (eigvals A) - {#1::complex#}))"
    and find_\<gamma>\<^sub>2: "\<gamma>\<^sub>2 \<in># image_mset norm (mset (eigvals A) - {#1::complex#})"
proof -
  have "length (eigvals A :: complex list) = n"
    using A_mat eigvals_poly_length by auto
  moreover have "(1::complex) \<in># mset (eigvals A)"
    using A_markov by simp
  ultimately have "size (mset (eigvals A) - {#(1::complex)#}) = n -1"
    by (simp add: size_Diff_singleton)
  hence "set_mset (mset (eigvals A) - {#(1::complex)#}) \<noteq> {}"
    using assms by auto
  hence 2: "norm ` set_mset (mset (eigvals A) - {#(1::complex)#}) \<noteq> {}"
    by simp
  have "\<gamma>\<^sub>2 = Lattices_Big.Max ((norm ` set_mset (mset (eigvals A) - {#(1::complex)#})) \<union> {0})"
    unfolding \<gamma>\<^sub>2_def by simp
  also have "... = max (Lattices_Big.Max (norm ` set_mset (mset (eigvals A) - {#(1::complex)#}))) (Lattices_Big.Max {0})"
    using 2 by (intro Max_Un finite_imageI) auto
  also have "... = max (Lattices_Big.Max (norm ` set_mset (mset (eigvals A) - {#(1::complex)#}))) 0"
    by simp
  also have "... = Lattices_Big.Max (norm ` set_mset (mset (eigvals A) - {#(1::complex)#}))"
    using Max_in[OF _ 2] by (intro max_absorb1) auto
  also have "... = Max_mset (image_mset norm (mset (eigvals A) - {#(1::complex)#}))"
    by simp
  finally show 3:"\<gamma>\<^sub>2 = Max_mset (image_mset norm (mset (eigvals A) - {#(1::complex)#}))"
    by simp
  have "\<gamma>\<^sub>2 \<in> set_mset (image_mset norm (mset (eigvals A) - {#1::complex#}))"
    unfolding 3 using 2 by (intro Max_in) auto
  thus "\<gamma>\<^sub>2 \<in># image_mset norm (mset (eigvals A) - {#1::complex#})"
    by simp
qed

lemma \<gamma>\<^sub>2_eq_0:
  assumes "n = 1"
  shows "\<gamma>\<^sub>2 = 0"
proof -
  have "length (eigvals A :: complex list) = 1"
    using A_mat eigvals_poly_length assms by auto
  hence "size (mset (eigvals A :: complex list)) = 1" by simp
  moreover have "(1::complex) \<in># mset (eigvals A)"
    using A_markov by simp
  ultimately have "mset (eigvals A) = {#(1::complex)#}"
    by (metis add_mset_eq_single diff_single_eq_union size_1_singleton_mset)
  thus ?thesis
    unfolding \<gamma>\<^sub>2_def by simp
qed

definition K :: "complex Matrix.mat"
  where "K = Matrix.mat n n (\<lambda> (i,j). 1/n)"

lemma K_mat: "K \<in> carrier_mat n n"
  unfolding K_def by simp

lemma K_sym: "hermitian K"
  unfolding K_def hermitian_def
  by (intro eq_matI) (auto simp add:adjoint_eval adjoint_dim)

lemma K_eigvals: "mset (eigvals K) = {#1#} + replicate_mset (n - 1) 0"
proof -
  define \<alpha> :: "nat \<Rightarrow> real" where "\<alpha> i = (sqrt (i^2+i))" for i :: nat

  define q :: "nat \<Rightarrow> nat \<Rightarrow> real"
    where "q i j = (
        if i = 0 then (1/sqrt n) else (
        if j < i then ((-1) / \<alpha> i) else (
        if j = i then (i / \<alpha> i) else 0)))" for i j

  define Q :: "complex Matrix.mat" where "Q = Matrix.mat n n (\<lambda> (i,j). complex_of_real (q i j))"

  define D :: "complex Matrix.mat" where 
    "D = Matrix.mat n n (\<lambda>(i,j). if i = 0 \<and> j = 0 then 1 else 0)"

  have Q_mat: "Q \<in> carrier_mat n n" "mat_adjoint Q \<in> carrier_mat n n"
    using adjoint_dim unfolding Q_def by auto

  have D_mat: "D \<in> carrier_mat n n"
    unfolding D_def by simp

  have 2: "[0..<n] = 0#[1..<n]"
    using n_gt_0 upt_conv_Cons by auto

  have 0: "(\<Sum>k = 0..<n. q j k * q i k) = of_bool (i = j)" if 1:"i \<le> j" "j < n"  for i j
  proof -
    consider (a) "i = j \<and> j = 0" | (b) "i = 0 \<and> i < j" | (c) " 0 < i \<and> i < j" | (d) "0 < i \<and> i = j"
      using 1 by linarith
    thus ?thesis
    proof (cases)
      case a
      then show ?thesis using n_gt_0 by (simp add:q_def)
    next
      case b
      have "(\<Sum>k = 0..<n. q j k*q i k)=(\<Sum>k\<in>insert j ({0..<j} \<union> {j+1..<n}). q j k*q i k)"
        using that(2) by (intro sum.cong) auto
      also have "...=q j j*q i j+(\<Sum>k=0..<j. q j k * q i k)+(\<Sum>k=j+1..<n. q j k * q i k)"
        by (subst sum.insert) (auto simp add: sum.union_disjoint)
      also have "... = 0" using b unfolding q_def by simp
      finally show ?thesis using b by simp
    next
      case c
      have "(\<Sum>k = 0..<n. q j k*q i k)=(\<Sum>k\<in>insert i ({0..<i} \<union> {i+1..<n}). q j k*q i k)"
        using that(2) c by (intro sum.cong) auto
      also have "...=q j i*q i i+(\<Sum>k=0..<i. q j k * q i k)+(\<Sum>k=i+1..<n. q j k * q i k)"
        by (subst sum.insert) (auto simp add: sum.union_disjoint)
      also have "... =(-1) / \<alpha> j * i / \<alpha> i+ i * ((-1) / \<alpha> j *  (-1) / \<alpha> i)"
        using c unfolding q_def by simp
      also have "... = 0"
        by (simp add:algebra_simps)
      finally show ?thesis using c by simp
    next
      case d
      have "real i + real i^2 = real (i + i^2)" by simp
      also have "... \<noteq> real 0" 
        unfolding of_nat_eq_iff using d by simp
      finally have d_1: "real i  + real i^2 \<noteq> 0" by simp
      have "(\<Sum>k = 0..<n. q j k*q i k)=(\<Sum>k\<in>insert i ({0..<i} \<union> {i+1..<n}). q j k*q i k)"
        using that(2) d by (intro sum.cong) auto
      also have "...=q j i*q i i+(\<Sum>k=0..<i. q j k * q i k)+(\<Sum>k=i+1..<n. q j k * q i k)"
        by (subst sum.insert) (auto simp add: sum.union_disjoint)
      also have "... = i/ \<alpha> i * i / \<alpha> i+ i * ((-1) / \<alpha> i *  (-1) / \<alpha> i)"
        using d that unfolding q_def by simp
      also have "... = (i^2 + i) / (\<alpha> i)^2"
        by (simp add: power2_eq_square divide_simps)
      also have "... = 1"
        using d_1 unfolding \<alpha>_def by (simp add:algebra_simps) 
      finally show ?thesis using d by simp
    qed
  qed

  have "(Matrix.row Q j) \<bullet>c (Matrix.row Q i) = of_bool(i=j)" 
    (is "?L = ?R")
    if "i < n" "j < n" for i j
  proof (cases "i \<le> j")
    case True
    have "?L = complex_of_real (\<Sum>k = 0..<n. q j k * q i k)" 
      unfolding Q_def using that by (simp add:case_prod_beta Matrix.scalar_prod_def)
    also have "... = of_bool(i=j)"
      using 0 that True by simp 
    finally show ?thesis by simp
  next
    case False
    have "?L = complex_of_real (\<Sum>k = 0..<n. q i k * q j k)" 
      unfolding Q_def using that by (simp add:case_prod_beta Matrix.scalar_prod_def algebra_simps)
    also have "... = of_bool(i=j)"
      using 0 that False by simp 
    finally show ?thesis by simp
  qed

  hence "Q * mat_adjoint Q = 1\<^sub>m n"
    using Q_mat by (intro eq_matI) (auto simp add: adjoint_dim adjoint_col case_prod_beta) 
  hence unit_Q: "unitary Q"
    by (intro unitaryI[OF Q_mat(1)])

  have 1:"mat_adjoint Q * D = mat n n (\<lambda>(i, j). if j = 0 then complex_of_real (1/sqrt n) else 0)"
    unfolding Q_def D_def using n_gt_0 by (intro eq_matI) 
      (auto simp add:adjoint_row Matrix.scalar_prod_def if_distrib if_distribR sum.If_cases q_def)

  have "(mat_adjoint Q * D * Q) $$ (i, j) = K $$ (i, j)" (is "?L1 = ?R1") if "i < n" "j < n" for i j 
  proof - 
    have "?L1 =1/((sqrt (real n)) * complex_of_real (sqrt (real n)))"
      unfolding 1 unfolding Q_def using that n_gt_0
      by (auto simp add:Matrix.scalar_prod_def q_def if_distrib if_distribR sum.If_cases) 
    also have "... = 1/sqrt (real n)^2"
      unfolding of_real_divide of_real_mult power2_eq_square
      by simp
    also have "... = K $$ (i,j)"
      unfolding K_def using that by simp
    finally show ?thesis by simp
  qed

  hence "mat_adjoint Q * D  * Q = K"
    using Q_mat K_mat D_mat by (intro eq_matI) auto

  hence "similar_mat K D"
    using K_mat Q_mat D_mat unit_Q
    by (intro similar_matI[where P="mat_adjoint Q" and Q="Q" and n="n"]) auto

  hence "mset (eigvals K) = mset (eigvals D)"
    by (intro similar_mat_eigvals)
  also have "... = mset (diag_mat D)"
    by (intro upper_tri_eigvals[OF D_mat]) (simp add:D_def upper_triangular_def)
  also have "... = mset (map (\<lambda>i. of_bool(i=0)) [0..<n])"
    unfolding diag_mat_def D_def by (intro arg_cong[where f="mset"] map_cong) auto
  also have "... = mset (1 # map (\<lambda>i. 0) [1..<n])"
    unfolding 2 by (intro arg_cong[where f="mset"]) simp
  also have "... = {#1#} + replicate_mset (n-1) 0"
    using n_gt_0 by (simp add:map_replicate_const mset_repl)
  finally show ?thesis by simp
qed

lemma K_unit: "K *\<^sub>v unit = unit" 
  unfolding K_def unit_def
  by (intro eq_vecI) (simp_all add:case_prod_beta scalar_prod_def)

lemma K_A_comm:
  "K * A = A * K"
proof -
  have "scalar_prod (row K i) (col A j) = scalar_prod (row A i) (col K j)" (is "?L = ?R")
    if "i < n" "j < n" for i j
  proof -
    have "?L = scalar_prod unit (conjugate (conjugate (col A j)))"
      unfolding K_def unit_def using that
      by (intro arg_cong2[where f="scalar_prod"]) auto
    also have "... = scalar_prod unit (conjugate (row (mat_adjoint A) j))"
      using that A_mat adjoint_row[symmetric] by (intro arg_cong2[where f="scalar_prod"] 
          arg_cong[where f="conjugate"] refl adjoint_row[symmetric]) auto
    also have "... = scalar_prod unit (conjugate (row A j))"
      using A_sym unfolding hermitian_def by simp
    also have "... = scalar_prod unit (row A j)"
      using A_mat that by (intro arg_cong2[where f="scalar_prod"]) (auto simp add:A_def)
    also have "... = (1::complex)/of_nat n"
      using A_row_unit unit_vec A_mat[where 'c="complex"] that 
      by (subst comm_scalar_prod[OF unit_vec]) auto 
    also have "... = scalar_prod (row A i) unit"
      using A_row_unit unit_vec A_mat that by auto
    also have "... = ?R"
      unfolding unit_def K_def using that
      by (intro arg_cong2[where f="scalar_prod"] refl eq_vecI) auto
    finally show ?thesis by simp
  qed
  thus ?thesis
    using A_mat K_mat
    by (intro eq_matI) auto
qed

text \<open>The following obtains an eigen-vector for the second largest eigenvalue, that is orthogonal
to the unit vector. Because A is symmetric, this is straight-forward when @{term "\<gamma>\<^sub>2 < 1"} but it
is more complex to establish if @{term "\<gamma>\<^sub>2 = 1"}. The proof below relies on a simultaneous 
diagonalization argument for @{term "A"} and @{term "K"}.\<close>

lemma
  assumes "n > 1"
  shows evs_real: "set (eigvals A::complex list) \<subseteq> \<real>" (is "?R1")
    and \<gamma>\<^sub>2_ev: 
    "\<exists>v\<in>carrier_vec n. (\<exists>\<alpha>\<in>\<real>. norm \<alpha>=\<gamma>\<^sub>2\<and>v \<bullet>c unit = (0::complex) \<and> v \<bullet>c v = 1 \<and> A *\<^sub>v v = \<alpha> \<cdot>\<^sub>v v)"  
      (is "?R2")
    and \<gamma>\<^sub>2_bound: 
    "\<forall>v \<in> carrier_vec n. v \<bullet>c unit = (0::complex) \<longrightarrow> r_norm_vec (A *\<^sub>v v) \<le> \<gamma>\<^sub>2 * r_norm_vec v"
      (is "?R3")
proof -
  define Ms where "Ms = {A, K}"

  have "\<exists>U. \<forall>A\<in>Ms. \<exists>B. real_diag_decomp A B U"
    unfolding Ms_def using A_mat K_mat n_gt_0 A_sym K_sym K_A_comm
    by (intro commuting_hermitian_family_diag[where n="n"]) auto
  then obtain U Ad Kd 
    where A_decomp: "real_diag_decomp A Ad U" and K_decomp: "real_diag_decomp K Kd U"
    unfolding Ms_def by auto

  have K_sim: "similar_mat_wit K Kd U (Complex_Matrix.adjoint U)" "diagonal_mat Kd"
    using K_decomp unfolding real_diag_decomp_def unitary_diag_def unitarily_equiv_def
    by auto

  have K_dim: "n = dim_row K"
    unfolding K_def by simp

  have Kd_mat: "Kd \<in> carrier_mat n n" and U_mat: "U \<in> carrier_mat n n"
    using similar_mat_witD[OF K_dim K_sim(1)] by auto

  have unit_U: "unitary U"
    using similar_mat_witD[OF K_dim K_sim(1)]
    by (intro unitaryI[OF U_mat]) auto

  have len_diag_mat_Kd: "length (diag_mat Kd) = n"
    using Kd_mat unfolding diag_mat_def by simp

  have "mset (diag_mat Kd) = mset (eigvals Kd)" 
    using K_sim(2) Kd_mat diagonal_imp_upper_triangular
    by (intro upper_tri_eigvals[symmetric]) auto
  also have "... = mset (eigvals K)"
    using K_decomp unfolding real_diag_decomp_def unitary_diag_def unitarily_equiv_def
    by (intro similar_mat_eigvals[symmetric]) (auto simp add:similar_mat_def) 
  also have "... = {#1#} + replicate_mset (n - 1) 0"
    unfolding K_eigvals by simp
  finally have 0:"mset (diag_mat Kd) = {#1#} + replicate_mset (n - 1) 0"
    by simp
  hence "1 \<in># mset (diag_mat Kd)" by simp
  hence "1 \<in> set (diag_mat Kd)" by simp
  then obtain i where i_def:"diag_mat Kd ! i = 1" "i < length (diag_mat Kd)"
    by (meson in_set_conv_nth)
  have "replicate_mset (n - 1) 0 = ({#1#} + replicate_mset (n - 1) 0 ) - {#1#}"
    by simp
  also have "... = mset (diag_mat Kd) - {#1#}"
    unfolding 0 by simp
  also have "... = mset (nths (diag_mat Kd) ({..<n}-{i} \<union> {i})) - {#1#}"
    using Kd_mat by (subst nths_all) (simp_all add:diag_mat_def)
  also have "... = mset (nths (diag_mat Kd) ({..<n}-{i})) + mset (nths (diag_mat Kd) {i}) - {#1#}"
    by (subst mset_nths_union[symmetric], simp_all)
  also have "... = mset (nths (diag_mat Kd) ({..<n}-{i})) + {#1#} - {#1#}"
    using i_def unfolding nths_single
    by (intro arg_cong2[where f="(-)"]  arg_cong2[where f="(+)"] refl) simp
  also have "... = mset (nths (diag_mat Kd) ({..<n}-{i}))" by simp
  finally have 1:"replicate_mset (n - 1) 0 = mset (nths (diag_mat Kd) ({..<n}-{i}))" by simp
  have "set (nths (diag_mat Kd) ({..<n}-{i})) = set_mset (mset (nths (diag_mat Kd) ({..<n}-{i})))"
    unfolding set_mset_mset by simp
  also have "... = set_mset (replicate_mset (n - 1) 0)"
    unfolding 1 by simp
  also have "... \<subseteq> {0}"
    by simp
  finally have "set (nths (diag_mat Kd) ({..<n}-{i})) \<subseteq> {0}" by simp
  hence 2:"diag_mat Kd ! j = 0" if "j < n" "j \<noteq> i" for j
    using subsetD[where c="diag_mat Kd ! j"] that unfolding set_nths len_diag_mat_Kd by auto

  define u where "u = mat_adjoint U *\<^sub>v unit"
  define \<alpha> where "\<alpha> = vec_index u i"

  have u_vec: "u \<in> carrier_vec n" 
    using U_mat unit_vec[where 'c=complex] adjoint_dim[OF U_mat] unfolding u_def by simp

  have "U *\<^sub>v u = (U * mat_adjoint U) *\<^sub>v unit"
    unfolding u_def using U_mat adjoint_dim[OF U_mat] unit_vec
    by (intro assoc_mult_mat_vec[symmetric]) auto
  also have "... = unit"
    using unit_vec[where 'c=complex]
    unfolding similar_mat_witD[OF K_dim K_sim(1)] by simp
  also have "... \<noteq> 0\<^sub>v n" 
    using n_gt_0  unfolding unit_def by (auto simp add:veq_eq_iff)
  finally have "U *\<^sub>v u \<noteq> 0\<^sub>v n" by simp 
  hence u_nz: "u \<noteq> 0\<^sub>v n" 
    using U_mat by (cases "u = 0\<^sub>v n") auto

  have "Kd *\<^sub>v u = mat_adjoint U * U * Kd * mat_adjoint U *\<^sub>v unit"
    using Kd_mat U_mat unit_vec[where 'c=complex] adjoint_dim[OF U_mat]
    unfolding u_def similar_mat_witD[OF K_dim K_sim(1)] by (simp add:algebra_simps)
  also have "... = (mat_adjoint U * U) * (Kd * mat_adjoint U) *\<^sub>v unit"
    using Kd_mat U_mat adjoint_dim[OF U_mat]
    by (intro arg_cong2[where f="(*\<^sub>v)"] refl assoc_mult_mat) auto
  also have "... = mat_adjoint U * (U * (Kd * mat_adjoint U)) *\<^sub>v unit"
    using Kd_mat U_mat adjoint_dim[OF U_mat]
    by (intro arg_cong2[where f="(*\<^sub>v)"] refl assoc_mult_mat) auto
  also have "... = mat_adjoint U * (U * Kd * mat_adjoint U) *\<^sub>v unit"
    using Kd_mat U_mat adjoint_dim[OF U_mat]
    by (intro arg_cong2[where f="(*\<^sub>v)"] refl assoc_mult_mat) auto
  also have "... = mat_adjoint U * K *\<^sub>v unit"
    unfolding similar_mat_witD(3)[OF K_dim K_sim(1)] by simp
  also have "... = u"
    unfolding u_def  using Kd_mat U_mat unit_vec[where 'c=complex] adjoint_dim[OF U_mat] K_mat
    by (auto simp add:K_unit)
  finally have u_ev: "Kd *\<^sub>v u = u" by simp

  hence "vec n (\<lambda>k. diag_mat Kd ! k * vec_index u k) = Kd *\<^sub>v u"
    by (intro diag_mat_mult[symmetric] K_sim Kd_mat u_vec)
  also have "... = u"
    using u_ev by simp
  finally have 3:"u = vec n (\<lambda>k. diag_mat Kd ! k * vec_index u k)"
    by simp
  have "vec_index u k = vec_index u k * diag_mat Kd ! k" if "k < n" for k 
    using that by (subst 3) simp
  hence "vec_index u k = 0" if "k < n" "k \<noteq> i" for k 
    using that 2 by (metis mult_cancel_right2)
  hence u_alt: "u = \<alpha> \<cdot>\<^sub>v unit_vec n i"
    using u_vec unfolding \<alpha>_def unit_vec_def
    by (intro eq_vecI, simp_all) 

  have \<alpha>_nz: "\<alpha> \<noteq> 0"
    using u_nz unfolding u_alt by auto

  have A_sim: "similar_mat_wit A Ad U (Complex_Matrix.adjoint U)" "diagonal_mat Ad"
    using A_decomp unfolding real_diag_decomp_def unitary_diag_def unitarily_equiv_def
    by auto

  have Ad_real: "set (diag_mat Ad) \<subseteq> \<real>"
    unfolding diag_mat_def set_map using A_decomp unfolding real_diag_decomp_def
    by (intro image_subsetI) simp

  have A_dim: "n = dim_row A"
    unfolding A_def by simp

  have Ad_mat: "Ad \<in> carrier_mat n n"
    using similar_mat_witD[OF A_dim A_sim(1)] by simp
  have len_diag_mat_Ad: "length (diag_mat Ad) = n"
    unfolding diag_mat_def using Ad_mat by simp

  have i_lt_n: "i < n"
    using i_def(2) len_diag_mat_Kd by simp

  have "mset (eigvals A) = mset (eigvals Ad)"
    using A_decomp unfolding real_diag_decomp_def unitary_diag_def unitarily_equiv_def
    by (intro similar_mat_eigvals) (auto simp add:similar_mat_def) 
  also have "... = mset (diag_mat Ad)"
    by (intro upper_tri_eigvals[OF Ad_mat] diagonal_imp_upper_triangular[OF A_sim(2) Ad_mat])
  finally have 3:"mset (diag_mat Ad) = mset (eigvals A)" by simp

  show "set (eigvals A :: complex list) \<subseteq> \<real>"
    using 3 Ad_real mset_eq_setD by blast

  have "Ad *\<^sub>v u = mat_adjoint U * U * Ad * mat_adjoint U *\<^sub>v unit"
    using Ad_mat U_mat unit_vec[where 'c=complex] adjoint_dim[OF U_mat]
    unfolding u_def similar_mat_witD[OF A_dim A_sim(1)] by (simp add:algebra_simps)
  also have "... = (mat_adjoint U * U) * (Ad * mat_adjoint U) *\<^sub>v unit"
    using Ad_mat U_mat adjoint_dim[OF U_mat]
    by (intro arg_cong2[where f="(*\<^sub>v)"] refl assoc_mult_mat) auto
  also have "... = mat_adjoint U * (U * (Ad * mat_adjoint U)) *\<^sub>v unit"
    using Ad_mat U_mat adjoint_dim[OF U_mat]
    by (intro arg_cong2[where f="(*\<^sub>v)"] refl assoc_mult_mat) auto
  also have "... = mat_adjoint U * (U * Ad * mat_adjoint U) *\<^sub>v unit"
    using Ad_mat U_mat adjoint_dim[OF U_mat]
    by (intro arg_cong2[where f="(*\<^sub>v)"] refl assoc_mult_mat) auto
  also have "... = mat_adjoint U * A *\<^sub>v unit"
    unfolding similar_mat_witD(3)[OF A_dim A_sim(1)] by simp
  also have "... = u"
    unfolding u_def using A_mat[where 'c="complex"] U_mat unit_vec[where 'c=complex] adjoint_dim[OF U_mat]
    by (auto simp add:A_markov)
  finally have u_ev_A: "Ad *\<^sub>v u = u" by simp
  hence "vec n (\<lambda>k. diag_mat Ad ! k * vec_index u k) = u"
    using diag_mat_mult[OF A_sim(2) Ad_mat] u_vec by simp
  hence "diag_mat Ad ! i * vec_index u i = vec_index u i" 
    using i_lt_n by (metis (no_types, lifting) index_vec)
  moreover have "vec_index u i = \<alpha>"
    using u_alt i_lt_n by simp 
  ultimately have 5:"diag_mat Ad ! i = 1"
    using \<alpha>_nz by auto

  have "mset (eigvals A) - {#1#} = mset (nths (diag_mat Ad) ({..<n}-{i}\<union>{i})) - {#1#}"
    unfolding 3[symmetric] using len_diag_mat_Ad by (subst nths_all) auto
  also have "... = mset (nths (diag_mat Ad) ({..<n}-{i})) + mset (nths (diag_mat Ad) {i}) - {#1#}"
    by (subst mset_nths_union[symmetric], simp_all)
  also have "... = mset (nths (diag_mat Ad) ({..<n}-{i}))"
    using i_lt_n unfolding nths_single 5 len_diag_mat_Ad by simp
  finally have 4:"mset (eigvals A) - {#1#} = mset (nths (diag_mat Ad) ({..<n}-{i}))" by simp

  have "\<gamma>\<^sub>2 \<in># image_mset cmod (mset (nths (diag_mat Ad) ({..<n}-{i})))"
    using find_\<gamma>\<^sub>2 assms 4 by simp
  hence "\<gamma>\<^sub>2 \<in> cmod ` set (nths (diag_mat Ad) ({..<n}-{i}))"
    by simp
  then obtain j where j_def: "norm (diag_mat Ad ! j) = \<gamma>\<^sub>2" "j \<noteq> i" "j < n" 
    unfolding set_nths by auto

  have norm_Ad: "norm (diag_mat Ad ! k) \<le> \<gamma>\<^sub>2 \<or> k = i" if  "k < n" for k
  proof (cases "k=i")
    case True
    then show ?thesis by simp
  next
    case False
    hence "k \<in> {..<n}-{i}" using that by simp
    hence "diag_mat Ad ! k \<in> set (nths (diag_mat Ad) ({..<n}-{i}))"
      unfolding set_nths setcompr_eq_image 
      by (intro imageI) (simp add:len_diag_mat_Ad)
    hence "diag_mat Ad ! k \<in># mset (eigvals A) - {#1#}"
      unfolding 4 by simp
    hence "norm (diag_mat Ad ! k) \<in># image_mset cmod (mset (eigvals A) - {#1#})"
      by (auto intro!:imageI)
    hence "norm (diag_mat Ad ! k) \<le> \<gamma>\<^sub>2"
      unfolding \<gamma>\<^sub>2_iff_n_gt_1[OF assms] by (intro Max_ge) auto
    then show ?thesis by simp
  qed

  define \<beta> where "\<beta> = diag_mat Ad ! j"
  define v :: "complex Matrix.vec" where "v = U *\<^sub>v unit_vec n j" 

  have v_vec: "v \<in> carrier_vec n"
    unfolding v_def using U_mat j_def(3) by simp

  have \<beta>_real: "\<beta> \<in> \<real>"
    using Ad_real j_def(3) len_diag_mat_Ad unfolding \<beta>_def by fastforce

  have "A *\<^sub>v v = (A * U) *\<^sub>v unit_vec n j"
    unfolding v_def using A_mat[where 'c="complex"] U_mat by auto
  also have "... = ((U * Ad * mat_adjoint U)  * U) *\<^sub>v unit_vec n j"
    unfolding similar_mat_witD(3)[OF A_dim A_sim(1)] by simp
  also have "... = ((U * Ad) * (mat_adjoint U * U)) *\<^sub>v unit_vec n j"
    using U_mat Ad_mat adjoint_dim
    by (intro arg_cong2[where f="(*\<^sub>v)"] assoc_mult_mat) auto
  also have "... = U *\<^sub>v (Ad *\<^sub>v unit_vec n j)"
    using U_mat Ad_mat unfolding similar_mat_witD(2)[OF A_dim A_sim(1)] by simp
  also have "... = U *\<^sub>v (vec n (\<lambda>k. diag_mat Ad ! k * vec_index (unit_vec n j) k))"
    by (subst diag_mat_mult[OF A_sim(2) Ad_mat]) auto
  also have "... = U *\<^sub>v (\<beta> \<cdot>\<^sub>v unit_vec n j)"
    unfolding \<beta>_def using j_def(3)
    by (intro arg_cong2[where f="(*\<^sub>v)"] eq_vecI refl) auto
  also have "... = \<beta> \<cdot>\<^sub>v v"
    using U_mat unfolding v_def by auto
  finally have 5:"A *\<^sub>v v = \<beta> \<cdot>\<^sub>v v" by simp

  have "v \<bullet>c unit = unit_vec n j \<bullet>c (mat_adjoint U *\<^sub>v unit)"
    unfolding v_def using U_mat by (meson adjoint_def_alter unit_vec unit_vec_carrier)
  also have "... = unit_vec n j \<bullet>c (\<alpha> \<cdot>\<^sub>v unit_vec n i)"
    unfolding u_def[symmetric] u_alt by simp
  also have "... = cnj \<alpha> * (unit_vec n j \<bullet>c unit_vec n i)"
    using unit_vec_carrier by (simp add: conjugate_smult_vec)
  also have "... = 0"
    using j_def(2,3) i_lt_n by simp
  finally have 6:"v \<bullet>c unit = 0" by simp

  have "v\<bullet>cv=unit_vec n j\<bullet>c(mat_adjoint U *\<^sub>v (U *\<^sub>v unit_vec n j))"
    unfolding v_def using U_mat by (intro adjoint_def_alter) auto
  also have "... = unit_vec n j\<bullet>c(mat_adjoint U * U *\<^sub>v unit_vec n j)"
    using U_mat adjoint_dim[OF U_mat] by simp
  also have "... = 1"
    using j_def(3) unfolding similar_mat_witD(2)[OF A_dim A_sim(1)] by simp
  finally have 7:"v\<bullet>cv = 1" by simp

  show ?R2
    using j_def(1) \<beta>_def \<beta>_real v_vec
    by (intro bexI[where x="v"] bexI[where x="\<beta>"] conjI 5 6 7) auto

  have "r_norm_vec (A *\<^sub>v w) \<le> \<gamma>\<^sub>2 * r_norm_vec w" if "w\<in>carrier_vec n" "w \<bullet>c unit = (0::complex)" for w
  proof -
    define w' where "w' = mat_adjoint U *\<^sub>v w"
    have w'_vec: "w' \<in> carrier_vec n"
      unfolding w'_def using that(1) adjoint_dim[OF U_mat] mult_mat_vec_carrier w'_def by blast

    have "vec_index w' i = scalar_prod w' (unit_vec n i)"
      by (intro scalar_prod_right_unit[symmetric] i_lt_n)
    also have "... = w' \<bullet>c (unit_vec n i)"
      using i_lt_n by (intro arg_cong2[where f="scalar_prod"]) auto
    also have "... = w' \<bullet>c ((1 / \<alpha>) \<cdot>\<^sub>v u)"
      using \<alpha>_nz unfolding u_alt by (intro arg_cong2[where f="(\<bullet>c)"]) auto
    also have "... = cnj (1 / \<alpha>) * (w' \<bullet>c u)"
      using w'_vec u_vec \<alpha>_nz unfolding inner_prod_smult_right[OF u_vec w'_vec] by simp
    also have "... = cnj (1 / \<alpha>) * (w \<bullet>c unit)"
      unfolding w'_def u_def using unit_U U_mat
      by (intro arg_cong2[where f="(*)"] unitary_inner_prod[OF unit_vec that(1)]) auto
    also have "... = 0"
      using that by simp
    finally have w'_orth: "vec_index w' i = 0" by simp

    have "r_norm_vec (A *\<^sub>v w) = r_norm_vec (U * Ad * mat_adjoint U *\<^sub>v w)"
      unfolding similar_mat_witD(3)[OF A_dim A_sim(1)] by simp
    also have "... = r_norm_vec (U * Ad *\<^sub>v w')"
      unfolding w'_def
      using U_mat Ad_mat adjoint_dim[OF U_mat] that(1)
      by (intro arg_cong[where f="r_norm_vec"] assoc_mult_mat_vec) auto
    also have "... = r_norm_vec (U *\<^sub>v (Ad *\<^sub>v w'))"
      using U_mat Ad_mat adjoint_dim[OF U_mat] w'_vec
      by (intro arg_cong[where f="r_norm_vec"] assoc_mult_mat_vec) auto
    also have "... = r_norm_vec (Ad *\<^sub>v w')"
      using unit_U U_mat Ad_mat w'_vec by (intro unitary_iso[OF _ U_mat]) auto
    also have "... = r_norm_vec (vec n (\<lambda>k. diag_mat Ad ! k * vec_index w' k))" 
      by (intro arg_cong[where f="r_norm_vec"] diag_mat_mult A_sim(2) w'_vec Ad_mat)
    also have "... = sqrt (\<Sum>i<n. (cmod (diag_mat Ad ! i) * cmod (vec_index w' i))^2)"
      unfolding r_norm_vec_def by (simp add:norm_mult)
    also have "... \<le> sqrt (\<Sum>i<n. (\<gamma>\<^sub>2 * cmod (vec_index w' i))^2)"
      using norm_Ad w'_orth by (intro real_sqrt_le_mono sum_mono power_mono mult_right_mono') auto
    also have "... = sqrt (\<gamma>\<^sub>2^2 * (\<Sum>i<n. (cmod (vec_index w' i))^2))"
      by (simp add:power_mult_distrib sum_distrib_left)
    also have "... = \<gamma>\<^sub>2 * sqrt (\<Sum>i<n. (cmod (vec_index w' i))^2)"
      using \<gamma>\<^sub>2_nonneg by (simp add:real_sqrt_mult)
    also have "... = \<gamma>\<^sub>2 * r_norm_vec w'"
      using w'_vec unfolding r_norm_vec_def by simp
    also have "... = \<gamma>\<^sub>2 * r_norm_vec w"
      unfolding w'_def using that U_mat unit_U
      by (intro arg_cong2[where f="(*)"] unitary_iso refl) auto
    finally show ?thesis by simp
  qed

  thus ?R3 
    by simp
qed

lemma \<gamma>\<^sub>2_real_ev:
  assumes "n > 1"
  shows "\<exists>v\<in>carrier_vec n. (\<exists>\<alpha>. abs \<alpha>=\<gamma>\<^sub>2 \<and> v \<bullet> unit=(0::real) \<and> v \<noteq> 0\<^sub>v n \<and> A *\<^sub>v v = \<alpha> \<cdot>\<^sub>v v)"  
proof -
  obtain w \<beta> where w_def:
    "w \<in> carrier_vec n" "\<beta> \<in> \<real>"
    "cmod \<beta> = \<gamma>\<^sub>2" "w \<bullet>c unit = 0" "w \<bullet>c w = 1" "A *\<^sub>v w = \<beta> \<cdot>\<^sub>v w"
    using \<gamma>\<^sub>2_ev[OF assms] by auto

  obtain \<alpha> where \<alpha>_def: "\<beta> = of_real \<alpha>"
    using w_def(2) Reals_cases by auto

  have "w = 0\<^sub>v n" if 0:"map_vec Re (1 \<cdot>\<^sub>v w) = 0\<^sub>v n"  "map_vec Re (\<i> \<cdot>\<^sub>v w) = 0\<^sub>v n"
  proof -
    have "vec_index w i = 0" if "i < n"  for i
    proof (rule complex_eqI)
      have "Re (vec_index w i) = vec_index (map_vec Re (1 \<cdot>\<^sub>v w)) i"
        using that w_def(1) by simp
      also have "... = Re 0"
        unfolding 0 using that by simp
      finally show "Re (vec_index w i) = Re 0" by simp
    next 
      have "Im (vec_index w i) = - vec_index (map_vec Re (\<i> \<cdot>\<^sub>v w)) i"
        using that w_def(1) by simp
      also have "... = Im 0"
        unfolding 0 using that by simp
      finally show "Im (vec_index w i) = Im 0" by simp
    qed
    thus ?thesis
      using w_def(1) by (intro eq_vecI) auto
  qed
  moreover have "w \<noteq> 0\<^sub>v n" 
    using w_def(5) by auto
  ultimately obtain c where c_def:"map_vec Re (c \<cdot>\<^sub>v w) \<noteq> 0\<^sub>v n"
    by blast

  define u where "u =c \<cdot>\<^sub>v w"

  define v where "v = map_vec Re u" 

  have u_vec: "u \<in> carrier_vec n"
    unfolding u_def using w_def(1) by simp
  have v_vec: "v \<in> carrier_vec n"
    unfolding v_def using u_vec by simp

  have "scalar_prod v unit = Re (u \<bullet>c unit)"
    using u_vec unfolding v_def scalar_prod_def Re_sum unit_def
    by (intro sum.cong, auto)
  also have "... = Re (c * (w \<bullet>c unit))"
    unfolding u_def using w_def(1) unit_vec carrier_vec_conjugate
    by (intro smult_scalar_prod_distrib arg_cong[where f="Re"]) auto
  also have "... = 0"
    unfolding w_def by simp
  finally have 1:"scalar_prod v unit = 0" by simp

  have "scalar_prod (row A i) v = \<alpha> * vec_index v i" if i_lt_n: "i < n" for i
  proof -
    have "Im (vec_index (row A i) j) = 0" if "j < n" for j
      unfolding A_def using that i_lt_n by simp
    moreover have "Re (vec_index (row A i) j) = (vec_index (row A i) j)" if "j < n" for j
      unfolding A_def using that i_lt_n by simp
    ultimately have "scalar_prod (row A i) v = Re (scalar_prod (row A i) u)"
      using u_vec unfolding v_def scalar_prod_def Re_sum 
      by (intro sum.cong, auto)
    also have "... = Re (vec_index (A *\<^sub>v u) i)"
      using A_mat u_vec that by simp
    also have "... = Re (vec_index (\<beta> \<cdot>\<^sub>v u) i)"
      unfolding u_def using w_def(1,6) A_mat[where 'c="complex"]
      by (intro arg_cong2[where f="vec_index"] arg_cong[where f="Re"]) (auto simp add:mult_mat_vec)
    also have "... = \<alpha> * vec_index v i"
      unfolding \<alpha>_def v_def using that u_vec by simp
    finally show ?thesis by simp
  qed 

  hence 2:"A *\<^sub>v v = \<alpha> \<cdot>\<^sub>v v"
    using A_mat[where 'c="complex"] v_vec
    by (intro eq_vecI) auto

  have 3:"v \<noteq> 0\<^sub>v n" 
    unfolding v_def u_def using c_def by simp

  have 4: "\<bar>\<alpha>\<bar> = \<gamma>\<^sub>2" 
    using \<alpha>_def w_def(3,4) by simp

  show ?thesis
    by (intro bexI[where x="v"] exI[where x="\<alpha>"] conjI v_vec 1 2 3 4)
qed

lemma \<gamma>\<^sub>2_bound_1:
  assumes "c \<ge> (0::real)"
  assumes "\<And>v. v \<in> carrier_vec n \<Longrightarrow> v \<bullet> unit = 0 \<Longrightarrow> \<bar>v \<bullet> (A *\<^sub>v v)\<bar> \<le> c * (v \<bullet> v)" 
  shows "\<gamma>\<^sub>2 \<le> c"
proof (cases "n > 1")
  case True
  obtain v \<alpha> where v_def:
    "v \<in> carrier_vec n" "scalar_prod v unit = (0::real)" "abs \<alpha> = \<gamma>\<^sub>2"
    "A *\<^sub>v v = \<alpha> \<cdot>\<^sub>v v" "v \<noteq> 0\<^sub>v n"
    using \<gamma>\<^sub>2_real_ev[OF True] by auto

  have "\<gamma>\<^sub>2 * (v \<bullet> v) = \<bar>\<alpha> * (v \<bullet> v)\<bar>"
    unfolding v_def(3)[symmetric] norm_vec_sq_real[OF v_def(1), symmetric] using v_def(1) 
    by (simp add:abs_mult)
  also have "... = \<bar>v \<bullet> (\<alpha> \<cdot>\<^sub>v v)\<bar>"
    using v_def by simp
  also have "... = \<bar>v \<bullet> (A *\<^sub>v v)\<bar>"
    unfolding v_def by simp
  also have "... \<le> c * (v \<bullet> v)"
    by (intro assms(2) v_def)
  finally have "\<gamma>\<^sub>2 * (v \<bullet> v) \<le> c * (v \<bullet> v)" by simp
  moreover have "v \<bullet> v > 0" 
    unfolding norm_vec_sq_real[OF v_def(1), symmetric]
    using v_def(1,5) r_norm_vec_0_iff[OF v_def(1)] by simp
  ultimately show "\<gamma>\<^sub>2 \<le> c" by simp
next
  case False
  then show ?thesis
    using \<gamma>\<^sub>2_eq_0 assms(1) n_gt_0 by linarith
qed

lemma \<gamma>\<^sub>2_bound_2:
  assumes "v \<in> carrier_vec n"
  assumes "scalar_prod v unit = (0::real)"
  shows "r_norm_vec (A *\<^sub>v v) \<le> \<gamma>\<^sub>2 * r_norm_vec v"
proof (cases "n > 1")
  case True
  define w where "w = map_vec complex_of_real v"

  have w_vec: "w \<in> carrier_vec n"
    unfolding w_def using assms(1) by simp

  have "w \<bullet>c unit = scalar_prod v unit"
    unfolding w_def unit_def scalar_prod_def of_real_sum
    using assms(1) by (intro sum.cong) auto
  also have "... = 0" using assms(2) by simp
  finally have 0:"w \<bullet>c unit = 0" by simp

  have "r_norm_vec (A *\<^sub>v v) = r_norm_vec (map_vec complex_of_real (A *\<^sub>v v))" 
    using A_mat assms(1) by (intro r_norm_vec_of_real[symmetric] mult_mat_vec_carrier) auto
  also have "... = r_norm_vec (map_mat of_real A *\<^sub>v w)"
    unfolding w_def  using assms(1) A_mat
    by (intro arg_cong[where f="r_norm_vec"] of_real_hom.mult_mat_vec_hom) auto
  also have "... = r_norm_vec (A *\<^sub>v w)"
    unfolding A_def
    by (intro arg_cong[where f="r_norm_vec"] arg_cong2[where f="(*\<^sub>v)"]) auto
  also have "... \<le> \<gamma>\<^sub>2 * r_norm_vec w"
    using \<gamma>\<^sub>2_bound[OF True] w_vec 0 by simp
  also have "... = \<gamma>\<^sub>2 * r_norm_vec v"
    unfolding w_def r_norm_vec_of_real[OF assms(1)] by simp
  finally show ?thesis by simp
next
  case False 
  hence "n = 1"
    using n_gt_0 by simp
  hence 0:"v = 0\<^sub>v n"
    using assms(1,2) unit_vec
    by (intro eq_vecI) (auto simp add:scalar_prod_def unit_def)
  have "r_norm_vec (A *\<^sub>v v) = r_norm_vec (A *\<^sub>v (0\<^sub>v n :: real Matrix.vec))"
    unfolding 0 by simp
  also have "... = r_norm_vec (0\<^sub>v n :: real Matrix.vec)"
    by (intro arg_cong[where f="r_norm_vec"] eq_vecI)  (auto simp add: A_mat)
  also have "... = 0"
    by (subst r_norm_vec_0_iff) auto
  also have "... \<le> \<gamma>\<^sub>2 * r_norm_vec v"
    by (intro mult_nonneg_nonneg \<gamma>\<^sub>2_nonneg r_norm_vec_nonneg)
  finally show ?thesis by simp
qed

subsection \<open>Correspondence between n-dim vectors and functions defined on the vertices.\<close>

lemma g_inner_conv: 
  "g_inner f g = (vec n (f \<circ> enum_verts)) \<bullet> (vec n (g \<circ> enum_verts))" (is "?L = ?R")
proof -
  have "?L = (\<Sum>x\<in>verts G. f x * g x)"
    unfolding g_inner_def by simp
  also have "... = (\<Sum>x \<in> {..<n}. f (enum_verts x) * g (enum_verts x))"
    by (intro sum.reindex_bij_betw[symmetric] enum_verts)
  also have "... = ?R"
    unfolding scalar_prod_def using atLeast0LessThan by simp
  finally show ?thesis by simp
qed

lemma g_norm_conv:
  "g_norm f  = r_norm_vec (vec n (f \<circ> enum_verts))"
proof -
  have 0:"g_norm f^2 = r_norm_vec (vec n (f \<circ> enum_verts))^2"
    unfolding g_norm_sq g_inner_conv by (subst norm_vec_sq_real) auto
  show ?thesis
    by (intro power2_eq_imp_eq[OF 0] g_norm_nonneg r_norm_vec_nonneg)
qed

lemma g_step_conv: 
  "vec n (g_step f \<circ> enum_verts) = A *\<^sub>v (vec n (f \<circ> enum_verts))"
proof -
  have "g_step f (enum_verts i) = row A i \<bullet> vec n (f \<circ> enum_verts)" (is "?L = ?R") if "i < n" for i
  proof -
    have "?L = (\<Sum>a\<in>in_arcs G (enum_verts i). f (tail G a) / real d)"
      unfolding g_step_def 
      by (intro sum.cong refl arg_cong2[where f="(/)"] arg_cong[where f="real"] reg) simp
    also have "... = (\<Sum>a\<in>(\<Union>v \<in> verts G. arcs_betw G v (enum_verts i)). f (tail G a) / real d)" 
      unfolding in_arcs_def arcs_betw_def by (intro sum.cong) auto
    also have "...= (\<Sum>v \<in> verts G. (\<Sum>a\<in>arcs_betw G v (enum_verts i). f (tail G a) / real d))"
      unfolding arcs_betw_def by (intro sum.UNION_disjoint) auto
    also have "...= (\<Sum>v \<in> verts G. (\<Sum>a\<in>arcs_betw G v (enum_verts i). f v / real d))"
      unfolding arcs_betw_def by (intro sum.cong) auto
    also have "...= (\<Sum>v \<in> verts G. count (edges G) (v,enum_verts i) * f v / real d)" 
      unfolding count_edges by (intro sum.cong) auto
    also have "... = (\<Sum>j=0..<n. count(edges G)(enum_verts j,enum_verts i)*f(enum_verts j)/real d)"
      using enum_verts atLeast0LessThan
      by (intro sum.reindex_bij_betw[symmetric]) auto
    also have "... = ?R"
      unfolding A_def scalar_prod_def using that by simp
    finally show ?thesis by simp
  qed
  thus ?thesis
    using  A_mat by (intro eq_vecI) auto
qed

definition fun_of_vec 
  where "fun_of_vec v x = v $ to_nat_on (verts G) x"

lemma fun_of_vec:
  assumes "v \<in> carrier_vec n"
  shows "v = vec n (fun_of_vec v \<circ> enum_verts)"
proof -
  have "v $ i = v $ to_nat_on (verts G) (from_nat_into (verts G) i)"  if "i < n" for i
  proof -
    have "i < card (verts G)"  using that unfolding n_def by simp
    thus ?thesis
      by (subst to_nat_on_from_nat_into') auto
  qed
  thus ?thesis
    using assms unfolding enum_verts_def fun_of_vec_def 
    by (intro eq_vecI) auto
qed

lemma \<Lambda>_eq_\<gamma>\<^sub>2: "\<Lambda> = \<gamma>\<^sub>2"
proof (rule order_antisym)
  have "\<bar>\<Sum>a\<in>arcs G. f (head G a) * f (tail G a)\<bar> \<le> \<gamma>\<^sub>2 * real d * (g_norm f)\<^sup>2" (is "?L \<le> ?R")
    if "g_inner f (\<lambda>_. 1) = 0" for f
  proof -
    have "vec n (f \<circ> enum_verts) \<bullet> unit =vec n (f \<circ> enum_verts) \<bullet> ((1/real n) \<cdot>\<^sub>v vec n (\<lambda>_. 1))"
      unfolding unit_def by (intro arg_cong2[where f="(\<bullet>)"] eq_vecI) auto 
    also have "... = (1/real n) * (vec n (f \<circ> enum_verts) \<bullet> vec n ((\<lambda>_. 1) \<circ> enum_verts))"
      by simp
    also have "... = (1/real n) * g_inner f (\<lambda>_. 1)"
      unfolding g_inner_conv by simp
    also have "... = 0" 
      using that by simp
    finally have 0: "vec n (f \<circ> enum_verts) \<bullet> unit = 0" by simp

    have "?L = d * \<bar>g_inner f (g_step f)\<bar>"
      unfolding g_inner_step_eq using d_gt_0 by simp
    also have "... \<le> d * (g_norm f * g_norm (g_step f))"
      by (intro mult_left_mono g_inner_cauchy_schwartz) auto
    also have "... = (d * g_norm f) * r_norm_vec (A *\<^sub>v vec n (f \<circ> enum_verts))"
      unfolding g_norm_conv g_step_conv by simp
    also have "... \<le> (d * g_norm f) * (\<gamma>\<^sub>2 * r_norm_vec (vec n (f \<circ> enum_verts)))"
      using g_norm_nonneg 0 by (intro mult_left_mono \<gamma>\<^sub>2_bound_2) auto
    also have "... = ?R"
      unfolding g_norm_conv by (simp add:algebra_simps power2_eq_square)
    finally show ?thesis
      by simp
  qed

  hence "\<Lambda> \<le> \<gamma>\<^sub>2 * d / real d"
    using \<gamma>\<^sub>2_nonneg by (intro expander_intro) auto
  thus "\<Lambda> \<le> \<gamma>\<^sub>2"
    using d_gt_0 by simp
next
  show "\<Lambda> \<ge> \<gamma>\<^sub>2"
  proof (cases "n > 1")
    case True
    obtain v :: "real Matrix.vec" and \<alpha> :: real where v_def: 
      "v \<in> carrier_vec n"
      "\<bar>\<alpha>\<bar> = \<gamma>\<^sub>2"  "v \<bullet> unit = 0"  "v \<noteq> 0\<^sub>v n" "A *\<^sub>v v = \<alpha> \<cdot>\<^sub>v v"
      using \<gamma>\<^sub>2_real_ev[OF True] by auto
    define f where "f = fun_of_vec v"
  
    have "g_inner f (\<lambda>_. 1) = v \<bullet> vec n (\<lambda>_. 1)"
      unfolding g_inner_conv f_def fun_of_vec[OF v_def(1), symmetric] by simp
    also have "... = v \<bullet> (n \<cdot>\<^sub>v unit)"
      using n_gt_0 unfolding unit_def
      by (intro arg_cong2[where f="(\<bullet>)"] refl eq_vecI) auto
    also have "... = n * (v \<bullet> unit)"
      using v_def(1) unit_vec scalar_prod_smult_distrib by auto
    also have "... = 0"
      using v_def(3) by simp
    finally have 0: "g_inner f (\<lambda>_. 1) = 0" by simp 
  
    have "\<bar>\<Sum>a \<in> arcs G. f(head G a) * f(tail G a)\<bar> = d * \<bar>g_inner f (g_step f)\<bar>"
      unfolding g_inner_step_eq using d_gt_0 by simp
    also have "... = d * \<bar>vec n (f \<circ> enum_verts) \<bullet> (A *\<^sub>v vec n (f \<circ> enum_verts))\<bar>"
      unfolding g_inner_conv g_step_conv by simp
    also have "... = d * \<bar>v \<bullet> (A *\<^sub>v v)\<bar>"
      unfolding f_def fun_of_vec[OF v_def(1), symmetric] by simp
    also have "... = d * \<bar>\<alpha>\<bar> * \<bar>(v \<bullet> v)\<bar>"
      unfolding v_def(5) using v_def(1) by (simp add:abs_mult)
    also have "... = d * \<gamma>\<^sub>2 * r_norm_vec v^2"
      unfolding norm_vec_sq_real[OF v_def(1),symmetric] v_def(2) by simp
    also have "... = d * \<gamma>\<^sub>2 * g_norm f^2"
      unfolding f_def g_norm_conv fun_of_vec[OF v_def(1), symmetric] by simp
    finally have 1: "\<bar>\<Sum>a \<in> arcs G. f(head G a) * f(tail G a)\<bar> = d * \<gamma>\<^sub>2 * g_norm f^2" by simp
  
    have "r_norm_vec v \<noteq> 0" 
      using r_norm_vec_0_iff[OF v_def(1)] v_def(4) by auto
    hence "g_norm f \<noteq> 0"
      unfolding g_norm_conv f_def fun_of_vec[OF v_def(1), symmetric] by simp
    hence 2: "g_norm f^2 > 0" by simp
  
    have "d * \<gamma>\<^sub>2 * g_norm f^2 \<le> d * \<Lambda> * g_norm f^2"
      unfolding 1[symmetric] by (intro expansionD 0)
    thus ?thesis
      using d_gt_0 2 by simp
  next
    case False
    hence "n = 1" using n_gt_0
      by simp
    hence "\<gamma>\<^sub>2 = 0" using \<gamma>\<^sub>2_eq_0 by simp
  
    then show ?thesis using \<Lambda>_ge_0 by simp
  qed
qed

lemma expansionD2:
  assumes "g_inner f (\<lambda>_. 1) = 0"
  shows "g_norm (g_step f) \<le> \<Lambda> * g_norm f" (is "?L \<le> ?R")
proof -
  have "vec n (f \<circ> enum_verts) \<bullet> unit =vec n (f \<circ> enum_verts) \<bullet> ((1/real n) \<cdot>\<^sub>v vec n (\<lambda>_. 1))"
    unfolding unit_def by (intro arg_cong2[where f="(\<bullet>)"] eq_vecI) auto 
  also have "... = (1/real n) * (vec n (f \<circ> enum_verts) \<bullet> vec n ((\<lambda>_. 1) \<circ> enum_verts))"
    by simp
  also have "... = (1/real n) * g_inner f (\<lambda>_. 1)"
    unfolding g_inner_conv by simp
  also have "... = 0" 
    using assms by simp
  finally have 0: "vec n (f \<circ> enum_verts) \<bullet> unit = 0" by simp

  have "?L = r_norm_vec (A *\<^sub>v vec n (f \<circ> enum_verts))"
    unfolding g_norm_conv g_step_conv by simp
  also have "... \<le> \<Lambda> * r_norm_vec (vec n (f \<circ> enum_verts))"
    unfolding \<Lambda>_eq_\<gamma>\<^sub>2 by (intro \<gamma>\<^sub>2_bound_2 0) auto
  also have "... = ?R"
    unfolding g_norm_conv by simp
  finally show ?thesis by simp
qed

end

text \<open>Lift expansionD2 from pre_expander_graph to pre_expander_graph_spectral.\<close>

lemma (in pre_expander_graph) expansionD2:
  assumes "g_inner f (\<lambda>_. 1) = 0"
  shows "g_norm (g_step f) \<le> \<Lambda> * g_norm f" (is "?L \<le> ?R")
proof -
  interpret "pre_expander_graph_spectral" "G"
    by unfold_locales
  show ?thesis
    using expansionD2[OF assms] by simp
qed


end