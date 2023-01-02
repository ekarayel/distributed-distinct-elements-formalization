theory Expander_Graphs
  imports Main 
    "HOL-Library.FuncSet" 
    "HOL-Library.Multiset" 
    "HOL-Types_To_Sets.Types_To_Sets"
    "HOL-Analysis.Finite_Cartesian_Product"
    "Smooth_Manifolds.Analysis_More"
    "HOL-Analysis.Cartesian_Space"
begin

section "Missing Finite Cartesian Product"

lemma pythagoras: 
  fixes v w :: "'a::real_inner"
  assumes "inner v w  = 0"
  shows "norm (v+w)^2 = norm v^2 + norm w^2"  
  using assms by (simp add:power2_norm_eq_inner algebra_simps inner_commute)

definition diag :: "('a :: zero)^'n \<Rightarrow> 'a^'n^'n"
  where "diag v = (\<chi> i j. if i = j then (v $ i) else 0)"

lemma diag_mult_eq: "diag x ** diag y = diag (x * y)"
  unfolding diag_def 
  by (vector matrix_matrix_mult_def) 
   (auto simp add:if_distrib if_distribR sum.If_cases)

definition matrix_norm_bound :: "real^'n^'m \<Rightarrow> real \<Rightarrow> bool"
  where "matrix_norm_bound A l = (\<forall>x. norm (A *v x ) \<le> l * norm x)"

lemma  matrix_norm_boundI:
  assumes "\<And>x. norm (A *v x) \<le> l * norm x"
  shows "matrix_norm_bound A l"
  using assms unfolding matrix_norm_bound_def by simp

lemma matrix_norm_boundD:
  assumes "matrix_norm_bound A l"
  shows "norm (A *v x) \<le> l * norm x"
  using assms unfolding matrix_norm_bound_def by simp

lemma matrix_norm_bound_nonneg:
  fixes A :: "real^'n^'m"
  assumes "matrix_norm_bound A l"
  shows "l \<ge> 0" 
proof -
  have "0 \<le> norm (A *v 1)" by simp
  also have "... \<le> l * norm (1::real^'n)" 
    using assms(1) unfolding matrix_norm_bound_def by simp
  finally have "0 \<le> l  * norm (1::real^'n)"
    by simp
  moreover have "norm (1::real^'n) > 0"
    by simp
  ultimately show ?thesis 
    by (simp add: zero_le_mult_iff)
qed

lemma  matrix_norm_bound_0: 
  assumes "matrix_norm_bound A 0" 
  shows "A = (0::real^'n^'m)"
proof (intro iffD2[OF matrix_eq] allI)
  fix x :: "real^'n"
  have "norm (A *v x) = 0"
    using assms unfolding matrix_norm_bound_def by simp
  thus "A *v x = 0 *v x"
    by simp
qed

lemma matrix_norm_bound_diag:
  fixes x :: "real^'n"
  assumes "\<And>i. \<bar>x $ i\<bar> \<le> l"
  shows "matrix_norm_bound (diag x) l"
proof (rule matrix_norm_boundI)
  fix y :: "real^'n"

  have l_ge_0: "l \<ge> 0" using assms by fastforce

  have a: "\<bar>x $ i * v\<bar> \<le> \<bar>l * v\<bar>" for v i
    using l_ge_0 assms by (simp add:abs_mult mult_right_mono)

  have "norm (diag x *v y) = sqrt (\<Sum>i \<in> UNIV. (x $ i * y $ i)^2)"
    unfolding matrix_vector_mult_def diag_def norm_vec_def L2_set_def
    by (auto simp add:if_distrib if_distribR sum.If_cases)
  also have "... \<le> sqrt (\<Sum>i \<in> UNIV. (l * y $ i)^2)"
    by (intro real_sqrt_le_mono sum_mono iffD1[OF abs_le_square_iff] a)
  also have "... = l * norm y"
    using l_ge_0 by (simp add:norm_vec_def L2_set_def algebra_simps 
        sum_distrib_left[symmetric] real_sqrt_mult)
  finally show "norm (diag x *v y) \<le> l * norm y" by simp
qed

lemma vector_scaleR_matrix_ac_2: "b *\<^sub>R (A::real^'n^'m) *v x = b *\<^sub>R (A *v x)" 
  unfolding vector_transpose_matrix[symmetric]  transpose_scalar
  by (intro vector_scaleR_matrix_ac)

lemma matrix_vector_mul_assoc_2: 
  fixes x :: "('a::comm_semiring_1)^_"
  shows "(x v* A) v* B= x v* (A ** B)"
  unfolding transpose_matrix_vector[symmetric] matrix_transpose_mul matrix_vector_mul_assoc by simp

lemma  matrix_norm_bound_scale: 
  assumes "matrix_norm_bound A l"
  shows "matrix_norm_bound (b *\<^sub>R A) (\<bar>b\<bar> * l)"
proof (intro matrix_norm_boundI)
  fix x
  have "norm (b *\<^sub>R A *v x) = norm (b *\<^sub>R (A *v x))" 
    by (metis transpose_scalar vector_scaleR_matrix_ac vector_transpose_matrix)
  also have "... = \<bar>b\<bar> * norm (A *v x)" 
    by simp
  also have "... \<le> \<bar>b\<bar> * (l * norm x)"
    using assms matrix_norm_bound_def by (intro mult_left_mono) auto
  also have "... \<le> (\<bar>b\<bar> * l) * norm x" by simp
  finally show "norm (b *\<^sub>R A *v x) \<le> (\<bar>b\<bar> * l) * norm x" by simp
qed

section \<open>Expander Graphs - Algebra\<close>

definition spec_bound :: "real^'n^'n \<Rightarrow> real \<Rightarrow> bool"
  where "spec_bound A l = (l \<ge> 0 \<and> (\<forall>v. inner v 1 = 0 \<longrightarrow> norm (A *v v) \<le> l * norm v))"

lemma spec_boundD1:
  assumes "spec_bound A l"
  shows "0 \<le> l" 
  using assms unfolding spec_bound_def by simp

lemma spec_boundD2:
  assumes "spec_bound A l"
  assumes "inner v 1 = 0 "
  shows "norm (A *v v) \<le> l * norm v" 
  using assms unfolding spec_bound_def by simp

definition nonneg_mat :: "real^'n^'m \<Rightarrow> bool"
  where "nonneg_mat A = (\<forall>i j. (A $ i) $ j \<ge> 0)"

lemma nonneg_mat_prod:
  assumes "nonneg_mat A" "nonneg_mat B"
  shows "nonneg_mat (A ** B)"
  using assms unfolding nonneg_mat_def matrix_matrix_mult_def 
  by (auto intro:sum_nonneg)

lemma nonneg_mat_transpose:
  "nonneg_mat (transpose A) = nonneg_mat A"
  unfolding nonneg_mat_def transpose_def 
  by auto

definition markov :: "real^'n^'n \<Rightarrow> bool"
  where "markov A = (nonneg_mat A \<and> A *v 1  = 1 \<and> 1 v* A = 1)"

definition stat :: "real^'n"
  where "stat = (1 / real CARD('n)) *\<^sub>R 1"

definition J :: "real^'n^'n"
  where "J = (\<chi> i j. 1 / real CARD('n))"

lemma inner_1_1: "inner 1 (1::real^'n) = CARD('n)"
  unfolding inner_vec_def by simp

lemma markov_apply:
  assumes "markov A"
  shows "A *v 1 = 1" "1 v* A = 1"
  using assms unfolding markov_def by auto

lemma markov_transpose:
  "markov A = markov (transpose A)"
  unfolding markov_def nonneg_mat_transpose by auto

definition proj_unit :: "real^'n \<Rightarrow> real^'n"
  where "proj_unit v = (inner 1 v) *\<^sub>R stat"

definition proj_rem :: "real^'n \<Rightarrow> real^'n" 
  where "proj_rem v = v - proj_unit v"

lemma proj_rem_orth: "inner 1 (proj_rem v) = 0"
  unfolding proj_rem_def proj_unit_def inner_diff_right stat_def
  by (simp add:inner_1_1)

lemma split_vec: "v = proj_unit v + proj_rem v" 
  unfolding proj_rem_def by simp

lemma apply_J: "J *v x = proj_unit x"
proof (intro iffD2[OF vec_eq_iff] allI)
  fix i
  have "(J *v x) $ i = inner (\<chi> j. 1 / real CARD('a)) x" 
    unfolding matrix_vector_mul_component J_def by simp
  also have "... = inner stat x"
    unfolding stat_def scaleR_vec_def by auto
  also have "... = (proj_unit x) $ i"
    unfolding proj_unit_def stat_def by simp
  finally show "(J *v x) $ i = (proj_unit x) $ i" by simp
qed 

fun matrix_pow where 
  "matrix_pow A 0 = mat 1" |
  "matrix_pow A (Suc n) = A ** (matrix_pow A n)"

lemma markov_orth_inv: 
  assumes "markov A"
  assumes "inner x 1 = 0"
  shows "inner (A *v x) 1 = 0"
proof -
  have "inner (A *v x) 1 = inner x (1 v* A)"
    using dot_lmul_matrix inner_commute by metis
  also have "... = inner x 1"
    using markov_apply[OF assms(1)] by simp
  also have "... = 0"
    using assms(2) by simp
  finally show ?thesis by simp
qed

lemma markov_mult:
  assumes "markov A" "markov B"
  shows "markov (A ** B)"
proof -
  have "nonneg_mat (A ** B)"
    using assms unfolding markov_def by (intro nonneg_mat_prod) auto
  moreover have "(A ** B) *v 1 = 1" 
    using assms unfolding markov_def
    unfolding matrix_vector_mul_assoc[symmetric] by simp
  moreover have "1 v* (A ** B) = 1" 
    using assms unfolding markov_def
    unfolding matrix_vector_mul_assoc_2[symmetric] by simp
  ultimately show ?thesis
    unfolding markov_def by simp
qed

lemma markov_orth_inv_pow: 
  assumes "markov A"
  assumes "inner x 1 = 0"
  shows "inner (matrix_pow A k *v x) 1 = 0"
proof (induction k)
  case 0
  then show ?case using assms(2) by simp
next
  case (Suc k)
  have "inner (A *v ( matrix_pow A k *v x)) 1 = 0"
    by (intro markov_orth_inv[OF assms(1)] Suc)
  then show ?case by (simp add:matrix_vector_mul_assoc)
qed

lemma spec_bound_prod: 
  assumes "markov A" "markov B"
  assumes "spec_bound A la" "spec_bound B lb"
  shows "spec_bound (A ** B) (la*lb)"
proof -
  have la_ge_0: "la \<ge> 0" using spec_boundD1[OF assms(3)] by simp

  have "norm ((A ** B) *v x) \<le> (la * lb) * norm x" if "inner x 1 = 0" for x
  proof -
    have "norm ((A ** B) *v x) = norm (A *v (B *v x))"
      by (simp add:matrix_vector_mul_assoc)
    also have "... \<le> la * norm (B *v x)"
      by (intro spec_boundD2[OF assms(3)] markov_orth_inv that assms(2))
    also have "... \<le> la * (lb * norm x)" 
      by (intro spec_boundD2[OF assms(4)] mult_left_mono that la_ge_0)
    finally show ?thesis by simp
  qed
  moreover have "la * lb \<ge> 0"
    using la_ge_0 spec_boundD1[OF assms(4)] by simp
  ultimately show ?thesis
    using spec_bound_def by auto
qed

(* SHOULD FOLLOW FROM LAST *)
lemma spec_bound_pow: 
  assumes "markov A"
  assumes "spec_bound A l"
  shows "spec_bound (matrix_pow A k) (l^k)"
proof (induction k)
  case 0
  then show ?case unfolding spec_bound_def by simp
next
  case (Suc k)
  have "norm (matrix_pow A (Suc k) *v x) \<le> l^(Suc k) * norm x" if "inner x 1 = 0" for x
  proof -
    have "norm (matrix_pow A (Suc k) *v x) = norm (A *v (matrix_pow A k *v x))"
      by (simp add:matrix_vector_mul_assoc)
    also have "... \<le> l * norm (matrix_pow A k *v x)"
      by (intro spec_boundD2[OF assms(2)] markov_orth_inv_pow that assms(1)) 
    also have "... \<le> l * (l^k * norm x)"
      by (intro mult_left_mono spec_boundD2[OF Suc] that spec_boundD1[OF assms(2)])
    also have "... = l^(Suc k) * norm x"
      by simp
    finally show ?thesis
      by simp
  qed
  moreover have "l^Suc k \<ge> 0" 
    using spec_boundD1[OF assms(2)] by simp
  ultimately show ?case 
    unfolding spec_bound_def by simp
qed

(* REMOVE *)
lemma spec_bound_J: "spec_bound (J :: real^'n^'n) 0"
proof -
  have "norm (J *v v) = 0" if "inner v 1 = 0" for v :: "real^'n"
  proof -
    have "inner (proj_unit v + proj_rem v) 1 = 0"
      using that by (subst (asm) split_vec[of "v"], simp)
    hence "inner (proj_unit v) 1 = 0"
      using proj_rem_orth inner_commute unfolding inner_add_left 
      by (metis add_cancel_left_right)
    hence "proj_unit v = 0"
      unfolding proj_unit_def stat_def by simp
    hence "J *v v = 0"
      unfolding apply_J by simp
    thus ?thesis by simp
  qed
  thus ?thesis
    unfolding spec_bound_def by simp
qed

lemma matrix_decomposition_lemma_aux:
  fixes A :: "real^'n^'n"
  assumes "markov A"
  shows "spec_bound A l \<longleftrightarrow> matrix_norm_bound (A - (1-l) *\<^sub>R J) l" (is "?L \<longleftrightarrow> ?R")
proof 
  assume a:"?L"
  hence l_ge_0: "l \<ge> 0" using spec_boundD1 by auto 
  show "?R" 
  proof (rule matrix_norm_boundI)
    fix x :: "real^'n"
    have "(A - (1-l) *\<^sub>R J) *v x = A *v x - (1-l) *\<^sub>R (proj_unit x)"
      by (simp add:algebra_simps vector_scaleR_matrix_ac_2 apply_J)
    also have "... = A *v proj_unit x + A *v proj_rem x - (1-l) *\<^sub>R (proj_unit x)"
      by (subst split_vec[of "x"], simp add:algebra_simps)
    also have "... = proj_unit x + A *v proj_rem x - (1-l) *\<^sub>R (proj_unit x)"
      using markov_apply[OF assms(1)]
      unfolding proj_unit_def stat_def by (simp add:algebra_simps)
    also have "... = A *v proj_rem x + l *\<^sub>R proj_unit x" (is "_ = ?R1")
      by (simp add:algebra_simps)
    finally have d:"(A - (1-l) *\<^sub>R J) *v x = ?R1" by simp

    have "inner (l *\<^sub>R proj_unit x) (A *v proj_rem x) = 
      inner ((l * inner 1 x / real CARD('n)) *\<^sub>R 1 v* A) (proj_rem x)"
      by (subst dot_lmul_matrix[symmetric]) (simp add:proj_unit_def stat_def) 
    also have "... = (l * inner 1 x / real CARD('n)) * inner 1 (proj_rem x)" 
      unfolding scaleR_vector_matrix_assoc markov_apply[OF assms] by simp
    also have "... = 0"
      unfolding proj_rem_orth by simp
    finally have b:"inner (l *\<^sub>R proj_unit x) (A *v proj_rem x) = 0" by simp

    have c: "inner (proj_rem x) (proj_unit x) = 0" 
      using proj_rem_orth[of "x"]
      unfolding proj_unit_def stat_def by (simp add:inner_commute)

    have "norm (?R1)^2 = norm (A *v proj_rem x)^2 + norm (l *\<^sub>R proj_unit x)^2" 
      using b by (intro pythagoras) (simp add:inner_commute)
    also have "... \<le> (l * norm (proj_rem x))^2 + norm (l *\<^sub>R proj_unit x)^2" 
      using proj_rem_orth[of "x"]
      by (intro add_mono power_mono spec_boundD2 a) (auto simp add:inner_commute)
    also have "... = l^2 * (norm (proj_rem x)^2 + norm (proj_unit x)^2)"
      by (simp add:algebra_simps)
    also have "... = l^2 * (norm (proj_rem x + proj_unit x)^2)"
      using c by (subst pythagoras) auto
    also have "... = l^2 * norm x^2"
      by (subst (3) split_vec[of "x"]) (simp add:algebra_simps)
    also have "... = (l * norm x)^2"
      by (simp add:algebra_simps)
    finally have "norm (?R1)^2 \<le> (l * norm x)^2" by simp
    hence "norm (?R1) \<le> l * norm x"
      using l_ge_0 by (subst (asm) power_mono_iff) auto

    thus "norm ((A - (1-l) *\<^sub>R J) *v x) \<le> l * norm x"
      unfolding d by simp
  qed
next  
  assume a:"?R" 
  have "norm (A *v x) \<le> l * norm x" if "inner x 1 = 0" for x 
  proof -
    have "(1 - l) *\<^sub>R J *v x = (1 - l) *\<^sub>R (proj_unit x)" 
      by (simp add:vector_scaleR_matrix_ac_2 apply_J)
    also have "... = 0"
      unfolding proj_unit_def using that by (simp add:inner_commute)
    finally have b: "(1 - l) *\<^sub>R J *v x = 0" by simp

    have "norm (A *v x) = norm ((A - (1-l) *\<^sub>R J) *v x  + ((1-l) *\<^sub>R J) *v x)"
      by (simp add:algebra_simps)
    also have "... \<le> norm ((A - (1-l) *\<^sub>R J) *v x) + norm (((1-l) *\<^sub>R J) *v x)"
      by (intro norm_triangle_ineq)
    also have "... \<le> l * norm x + 0"
      using a b unfolding  matrix_norm_bound_def by (intro add_mono, auto)
    also have "... = l * norm x"
      by simp
    finally show ?thesis by simp
  qed

  moreover have "l \<ge> 0" 
    using a matrix_norm_bound_nonneg by blast

  ultimately show "?L" 
    unfolding spec_bound_def by simp
qed

lemma matrix_decomposition_lemma:
  fixes A :: "real^'n^'n"
  assumes "markov A"
  shows "spec_bound A l \<longleftrightarrow> (\<exists>E. A = (1-l) *\<^sub>R J + l *\<^sub>R E \<and> matrix_norm_bound E 1 \<and> l \<ge> 0)" 
    (is "?L \<longleftrightarrow> ?R")
proof -
  have "?L \<longleftrightarrow> matrix_norm_bound (A - (1-l) *\<^sub>R J) l" 
    using matrix_decomposition_lemma_aux[OF assms] by simp
  also have "... \<longleftrightarrow> ?R"
  proof
    assume a:"matrix_norm_bound (A - (1 - l) *\<^sub>R J) l"
    hence l_ge_0: "l \<ge> 0" using matrix_norm_bound_nonneg by auto
    define E where "E = (1/l) *\<^sub>R (A - (1-l) *\<^sub>R J)"
    have "A = J" if "l = 0" 
    proof -
      have "matrix_norm_bound (A - J) 0"
        using a that by simp
      hence "A - J = 0" using matrix_norm_bound_0 by blast
      thus "A = J" by simp
    qed
    hence "A = (1-l) *\<^sub>R J + l *\<^sub>R E"
      unfolding E_def by simp
    moreover have "matrix_norm_bound E 1" 
    proof (cases "l = 0")
      case True
      hence "E = 0" if "l = 0"
        unfolding E_def by simp
      thus "matrix_norm_bound E 1" if "l = 0"
        using that unfolding matrix_norm_bound_def by auto
    next
      case False
      hence "l > 0" using l_ge_0 by simp
      moreover have "matrix_norm_bound E (\<bar>1 / l\<bar>* l)"
        unfolding E_def
        by (intro matrix_norm_bound_scale a)
      ultimately show ?thesis by auto
    qed
    ultimately show ?R using l_ge_0 by auto
  next
    assume a:?R
    then obtain E where E_def: "A = (1 - l) *\<^sub>R J + l *\<^sub>R E"  "matrix_norm_bound E 1" "l \<ge> 0"
      by auto
    have "matrix_norm_bound (l *\<^sub>R E) (abs l*1)" 
      by (intro matrix_norm_bound_scale E_def(2))
    moreover have "l \<ge> 0" using E_def by simp 
    moreover have " l *\<^sub>R E = (A - (1 - l) *\<^sub>R J)" 
      using E_def(1) by simp
    ultimately show "matrix_norm_bound (A - (1 - l) *\<^sub>R J) l"
      by simp  
  qed
  finally show ?thesis by simp
qed

lemma hitting_property:
  fixes S :: "('n :: finite) set"
  assumes l_range: "l \<in> {0..1}"
  defines "P \<equiv> diag (\<chi> i. of_bool (i \<in> S))"
  defines "\<mu> \<equiv> card S / CARD('n)"
  assumes "\<And>M. M \<in> set Ms \<Longrightarrow> spec_bound M l \<and> markov M"
  shows "inner (foldl (\<lambda>x M. P *v (M *v x)) (P *v stat) Ms) 1 \<le> (\<mu> + l * (1-\<mu>))^(length Ms+1)"
proof -
  define t :: "real^'n" where "t = (\<chi> i. of_bool (i \<in> S))"
  define r where "r = foldl (\<lambda>x M. P *v (M *v x)) (P *v stat) Ms"
  have P_proj: "P ** P = P"
    unfolding P_def diag_mult_eq by (intro arg_cong[where f="diag"]) (vector)

  have P_1_left: "1 v* P = t"
    unfolding P_def diag_def vector_matrix_mult_def t_def by simp

  have P_1_right: "P *v 1 = t"
    unfolding P_def diag_def matrix_vector_mult_def t_def by simp

  have P_norm :"matrix_norm_bound P 1"
    unfolding P_def by (intro matrix_norm_bound_diag) simp

  have norm_t: "norm t = sqrt (real (card S))" 
    unfolding t_def norm_vec_def L2_set_def of_bool_def
    by (simp add:sum.If_cases if_distrib if_distribR)

  have \<mu>_range: "\<mu> \<ge> 0" "\<mu> \<le> 1" 
    unfolding \<mu>_def by (auto simp add:card_mono) 

  define condition :: "real^'n \<Rightarrow> nat \<Rightarrow> bool" 
    where "condition = (\<lambda>x n. norm x \<le> (\<mu> + l * (1-\<mu>))^n * sqrt (card S)/CARD('n) \<and> P *v x = x)" 

  have a:"condition r (length Ms)"
    unfolding r_def using assms(4)
  proof (induction Ms rule:rev_induct)
    case Nil
    have "norm (P *v stat) = (1 / real CARD('n)) * norm t"
      unfolding stat_def matrix_vector_mult_scaleR P_1_right by simp
    also have "... \<le>  (1 / real CARD('n)) * sqrt (real (card S))"
      using  norm_t by (intro mult_left_mono) auto
    also have "... = sqrt (card S)/CARD('n)" by simp
    finally have "norm (P *v stat) \<le> sqrt (card S)/CARD('n)" by simp
    moreover have "P *v (P *v stat) = P *v stat"
      unfolding matrix_vector_mul_assoc P_proj by simp
    ultimately show ?case unfolding condition_def by simp
  next
    case (snoc M xs)
    hence "spec_bound M l \<and> markov M"
        using snoc(2) by simp
    then obtain E where E_def: "M = (1-l) *\<^sub>R J + l *\<^sub>R E" "matrix_norm_bound E 1" 
      using iffD1[OF matrix_decomposition_lemma] by auto

    define y where "y = foldl (\<lambda>x M. P *v (M *v x)) (P *v stat) xs"
    have b:"condition y (length xs)"
      using snoc unfolding y_def by simp
    hence a:"P *v y = y" using condition_def by simp

    have "norm (P *v (M *v y)) = norm (P *v ((1-l)*\<^sub>R J *v y) + P *v (l *\<^sub>R E *v y))"
      by (simp add:E_def algebra_simps)
    also have "... \<le> norm (P *v ((1-l)*\<^sub>R J *v y)) + norm (P *v (l *\<^sub>R E *v y)) "
      by (intro norm_triangle_ineq)
    also have "... = (1 - l) * norm (P *v (J *v y)) + l * norm (P *v (E *v y))"
      using l_range
      by (simp add:vector_scaleR_matrix_ac_2 matrix_vector_mult_scaleR)
    also have "... = (1-l) * \<bar>inner 1 (P *v y)/real CARD('n)\<bar> * norm t + l * norm (P *v (E *v y))"
      by (subst a[symmetric]) 
        (simp add:apply_J proj_unit_def stat_def P_1_right matrix_vector_mult_scaleR)
    also have "... = (1-l) * \<bar>inner t y\<bar>/real CARD('n) * norm t + l * norm (P *v (E *v y))"
      by (subst dot_lmul_matrix[symmetric]) (simp add:P_1_left)
    also have "... \<le> (1-l) * (norm t * norm y) / real CARD('n) * norm t + l * (1 * norm (E *v y))"
      using P_norm Cauchy_Schwarz_ineq2 l_range
      by (intro add_mono mult_right_mono mult_left_mono divide_right_mono matrix_norm_boundD) auto
    also have "... = (1-l) * \<mu> * norm y + l * norm (E *v y)"
      unfolding \<mu>_def norm_t by simp
    also have "... \<le> (1-l) * \<mu> * norm y + l * (1 * norm y)"
      using \<mu>_range l_range
      by (intro add_mono matrix_norm_boundD mult_left_mono E_def) auto
    also have "... = (\<mu> + l * (1-\<mu>)) * norm y"
      by (simp add:algebra_simps)
    also have "... \<le> (\<mu> + l * (1-\<mu>)) * ((\<mu> + l * (1-\<mu>))^length xs * sqrt (card S)/CARD('n))"
      using b \<mu>_range l_range unfolding condition_def
      by (intro mult_left_mono) auto
    also have "... = (\<mu> + l * (1-\<mu>))^(length xs +1) * sqrt (card S)/CARD('n)"
      by simp
    finally have "norm (P *v (M *v y)) \<le> (\<mu> + l * (1-\<mu>))^(length xs +1) * sqrt (card S)/CARD('n)"
      by simp

    moreover have "P *v (P *v (M *v y)) = P *v (M *v y)"
      unfolding matrix_vector_mul_assoc matrix_mul_assoc P_proj 
      by simp

    ultimately have "condition (P *v (M *v y)) (length (xs@[M]))"
      unfolding condition_def by simp
  
    then show ?case 
      unfolding y_def by simp
  qed

  have "inner r 1 = inner (P *v r) 1"
    using a condition_def by simp
  also have "... = inner (1 v* P) r"
    unfolding dot_lmul_matrix by (simp add:inner_commute)
  also have "... = inner t r"
    unfolding P_1_left by simp
  also have "... \<le> norm t * norm r"
    by (intro norm_cauchy_schwarz)
  also have "... \<le> sqrt (card S) * ((\<mu> + l * (1-\<mu>))^(length Ms) * sqrt(card S)/CARD('n))"
    using a unfolding condition_def norm_t
    by (intro mult_mono) auto
  also have "... = (\<mu> + 0) * ((\<mu> + l * (1-\<mu>))^(length Ms))"
    by (simp add:\<mu>_def)
  also have "... \<le> (\<mu> + l * (1-\<mu>)) * (\<mu> + l * (1-\<mu>))^(length Ms)"
    using \<mu>_range l_range
    by (intro mult_right_mono zero_le_power add_mono) auto
  also have "... = (\<mu> + l * (1-\<mu>))^(length Ms+1)" by simp
  finally show ?thesis 
    unfolding r_def by simp
qed

section \<open>Expander Graphs\<close>

record implicit_graph =
  ig_size :: nat
  ig_degree :: nat
  ig_step :: "nat \<Rightarrow> nat \<Rightarrow> nat"

definition ig_edges where "ig_edges g = 
  {# (x, ig_step g x y). (x,y) \<in># (mset (List.product [0..<ig_size g] [0..<ig_degree g])) #}"

definition in_degree where "in_degree g k = size {# (i,j) \<in># ig_edges g. j = k #}"
definition out_degree where "out_degree g k = size {# (i,j) \<in># ig_edges g. i = k #}"

(* typedef / locale? *)
definition implicit_graph where
  "implicit_graph g = (
    ig_size g > 0 \<and> 
    ig_degree g > 0 \<and> 
    ig_step g \<in> {..<ig_size g} \<rightarrow> {..<ig_degree g} \<rightarrow> {..<ig_size g} \<and>
    (\<forall>i<ig_size g. in_degree g i = ig_degree g))"

definition spectral_bound where 
  "spectral_bound g \<alpha> = (\<forall>x. 
    sum x {..<ig_size g} = (0::real) \<longrightarrow> undefined )"

definition matrix_vec_mult ::
  "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real)" where
  "matrix_vec_mult n M x i = (\<Sum>j \<in> {..<n::nat}. M i j * x j)"


definition myrel :: "nat \<Rightarrow> int \<Rightarrow> bool" 
  where "myrel n x = (int n = x)"

definition myzero :: int where "myzero = 0" 

locale foo =
  assumes "True"
begin
context
  includes lifting_syntax 
begin

lemma [transfer_rule]: "((myrel ===> ((=))) ===> ((=))) (All) (Ball {0..})" 
  unfolding myrel_def apply (intro rel_funI) sorry

lemma [transfer_rule]: "myrel (0) myzero" 
  unfolding myrel_def myzero_def by auto

lemma [transfer_rule]: "(myrel ===> myrel) (Suc) ((+) 1)" 
  unfolding myrel_def by auto

lemma [transfer_rule]: "(myrel ===> myrel ===> ((=))) (\<le>) (\<le>)" 
  unfolding myrel_def by fastforce


end

lemma a:"0 \<le> (0::nat)" by simp
lemma b:"\<forall>x. x \<ge> (0::nat)" by simp

end

lemma "True"
  using foo.a[transferred] foo.b[transferred] sorry

lemma c:
   "(myzero \<le> (myzero))" apply transfer sorry

lemma "(x::int) < x+1"
  apply transfer
  apply (rule a)


end



lemma "True"
  using finite_dimensional_vector_space_def
  sorry

  
lemma test:
  assumes "n > 0"
  shows "True"
proof -
  define A where "A = {..<n}"

  have b:"True" if "\<exists>Rep Abs. type_definition Rep Abs A"
    by simp

  have c:"A \<noteq> {}" sorry
  note x = b[cancel_type_definition, OF c]
  show ?thesis by simp
qed



end