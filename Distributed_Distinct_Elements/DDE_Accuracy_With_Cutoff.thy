theory DDE_Accuracy_With_Cutoff
  imports DDE_Accuracy_Without_Cutoff
begin

lemma (in semilattice_set) Union:
  assumes "finite I" "I \<noteq> {}"
  assumes "\<And>i. i \<in> I \<Longrightarrow> finite (Z i)"
  assumes "\<And>i. i \<in> I \<Longrightarrow> Z i \<noteq> {}"
  shows "F (\<Union> (Z ` I)) = F ((\<lambda>i. (F (Z i))) ` I)"
  using assms(1,2,3,4)
proof (induction I rule:finite_ne_induct)
  case (singleton x)
  then show ?case by simp
next
  case (insert x I)
  have "F (\<Union> (Z ` insert x I)) = F ((Z x) \<union> (\<Union> (Z ` I)))"
    by simp
  also have "... = f (F (Z x)) (F (\<Union> (Z ` I)))"
    using insert by (intro union finite_UN_I) auto
  also have "... = f (F {F (Z x)}) (F ((\<lambda>i. F (Z i)) ` I))"
    using insert(5,6) by (subst insert(4)) auto
  also have "... = F ({F (Z x)} \<union> (\<lambda>i. F (Z i)) ` I)"
    using insert(1,2) by (intro union[symmetric] finite_imageI) auto
  also have "... = F ((\<lambda>i. F (Z i)) ` insert x I)"
    by simp
  finally show ?case by simp
qed

text \<open>This is similar to the existing @{thm [source] hom_Max_commute} with the crucial difference
that it works even if the function is a homomorphism between distinct lattices. 
An example application is @{term "Max (int ` A) = int (Max A)"}.\<close>

lemma hom_Max_commute':
  assumes "finite A" "A \<noteq> {}"
  assumes "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> max (f x) (f y) = f (max x y)"
  shows "Max (f ` A) = f (Max A)"
  using assms by (induction A rule:finite_ne_induct) auto

context inner_algorithm_fix_A
begin

definition t_1 (* tilde t\<^sub>1 *)
  where "t_1 \<psi> \<sigma> = (Max ((\<lambda>j. \<tau>\<^sub>1 \<psi> A \<sigma> j + \<sigma>) ` {..<b})) - b_exp + 9"

definition t_2 (* tilde t *)
  where "t_2 \<psi> \<sigma> = nat (t_1 \<psi> \<sigma>)"

definition p_1 (* tilde p *) 
  where "p_1 \<psi> \<sigma> = card {j\<in> {..<b}. \<tau>\<^sub>1 \<psi> A \<sigma> j + \<sigma> \<ge> t_2 \<psi> \<sigma>}"

definition A_1 (* tilde A* *)
  where "A_1 \<psi> \<sigma> = 2 ^ t_2 \<psi> \<sigma> * \<rho>' (p_1 \<psi> \<sigma>)"


lemma t_2_eq_t:
  assumes "(f,g,h) \<in> sample_set \<Psi>"
  assumes "\<sigma> \<le> t f"
  shows "t_2 (f,g,h) \<sigma> = t f"
proof -
  have "int (Max (f ` A)) - int b_exp + 9 \<le> int (Max (f ` A)) - 26 + 9"
    using b_exp_ge_26 by (intro add_mono diff_left_mono) auto
  also have "... \<le> int (Max (f ` A))" by simp
  finally have 1:"int (Max (f ` A)) - int b_exp + 9 \<le> int (Max (f ` A))"
    by simp
  have "\<sigma> \<le> int (t f)" using assms(2) by simp
  also have "... = max 0 (t\<^sub>1 f)"
    unfolding t_def t\<^sub>1_def by simp
  also have "... \<le> max 0 (int (Max (f ` A)))"
    unfolding t\<^sub>1_def using 1 by simp
  also have "... = int (Max (f ` A))"
    by simp
  finally have "\<sigma> \<le> int (Max (f ` A))"
    by simp
  hence 0: "int \<sigma> - 1 \<le> int (Max (f ` A))"
    by simp

  have c:"h \<in> sample_set (\<H> k (C6 * b\<^sup>2) [b]\<^sub>S)"
    using assms(1) sample_set_\<Psi> by auto
  hence "range h \<subseteq> sample_set [b]\<^sub>S"
    using \<Psi>\<^sub>3.\<H>_range sample_set_def by (metis imageE)
  hence h_range: "h x < b" for x
    unfolding sample_set_def nat_sample_space_def by auto

  have "(MAX j\<in>{..<b}. \<tau>\<^sub>1 (f, g, h) A \<sigma> j + int \<sigma>) =
    (MAX x\<in>{..<b}. Max ({int (f a) |a. a \<in> A \<and> h (g a) = x} \<union> {-1} \<union> {int \<sigma> -1}))"
    using fin_f[OF assms(1)] by (simp add:max_add_distrib_left max.commute)
  also have "... = Max (\<Union>x<b. {int (f a) |a. a \<in> A \<and> h (g a) = x} \<union> {- 1} \<union> {int \<sigma> - 1})"
    using fin_f[OF assms(1)] b_ne by (intro Max.Union[symmetric]) auto 
  also have "... = Max ({int (f a) |a. a \<in> A} \<union> {- 1, int \<sigma> - 1})"
    using h_range by (intro arg_cong[where f="Max"]) auto
  also have "... = max (Max (int ` f ` A)) (int \<sigma> - 1)"
    using A_nonempty fin_A unfolding Setcompr_eq_image image_image
    by (subst Max.union) auto
  also have "... = max (int (Max (f ` A))) (int \<sigma> - 1)"
    using fin_A A_nonempty by (subst hom_Max_commute') auto
  also have "... = int (Max (f ` A))"
    by (intro max_absorb1 0) 
  finally have "(MAX j\<in>{..<b}. \<tau>\<^sub>1 (f, g, h) A \<sigma> j + int \<sigma>) = Max (f ` A)" by simp

  thus ?thesis
    unfolding t_2_def t_1_def t_def t\<^sub>1_def by (simp del:\<tau>\<^sub>1.simps)
qed

lemma p_1_eq_p:
  assumes "(f,g,h) \<in> sample_set \<Psi>"
  assumes "\<sigma> \<le> t f"
  shows "p_1 (f,g,h) \<sigma> = p (f,g,h)"
proof -
  have "{j \<in> {..<b}. int (t f) \<le> max (\<tau>\<^sub>0 (f, g, h) A j) (int \<sigma> - 1)} = 
    {j \<in> {..<b}. int (t f) \<le> max (\<tau>\<^sub>0 (f, g, h) A j) (- 1)}"
    using assms(2) by auto
  thus ?thesis
    unfolding p_1_def p_def t_2_eq_t[OF assms(1,2)] 
    by (simp add:max_add_distrib_left del:\<tau>\<^sub>0.simps)
qed

lemma A_1_eq_A\<^sub>S:
  assumes "(f,g,h) \<in> sample_set \<Psi>"
  assumes "\<sigma> \<le> t f"
  shows "A_1 (f,g,h) \<sigma> = A\<^sub>S (f,g,h)"
  unfolding A_1_def  A\<^sub>S_def t_2_eq_t[OF assms(1,2)] p_1_eq_p[OF assms(1,2)] by simp

end

end