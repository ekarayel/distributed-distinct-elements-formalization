theory DDE_Accuracy_With_Cutoff
  imports DDE_Accuracy_Without_Cutoff DDE_Cutoff_Level
begin

hide_const Quantum.Z
unbundle intro_cong_syntax

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
  hence h_range: "h x < b" for x
    using h_range_1 by simp

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
    using assms(2) unfolding le_max_iff_disj by simp
  thus ?thesis
    unfolding p_1_def p_def t_2_eq_t[OF assms(1,2)] 
    by (simp add:max_add_distrib_left del:\<tau>\<^sub>0.simps)
qed

lemma A_1_eq_A\<^sub>S:
  assumes "(f,g,h) \<in> sample_set \<Psi>"
  assumes "\<sigma> \<le> t f"
  shows "A_1 (f,g,h) \<sigma> = A\<^sub>S (f,g,h)"
  unfolding A_1_def  A\<^sub>S_def t_2_eq_t[OF assms(1,2)] p_1_eq_p[OF assms(1,2)] by simp

lemma l_6_9: "measure \<Psi> {\<psi>. \<exists>\<sigma> \<le> s\<^sub>M. \<bar>A_1 \<psi> \<sigma> - real Y\<bar> > \<delta> * Y} \<le> 1/2^4" 
  (is "?L \<le> ?R")
proof -
  have "measure \<Psi> {\<psi>. \<exists>\<sigma> \<le> s\<^sub>M. \<bar>A_1 \<psi> \<sigma> - real Y\<bar> > \<delta> * real Y} \<le>
    measure \<Psi> {(f,g,h). \<bar>A\<^sub>S (f,g,h) - real Y\<bar> >  \<delta> * real Y \<or> t f < s\<^sub>M}"
  proof (rule pmf_mono)
    fix \<psi> 
    assume a:"\<psi> \<in> {\<psi>. \<exists>\<sigma>\<le>s\<^sub>M.  \<delta> * real Y < \<bar>A_1 \<psi> \<sigma> - real Y\<bar>}"
    assume d:"\<psi> \<in> set_pmf (sample_pmf \<Psi>)"
    obtain \<sigma> where b:"\<sigma> \<le> s\<^sub>M" and c:" \<delta> * real Y < \<bar>A_1 \<psi> \<sigma> - real Y\<bar>"
      using a by auto
    obtain f g h where \<psi>_def: "\<psi> = (f,g,h)" by (metis prod_cases3)
    hence e:"(f,g,h) \<in> sample_set \<Psi>"
      using d unfolding sample_space_alt[OF sample_space_\<Psi>] by simp

    show "\<psi> \<in> {(f, g, h). \<delta> * real Y < \<bar>A\<^sub>S (f, g, h) - real Y\<bar> \<or> t f < s\<^sub>M}" 
    proof (cases "t f \<ge> s\<^sub>M")
      case True
      hence f:"\<sigma> \<le> t f" using b by simp
      have "\<delta> * real Y < \<bar>A\<^sub>S \<psi> - real Y\<bar>"
        using A_1_eq_A\<^sub>S[OF e f] c unfolding \<psi>_def by simp      
      then show ?thesis unfolding \<psi>_def by simp
    next
      case False
      then show ?thesis unfolding \<psi>_def by simp
    qed
  qed
  also have "... \<le> 1/2^4"
    using l_6_8 by simp
  finally show ?thesis by simp
qed

lemma estimate1_eq: 
  assumes "j < l"
  shows "estimate1 (\<tau>\<^sub>2 \<omega> A \<sigma>, \<sigma>) j = A_1 (\<omega> j) \<sigma>" (is "?L = ?R")
proof -
  define t where "t = max 0 (Max ((\<tau>\<^sub>2 \<omega> A \<sigma> j) ` {..<b}) + \<sigma> - \<lfloor>log 2 b\<rfloor> + 9)"
  define p where "p = card { k. k \<in> {..<b} \<and> (\<tau>\<^sub>2 \<omega> A \<sigma> j k) + \<sigma> \<ge> t }"

  have 0: "int (nat x) = max 0 x" for x
    by simp
  have 1: "\<lfloor>log 2 b\<rfloor> = b_exp"
    unfolding b_def by simp

  have "b > 0" 
    using b_min by simp
  hence 2: " {..<b} \<noteq> {}" by auto

  have "t = int (nat (Max ((\<tau>\<^sub>2 \<omega> A \<sigma> j) ` {..<b}) + \<sigma> - b_exp + 9))"
    unfolding t_def 0 1 by (rule refl)
  also have "... = int (nat (Max ((\<lambda>x. x + \<sigma>) ` (\<tau>\<^sub>2 \<omega> A \<sigma> j) ` {..<b}) - b_exp + 9))"
    by (intro_cong "[\<sigma>\<^sub>1 int,\<sigma>\<^sub>1 nat,\<sigma>\<^sub>2(+),\<sigma>\<^sub>2(-)]" more:hom_Max_commute) (simp_all add:2 del:s.simps)
  also have "... = int (t_2 (\<omega> j) \<sigma>)"
    using assms
    unfolding t_2_def t_1_def \<tau>\<^sub>2.simps image_image by (simp del:s.simps \<tau>\<^sub>1.simps)
  finally have 3:"t = int (t_2 (\<omega> j) \<sigma>)"
    by simp

  have 4: "p = p_1 (\<omega> j) \<sigma>"
    using assms unfolding p_def p_1_def 3 by (simp del:s.simps)

  have "?L = 2 powr t * ln (1-p/b) / ln(1-1/b)"
    unfolding estimate1.simps \<tau>.simps \<tau>\<^sub>3.simps 
    by (simp only:t_def p_def Let_def)
  also have "... = 2 powr (t_2 (\<omega> j) \<sigma>) * \<rho>' p"
    unfolding 3 \<rho>'_def by (simp del:s.simps)
  also have "... = ?R"
    unfolding A_1_def 3 4 by (simp add:powr_realpow del:s.simps)
  finally show ?thesis
    by blast
qed

lemma l_6_10:
  "measure \<Omega> {\<omega>. (\<exists>\<sigma>\<le>s\<^sub>M. \<delta>*Y < \<bar>estimate (\<tau>\<^sub>2 \<omega> A \<sigma>,\<sigma>)-Y\<bar>) } \<le> \<epsilon>/2"
    (is "?L \<le> ?R")
proof -
  define I :: "real set" where "I = {x. \<bar>x - real Y\<bar> \<le> \<delta>*Y}"

  define \<mu> where "\<mu> = measure \<Psi> {\<psi>. \<exists>\<sigma>\<le>s\<^sub>M. A_1 \<psi> \<sigma>\<notin>I}"

  have int_I: "interval I" 
    unfolding interval_def I_def by auto

  have "\<mu> = measure \<Psi> {\<psi>. \<exists>\<sigma> \<le> s\<^sub>M. \<bar>A_1 \<psi> \<sigma> - real Y\<bar> > \<delta> * Y}"
    unfolding \<mu>_def I_def by (simp add:not_le)
  also have "... \<le>  1 / 2 ^ 4"
    by (intro l_6_9)
  also have "... = 1/ 16" 
    by simp
  finally have 1:"\<mu> \<le> 1 / 16" by simp

  have "(\<mu> + \<Lambda>) \<le> 1/16 + 1/16"
    unfolding \<Lambda>_def by (intro add_mono 1) auto
  also have "... \<le> 1/8" 
    by simp
  finally have 2:"(\<mu> + \<Lambda>) \<le> 1/8" 
    by simp

  hence 0: "(\<mu> + \<Lambda>) \<le> 1/2" 
    by simp

  have "\<mu> \<ge> 0" 
    unfolding \<mu>_def by simp
  hence 3: "\<mu> + \<Lambda> > 0" 
    by (intro add_nonneg_pos \<Lambda>_gt_0)

  have "?L = measure \<Omega> {\<omega>. (\<exists>\<sigma>\<le>s\<^sub>M. \<delta>*Y < \<bar>median l (estimate1 (\<tau>\<^sub>2 \<omega> A \<sigma>,\<sigma>))-Y\<bar>) }"
    by simp
  also have "... = measure \<Omega> {\<omega>. (\<exists>\<sigma>\<le>s\<^sub>M. median l (estimate1 (\<tau>\<^sub>2 \<omega> A \<sigma>,\<sigma>)) \<notin> I)}"
    unfolding I_def by (intro measure_pmf_cong) auto
  also have "... \<le> measure \<Omega> {\<omega>. real(card{i\<in>{..<l}.(\<exists>\<sigma>\<le>s\<^sub>M. A_1 (\<omega> i) \<sigma>\<notin>I)})\<ge> real l/2}"
  proof (rule pmf_mono)
    fix \<omega>
    assume "\<omega> \<in> set_pmf \<Omega>" "\<omega> \<in> {\<omega>. \<exists>\<sigma>\<le>s\<^sub>M. median l (estimate1 (\<tau>\<^sub>2 \<omega> A \<sigma>, \<sigma>)) \<notin> I}" 
    then obtain \<sigma> where \<sigma>_def: "median l (estimate1 (\<tau>\<^sub>2 \<omega> A \<sigma>, \<sigma>)) \<notin> I" "\<sigma>\<le>s\<^sub>M"
      by auto

    have "real l = 2 * real l - real l" 
      by simp
    also have "... \<le> 2 * real l - 2 * card {i. i < l \<and> estimate1 (\<tau>\<^sub>2 \<omega> A \<sigma>, \<sigma>) i \<in> I}"
      using \<sigma>_def median_est[OF int_I, where n="l"] not_less  
      by (intro diff_left_mono Nat.of_nat_mono) (auto simp del:estimate1.simps)
    also have "... = 2 * (real (card {..<l}) -card {i. i < l \<and> estimate1 (\<tau>\<^sub>2 \<omega> A \<sigma>, \<sigma>) i \<in> I})"
      by (simp del:estimate1.simps)
    also have "... = 2 * real (card {..<l} -card {i. i < l \<and> estimate1 (\<tau>\<^sub>2 \<omega> A \<sigma>, \<sigma>) i \<in> I})"
      by (intro_cong "[\<sigma>\<^sub>2 (*)]" more:of_nat_diff[symmetric] card_mono)
        (auto simp del:estimate1.simps)
    also have "... = 2 * real (card ({..<l} - {i. i < l \<and> estimate1 (\<tau>\<^sub>2 \<omega> A \<sigma>, \<sigma>) i \<in> I}))"
      by (intro_cong "[\<sigma>\<^sub>2 (*), \<sigma>\<^sub>1 of_nat]" more:card_Diff_subset[symmetric]) 
        (auto simp del:estimate1.simps)
    also have "... = 2 * real (card {i\<in>{..<l}. estimate1 (\<tau>\<^sub>2 \<omega> A \<sigma>, \<sigma>) i \<notin> I})"
      by (intro_cong "[\<sigma>\<^sub>2 (*), \<sigma>\<^sub>1 of_nat, \<sigma>\<^sub>1 card]") (auto simp del:estimate1.simps)
    also have "... = 2 * real (card {i \<in> {..<l}. A_1 (\<omega> i) \<sigma> \<notin> I})"
      using estimate1_eq by (intro_cong "[\<sigma>\<^sub>2 (*), \<sigma>\<^sub>1 of_nat, \<sigma>\<^sub>1 card]" more:restr_Collect_cong) auto
    also have "... \<le> 2 * real (card {i \<in> {..<l}. (\<exists>\<sigma>\<le>s\<^sub>M. A_1 (\<omega> i) \<sigma> \<notin> I)})"
      using \<sigma>_def(2) by (intro mult_left_mono Nat.of_nat_mono card_mono) auto
    finally have "real l \<le> 2 * real (card {i \<in> {..<l}. (\<exists>\<sigma>\<le>s\<^sub>M. A_1 (\<omega> i) \<sigma> \<notin> I)})"
      by simp
    thus "\<omega> \<in> {\<omega>. real l/2 \<le> real (card {i \<in> {..<l}. \<exists>\<sigma>\<le>s\<^sub>M. A_1 (\<omega> i) \<sigma> \<notin> I})}"
      by simp
  qed
  also have "... = measure \<Omega> {\<omega>. real (card{i\<in>{..<l}. (\<exists>\<sigma>\<le>s\<^sub>M. A_1 (\<omega> i) \<sigma>\<notin>I)}) \<ge> (1/2)*real l}"
    unfolding sample_pmf_alt[OF \<Omega>.sample_space] p_def by simp
  also have "... \<le> exp (- real l * ((1/2) * ln (1 / (\<mu> + \<Lambda>)) - 2 * exp (- 1)))"
    using 0 unfolding \<mu>_def by (intro \<Omega>.tail_bound l_gt_0 \<Lambda>_gt_0) auto
  also have "... = exp (- (real l * ((1/2) * ln (1 / (\<mu> + \<Lambda>)) - 2 * exp (- 1))))"
    by simp
  also have "... \<le> exp (- (real l * ((1/2) * ln 8 - 2 * exp (- 1))))"
    using 2 3 l_gt_0 by (intro iffD2[OF exp_le_cancel_iff] le_imp_neg_le mult_left_mono diff_mono) 
      (auto simp add:divide_simps)
  also have "... \<le> exp (- (real l * (1/4)))"
    by (intro iffD2[OF exp_le_cancel_iff] le_imp_neg_le mult_left_mono of_nat_0_le_iff)
     (approximation 5)
  also have "... \<le> exp (- (C5 * ln (2/ \<epsilon>)*(1/4)))"
    by (intro iffD2[OF exp_le_cancel_iff] le_imp_neg_le mult_right_mono l_lbound) auto
  also have "... = exp ( - ln (2/ \<epsilon>))"
    unfolding C5_def by simp
  also have "... = ?R"
    using \<epsilon>_gt_0 by (subst ln_inverse[symmetric]) auto
  finally show ?thesis 
    by simp
qed

theorem theorem_6_2:
  "measure \<Omega> {\<omega>. \<bar>estimate (\<tau> \<omega> A)- Y\<bar> >  \<delta> * Y} \<le>  \<epsilon>"
  (is "?L \<le> ?R")
proof -
  let ?P = "measure \<Omega>"
  have "?L \<le> ?P {\<omega>. (\<exists>\<sigma>\<le>s\<^sub>M.  \<delta>*real Y<\<bar>estimate (\<tau>\<^sub>2 \<omega> A \<sigma>, \<sigma>)-real Y\<bar>)\<or>s \<omega> A> s\<^sub>M}"
    unfolding \<tau>.simps \<tau>\<^sub>3.simps not_le[symmetric] 
    by (intro pmf_mono) (auto simp del:s.simps estimate.simps) 
  also have "...\<le> ?P {\<omega>. (\<exists>\<sigma>\<le>s\<^sub>M.  \<delta>*real Y<\<bar>estimate (\<tau>\<^sub>2 \<omega> A \<sigma>,\<sigma>)-Y\<bar>)} + ?P {\<omega>. s \<omega> A> s\<^sub>M}"
    by (intro pmf_add) auto
  also have "...\<le>  \<epsilon>/2 +  \<epsilon>/2"
    by (intro add_mono cutoff_level l_6_10) 
  also have "... =  \<epsilon>"
    by simp 
  finally show ?thesis 
    by simp
qed

end

lemma (in inner_algorithm) theorem_6_2:
  assumes "A \<subseteq> {..<n}" "A \<noteq> {}"
  shows "measure \<Omega> {\<omega>. \<bar>estimate (\<tau> \<omega> A)- real (card A)\<bar> >  \<delta> * real (card A)} \<le> \<epsilon>" (is "?L \<le> ?R")
proof -
  interpret inner_algorithm_fix_A
    using assms by unfold_locales auto
  have "?L = measure \<Omega> {\<omega>. \<bar>estimate (\<tau> \<omega> A)- Y\<bar> >  \<delta> * Y}"
    unfolding Y_def by simp
  also have "... \<le> ?R"
    by (intro theorem_6_2)
  finally show ?thesis
    by simp
qed


unbundle no_intro_cong_syntax

end