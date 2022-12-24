theory Poly_Extras
  imports 
    "HOL-Computational_Algebra.Polynomial"  
    "HOL-Library.Function_Algebras"     
    "Discrete_Summation.Factorials" 
begin

definition Polynomials ("\<bbbP>") 
  where "Polynomials k = {f. \<exists>p. f = poly p \<and> degree p \<le> k}" 

lemma Polynomials_mono: 
  assumes "s \<le> t"
  shows "\<bbbP> s \<subseteq> \<bbbP> t"
  using assms unfolding Polynomials_def by auto

lemma Polynomials_addI:
  assumes "f \<in> \<bbbP> k" "g \<in> \<bbbP> k" 
  shows "(\<lambda>\<omega>. f \<omega> + g \<omega>) \<in> \<bbbP> k"
proof -
  obtain pf pg where fg_def: "f = poly pf" "degree pf  \<le> k" "g = poly pg" "degree pg \<le> k"
    using assms unfolding Polynomials_def by blast
  hence "degree (pf + pg) \<le> k" "(\<lambda>x. f x + g x) = poly (pf + pg)"
    using degree_add_le by auto
  thus ?thesis unfolding Polynomials_def by auto
qed

lemma Polynomials_diffI:
  fixes f g :: "'a :: comm_ring \<Rightarrow> 'a"
  assumes "f \<in> \<bbbP> k" "g \<in> \<bbbP> k" 
  shows "(\<lambda>x. f x - g x) \<in> \<bbbP> k"
proof -
  obtain pf pg where fg_def: "f = poly pf" "degree pf  \<le> k" "g = poly pg" "degree pg \<le> k"
    using assms unfolding Polynomials_def by blast
  hence "degree (pf - pg) \<le> k" "(\<lambda>x. f x - g x) = poly (pf - pg)"
    using degree_diff_le by auto
  thus ?thesis unfolding Polynomials_def by auto
qed

lemma Polynomials_idI:
  "(\<lambda>x. x) \<in> (\<bbbP> 1 :: ('a::comm_ring_1 \<Rightarrow> 'a) set)"
proof -
  have "(\<lambda>x. x) = poly [: 0,(1::'a) :]"
    by (intro ext, auto)
  also have "... \<in> \<bbbP> 1" 
    unfolding Polynomials_def by auto
  finally show ?thesis by simp
qed

lemma Polynomials_constI:
  "(\<lambda>x. c) \<in> \<bbbP> k"
proof -
  have "(\<lambda>x. c) = poly [: c :]"
    by (intro ext, simp)
  also have "... \<in> \<bbbP> k" 
    unfolding Polynomials_def by auto
  finally show ?thesis by simp
qed

lemma Polynomials_multI:
  fixes f g :: "'a :: {comm_ring} \<Rightarrow> 'a"
  assumes "f \<in> \<bbbP> s" "g \<in> \<bbbP> t" 
  shows "(\<lambda>x. f x * g x) \<in> \<bbbP> (s+t)"
proof -
  obtain pf pg where xy_def: "f = poly pf" "degree pf \<le> s" "g = poly pg" "degree pg \<le> t"
    using assms unfolding Polynomials_def by blast

  have "degree (pf * pg) \<le> degree pf + degree pg"
    by (intro degree_mult_le)
  also have "... \<le> s + t" 
    using xy_def by (intro add_mono) auto
  finally have "degree (pf * pg) \<le> s+t" by simp
  moreover have "(\<lambda>x. f x * g x) = poly (pf * pg)"
    using xy_def by auto
  ultimately show ?thesis unfolding Polynomials_def by auto
qed

lemma Polynomials_composeI:
  fixes f g :: "'a :: {comm_semiring_0, semiring_no_zero_divisors} \<Rightarrow> 'a"
  assumes "f \<in> \<bbbP> s" "g \<in> \<bbbP> t" 
  shows "(\<lambda>x. f (g x)) \<in> \<bbbP> (s*t)"
proof -
  obtain pf pg where xy_def: "f = poly pf" "degree pf \<le> s" "g = poly pg" "degree pg \<le> t"
    using assms unfolding Polynomials_def by blast
  have "degree (pf \<circ>\<^sub>p pg) = degree pf * degree pg"
    by (intro degree_pcompose)
  also have "... \<le> s * t"
    using xy_def by (intro mult_mono) auto
  finally have "degree (pf \<circ>\<^sub>p pg) \<le> s * t"
    by simp
  moreover have "(\<lambda>x. f (g x)) = poly (pf \<circ>\<^sub>p pg)"
    unfolding xy_def
    by (intro ext poly_pcompose[symmetric])
  ultimately show ?thesis unfolding Polynomials_def by auto
qed

lemma Polynomials_const_left_multI:
  fixes c :: "'a :: {comm_ring}"
  assumes "f \<in> \<bbbP> k"
  shows "(\<lambda>x. c * f x) \<in> \<bbbP> k"
proof -
  have "(\<lambda>x. c * f x) \<in> \<bbbP> (0+k)"
    by (intro Polynomials_multI Polynomials_constI assms)
  thus ?thesis by simp
qed

lemma Polynomials_const_right_multI:
  fixes c :: "'a :: {comm_ring}"
  assumes "f \<in> \<bbbP> k"
  shows "(\<lambda>x. f x * c) \<in> \<bbbP> k"
proof -
  have "(\<lambda>x. f x * c) \<in> \<bbbP> (k+0)"
    by (intro Polynomials_multI Polynomials_constI assms)
  thus ?thesis by simp
qed

lemma Polynomials_const_divI:
  fixes c :: "'a :: {field}"
  assumes "f \<in> \<bbbP> k"
  shows "(\<lambda>x. f x / c) \<in> \<bbbP> k"
proof -
  have "(\<lambda>x. f x * (1/c)) \<in> \<bbbP> (k+0)"
    by (intro Polynomials_multI Polynomials_constI assms)
  thus ?thesis by simp
qed

lemma Polynomials_ffact: "(\<lambda>x. ffact s (x - y))  \<in> (\<bbbP> s :: ('a :: comm_ring_1  \<Rightarrow> 'a) set)"
proof (induction s arbitrary: y)
  case 0
  then show ?case 
    using Polynomials_constI[where c="1"] by simp
next
  case (Suc s)
  have "(\<lambda>(x :: 'a). ffact (Suc s) (x-y)) = (\<lambda>x. (x-y) * ffact s (x - (y+1)))"
    by (simp add: ffact_Suc algebra_simps)
  also have "... \<in> \<bbbP> (1+s)"
    by (intro Polynomials_multI Suc Polynomials_diffI Polynomials_idI Polynomials_constI)
  finally show ?case by simp
qed

lemmas Polynomials_intros =
  Polynomials_const_divI
  Polynomials_composeI
  Polynomials_const_left_multI
  Polynomials_const_right_multI
  Polynomials_multI
  Polynomials_addI
  Polynomials_diffI
  Polynomials_idI
  Polynomials_constI
  Polynomials_ffact  

end