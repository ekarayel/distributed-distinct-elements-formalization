theory F0
  imports 
    "HOL-Library.Log_Nat"
    "Median_Method.Median"
    "Pseudorandom_Combinators"
begin

definition C3 :: int where "C3 = 17"
definition C6 :: nat where "C6 = 17"

context
  fixes n :: nat
  fixes \<epsilon> :: rat
  fixes \<delta> :: rat
begin

definition b :: nat where "b = nat (\<lceil>1/ \<delta>\<^sup>2\<rceil>)"
definition l :: nat where "l = nat (\<lceil>ln (1/real_of_rat \<epsilon>)\<rceil>)"
definition k :: nat where "k = nat (\<lceil>ln (b\<^sup>2)\<rceil>)"

lemma l_gt_0: "l > 0" sorry
lemma b_gt_0: "b > 0" sorry

definition \<Omega> where 
  "\<Omega> = \<E> ((\<G> 2 n) \<times>\<^sub>S (\<H> 2 n (C6*b\<^sup>2)) \<times>\<^sub>S (\<H> k (C6*b\<^sup>2) b)) l 0.1"

type_synonym f0_state = "(nat \<Rightarrow> nat \<Rightarrow> int) \<times> (nat)"

fun is_too_large :: "(nat \<Rightarrow> nat \<Rightarrow> int) \<Rightarrow> bool" where
  "is_too_large B = ((\<Sum> (i,j) \<in> {..<l} \<times> {..<b}.  \<lfloor>log 2 (max (B i j) (-1) + 2)\<rfloor>) > C3 * b * l)" 

fun compress_step :: "f0_state \<Rightarrow> f0_state" where
  "compress_step (B,s) = (\<lambda> i j. max (B i j - 1) (-1), s+1)"

function compress :: "f0_state \<Rightarrow> f0_state" where
  "compress (B,s) = (
    if is_too_large B 
      then (compress (compress_step (B,s)))
      else (B,s))"
  by auto

fun compress_termination_measure :: "f0_state \<Rightarrow> nat" where
  "compress_termination_measure (B,s) = (\<Sum> (i,j) \<in> {..<l} \<times> {..<b}. nat (B i j + 1))"

(*
lemma max_image_mono:
  assumes "finite S"
  assumes "S \<noteq> {}"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<le> g i"
  shows "Max (f ` S) \<le> Max (g ` S)"
  using assms
proof (induct rule:finite_ne_induct)
  case (singleton x)
  then show ?case by simp
next
  case (insert x F)
  have "Max (f ` insert x F) = max (f x) (Max (f ` F))"
    using insert by auto
  also have "... \<le> max (g x) (Max (g ` F))"
    using insert by (intro max.mono, auto) 
  also have "... = Max (g ` insert x F)"
    using insert by auto
  finally show ?case by simp
qed
*)
lemma compress_termination: 
  assumes "is_too_large B"
  shows "compress_termination_measure (compress_step (B,s)) < compress_termination_measure (B,s)"
proof (rule ccontr)
  let ?I = "{..<l} \<times> {..<b}"
  have a: "nat (max (B i j - 1) (- 1) + 1) \<le> nat (B i j + 1)" for i j
    by simp
  assume "\<not> compress_termination_measure (compress_step (B, s)) < compress_termination_measure (B, s)"
  hence "(\<Sum> (i,j) \<in> ?I. nat (B i j + 1)) \<le> (\<Sum> (i,j) \<in> ?I. nat (max (B i j - 1) (-1) + 1))"
    by simp
  moreover have "(\<Sum> (i,j) \<in> ?I. nat (B i j + 1)) \<ge> (\<Sum> (i,j) \<in> ?I. nat (max (B i j - 1) (-1) + 1))"
    by (intro sum_mono) auto
  ultimately have b:
    "(\<Sum> (i,j) \<in> ?I. nat (max (B i j - 1) (-1) + 1)) = (\<Sum> (i,j) \<in> ?I. nat (B i j + 1))"
    using order_antisym by simp
  have "nat (B i j + 1) = nat (max (B i j - 1) (-1) + 1)" if "(i,j) \<in> ?I" for i j
    using sum_mono_inv[OF b] that a by auto
  hence "max (B i j) (-1) = -1" if "(i,j) \<in> ?I" for i j
    using that by fastforce
  hence "(\<Sum>(i,j) \<in> ?I. \<lfloor>log 2 (max (B i j) (-1) + 2)\<rfloor>) = (\<Sum>(i,j) \<in> ?I. 0)"
    by (intro sum.cong, auto)
  also have "... = 0" by simp
  also have "... \<le> C3 * b * l" unfolding C3_def by simp
  finally have "\<not> is_too_large B" by simp
  thus "False" using assms by simp
qed

termination compress
  using measure_def compress_termination
  by (relation "Wellfounded.measure (compress_termination_measure)", auto)

fun merge1 :: "f0_state \<Rightarrow> f0_state \<Rightarrow> f0_state" where
  "merge1 (B1,s1) (B2, s2) = (
    let s = max s1 s2 in (\<lambda> i j. max (B1 i j + s1 - s) (B2 i j + s2 -s), s))"

fun merge :: "f0_state \<Rightarrow> f0_state \<Rightarrow> f0_state" where
  "merge x y = compress (merge1 x y)"


fun single1 :: "nat \<Rightarrow> nat \<Rightarrow> f0_state" where
  "single1 x coins = (\<lambda> i j. 
     let (f,g,h) = (select \<Omega> coins) i in (
     if h( g x) = j then int (f x) else (-1)), 0)"

fun single :: "nat \<Rightarrow> nat \<Rightarrow> f0_state" where
  "single x coins = compress (single1 x coins)"

fun estimate1 :: "f0_state \<Rightarrow> nat \<Rightarrow> real" where
  "estimate1 (B,s) i = (
    let t = max 0 (Max ((B i) ` {..<b}) + s - \<lfloor>log 2 b\<rfloor> + 8); 
        p = card { j. j \<in> {..<b} \<and> B i j + s \<ge> t } in
        2 powr t * ln (1-p/b) / ln(1-1/b))"

fun estimate :: "f0_state \<Rightarrow> real" where
  "estimate x = median l (estimate1 x)"

end

print_statement "single.simps"
lemma "estimate 2 = undefined"
  sorry


end