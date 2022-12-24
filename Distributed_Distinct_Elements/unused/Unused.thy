theory Unused
  imports Main
begin

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

end
