theory Pseudorandom_Combinators_Expander
  imports 
    Pseudorandom_Combinators
    Expander_Graphs.Expander_Graphs_Strongly_Explicit
begin

definition \<E> :: "nat \<Rightarrow> real \<Rightarrow> 'a sample_space \<Rightarrow> (nat \<Rightarrow> 'a) sample_space"
  where "\<E> l \<Lambda> S = (let e = see_standard (size S) \<Lambda> in 
    \<lparr> size = see_size e * see_degree e^l, 
      sample_space_select = (\<lambda>i j. select S (see_sample_walk e i l ! j)) \<rparr>) "

locale expander_sample_space =
  fixes l :: nat
  fixes \<Lambda> :: real
  fixes S :: "'a sample_space"
  assumes l_gt_0: "l > 0"
  assumes \<Lambda>_gt_0: "\<Lambda> > 0"
  assumes sample_space_S: "sample_space S"
begin

definition e where "e = see_standard (size S) \<Lambda>"

lemma size_S_gt_0: "size S > 0" 
  using sample_space_S unfolding sample_space_def by simp

lemma \<E>_alt: "(\<E> l \<Lambda> S) = 
  \<lparr> size = see_size e * see_degree e^l, 
    sample_space_select = (\<lambda>i j. select S (see_sample_walk e i l ! j)) \<rparr>"
  unfolding \<E>_def e_def[symmetric] by (simp add:Let_def)

lemmas see_standard = see_standard[OF size_S_gt_0 \<Lambda>_gt_0]

lemma e_deg_gt_0: "see_degree e > 0"
  unfolding e_def see_standard by simp

lemma e_size_gt_0: "see_size e > 0"
  unfolding e_def see_standard using size_S_gt_0 by simp

lemma sample_space: "sample_space (\<E> l \<Lambda> S)"
  unfolding sample_space_def \<E>_alt using e_size_gt_0 e_deg_gt_0 by simp

lemma range: "select (\<E> l \<Lambda> S) i j \<in> sample_set S"
proof -
  define \<alpha> where "\<alpha> = select (\<E> l \<Lambda> S) i" 
  have "\<alpha> \<in> sample_set (\<E> l \<Lambda> S)"
    unfolding \<alpha>_def by (intro select_range sample_space)
  then obtain k where "\<alpha> = sample_space_select  (\<E> l \<Lambda> S) k"
    using sample_set_alt[OF sample_space] by auto
  hence "\<alpha> j \<in> sample_set S" 
    unfolding \<E>_alt using select_range[OF sample_space_S] by simp
  thus ?thesis
    unfolding \<alpha>_def by simp
qed

end


lemma \<E>_range:
  assumes "sample_space S"
  shows "select (\<E> l \<Lambda> S) i j \<in> sample_set S"
  sorry


end