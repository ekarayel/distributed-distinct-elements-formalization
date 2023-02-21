theory Expander_Graphs_TTS
  imports 
    Expander_Graphs_Definition     
    "HOL-Analysis.Cartesian_Space"
    "HOL-Types_To_Sets.Types_To_Sets"
begin

locale pre_expander_graph_tts = pre_expander_graph +
  fixes n_itself :: "('n :: finite) itself"
  assumes td: "\<exists>(enum_verts :: ('n \<Rightarrow> 'a)) enum_verts_inv. type_definition enum_verts enum_verts_inv (verts G)"
begin

definition td_components :: "('n \<Rightarrow> 'a) \<times> ('a \<Rightarrow> 'n)" 
  where "td_components = (SOME q. type_definition (fst q) (snd q) (verts G))"

sublocale type_definition "(fst td_components)" "(snd td_components)" "verts G"
proof -
  have 0:"\<exists>q'. type_definition ((fst q')::(('n :: finite) \<Rightarrow> 'a)) (snd q') (verts G)"
    using td by simp
  show "type_definition (fst td_components) (snd td_components) (verts G)"
    unfolding td_components_def using someI_ex[OF 0] by simp
qed

definition enum_verts where "enum_verts = fst td_components"

lemma enum_verts: "bij_betw enum_verts UNIV (verts G)"
  unfolding bij_betw_def  by (simp add: Rep_inject Rep_range enum_verts_def inj_on_def)

end

lemma eg_tts_1:
  assumes "pre_expander_graph G"
  assumes "\<exists>(f::('n::finite) \<Rightarrow> 'a) g. type_definition f g (verts G)"
  shows "pre_expander_graph_tts TYPE('n) G"
  using assms  
  unfolding pre_expander_graph_tts_def  pre_expander_graph_tts_axioms_def by auto


context pre_expander_graph 
begin

lemma eg_tts_2:
  assumes "\<exists>(f :: ('n \<Rightarrow> 'a)) g. type_definition f g (verts G)"
  shows "class.finite TYPE('n)"
proof -
  obtain Rep :: "'n \<Rightarrow> 'a" and Abs where d:"type_definition Rep Abs (verts G)"
    using assms by auto
  interpret type_definition Rep Abs "verts G"
    using d by simp
                              
  have "finite (verts G)" by simp 
  thus ?thesis
    unfolding class.finite_def univ by auto
qed


lemma remove_finite_premise_aux:
  assumes "\<exists>(Rep :: 'n  \<Rightarrow> 'a) Abs. type_definition Rep Abs (verts G)"
  shows "class.finite TYPE('n)"
proof -
  obtain Rep :: "'n \<Rightarrow> 'a" and Abs where d:"type_definition Rep Abs (verts G)"
    using assms by auto
  interpret type_definition Rep Abs "verts G"
    using d by simp
                              
  have "finite (verts G)" by simp 
  thus ?thesis
    unfolding class.finite_def univ by auto
qed

lemma remove_finite_premise: 
  "(class.finite TYPE('n) \<Longrightarrow> \<exists>(Rep :: 'n  \<Rightarrow> 'a) Abs. type_definition Rep Abs (verts G) \<Longrightarrow> PROP Q) 
  \<equiv> (\<exists>(Rep :: 'n  \<Rightarrow> 'a) Abs. type_definition Rep Abs (verts G) \<Longrightarrow> PROP Q)" 
  (is "?L \<equiv> ?R")
proof (intro Pure.equal_intr_rule)
  assume e:"\<exists>(Rep :: 'n  \<Rightarrow> 'a) Abs. type_definition Rep Abs (verts G)" and l:"PROP ?L"
  hence f: "class.finite TYPE('n)" 
    using remove_finite_premise_aux[OF e] by simp

  show "PROP ?R"
    using l[OF f] by auto
next
  assume "\<exists>(Rep :: 'n  \<Rightarrow> 'a) Abs. type_definition Rep Abs (verts G)" and l:"PROP ?R"
  show "PROP ?L"
    using l by auto
qed

end



end