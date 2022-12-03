theory E4
  imports E3
begin

context inner_algorithm_fix_A 
begin

definition E\<^sub>4 where "E\<^sub>4 = (\<lambda>(f,g,h). \<bar>card (R f) - Y / 2^(t f)\<bar> \<le> real_of_rat \<delta>/3 * Y / 2^(t f))"

lemma "\<Psi>.prob {\<psi>. E\<^sub>1 \<psi> \<and> E\<^sub>2 \<psi> \<and> E\<^sub>3 \<psi> \<and> \<not>E\<^sub>4 \<psi>} \<le> 1/2^6" (is "?L \<le> ?R")
proof -
  show ?thesis sorry
qed

end

end