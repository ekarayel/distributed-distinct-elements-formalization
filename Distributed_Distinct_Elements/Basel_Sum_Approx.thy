theory Basel_Sum_Approx
  imports "HOL.Transcendental" "HOL-Analysis.Interval_Integral"
begin


lemma basel_sum: 
  assumes "k > 0"
  shows "(\<Sum>y\<in>{k+1..m}. 1 / real y^2) \<le> 1/real k" (is "?L \<le> ?R")
proof -

  have "?L = (LBINT y=k..m. 1/ \<lceil>y\<rceil>^2)" sorry
  also have "... \<le> (LBINT y=k..m. 1/ y^2)"
    using integral_mono
    sorry


  show ?thesis sorry
qed


(* 1/ceil y^2) \<le> 1/y^2 *)


end