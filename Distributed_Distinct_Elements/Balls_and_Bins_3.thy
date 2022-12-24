theory Balls_and_Bins_3
  imports
    "HOL-Combinatorics.Stirling"
    "HOL-Computational_Algebra.Polynomial"
    "Discrete_Summation.Factorials" 
    "Poly_Extras"
    "DDE_Preliminary"
begin

locale balls_and_bins =
  fixes R :: "'a set" (* TODO: Use 'r *)
  fixes B :: "'b set"
  fixes k :: nat
  assumes fin_R: "finite R" 
  assumes fin_B: "finite B"
  assumes B_nonempty: "B \<noteq> {}"
begin

definition Y :: "('a \<Rightarrow> 'b) \<Rightarrow> real"
  where "Y \<omega> = card (\<omega> ` R)"

definition Z :: "'b \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> real"
  where "Z i \<omega> = card {r \<in> R. \<omega> r =  i}"

definition \<Omega> where "\<Omega> = prod_pmf R (\<lambda>_. pmf_of_set B)"




end


end