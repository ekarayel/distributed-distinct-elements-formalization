theory Pseudorandom_Combinators_2
  imports
    HOL.Rat 
    "Finite_Fields.Card_Irreducible_Polynomials" 
    "Universal_Hash_Families.Carter_Wegman_Hash_Family"
    "Frequency_Moments.Product_PMF_Ext"
begin

record 'a sample_space = 
  size :: "nat"
  select :: "nat \<Rightarrow> 'a"


definition sample_pmf
  where "sample_pmf S = map_pmf (select S) (pmf_of_set {..<size S})"

definition nat_sample_space :: "nat \<Rightarrow> nat sample_space" ("[_]\<^sub>S")
  where "nat_sample_space n = \<lparr> size = n, select = id \<rparr>"

lemma nat_sample_pmf: 
  "sample_pmf ([x]\<^sub>S) = pmf_of_set {..<x}"
  unfolding nat_sample_space_def sample_pmf_def by simp

definition prod_sample_space :: 
  "'a sample_space \<Rightarrow> 'b sample_space \<Rightarrow> ('a \<times> 'b) sample_space" (infixr "\<times>\<^sub>S" 65)
  where 
    "prod_sample_space s t = 
      \<lparr> size = size s * size t, 
        select = (\<lambda>i. (select s (i mod (size s)), select t ((i div (size s)) mod (size t)))) \<rparr>"

lemma prod_sample_pmf:
  assumes "size S > 0" "size T > 0"
  shows "sample_pmf (S \<times>\<^sub>S T) = pair_pmf (sample_pmf S) (sample_pmf T)"
  sorry





end