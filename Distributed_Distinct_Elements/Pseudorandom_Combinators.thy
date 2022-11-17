theory Pseudorandom_Combinators
  imports Main HOL.Rat
begin

record 'a sample_space = 
  size :: "nat"
  select :: "nat \<Rightarrow> 'a"

definition triv_sample_space :: "nat \<Rightarrow> nat sample_space" 
  where "triv_sample_space n = \<lparr> size = n, select = id \<rparr>"

definition prod_sample_space :: 
  "'a sample_space \<Rightarrow> 'b sample_space \<Rightarrow> ('a \<times> 'b) sample_space" (infixr "\<times>\<^sub>S" 65)
  where 
    "prod_sample_space s t = 
      \<lparr> size = size s * size t, 
        select = (\<lambda>i. (select s (i mod (size s)), select t (i div (size s)))) \<rparr>"

definition \<E> :: "'a sample_space \<Rightarrow> nat \<Rightarrow> rat \<Rightarrow> (nat \<Rightarrow> 'a) sample_space"
  where "\<E> S l u = undefined"

definition \<H> :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) sample_space"
  where "\<H> k d r = undefined"

definition \<G> :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) sample_space"
  where "\<G> k r = undefined"


end