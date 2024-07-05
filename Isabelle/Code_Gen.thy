theory Code_Gen
  imports Main
begin

fun fib :: "nat \<Rightarrow> nat" where
  "fib 0 = 0"
| "fib (Suc 0) = Suc 0"
| "fib (Suc (Suc n)) = fib n + fib (Suc n)"

definition fib_step :: "nat \<Rightarrow> nat \<times> nat" where
  "fib_step n = (fib (Suc n), fib n)"

lemma [code]:
  "fib_step 0 = (Suc 0, 0)"
  "fib_step (Suc n) = (let (m, q) = fib_step n in (m + q, m))"
  by (simp_all add: fib_step_def)

lemma [code]:
  "fib 0 = 0"
  "fib (Suc n) = fst (fib_step n)"
  by (simp_all add: fib_step_def)

text \<open>how do I show the damn code?? \<close>

export_code fib fib_step in Haskell
  module_name MyFib

end