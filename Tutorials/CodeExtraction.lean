-- @[export lean_code_extraction_test]
-- def codeExtractionTest : IO Unit :=
--   IO.println "Hello, world!"


-- Interesting ways to optimize array operations (https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.E2.9C.94.20Speed.20issue.28.3F.29.20with.20.60Array.2EmapM.60/near/450184733)

#eval
  for n in [12:16] do
    timeit s!"2^{n}" $ discard $ StateT.run (s := 0) $
      Array.mkArray (2^n) 1 |>.mapM fun x => modify (· + x) *> get

#eval
  for n in [12:16] do
    discard $ timeit s!"2^{n}" do
      let mut result := Array.mkEmpty (2^n)
      for i in [0:2^n] do
        result := result.push i
      return result

#eval
  for n in [12:16] do
    discard $ timeit s!"2^{n}" do
      let mut i := 0
      let mut result := Array.mkEmpty (2^n)
      while i < 2^n do
        result := result.push i
        i := i + 1
      return result


def fibonacci (n : Nat) : Nat :=
  let rec loop (n : Nat) : Nat × Nat :=
    if n = 0 then (0, 1) else
      let (a, b) := loop (n - 1)
      (b, a + b)
  (loop n).snd

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

noncomputable def factorial' : Nat → Nat := factorial


#eval factorial 5  -- This will work and output 120

def main : IO Unit := do
  IO.println (fibonacci 5000)
