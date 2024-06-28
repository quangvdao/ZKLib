-- @[export lean_code_extraction_test]
-- def codeExtractionTest : IO Unit :=
--   IO.println "Hello, world!"

-- def square (x : UInt8) : UInt8 := x * x

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
