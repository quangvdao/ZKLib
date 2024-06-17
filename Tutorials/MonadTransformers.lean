

def two : Nat := Id.run do
  let mut x := 0
  x := x + 1
  x := x + 1
  return x

#eval two
