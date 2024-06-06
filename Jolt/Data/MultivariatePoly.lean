
section MvPolynomial

-- multivariate polynomials without explicit bound on number of variables
-- def MvPolynomial'' (R : Type) := List (R × List ??)

def MvPolynomial' (R : Type) (n : ℕ) := List (R × List (Fin n))

def MvPolynomial'.C {R : Type} {n : ℕ} [CommSemiring R] (r : R) : MvPolynomial' R n := [(r, [])]
def MvPolynomial'.X {R : Type} {n : ℕ} [CommSemiring R] (s : (Fin n)) : MvPolynomial' R n := [(1, [s])]


def MvPolynomial'.eval {R : Type} {n : ℕ} [Zero R] [Add R] [Mul R] (f : (Fin n) → R) (p : MvPolynomial' R n) : R := 0 -- TODO implement
def MvPolynomial'.eval₂ {R S₁ : Type} {n : ℕ} [CommSemiring R] [Zero S₁] [One S₁] [Add S₁] [Mul S₁] (f : R → S₁) (g : (Fin n) → S₁) (p : MvPolynomial' R n) : S₁ :=
  (p.map (fun ⟨r, s⟩ => (f r * (s.map g).prod))).sum


def MvPolynomial'.add {R : Type} {n : ℕ} [CommSemiring R] (p q : MvPolynomial' R n) : MvPolynomial' R n := List.append p q
def MvPolynomial'.mul {R : Type} {n : ℕ} [CommSemiring R] (p q : MvPolynomial' R n) : MvPolynomial' R n := List.foldl (fun a b => a.add (List.map (fun ⟨r, s⟩ => (r * b.1, s ++ b.2)) q)) [] p
def MvPolynomial'.neg {R : Type} {n : ℕ} [CommRing R] (p : MvPolynomial' R n) : MvPolynomial' R n := List.map (fun ⟨r, s⟩ => (-r, s)) p
def MvPolynomial'.sub {R : Type} {n : ℕ} [CommRing R] (p q : MvPolynomial' R n) : MvPolynomial' R n := p.add q.neg
def MvPolynomial'.pow {R : Type} {n : ℕ} [CommSemiring R] (p : MvPolynomial' R n) (n' : Nat) : MvPolynomial' R n := List.foldl (fun a b => a.mul p) (MvPolynomial'.C 1) (List.replicate n' p)

instance {R : Type} {n : ℕ} [CommSemiring R] : Zero (MvPolynomial' R n) := ⟨[]⟩
instance {R : Type} {n : ℕ} [CommSemiring R] : Add (MvPolynomial' R n) := ⟨MvPolynomial'.add⟩
instance {R : Type} {n : ℕ} [CommSemiring R] : Mul (MvPolynomial' R n) := ⟨MvPolynomial'.mul⟩
instance {R : Type} {n : ℕ} [CommRing R] : Neg (MvPolynomial' R n) := ⟨MvPolynomial'.neg⟩
instance {R : Type} {n : ℕ} [CommRing R] : Sub (MvPolynomial' R n) := ⟨MvPolynomial'.sub⟩
instance {R : Type} {n : ℕ} [CommSemiring R] : Pow (MvPolynomial' R n) Nat := ⟨MvPolynomial'.pow⟩

end MvPolynomial
