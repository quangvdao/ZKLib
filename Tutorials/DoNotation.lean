import Mathlib.Data.List.Basic



variable [Monad m]
variable (b : Bool)

theorem eq_do_mut [LawfulMonad m] (b : Bool) (ma ma' : m α) :
    (do let mut x ← ma;
        if b then { x ← ma' };
        return x) =
    (ma >>= fun x => if b then ma' else pure x) := by simp

theorem byCases_Bool_bind (x : m Bool) (f g : Bool → m β) (isTrue : f true = g true) (isFalse : f false = g false) :
    (x >>= f) = (x >>= g) := by
  have : f = g := by
    funext b
    cases b with
    | true => rw [isTrue]
    | false => rw [isFalse]
  rw [this]

variable (p : α → m Bool) (xs : List α)

theorem eq_findM [LawfulMonad m] :
    (do for x in xs do {
          let b ← p x;
          if b then { return some x }
        };
        pure none) =
    xs.findM? p := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.findM?, ← ih]; simp
    apply byCases_Bool_bind <;> simp


variable (xss : List (List α))

theorem eq_findSomeM_findM [Monad m] [LawfulMonad m] :
    (do for xs in xss do {
          for x in xs do {
            let b ← p x;
            if b then { return some x }
        } };
        pure none)
    = List.findSomeM? (fun xs => List.findM? p xs) xss := by
  induction xss with
  | nil => simp
  | cons xs xss ih =>
    simp [List.findSomeM?]
    rw [← ih, ← eq_findM]
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp
      apply byCases_Bool_bind <;> simp [ih]

def List.untilM (p : α → m Bool) : List α → m Unit
  | []    => pure ()
  | a::as => p a >>= fun | true => pure () | false => as.untilM p

theorem eq_untilM [LawfulMonad m] :
    (do for x in xs do {
          let b ← p x;
          if b then {
            break
          }
        })
    = xs.untilM p
  := by induction xs with
      | nil => simp!
      | cons x xs ih =>
        simp!; rw [← ih];
        apply byCases_Bool_bind <;> simp
