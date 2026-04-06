import Lean4NaturalNumberGame.Base

open MyNat

/- Level 1 / 5 : zero_add -/
theorem zero_add (n : ℕ) : zero + n = n := by
  induction n with
  | zero =>
    rw [add_zero]
  | succ n ih =>
    rw [add_succ]
    rw [ih]

/- Level 2 / 5 : succ_add -/
theorem succ_add (a b : ℕ) : succ a + b = succ (a + b) := by
  induction b with
  | zero =>
    repeat rw [add_zero]
  | succ b ih =>
    repeat rw [add_succ]
    rw [ih]

/- Level 3 / 5 : add_comm (level boss) -/
lemma add_comm (a d : ℕ) :
  a + d = d + a := by
  induction d with
  | zero =>
    rw [zero_add]
    rw [add_zero]
  | succ d ih =>
    rw [add_succ]
    rw [succ_add]
    rw [ih]

/- Level 4 / 5 : add_assoc (associativity of addition) -/
lemma add_assoc (a b c : ℕ) :
  (a + b) + c = a + (b + c) := by
  induction c with
  | zero =>
    repeat rw [add_zero]
  | succ c ih =>
    repeat rw [add_succ]
    rw [ih]


/- Level 5 / 5 : add_right_comm -/
theorem add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
  rw [add_assoc]
  rw [add_comm b c]
  rw [← add_assoc]
