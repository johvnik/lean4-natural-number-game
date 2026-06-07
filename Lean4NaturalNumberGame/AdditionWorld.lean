import Lean4NaturalNumberGame.Base

set_option warn.sorry false

open MyNat

/- Level 1 / 5 : zero_add -/
theorem zero_add (n : ℕ) : zero + n = n := by
  sorry

/- Level 2 / 5 : succ_add -/
theorem succ_add (a b : ℕ) : succ a + b = succ (a + b) := by
  sorry

/- Level 3 / 5 : add_comm (level boss) -/
lemma add_comm (a d : ℕ) :
  a + d = d + a := by
  sorry

/- Level 4 / 5 : add_assoc (associativity of addition) -/
lemma add_assoc (a b c : ℕ) :
  (a + b) + c = a + (b + c) := by
  sorry

/- Level 5 / 5 : add_right_comm -/
theorem add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
  sorry
