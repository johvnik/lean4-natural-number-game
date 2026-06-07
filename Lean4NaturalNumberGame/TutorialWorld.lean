import Lean4NaturalNumberGame.Base

set_option warn.sorry false

open MyNat

/- Level 1 / 8 : The rfl tactic -/
example (x q : ℕ) : 37 * x + q = 37 * x + q := by
  sorry

/-  Level 2 / 8 : the rw tactic -/
example (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  sorry

/-  Level 3 / 8 : Numbers -/
example : 2 = succ (succ zero) := by
  sorry

/-  Level 4 / 8 : rewriting backwards -/
example : 2 = succ (succ zero) := by
  sorry

/-  Level 5 / 8 : Adding zero -/
example (a b c : ℕ) : a + (b + zero) + (c + zero) = a + b + c := by
  sorry

/- Level 6 / 8 : Precision rewriting -/
example (a b c : ℕ) : a + (b + zero) + (c + zero) = a + b + c := by
  sorry

/- Level 7 / 8 : add_succ -/
theorem succ_eq_add_one (n : ℕ) : succ n = n + 1 := by
  sorry

/- Level 8 / 8 : 2+2=4 -/
example : (2 : ℕ) + 2 = 4 := by
  sorry
