import Lean4NaturalNumberGame.Base

open MyNat

/- Level 1 / 8 : The rfl tactic -/
example (x q : ℕ) : 37 * x + q = 37 * x + q := by
  rfl

/-  Level 2 / 8 : the rw tactic -/
example (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw [h]

/-  Level 3 / 8 : Numbers -/
example : 2 = succ (succ zero) := by
  rw [← one_eq_succ_zero]
  rw [← two_eq_succ_one]

/-  Level 4 / 8 : rewriting backwards -/
example : 2 = succ (succ zero) := by
  rw [← one_eq_succ_zero]
  rw [← two_eq_succ_one]

/-  Level 5 / 8 : Adding zero -/
example (a b c : ℕ) : a + (b + zero) + (c + zero) = a + b + c := by
  rw [add_zero]
  rw [add_zero]

/- Level 6 / 8 : Precision rewriting -/
example (a b c : ℕ) : a + (b + zero) + (c + zero) = a + b + c := by
  rw [add_zero b]
  rw [add_zero c]

/- Level 7 / 8 : add_succ -/
theorem succ_eq_add_one n : succ n = n + 1 := by
  rw [one_eq_succ_zero]
  rw [add_succ]
  rw [add_zero]

/- Level 8 / 8 : 2+2=4 -/
example : (2 : ℕ) + 2 = 4 := by
  rw [two_eq_succ_one]
  rw [add_succ]
  rw [one_eq_succ_zero]
  rw [add_succ]
  rw [add_zero]
  rw [← one_eq_succ_zero]
  rw [← two_eq_succ_one]
  rw [← three_eq_succ_two]
  rw [← four_eq_succ_three]
