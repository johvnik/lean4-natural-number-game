import Lean4NaturalNumberGame.Base
import Lean4NaturalNumberGame.MultiplicationWorld
import Lean4NaturalNumberGame.AlgorithmWorld
import Lean4NaturalNumberGame.LessEqualWorld

open MyNat

/- Level 1 / 10 : mul_le_mul_right -/
theorem mul_le_mul_right (a b t : ℕ) (h : a ≤ b) : a * t ≤ b * t := by
  sorry

/- Level 2 / 10 : mul_left_ne_zero -/
theorem mul_left_ne_zero (a b : ℕ) (h : a * b ≠ zero) : b ≠ zero := by
  sorry

/- Level 3 / 10 : eq_succ_of_ne_zero -/
theorem eq_succ_of_ne_zero (a : ℕ) (ha : a ≠ zero) : ∃ n, a = succ n := by
  sorry

/- Level 4 / 10 : one_le_of_ne_zero -/
theorem one_le_of_ne_zero (a : ℕ) (ha : a ≠ zero) : 1 ≤ a := by
  sorry

/- Level 5 / 10 : le_mul_right -/
theorem le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  sorry

/- Level 6 / 10 : mul_right_eq_one -/
theorem mul_right_eq_one (x y : ℕ) (h : x * y = 1) : x = 1 := by
  sorry

/- Level 7 / 10 : mul_ne_zero -/
theorem mul_ne_zero (a b : ℕ) (ha : a ≠ zero) (hb : b ≠ zero) : a * b ≠ zero := by
  sorry

/- Level 8 / 10 : mul_eq_zero -/
/- NOTE: Tauto import from Mathlib conflicts with our ℕ override -/
theorem mul_eq_zero (a b : ℕ) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  sorry

/- Level 9 / 10 : mul_left_cancel -/
theorem mul_left_cancel (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  sorry

/- Level 10 / 10 : mul_right_eq_self -/
theorem mul_right_eq_self (a b : ℕ) (ha : a ≠ 0) (h : a * b = a) : b = 1 := by
  sorry
