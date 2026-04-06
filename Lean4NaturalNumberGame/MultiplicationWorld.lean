import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NthRewrite

import Lean4NaturalNumberGame.Base
import Lean4NaturalNumberGame.TutorialWorld
import Lean4NaturalNumberGame.AdditionWorld

open MyNat

-- Define mul_succ here because we need add_comm to easily solve this from
-- mul_succ', which is easily solved with rfl from definition
theorem mul_succ (a b : ℕ) : a * succ b = a * b + a := by
  sorry

/- Level 1 / 9 : mul_one -/
theorem mul_one (m : ℕ) : m * 1 = m := by
  sorry

/- Level 2 / 9 : zero_mul -/
theorem zero_mul (m : ℕ) : zero * m = zero := by
  sorry

/- Level 3 / 9 : succ_mul -/
theorem succ_mul (a b : ℕ) : succ a * b = a * b + b := by
  sorry

/- Level 4 / 9 : mul_comm -/
theorem mul_comm (a b : ℕ) : a * b = b * a := by
  sorry

/- Level 5 / 9 : one_mul -/
theorem one_mul (m : ℕ) : 1 * m = m := by
  sorry

/- Level 6 / 9 : two_mul -/
theorem two_mul (m : ℕ) : 2 * m = m + m := by
  sorry

/- Level 7 / 9 : mul_add -/
theorem mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  sorry

/- Level 8 / 9 : add_mul -/
theorem add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  sorry

/- Level 9 / 9 : mul_assoc -/
theorem mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c) := by
  sorry
