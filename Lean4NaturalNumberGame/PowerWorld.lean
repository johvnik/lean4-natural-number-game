import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NthRewrite

import Lean4NaturalNumberGame.Base
import Lean4NaturalNumberGame.MultiplicationWorld

open MyNat

theorem pow_succ (a m : ℕ) : a ^ succ m = a ^ m * a := by
  sorry

/- Level 1 / 10 : zero_pow_zero -/
theorem zero_pow_zero : zero ^ zero = 1 := by
  sorry

/- Level 2 / 10 : zero_pow_succ -/
theorem zero_pow_succ (m : ℕ) : zero ^ (succ m) = zero := by
  sorry

/- Level 3 / 10 : pow_one -/
theorem pow_one (a : ℕ) : a ^ (1 : ℕ) = a := by
  sorry

/- Level 4 / 10 : one_pow -/
theorem one_pow (m : ℕ) : (1 : ℕ) ^ m = 1 := by
  sorry

/- Level 5 / 10 : pow_two -/
theorem pow_two (a : ℕ) : a ^ (2 : ℕ) = a * a := by
  sorry

/- Level 6 / 10 : pow_add -/
theorem pow_add (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  sorry

/- Level 7 / 10 : mul_pow -/
theorem mul_pow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  sorry

/- Level 8 / 10 : pow_pow -/
theorem pow_pow (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by
  sorry

/- Level 9 / 10 : add_sq -/
theorem add_sq (a b : ℕ) : (a + b) ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ) + 2 * a * b := by
  sorry

/- Level 10 / 10 : Fermat's Last Theorem -/
-- example (a b c n : ℕ) : (a + 1) ^ (n + 3) + (b + 1) ^ (n + 3) ≠ (c + 1) ^ (n + 3) := by
--   sorry
