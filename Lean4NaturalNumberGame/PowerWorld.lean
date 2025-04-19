import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NthRewrite

import Lean4NaturalNumberGame.Base
import Lean4NaturalNumberGame.MultiplicationWorld

open MyNat

theorem pow_succ (a m : ℕ) : a ^ succ m = a ^ m * a := by
  rw [pow_succ']
  rw [mul_comm]

/- Level 1 / 10 : zero_pow_zero -/
theorem zero_pow_zero : zero ^ zero = 1 := by
  rw [pow_zero]

/- Level 2 / 10 : zero_pow_succ -/
theorem zero_pow_succ (m : ℕ) : zero ^ (succ m) = zero := by
  rw [pow_succ]
  rw [mul_zero]

/- Level 3 / 10 : pow_one -/
theorem pow_one (a : ℕ) : a ^ (1: ℕ) = a := by
  rw [one_eq_succ_zero]
  rw [pow_succ]
  rw [pow_zero]
  rw [one_mul]

/- Level 4 / 10 : one_pow -/
theorem one_pow (m : ℕ) : (1 : ℕ) ^ m = 1 := by
  induction m with
  | zero =>
    rw [pow_zero]
  | succ m ih =>
    rw [pow_succ]
    rw [ih]
    rw [mul_one]

/- Level 5 / 10 : pow_two -/
theorem pow_two (a : ℕ) : a ^ (2 : ℕ) = a * a := by
  rw [two_eq_succ_one]
  rw [pow_succ]
  rw [pow_one]

/- Level 6 / 10 : pow_add -/
theorem pow_add (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero =>
    rw [add_zero]
    rw [pow_zero]
    rw [mul_one]
  | succ n ih =>
    rw [add_succ]
    repeat rw [pow_succ]
    rw [ih]
    rw [← mul_assoc]

/- Level 7 / 10 : mul_pow -/
theorem mul_pow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero =>
    repeat rw [pow_zero]
    rw [mul_one]
  | succ n ih =>
    repeat rw [pow_succ]
    rw [ih]
    repeat rw [← mul_assoc]
    nth_rewrite 4 [mul_assoc]
    rw [mul_comm a (b ^ n)]
    rw [← mul_assoc]

/- Level 8 / 10 : pow_pow -/
theorem pow_pow (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    rw [mul_zero]
    rw [pow_zero]
  | succ n ih =>
    rw [pow_succ]
    rw [mul_succ]
    rw [pow_add]
    rw [ih]

/- Level 9 / 10 : add_sq -/
theorem add_sq (a b : ℕ) : (a + b) ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ) + 2 * a * b := by
  rw [two_eq_succ_one]
  repeat rw [pow_succ]
  rw [pow_one]
  repeat rw [pow_one]
  rw [mul_add]
  repeat rw [add_mul]
  rw [← add_assoc]
  rw [add_assoc]
  rw [add_comm (a * b) (b * b)]
  rw [← add_assoc]
  rw [add_assoc (a * a) (b * a) (b * b)]
  rw [add_comm (b * a) (b * b)]
  rw [← add_assoc]
  rw [add_assoc]
  rw [mul_comm b a]
  rw [← two_mul]
  rw [← mul_assoc]
  rw [two_eq_succ_one]

/- Level 10 / 10 : Fermat's Last Theorem -/
-- example (a b c n : ℕ) : (a + 1) ^ (n + 3) + (b + 1) ^ (n + 3) ≠ (c + 1) ^ (n + 3) := by
--   sorry
