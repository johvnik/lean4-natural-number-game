import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NthRewrite

import Lean4NaturalNumberGame.Base
import Lean4NaturalNumberGame.TutorialWorld
import Lean4NaturalNumberGame.AdditionWorld

open MyNat

-- Define mul_succ here because we need add_comm to easily solve this from
-- mul_succ', which is easily solved with rfl from definition
theorem mul_succ (a b : ℕ) : a * succ b = a * b + a := by
  rw [mul_succ']
  rw [add_comm]

/- Level 1 / 9 : mul_one -/
theorem mul_one (m : ℕ) : m * 1 = m := by
  rw [one_eq_succ_zero]
  rw [mul_succ]
  rw [mul_zero]
  rw [zero_add]

/- Level 2 / 9 : zero_mul -/
theorem zero_mul (m : ℕ) : zero * m = zero := by
  induction m with
  | zero =>
    rw [mul_zero]
  | succ m ih =>
    rw [mul_succ]
    rw [add_zero]
    exact ih

/- Level 3 / 9 : succ_mul -/
theorem succ_mul (a b : ℕ) : succ a * b = a * b + b := by
  induction b with
  | zero =>
    repeat rw [mul_zero]
    rw [add_zero]
  | succ b ih =>
    repeat rw [mul_succ]
    repeat rw [add_succ]
    rw [ih]
    repeat rw [succ_eq_add_one]
    rw [add_assoc (a * b)]
    rw [add_comm b a]
    rw [← add_assoc]

/- Level 4 / 9 : mul_comm -/
theorem mul_comm (a b : ℕ) : a * b = b * a := by
  induction b with
  | zero =>
    rw [zero_mul]
    rw [mul_zero]
  | succ b ih =>
    rw [mul_succ]
    rw [succ_mul]
    rw [ih]

/- Level 5 / 9 : one_mul -/
theorem one_mul (m : ℕ): 1 * m = m := by
  induction m with
  | zero =>
    rw [mul_zero]
  | succ m ih =>
    rw [mul_succ]
    rw [ih]
    rw [succ_eq_add_one]

/- Level 6 / 9 : two_mul -/
theorem two_mul (m : ℕ): 2 * m = m + m := by
  rw [two_eq_succ_one]
  rw [succ_mul]
  rw [one_mul]

/- Level 7 / 9 : mul_add -/
theorem mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero =>
    rw [add_zero]
    rw [mul_zero]
    rw [add_zero]
  | succ c ih =>
    rw [add_succ]
    rw [mul_succ]
    rw [ih]
    rw [mul_succ]
    rw [← add_assoc]

/- Level 8 / 9 : add_mul -/
theorem add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  rw [mul_comm]
  rw [mul_add]
  rw [mul_comm]
  nth_rewrite 2 [mul_comm]
  rfl

/- Level 9 / 9 : mul_assoc -/
theorem mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c) := by
  induction a with
  | zero =>
    repeat rw [zero_mul]
  | succ a ih =>
    repeat rw [succ_mul]
    rw [add_mul]
    rw [ih]
