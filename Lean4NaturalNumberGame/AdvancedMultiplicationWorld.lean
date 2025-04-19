import Lean4NaturalNumberGame.Base
import Lean4NaturalNumberGame.MultiplicationWorld
import Lean4NaturalNumberGame.AlgorithmWorld
import Lean4NaturalNumberGame.LessEqualWorld

open MyNat

/- Level 1 / 10 : mul_le_mul_right -/
theorem mul_le_mul_right (a b t : ℕ) (h : a ≤ b) : a * t ≤ b * t := by
  obtain ⟨c, hc⟩ := h
  use c * t
  rw [hc]
  rw [add_mul]

/- Level 2 / 10 : mul_left_ne_zero -/
theorem mul_left_ne_zero (a b : ℕ) (h : a * b ≠ zero) : b ≠ zero := by
  intro hb
  apply h
  rw [hb]
  rw [mul_zero]

/- Level 3 / 10 : eq_succ_of_ne_zero -/
theorem eq_succ_of_ne_zero (a : ℕ) (ha : a ≠ zero) : ∃ n, a = succ n := by
  obtain zero | d := a
  · exfalso
    apply ha
    rfl
  · exists d

/- Level 4 / 10 : one_le_of_ne_zero -/
theorem one_le_of_ne_zero (a : ℕ) (ha : a ≠ zero) : 1 ≤ a := by
  apply eq_succ_of_ne_zero at ha
  obtain ⟨n, hn⟩ := ha
  use n
  rw [hn]
  rw [succ_eq_add_one]
  rw [add_comm]

/- Level 5 / 10 : le_mul_right -/
theorem le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  apply mul_left_ne_zero at h
  apply one_le_of_ne_zero at h
  apply mul_le_mul_right 1 b a at h
  rw [one_mul] at h
  rw [mul_comm] at h
  exact h

/- Level 6 / 10 : mul_right_eq_one -/
theorem mul_right_eq_one (x y : ℕ) (h : x * y = 1) : x = 1 := by
  have h2 : x * y ≠ zero := by
    intro contra
    rw [h] at contra
    contradiction
  apply le_mul_right at h2
  rw [h] at h2
  apply le_one at h2
  obtain h0 | h1 := h2
  · rw [h0] at h
    rw [zero_mul] at h
    contradiction
  · exact h1

/- Level 7 / 10 : mul_ne_zero -/
theorem mul_ne_zero (a b : ℕ) (ha : a ≠ zero) (hb : b ≠ zero) : a * b ≠ zero := by
  apply eq_succ_of_ne_zero at ha
  apply eq_succ_of_ne_zero at hb
  obtain ⟨n, ha⟩ := ha
  obtain ⟨m, hb⟩ := hb
  rw [ha, hb]
  rw [succ_mul, add_succ]
  symm
  apply zero_ne_succ

/- Level 8 / 10 : mul_eq_zero -/
/- NOTE: Tauto import from Mathlib conflicts with our ℕ override -/
theorem mul_eq_zero (a b : ℕ) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  match a with
  | 0 =>
    left
    rfl
  | succ a =>
    match b with
    | 0 =>
      right
      rfl
    | succ b =>
      have hab : succ a * succ b ≠ 0 := by
        rw [succ_mul] at h
        rw [add_succ] at h
        apply succ_ne_zero at h
        contradiction
      rw [h] at hab
      contradiction

/- Level 9 / 10 : mul_left_cancel -/
theorem mul_left_cancel (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  induction b generalizing c with
  | zero =>
    rw [mul_zero] at h
    symm at h
    apply mul_eq_zero at h
    cases h with
    | inl ha => contradiction
    | inr hc =>
      symm
      exact hc
  | succ d ih =>
    cases c with
    | zero =>
      rw [mul_zero] at h
      apply mul_eq_zero at h
      obtain ha | hd := h
      · contradiction
      · exact hd
    | succ c =>
      repeat rw [mul_succ] at h
      apply add_right_cancel at h
      apply ih at h
      rw [h]

/- Level 10 / 10 : mul_right_eq_self -/
theorem mul_right_eq_self (a b : ℕ) (ha : a ≠ 0) (h : a * b = a) : b = 1 := by
  nth_rewrite 2 [← mul_one a] at h
  apply mul_left_cancel at h
  · exact h
  · intro ha0
    contradiction
