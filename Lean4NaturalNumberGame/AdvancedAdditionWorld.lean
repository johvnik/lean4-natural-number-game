import Lean4NaturalNumberGame.Base
import Lean4NaturalNumberGame.AdditionWorld

open MyNat

/- Level 1 / 6 : add_right_cancel -/
theorem add_right_cancel (a b n : ℕ) : a + n = b + n → a = b := by
  induction n with
  | zero =>
    intro h
    repeat rw [add_zero] at h
    exact h
  | succ n ih =>
    intro h
    repeat rw [add_succ] at h
    apply succ_inj at h
    apply ih at h
    exact h

/- Level 2 / 6 : add_left_cancel -/
theorem add_left_cancel (a b n : ℕ) : n + a = n + b → a = b := by
  nth_rewrite 1 [add_comm]
  nth_rewrite 2 [add_comm]
  apply add_right_cancel

/- Level 3 / 6 : add_left_eq_self -/
theorem add_left_eq_self (x y : ℕ) : x + y = y → x = zero := by
  nth_rewrite 2 [← zero_add y]
  apply add_right_cancel

/- Level 4 / 6 : add_right_eq_self -/
theorem add_right_eq_self (x y : ℕ) : x + y = x → y = zero := by
  nth_rewrite 2 [← add_zero x]
  apply add_left_cancel

/- Level 5 / 6 : add_right_eq_zero -/
theorem add_right_eq_zero (a b : ℕ) : a + b = zero → a = zero := by
  cases b
  · intro h
    rw [add_zero] at h
    exact h
  · intro h
    rw [add_succ] at h
    cases h

/- Level 6 / 6 : add_left_eq_zero -/
theorem add_left_eq_zero (a b : ℕ) : a + b = 0 → b = zero := by
  intro h
  rw [add_comm] at h
  apply add_right_eq_zero at h
  exact h
