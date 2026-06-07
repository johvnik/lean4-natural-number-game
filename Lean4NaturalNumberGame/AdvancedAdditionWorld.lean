import Lean4NaturalNumberGame.Base
import Lean4NaturalNumberGame.AdditionWorld

set_option warn.sorry false

open MyNat

/- Level 1 / 6 : add_right_cancel -/
theorem add_right_cancel (a b n : ℕ) : a + n = b + n → a = b := by
  sorry

/- Level 2 / 6 : add_left_cancel -/
theorem add_left_cancel (a b n : ℕ) : n + a = n + b → a = b := by
  sorry

/- Level 3 / 6 : add_left_eq_self -/
theorem add_left_eq_self (x y : ℕ) : x + y = y → x = zero := by
  sorry

/- Level 4 / 6 : add_right_eq_self -/
theorem add_right_eq_self (x y : ℕ) : x + y = x → y = zero := by
  sorry

/- Level 5 / 6 : add_right_eq_zero -/
theorem add_right_eq_zero (a b : ℕ) : a + b = zero → a = zero := by
  sorry

/- Level 6 / 6 : add_left_eq_zero -/
theorem add_left_eq_zero (a b : ℕ) : a + b = 0 → b = zero := by
  sorry
