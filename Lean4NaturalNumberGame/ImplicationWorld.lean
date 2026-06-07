import Lean4NaturalNumberGame.Base
import Lean4NaturalNumberGame.TutorialWorld
import Lean4NaturalNumberGame.AdditionWorld

set_option warn.sorry false

open MyNat

/- Level 1 / 11 : The `exact` tactic -/
example (x y z : ℕ) (h1 : x + y = 37) (_h2 : 3 * x + z = 42) : x + y = 37 := by
  sorry

/- Level 2 / 11 : `exact` practice. -/
example (x : ℕ) (h : zero + x = zero + y + 2) : x = y + 2 := by
  sorry

/- Level 3 / 11 : The `apply` tactic. -/
example (x y : ℕ) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by
  sorry

/- Level 4 / 11 : succ_inj : the successor function is injective -/
example (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  sorry

example : ℕ -> ℕ := by
  sorry

example (a b : ℕ) (h : succ a = succ b) : a = b := by
  sorry

/- Level 5 / 11 : Arguing backwards -/
example (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  sorry

/- Level 6 / 11 : intro -/
example (x : ℕ) : x = 37 → x = 37 := by
  sorry

/- Level 7 / 11 : intro practice -/
example (x : ℕ) : x + 1 = y + 1 → x = y := by
  sorry

/- Level 8 / 11 : ≠ -/
example (x y : ℕ) (h1 : x = y) (h2 : x ≠ y) : False := by
  sorry

/- Level 9 / 11 : zero_ne_succ -/
theorem zero_ne_one : zero ≠ 1 := by
  sorry

/- Level 10 / 11 : 1 ≠ 0 -/
theorem one_ne_zero : 1 ≠ zero := by
  sorry

/- Level 11 / 11 : 2 + 2 ≠ 5 -/
example : succ (succ zero) + succ (succ zero) ≠ succ (succ (succ (succ (succ zero)))) := by
  sorry

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  sorry
