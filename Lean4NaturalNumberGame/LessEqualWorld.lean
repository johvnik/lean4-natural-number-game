import Lean4NaturalNumberGame.Base
import Lean4NaturalNumberGame.TutorialWorld
import Lean4NaturalNumberGame.AdvancedAdditionWorld

import Mathlib.Tactic.Use -- similar to exists tactic

open MyNat

/- NOTE
a ≤ b := ∃ c, b = a + c

To convert the left hand side to the right hand side,
use the `use` tactic. You may naturally pick any number for c.
-/

/- Level 1 / 11 : The `use` tactic -/
theorem le_refl (x : ℕ) : x ≤ x := by
  sorry

/- Level 2 / 11 : 0 ≤ x -/
theorem zero_le (x : ℕ) : zero ≤ x := by
  sorry

/- Level 3 / 11 : x ≤ succ x -/
theorem le_succ_self (x : ℕ) : x ≤ succ x := by
  sorry

/- Level 4 / 11 : x ≤ y and y ≤ z implies x ≤ z -/
theorem le_trans (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  sorry

/- Level 5 / 11 : x ≤ 0 → x = 0 -/
theorem le_zero (x : ℕ) (hx : x ≤ 0) : x = 0 := by
  sorry

/- Level 6 / 11 : x ≤ y and y ≤ x implies x = y -/
theorem le_antisymm (x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  sorry

/- Level 7 / 11 : Dealing with `or` -/
example (x y : ℕ) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  sorry

/- Level 8 / 11 : x ≤ y or y ≤ x -/
theorem le_total (x y : ℕ) : x ≤ y ∨ y ≤ x := by
  sorry

/- Level 9 / 11 : succ x ≤ succ y → x ≤ y -/
theorem succ_le_succ (x y : ℕ) (hx : succ x ≤ succ y) : x ≤ y := by
  sorry

/- Level 10 / 11 : x ≤ 1 -/
theorem le_one (x : ℕ) (hx : x ≤ 1) : x = zero ∨ x = 1 := by
  sorry

/- Level 11 / 11 : le_two -/
theorem le_two (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by
  sorry
