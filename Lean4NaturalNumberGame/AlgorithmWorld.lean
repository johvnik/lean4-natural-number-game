import Lean4NaturalNumberGame.Base
import Lean4NaturalNumberGame.AdditionWorld

set_option warn.sorry false

-- TODO:
-- import Mathlib.Data.Nat.Notation failed, environment already contains 'termℕ._closed_5._cstage2' from Lean4NaturalNumberGame.Base
-- Avoiding `contrapose!` tactic for now (Level 7).
-- import Mathlib.Tactic.Contrapose

open MyNat

/- Level 1 / 9 : add_left_comm -/
theorem add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  sorry

/- Level 2 / 9 : making life easier -/
example (a b c d : ℕ) : a + b + (c + d) = a + c + d + b := by
  sorry

/- Level 3 / 9 : making life simple -/
example (a b c d e f g h : ℕ) : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  sorry

macro "simp_add" : tactic => `(tactic|(
  simp only [add_assoc, add_left_comm, add_comm]))

/- Level 4 / 9 : the simplest approach -/
example (a b c d e f g h : ℕ) : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  sorry

/- Level 5 / 9 : pred -/
example (a b : ℕ) (h : succ a = succ b) : a = b := by
  sorry

/- Level 6 / 9 : is_zero -/
theorem succ_ne_zero (a : ℕ) : succ a ≠ zero := by
  sorry

/- Level 7 / 9 : An algorithm for equality -/
theorem succ_ne_succ (m n : ℕ) (h : m ≠ n) : succ m ≠ succ n := by
  sorry

/- Level 8 / 9 : decide -/
-- TODO: The `decide` tactic gives error:
-- failed to synthesize Decidable (20 + 20 = 40)
example : (20 : ℕ) + 20 = 40 := by
  sorry

/- Level 9 / 9 : decide again -/
-- TODO: The `decide` tactic gives error:
-- failed to synthesize Decidable (2 + 2 ≠ 5)
example : (2 : ℕ) + 2 ≠ 5 := by
  sorry
