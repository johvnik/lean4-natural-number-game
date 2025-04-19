import Lean4NaturalNumberGame.Base
import Lean4NaturalNumberGame.AdditionWorld

-- TODO:
-- import Mathlib.Data.Nat.Notation failed, environment already contains 'termℕ._closed_5._cstage2' from Lean4NaturalNumberGame.Base
-- Avoiding `contrapose!` tactic for now (Level 7).
-- import Mathlib.Tactic.Contrapose

open MyNat

/- Level 1 / 9 : add_left_comm -/
theorem add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc]
  rw [add_comm a b]
  rw [add_assoc]

/- Level 2 / 9 : making life easier -/
example (a b c d : ℕ) : a + b + (c + d) = a + c + d + b := by
  repeat rw [add_assoc]
  rw [add_left_comm b c]
  rw [add_comm b d]

/- Level 3 / 9 : making life simple -/
example (a b c d e f g h : ℕ) : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp only [add_assoc, add_left_comm, add_comm]

macro "simp_add" : tactic => `(tactic|(
  simp only [add_assoc, add_left_comm, add_comm]))

/- Level 4 / 9 : the simplest approach -/
example (a b c d e f g h : ℕ) : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp_add

/- Level 5 / 9 : pred -/
example (a b : ℕ) (h : succ a = succ b) : a = b := by
  rw [← pred_succ a]
  rw [h]
  rw [pred_succ]

/- Level 6 / 9 : is_zero -/
theorem succ_ne_zero (a : ℕ) : succ a ≠ zero := by
  intro h
  rw [← is_zero_succ a]
  rw [h]
  rw [is_zero_zero]

/- Level 7 / 9 : An algorithm for equality -/
theorem succ_ne_succ (m n : ℕ) (h : m ≠ n) : succ m ≠ succ n := by
  intro h'
  apply h
  apply succ_inj
  exact h'

/- Level 8 / 9 : decide -/
-- TODO: The `decide` tactic gives error:
-- failed to synthesize Decidable (20 + 20 = 40)
example : (20 : ℕ) + 20 = 40 := by
  rfl

/- Level 9 / 9 : decide again -/
-- TODO: The `decide` tactic gives error:
-- failed to synthesize Decidable (2 + 2 ≠ 5)
example : (2 : ℕ) + 2 ≠ 5 := by
  intro h
  cases h
