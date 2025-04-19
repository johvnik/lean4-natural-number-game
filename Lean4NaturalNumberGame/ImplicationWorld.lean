import Lean4NaturalNumberGame.Base
import Lean4NaturalNumberGame.TutorialWorld
import Lean4NaturalNumberGame.AdditionWorld

open MyNat

/- Level 1 / 11 : The `exact` tactic -/
example (x y z : ℕ) (h1 : x + y = 37) (_h2 : 3 * x + z = 42) : x + y = 37 := by
  exact h1

/- Level 2 / 11 : `exact` practice. -/
example (x : ℕ) (h : zero + x = zero + y + 2) : x = y + 2 := by
  repeat rw [zero_add] at h
  exact h

/- Level 3 / 11 : The `apply` tactic. -/
example (x y : ℕ) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by
  apply h2
  exact h1

/- Level 4 / 11 : succ_inj : the successor function is injective -/
example (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  rw [four_eq_succ_three] at h
  rw [← succ_eq_add_one] at h
  apply succ_inj
  exact h

example : ℕ -> ℕ := by
  intro n
  exact n + 1

example (a b : ℕ) (h : succ a = succ b) : a = b := by
  apply succ_inj at h
  exact h

/- Level 5 / 11 : Arguing backwards -/
example (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  apply succ_inj
  rw [succ_eq_add_one]
  rw [← four_eq_succ_three]
  exact h

/- Level 6 / 11 : intro -/
example (x : ℕ) : x = 37 → x = 37 := by
  intro h
  exact h

/- Level 7 / 11 : intro practice -/
example (x : ℕ) : x + 1 = y + 1 → x = y := by
  intro h
  apply succ_inj
  repeat rw [succ_eq_add_one]
  exact h

/- Level 8 / 11 : ≠ -/
example (x y : ℕ) (h1 : x = y) (h2 : x ≠ y) : False := by
  apply h2
  exact h1

/- Level 9 / 11 : zero_ne_succ -/
theorem zero_ne_one : zero ≠ 1 := by
  intro h
  apply zero_ne_succ
  rw [one_eq_succ_zero] at h
  exact h

/- Level 10 / 11 : 1 ≠ 0 -/
theorem one_ne_zero : 1 ≠ zero := by
  symm
  exact zero_ne_one

/- Level 11 / 11 : 2 + 2 ≠ 5 -/
example : succ (succ zero) + succ (succ zero) ≠ succ (succ (succ (succ (succ zero)))) := by
  intro h
  repeat rw [add_succ] at h
  repeat apply succ_inj at h
  apply zero_ne_one at h
  exact h

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim (And.right h)
    . intro hq
      apply Or.inl
      apply And.intro
      . exact And.left h
      . exact hq
    . intro hr
      apply Or.inr
      apply And.intro
      . exact And.left h
      . exact hr
  . intro h
    apply Or.elim h
    . intro hpq
      apply And.intro
      . exact And.left hpq
      . apply Or.inl
        exact And.right hpq
    . intro hpr
      apply And.intro
      . exact And.left hpr
      . apply Or.inr
        exact And.right hpr
