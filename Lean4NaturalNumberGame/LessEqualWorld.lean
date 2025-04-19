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
  use zero
  rw [add_zero]

/- Level 2 / 11 : 0 ≤ x -/
theorem zero_le (x : ℕ) : zero ≤ x := by
  use x
  rw [zero_add]

/- Level 3 / 11 : x ≤ succ x -/
theorem le_succ_self (x : ℕ) : x ≤ succ x := by
  use 1
  rw [succ_eq_add_one]

/- Level 4 / 11 : x ≤ y and y ≤ z implies x ≤ z -/
theorem le_trans (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  -- NOTE: using "more modern" `obtain` syntax
  obtain ⟨a, ha⟩ := hxy
  obtain ⟨b, hb⟩ := hyz
  use a + b
  rw [← add_assoc]
  rw [← ha]
  rw [← hb]
  -- NOTE: Alternative using `cases` syntax (for obtain ⟨_, _⟩ := _)
  -- cases hxy with
  -- | intro a ha =>
  --   cases hyz with
  --   | intro b hb =>
  --     use a + b
  --     rw [← add_assoc]
  --     rw [← ha]
  --     rw [← hb]

/- Level 5 / 11 : x ≤ 0 → x = 0 -/
theorem le_zero (x : ℕ) (hx : x ≤ 0) : x = 0 := by
  obtain ⟨a, ha⟩ := hx
  symm at ha
  apply add_right_eq_zero at ha
  exact ha

/- Level 6 / 11 : x ≤ y and y ≤ x implies x = y -/
theorem le_antisymm (x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  obtain ⟨a, ha⟩ := hxy
  obtain ⟨b, hb⟩ := hyx
  rw [ha] at hb
  rw [add_assoc x a b] at hb
  symm at hb
  apply add_right_eq_self at hb
  apply add_right_eq_zero at hb
  rw [hb] at ha
  rw [add_zero] at ha
  symm at ha
  exact ha

/- Level 7 / 11 : Dealing with `or` -/
example (x y : ℕ) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  obtain hx | hy := h
  · right
    exact hx
  · left
    exact hy
  -- NOTE: Alternative using `cases` syntax (for obtain _ | _ := _)
  -- cases h with
  -- | inl hx =>
  --   right
  --   exact hx
  -- | inr hy =>
  --   left
  --   exact hy

/- Level 8 / 11 : x ≤ y or y ≤ x -/
theorem le_total (x y : ℕ) : x ≤ y ∨ y ≤ x := by
  induction y with
  | zero =>
    right
    apply zero_le
  | succ y ih =>
    obtain hxy | hyx := ih
    · obtain ⟨a, ha⟩ := hxy
      left
      use a + 1
      rw [succ_eq_add_one]
      rw [ha]
      rw [add_assoc]
    · obtain ⟨a, ha⟩ := hyx
      obtain zero | a := a
      · rw [add_zero] at ha
        rw [ha]
        left
        apply le_succ_self
      · rw [ha]
        right
        use a
        repeat rw [succ_eq_add_one]
        rw [add_comm a 1]
        rw [← add_assoc]

/- Level 9 / 11 : succ x ≤ succ y → x ≤ y -/
theorem succ_le_succ (x y : ℕ) (hx : succ x ≤ succ y) : x ≤ y := by
  obtain ⟨d, hd⟩ := hx
  use d
  rw [succ_add] at hd
  apply succ_inj at hd
  exact hd

/- Level 10 / 11 : x ≤ 1 -/
theorem le_one (x : ℕ) (hx : x ≤ 1) : x = zero ∨ x = 1 := by
  obtain zero | x := x
  · left
    rfl
  · rw [one_eq_succ_zero] at hx
    apply succ_le_succ at hx
    apply le_zero at hx
    right
    rw [hx]
    rfl
  -- Alternative with `cases` syntax
  -- cases x with
  -- | zero =>
  --   left
  --   rfl
  -- | succ x =>
  --   rw [one_eq_succ_zero] at hx
  --   apply succ_le_succ at hx
  --   apply le_zero at hx
  --   right
  --   rw [hx]
  --   rfl

/- Level 11 / 11 : le_two -/
theorem le_two (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by
  obtain zero | x := x
  · left
    rfl
  · rw [two_eq_succ_one] at hx
    apply succ_le_succ at hx
    apply le_one at hx
    obtain h0 | h1 := hx
    · rw [h0]
      right
      left
      rfl
    · rw [h1]
      right
      right
      rfl
