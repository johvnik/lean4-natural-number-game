import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.ApplyAt


------------------------------------------------------------
-------------------------- MyNat ---------------------------
------------------------------------------------------------
inductive MyNat where
  | zero : MyNat
  | succ : MyNat -> MyNat
  deriving Repr

notation "ℕ" => MyNat

open MyNat

def nat_to_mynat (n : Nat) : ℕ  :=
  match n with
  | Nat.zero => zero
  | Nat.succ n' => succ (nat_to_mynat n')

instance : OfNat MyNat n where
  ofNat := nat_to_mynat n

def is_eq : ℕ → ℕ → Bool
  | zero, zero => true
  | zero, succ _ => false
  | succ _, zero => false
  | succ n, succ m => is_eq n m

theorem is_eq_correct : ∀ a b : ℕ, is_eq a b = true ↔ a = b := by
  intro a
  induction a with
  | zero =>
    intro b
    cases b with
    | zero => simp [is_eq]
    | succ b => simp [is_eq]
  | succ a ih =>
    intro b
    cases b with
    | zero => simp [is_eq]
    | succ b =>
      simp [is_eq]
      rw [ih]

-- NOTE: This function type syntax also works for the rest.
def is_zero : ℕ -> Bool
  | zero => true
  | _    => false

def pred (n : ℕ) : ℕ :=
  match n with
  | zero => zero
  | succ n' => n'

def add (m : ℕ) (n : ℕ) : ℕ :=
  match n with
  | zero => m
  | succ n' => succ (add m n')

instance : Add ℕ where
  add := add

def mul (m n : ℕ) : ℕ :=
  match n with
  | zero => zero
  | succ n' => add m (mul m n')

instance : Mul ℕ where
  mul := mul

def pow (m n : ℕ) : ℕ :=
  match n with
  | zero => 1
  | succ n' => mul m (pow m n')

instance : Pow ℕ ℕ where
  pow := pow

-- NOTE: Alternative for le
-- def le (m n : ℕ) : Prop :=
--   match m with
--   | zero => true
--   | succ m' =>
--     match n with
--     | zero => false
--     | succ n' => le m' n'

def le (a b : ℕ) := ∃ (c : ℕ), b = a + c

instance : LE ℕ where
 le := le

-- NOTE: Alternative for lt
-- def lt (m n : ℕ) : Prop :=
--   match m, n with
--   | _, zero => false
--   | zero, succ _ => true
--   | succ m', succ n' => lt m' n'

def lt (a b : ℕ) := a ≤ b ∧ ¬ (b ≤ a)

instance : LT ℕ where
  lt := lt

------------------------------------------------------------
------------------------ Theorems --------------------------
------------------------------------------------------------

/- Peano -/
theorem is_zero_succ (n : ℕ) : is_zero (succ n) = False := by
  simp [is_zero]

theorem is_zero_zero : is_zero zero := by
  simp [is_zero]

theorem pred_succ (n : ℕ) : pred (succ n) = n := by
  rfl

theorem succ_inj (a b : ℕ) : succ a = succ b → a = b := by
  intro h
  cases h
  rfl

theorem zero_ne_succ (a : ℕ) : zero ≠ succ a := by
  intro h
  cases h

/- 012 -/
theorem one_eq_succ_zero : 1 = succ zero := by
  rfl

theorem two_eq_succ_one : 2 = succ 1 := by
  rfl

theorem three_eq_succ_two : 3 = succ 2 := by
  rfl

theorem four_eq_succ_three : 4 = succ 3 := by
  rfl

/- + -/
theorem add_zero (a : ℕ) : a + zero = a := by
  rfl

theorem add_succ (a d : ℕ) : a + succ d = succ (a + d) := by
  rfl

/- * -/
theorem mul_zero (a : ℕ) : a * zero = zero := by
  rfl

lemma mul_succ' (a b : ℕ) : a * succ b = a + a * b := by
  rfl

/- ^ -/
theorem pow_zero (a : ℕ) : a ^ zero = 1 := by
  rfl

theorem pow_succ' (a b : ℕ) : a ^ succ b = a * a ^ b := by
  rfl

/- ≤ -/
-- theorem le_iff_exists_add (a b : ℕ) :
--   a ≤ b ↔ ∃ (c : ℕ), b = a + c := Iff.rfl
