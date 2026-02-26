import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variables (P Q R : Prop)

/- Creating functions. -/

example : ℕ → ℕ := sorry

example : P → P := sorry

-- use `rfl` as proof of reflexivity.
example : ∀ (x : ℕ), x = x := sorry

example : (x : ℕ) → x = x := sorry
example : ∀ (x : ℕ), ℕ := sorry

#check Not
example : ¬ False := sorry

/- Applying functions. -/

example (f : ℕ → ℝ) (g : ℝ → Bool) (n : ℕ) : Bool := sorry

example (f : P → Q) (g : Q → R) (p : P) : R := sorry

example (f : ∀ (x : Nat), x + 1 > x) : 2 + 1 > 2 := sorry

example (f : ¬ P) (p : P) : False := sorry

/- Structures -/

structure Point where
  x : Nat
  y : Nat

#check Point.mk
#check Point.x
#check Point.y

example (x : Nat) (y : Nat) : Point := sorry
example (p : Point) : Nat := sorry

#check And
#check And.intro
#check And.left
#check And.right

example (p : P) (q : Q) : P ∧ Q := sorry
example (h : P ∧ Q) : P := sorry

example (h : ∃ (x : Nat), P) : Nat := sorry
example (h : ∃ (x : Nat), P) : P := sorry

#check Iff
#check Iff.intro
#check Iff.mp
#check Iff.mpr

example (h : P ↔ Q) (p : P) : Q := sorry
example : P ↔ P := sorry

#check True.intro
example : True := sorry

#check Exists
#check Exists.intro
#check Exists.choose
#check Exists.choose_spec
example : ∃ (x : Nat), x = x := sorry

/- Enumerations -/

#check Bool
example : Bool := sorry

example (b : Bool) : Nat := sorry

#check Nat
#check Nat.zero
#check Nat.succ

example : Nat := sorry

def isZero (n : Nat) : Bool := sorry

#check Or
#check Or.inl
#check Or.inr

example (p : P) : P ∨ Q := sorry

example (h : P ∨ Q) (f : P → R) (g : Q → R) : R := sorry

#check False

example (f : False) : P := sorry

/- Recursion -/

#check Nat.le
#check Nat.le.refl
#check Nat.le.step

def zero_le_n (n : Nat) : 0 ≤ n := sorry

/- Practice -/

example (h : P ∧ ¬ Q) : ¬ (P → Q) := sorry

example (h : ¬ P ∧ ¬ Q) : ¬ (P ∨ Q) := sorry

variables (P Q : ℕ → Prop) in
example (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := sorry

/- Let statements -/

example (f : ℕ → ℝ) (g : ℝ → Bool) (n : ℕ) : Bool :=
  let r := f n
  g r

example (f : P → Q) (g : Q → R) (p : P) : R :=
  have q := f p
  g q

example (f : P → Q) (g : Q → R) (p : P) : R := by
  have q := f p
  exact g q


/- Specialized Automation -/
variable (a b c d : Int)

example (h : a = a * a) : b * a = b * (a * a) := by
  nth_rw 1 [h]

example (n : Nat) : 1*(n + 0)^1 = n := by simp

example : 123 * 345 = 42435 := by
  norm_num

example : (a + b)^2 = a^2 + 2*a*b + b^2 := by
  ring

/- Induction -/

def sum_up_to : Nat → Nat
  | 0 => 0
  | (n + 1) => (n + 1) + sum_up_to n

#check mul_add

example (n : Nat) : 2 * sum_up_to n = n * (n + 1) := by
  induction n with
  | zero =>
    rw [sum_up_to]
  | succ n ih =>
    rw [sum_up_to, mul_add, ih]
    ring

def sum_odds : Nat → Nat
  | 0 => 0
  | (n + 1) => (2 * n + 1) + sum_odds n

#check pow_two
#check mul_zero

theorem sum_odds_eq_square (n : Nat) : sum_odds n = n^2 := by
  induction n with
  | zero =>
    rw [sum_odds, pow_two, mul_zero]
  | succ n ih =>
    rw [sum_odds, ih]
    ring

open Nat

def add' : Nat → Nat → Nat
  | m, 0 => m
  | m, (n + 1) => (add' m n) + 1

theorem zero_add' (n : Nat) : add' 0 n = n := by
  induction n with
  | zero => rw [add']
  | succ n ih => rw [add', ih]

theorem succ_add' (m n : Nat) :
    add' (succ m) n = succ (add' m n) := by
  induction n with
  | zero =>
    sorry
  | succ n ih =>
    sorry

theorem add'_comm (m n : Nat) : add' m n = add' n m := by
  induction m with
  | zero =>
    sorry
  | succ m ih =>
    sorry

/- General Automation -/

example [CommRing α] (a b c : α) :
    a + b + c = 3 →
    a ^ 2 + b ^ 2 + c ^ 2 = 5 →
    a ^ 3 + b ^ 3 + c ^ 3 = 7 →
    a ^ 4 + b ^ 4 = 9 - c ^ 4 := by
  grind

example (x y : Fin 11) :
    x ^ 2 * y = 1 →
    x * y ^ 2 = y →
    y * x = 1 := by
  grind

example (x y : Int) :
    27 ≤ 11 * x + 13 * y →
    11 * x + 13 * y ≤ 45 →
    -10 ≤ 7 * x - 9 * y →
    7 * x - 9 * y ≤ 4 →
    False := by
  grind
