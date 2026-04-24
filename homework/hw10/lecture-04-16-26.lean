import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-
Implication and the universal quantifier
-/

section
variable
  (P Q R S : Nat → Prop)
  (a b : Nat)

variable
  (h1 : ∀ x, P x → Q x)
  (h2 : ∀ x y, Q x → R y → S (x + y))
  (h3 : P a)
  (h4 : R b)

#check h1
#check h1 a
#check h1 a h3
#check h2 a b (h1 a h3) h4

-- x and y are matched with a and b
example : S (a + b) := by
  apply h2
  . apply h1
    exact h3
  . exact h4

example : ∀ x y, P x → R y → S (x + y) := by
  intro u v hPu hRv
  apply h2
  . apply h1
    exact hPu
  . exact hRv

#check fun x y hP hR => h2 x y (h1 x hP) hR

end


section

variable (x y z w : ℤ)

#check add_lt_add_of_lt_of_le    -- ∀ a b c d, a < b → c ≤ d → a + c < b + d
#check mul_le_mul_of_nonneg_left -- ∀ a b c d, b ≤ c → 0 ≤ a → a * b ≤ a * c

example (h1 : x < y) (h2 : w ≤ z) : x + 3 * w < y + 3 * z := by
  apply add_lt_add_of_lt_of_le
  . exact h1
  . apply mul_le_mul_of_nonneg_left
    . exact h2
    . norm_num

#check mul_lt_mul'    -- ∀ a b c d, a ≤ b → c < d → 0 ≤ c → 0 < b → a * c < b * d
#check le_of_lt       -- ∀ a b, a < b → a ≤ b
#check pow_two_nonneg -- ∀ a, 0 ≤ a^2

-- fill in
example (h1 : x < y) (h2 : z^2 < w^2) (h3 : 0 < y) : x * z^2 < y * w^2 := by
  apply mul_lt_mul'
  . exact le_of_lt h1
  . exact h2
  . exact pow_two_nonneg z
  . exact h3


example (h1 : x < y) (h2 : z^2 < w^2) (h3 : 0 < y) :
    x * z^2 < y * w^2 :=
  mul_lt_mul' (le_of_lt h1) h2 (pow_two_nonneg z) h3

end

/-
So theorems can be applied to data and hypotheses
-/

theorem my_add_le_add (x y z w : ℝ) (h₁ : x ≤ y) (h₂ : z ≤ w) :
  x + z ≤ y + w := add_le_add h₁ h₂

section
variable (a b c d : ℝ)
variable (h₁ : a ≤ b)
variable (h₂ : c ≤ d)

#check my_add_le_add
#check my_add_le_add a b
#check my_add_le_add a b c d
#check my_add_le_add a b c d h₁
#check my_add_le_add a b c d h₁ h₂

end

/-
Implicit arguments using {} instead of () -- just FYI. (We won't use them.)
-/

theorem my_add_le_add' {x y z w : ℝ} (h₁ : x ≤ y) (h₂ : z ≤ w) :
  x + z ≤ y + w := add_le_add h₁ h₂

section
variable (a b c d : ℝ)
variable (h₁ : a ≤ b)
variable (h₂ : c ≤ d)

#check my_add_le_add' h₁
#check my_add_le_add' h₁ h₂

end


/-
To prove ∀ x, P x : `intro u`, and then prove `P u`.

To use `h : ∀ x, P x`, apply it.
-/

section

variable {α β : Type} (P Q R : α → Prop)

example (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  intro u
  apply h1
  apply h2

-- fill in
example (h1 : ∀ x, P x → Q x) (h2 : ∀ x, Q x → R x) : ∀ x, P x → R x := by
  intro u hPu
  apply h2
  apply h1
  exact hPu

/-
The existential quantifier.

To prove `∃ x, P x`, use `use`.

To use `h : ∃ x, P x`, use `rcases h with ⟨a, Pa⟩`.
-/

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 2.5
  norm_num

example (h1 : ∃ x, P x) (h2 : ∀ x, P x → Q x) : ∃ x, Q x := by
  rcases h1 with ⟨a, Pa⟩
  use a
  apply h2
  exact Pa

-- fill in
example (h : ∃ x, P x) : ∃ x, P x ∨ Q x := by
  rcases h with ⟨a, Pa⟩
  use a
  left
  exact Pa

end

/-
Injective and Surjective functions.
-/

open Function

#check Injective
#print Injective
#check Surjective
#print Surjective

variable (f : α → β) (g : β → γ)


example (Injf : Injective f) (Injg : Injective g) :
    Injective (g ∘ f) := by
  rw [Injective]  -- can be omitted
  dsimp           -- can be omitted
  intro u v h
  apply Injf
  apply Injg
  exact h


variable (Surjf : Surjective f) (b : β)
#check Surjf b

example (Surjf : Surjective f) (Surjg : Surjective g) :
    Surjective (g ∘ f) := by
  rw [Surjective]  -- can be omitted
  intro z
  rcases Surjg z with ⟨y, h1⟩
  rcases Surjf y with ⟨x, h2⟩
  use x
  dsimp            -- cannot be omitted, needed for final rewrites
  rw [h2,h1]

-- fill in
example (Surjgf : Surjective (g ∘ f)) :
    Surjective g := by
  rw [Surjective]  -- can be omitted
  intro z
  rcases Surjgf z with ⟨y, h1⟩
  use f y
  exact h1

example (Injgf : Injective (g ∘ f)) (Surjf : Surjective f) :
    Injective g := by
  rw [Injective]  -- can be omitted
  intro y1 y2 h
  rcases Surjf y1 with ⟨x1, h1⟩
  rcases Surjf y2 with ⟨x2, h2⟩
  have hx : x1 = x2 := by
    apply Injgf
    dsimp
    rw [h1, h2, h]
  rw [← h1, ← h2, hx]

/-
Example from the textbook.
-/

section

variable {α : Type}
  (Student : α → Prop)
  (Owns : α → α → Prop)
  (Iphone : α → Prop)
  (Laptop : α → Prop)
  (Headphones : α → Prop)
  (Buggy : α → Prop)
  (Sad : α → Prop)
  (h1 : ∀ x, Student x → ∃ y, Owns x y ∧ (Iphone y ∨ Laptop y))
  (h2 : ∀ x y, Student x ∧ Owns x y ∧ Laptop y → ∃ z, Owns x z ∧ Headphones z)
  (h3 : ∀ y, Iphone y → Buggy y)
  (h4 : ∀ y, Headphones y → Buggy y)
  (h5 : ∀ x y, Student x ∧ Owns x y ∧ Buggy y → Sad x)

example : ∀ x, Student x → Sad x := by
  intro u uStu
  rcases h1 u uStu with ⟨a, uaOwns, aIphone | aLaptop⟩
  . apply h5 u a
    constructor
    . exact uStu
    constructor
    . exact uaOwns
    -- alternatively you can use `use uStu, uaOwns`
    apply h3
    exact aIphone
  . rcases h2 u a ⟨uStu, uaOwns, aLaptop⟩ with ⟨b, ubOwns, bHead⟩
    apply h5 u b
    constructor
    . exact uStu
    constructor
    . exact ubOwns
    apply h4
    exact bHead


end


/-
Upper bounds

Not discussed in class, thus not part of the exam
-/

def fn_ub (f : ℝ → ℝ) (a : ℝ) := ∀ x, f x ≤ a

section

variable {f g : ℝ → ℝ} {a b : ℝ}

-- demonstrate variations on `apply`, `have`, and `specialize`
-- `dsimp` helps clarify the goal

theorem fn_ub_add (hfa : fn_ub f a) (hgb : fn_ub g b) :
  fn_ub (f + g) (a + b) := by
  rw [fn_ub]  -- can be omitted
  dsimp       -- can be omitted
  intro x
  apply add_le_add
  . apply hfa
  . apply hgb

example (hfa : fn_ub f a) (hgb : fn_ub g b) :
  fn_ub (f + g) (a + b) := by
  rw [fn_ub]  -- can be omitted
  dsimp       -- can be omitted
  intro x
  apply add_le_add
  . specialize hfa x
    exact hfa
  . specialize hgb x
    exact hgb

example (hfa : fn_ub f a) (hgb : fn_ub g b) :
  fn_ub (f + g) (a + b) := by
  rw [fn_ub]  -- can be omitted
  dsimp       -- can be omitted
  intro x
  have h1 : f x ≤ a := hfa x
  have h2 := hgb x
  exact add_le_add h1 h2

example (hfa : fn_ub f a) (hgb : fn_ub g b) :
  fn_ub (f + g) (a + b) := by
  intro x
  exact add_le_add (hfa x) (hgb x)

end

section

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a

variable {f g : ℝ → ℝ}

-- fill in
example (ubf : fn_has_ub f) (ubg : fn_has_ub g) :
  fn_has_ub (f + g) := by
  rcases ubf with ⟨a, ha⟩
  rcases ubg with ⟨b, hb⟩
  use a + b
  exact fn_ub_add ha hb

end
