import Mathlib.Tactic

/-
Replace each `sorry` by a proof. The examples from lecture will be helpful.

Each problem is worth 1 point.
-/

open Function

section

variable {α β : Type} (p q : α → Prop) (r : α → β → Prop)

example : (∀ x, p x) ∧ (∀ x, q x) → ∀ x, p x ∧ q x := by
  intro h
  rcases h with ⟨P,Q⟩
  intro u
  constructor
  apply P
  apply Q


example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h
  rcases h with P | Q
  intro u
  left
  apply P
  intro u
  right
  apply Q

example : (∃ x, p x ∧ q x) → ∃ x, p x := by
  intro h
  rcases h with ⟨X, P, Q⟩
  use X

example : (∃ x, ∀ y, r x y) → ∀ y, ∃ x, r x y := by
  intro h
  rcases h with ⟨X, R⟩
  intro u
  use X
  apply R

end

section
open Function

#check Injective
#print Injective
#check Surjective
#print Surjective


variable (f : α → β) (g : β → γ)

example (injgf : Injective (g ∘ f)) :
    Injective f := by
  intro u v h
  apply injgf
  rw [Function.comp, Function.comp, h]

-- this one is worth two points
example (surjgf : Surjective (g ∘ f)) (injg : Injective g) :
    Surjective f := by
  intro z
  rcases surjgf (g z) with ⟨y, h⟩
  use y
  apply injg
  exact h
end
