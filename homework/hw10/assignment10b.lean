import Mathlib.Tactic

/-
Replace each `sorry` by a proof. The examples from lecture will be helpful.

Each problem is worth 1 point.
-/

open Function

section

variable {α β : Type} (p q : α → Prop) (r : α → β → Prop)

example : (∀ x, p x) ∧ (∀ x, q x) → ∀ x, p x ∧ q x := by
  intro h1, h2

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  sorry

example : (∃ x, p x ∧ q x) → ∃ x, p x := by
  sorry

example : (∃ x, ∀ y, r x y) → ∀ y, ∃ x, r x y := by
  sorry

end

section
open Function

#check Injective
#check Surjective

variable (f : α → β) (g : β → γ)

example (injgf : Injective (g ∘ f)) :
    Injective f := by
  sorry

-- this one is worth two points
example (surjgf : Surjective (g ∘ f)) (injg : Injective g) :
    Surjective f := by
  sorry
end
