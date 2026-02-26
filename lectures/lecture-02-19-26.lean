
import Mathlib.Data.Real.Basic

/-
Propositional logic -- Section 9.1
-/

variable (P Q R S : Prop)

#check True
#check False
#check P ∧ Q
#check P ∨ Q
#check P → Q
#check P ↔ Q
#check ¬ P

theorem easy : P → P := by
  intro h
  apply h

#print easy

example : P → P := by
  intro h
  apply h

example : P → P := by
  intro h
  exact h
  done

example (h1 : P → Q) (h2 : P) : Q := by
  apply h1
  exact h2

example : P → Q → P ∧ Q := by
  intro hP
  intro hQ
  constructor
  . exact hP
  . exact hQ

example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor
  . exact hP
  . exact hQ

theorem and_com : P ∧ Q → Q ∧ P := by
  intro hPQ
  rcases hPQ with ⟨hP, hQ⟩
  constructor
  . exact hQ
  . exact hP

theorem or_com : P ∨ Q → Q ∨ P := by
  intro h
  rcases h with hP | hQ
  -- P ⊢ Q v P
  . right
    exact hP
  -- Q ⊢ Q v P
  . left
    exact hQ

theorem and_com_2 : (S ∧ Q) ∨ (S ∧ R) → (Q ∧ S) ∨ (R ∧ S):= by
  intro h
  rcases h with hSQ | hSR
  . left
    apply and_com
    exact hSQ
  . right
    apply and_com
    exact hSR

example : ¬ P → P → False := by
  intro h
  exact h

example (h : P → Q) : ¬ Q → ¬ P := by
  intro hnQ hP
  apply hnQ
  apply h
  exact hP

example (h : False) : P := by
  contradiction

example (h : False) : P := by
  rcases h

example (h1 : P) (h2 : ¬ P) : Q := by
  contradiction

example (h1 : P ∨ Q) (h2 : ¬ P) : Q := by
  rcases h1 with hP | hQ
  . contradiction
  . exact hQ

example (h1 : P ↔ Q) : Q ↔ P := by
  rcases h1 with ⟨hPQ, hQP⟩
  constructor
  . exact hQP
  . exact hPQ

-- classical logic

example (h1 : P → Q) : ¬ P ∨ Q := by
  by_cases hP : P
  . right
    apply h1
    exact hP
  . left
    exact hP

example : ¬ ¬ P → P := by
  intro hnnP
  by_cases hP : P
  . exact hP
  . contradiction

/-
To prove `A ∧ B`, use `constructor`
To use `h : A ∧ B`, use `rcases h with ⟨hA, hB⟩`
To prove `A ∨ B`, use `left` or `right`
To use `h : A ∨ B`, use `rcases h with hA | hB`
To prove `A → B`, use `intro h`
To use `h : A → B`, use `apply h`
To prove `¬ A`, use `intro h`
To use `h : ¬ A`, use `apply h`
To prove `False`, there is no canonical way
To use `h : False`, use `contradiction`
To prove `A ↔ B`, use `constructor`
To use `h : A ↔ B`, use `rcases h with ⟨hAB, hBA⟩`

When you need classical logic, use `by_cases h : A` or `by_contra h`,
-/

example (h1 : P ↔ Q) (h2 : P) : Q := by
  sorry

example : P ∧ Q ∧ (P → R) → R := by
  sorry

example (h : ¬ P ∧ ¬ Q) : ¬ (P ∨ Q) := by
  sorry

theorem dist_and_or (h : P ∧ (Q ∨ R)) : (P ∧ Q) ∨ (P ∧ R) := by
  sorry

#print dist_and_or
#print and_com_2

example (h : P ∧ (Q ∨ R)) : (Q ∧ P) ∨ (R ∧ P) := by
  apply and_com_2
  apply dist_and_or
  exact h


/-
Equational reasoning -- Section 13.1
-/

variable (a b c d : Int)
variable (f : Int → Int)

example : f (a + b) = f (a + b) := by
  rfl

example (h : b = c) : f (a + b) = f (a + c) := by
  rw [h]

example (h1 : a = c) (h2 : b = d) : f (a + b) = f (c + d) := by
  rw [h1]
  rw [h2]

example (h1 : a = c) (h2 : b = d) : f (a + b) = f (c + d) := by
  rw [←h1, h2]

example (h1 : a = c) (h2 : d = c + b) (h3 : d = e) :
    f (a + b) = f (e) := by
  rw [h1, ← h2, h3]


#check (mul_assoc : ∀ a b c, (a * b) * c = a * (b * c))
#check (mul_comm : ∀ a b, a * b = b * a)
#check (mul_left_comm : ∀ a b c, a * (b * c) = b * (a * c))

example : (c * b) * a = b * (a * c) := by
  rw [mul_assoc, mul_comm, ← mul_assoc]

example : (a * b) * c = b * (a * c) := by
  rw [mul_comm a b, mul_assoc b a c]

example : (a * b) * c = b * (a * c) := by
  rw [mul_comm a, mul_assoc]
