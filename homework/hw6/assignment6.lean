import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

variable (P Q R S : Prop)

/-
Replace the following sorry's by proofs.

RESTRICTION: You can only use the tactics: intro, exact,
  apply, constructor, rcases, left, right, and by_cases.
-/

example : (P → Q) ∧ (Q → R) → P → R := by
  intro h hP
  rcases h with ⟨ hPi, hQi ⟩
  apply hQi
  apply hPi
  exact hP

example (h : P → Q) (h1 : P ∧ R) : Q ∧ R := by
  rcases h1 with ⟨ p, r ⟩
  constructor
  . apply h
    exact p
  . exact r

example (h : ¬ (P ∧ Q)) : P → ¬ Q := by
  intro p q
  apply h
  constructor
  . apply p
  . apply q

example (h : ¬ (P → Q)) : ¬ Q := by
  intro q
  apply h
  intro hP
  exact q

example (h : P ∧ ¬ Q) : ¬ (P → Q) := by
  intro pq
  rcases h with ⟨ p, q ⟩
  apply q
  apply pq
  exact p

example (h1 : P ∨ Q) (h2 : P → R) : R ∨ Q := by
  rcases h1 with p | q
  . left
    apply h2
    exact p
  . right
    exact q


example (h1 : P ∨ Q → R) : (P → R) ∧ (Q → R) := by
  constructor
  . intro p
    apply h1
    . left
      exact p
  . intro q
    apply h1
    . right
      exact q


example (h1 : P → R) (h2 : Q → R) : P ∨ Q → R := by
  intro pq
  rcases pq with p | q
  apply h1
  exact p
  apply h2
  exact q


example (h : ¬ (P ∨ Q)) : ¬ P ∧ ¬ Q := by
  constructor
  . intro p
    apply h
    . left
      exact p
  . intro q
    apply h
    . right
      exact q


-- this one requires classical logic!
example (h : ¬ (P ∧ Q)) : ¬ P ∨ ¬ Q := by
  by_cases p : P
  . right
    intro q
    apply h
    constructor
    . exact p
    . exact q
  . left
    exact p


-- this one too
example (h : P → Q) : ¬ P ∨ Q := by
  by_cases p : P
  . right
    apply h
    exact p
  . left
    . exact p

/-
Prove the following using only `rw` and the identities given.

Remember that you can use `rw [← h]` to use an identity in the reverse direction,
and you can provides argument to general identities to instantiate them.
-/

#check add_assoc
#check add_comm
#check pow_mul
#check mul_comm
#check mul_add

/- RESTRICTION: You can only use the above rewrite rules -/

example (x y z : Nat) : (x + y) + z = (z + y) + x := by
  rw [add_assoc x y z, add_comm x (y+z), add_comm z y]

example (x y z : Nat) : (x^y)^z = (x^z)^y := by
  rw [←pow_mul x y z, mul_comm y z, ←pow_mul x z y]

example (x y z w : Nat) : (x^y)^(z + w) = x^(y * z + y * w) := by
  rw [←pow_mul x y (z+w), mul_add y z w]

/-
A *group* is a structure with *, ⁻¹, 1 satisfing the basic group laws.

  https://en.wikipedia.org/wiki/Group_(mathematics)
-/

section
-- Lean lets us declare a group as follows.
variable {G : Type*} [Group G]

#check @mul_inv_cancel
#check @inv_mul_cancel
#check @mul_one
#check @one_mul
#check @mul_assoc

example (x y : G) : x * y * y⁻¹ = x := by
  rw [mul_assoc, mul_inv_cancel, mul_one]

/-
A group is *abelian* if it satisfies the additional law that
`x * y = y * x` for all `x` and `y`.

Fill in the sorry's in the next two theorems. The final one shows that
any group satisfying `x * x = 1` for every `x` is abelian.

You can use `rw [h]` to replace any expression of the form `e * e` by `1`.
-/

/- RESTRICTION: You can only use the above rewrite rules -/

theorem fact1 (h : ∀ x : G, x * x = 1) (y z : G) :
    y * z = y * (y * z) * (y * z) * z := by
  sorry

theorem fact2 (h : ∀ x : G, x * x = 1) (y z : G) :
    z * y = y * (y * z) * (y * z) * z := by
  sorry

theorem main (h : ∀ x : G, x * x = 1) (y z : G) :
    y * z = z * y := by
  rw [fact1 h y z, fact2 h y z]

end
