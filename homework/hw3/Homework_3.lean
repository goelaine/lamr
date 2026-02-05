import LAMR

/-
exercise 5
-/

-- you can test whether two strings are equal
#eval if "p" = "q" then "yes" else "no"

namespace PropForm

-- Replace this with the real definition.
def substitute : PropForm → PropForm → String → PropForm
  | _, _, _ => tr

end PropForm

-- Putting the definition in the `PropForm` namespace means you can use the
-- "anonymous projection" notation below.

#eval toString <| prop!{p ∧ (q ∨ r)}.substitute prop!{r ∨ ¬ s} "q"
#eval toString <| prop!{p ∧ (q ∨ r)}.substitute prop!{r ∨ ¬ s} "p"
#eval toString <| prop!{p ∧ (q ∨ r)}.substitute prop!{r ∨ ¬ s} "t"


/-
exercise 6
-/

-- On the right-hand side, Lean determines that `.tr` is `PropForm.tr`
-- because it is expecting a `PropForm` there.

-- Replace this with the real definition.
def CnfForm.toPropForm (F : CnfForm) : PropForm :=
  .tr

#eval toString cnf!{p q r, r -s t, q t}.toPropForm


/-
exercise 7
-/

-- Remember the notation for propositional assignments.
#eval propassign!{p, q, -r}.eval "r"

-- Here are some operations on Booleans.
#eval true && false
#eval true || false
#eval !true

-- You will have to define auxiliary functions, like evaluation
-- for literals and clauses.

-- Rather than open the namespace explicitly, you can put the
-- function in the `CnfForm` namespace like this.
-- In the recursive call, refer to the function as just `eval`.

-- Replace this with the real definition.
def CnfForm.eval : CnfForm → PropAssignment → Bool
  | _, _      => true

#eval cnf!{p q r, r -s t, q t}.eval propassign!{-p, -q, -r, s, -t}


/-
exercise 8
-/

#check NnfForm
#check PropForm.toNnfForm

-- Replace this with the real definition.
inductive EnnfForm where
  -- the type is currently empty

namespace EnnfForm

-- Replace this with the real definition.
def toPropForm : EnnfForm → PropForm
  | _ => sorry

end EnnfForm

namespace PropForm

-- Replace this with the real definition.
def toEnnfForm : PropForm → EnnfForm
  | _ => sorry

end PropForm

-- #eval prop!{¬ ((p ↔ q ↔ r) ∨ s ↔ t)}.toEnnfForm
-- #eval toString <| prop!{¬ ((p ↔ q ↔ r) ∨ s ↔ t)}.toEnnfForm.toPropForm
