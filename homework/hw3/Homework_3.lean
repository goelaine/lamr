import LAMR

/-
exercise 5
-/

-- you can test whether two strings are equal
#eval if "p" = "q" then "yes" else "no"

namespace PropForm

-- Replace this with the real definition.
def substitute (A : PropForm) (B : PropForm) (p : String) : PropForm :=
match A with
  | .tr => tr
  | .fls => fls
  | var s => if s=p then B else var s
  | neg A1 => neg (substitute A1 B p)
  | conj A1 A2 => conj (substitute A1 B p) (substitute A2 B p)
  | disj A1 A2 => disj (substitute A1 B p) (substitute A2 B p)
  | impl A1 A2 => impl (substitute A1 B p) (substitute A2 B p)
  | biImpl A1 A2 => biImpl (substitute A1 B p) (substitute A2 B p)



end PropForm

-- Putting the definition in the `PropForm` namespace means you can use the
-- "anonymous projection" notation below.

#eval toString <| prop!{p ∧ (q ∨ r)}.substitute prop!{r ∨ ¬ s} "q"
#eval toString <| prop!{p ∧ (q ∨ r)}.substitute prop!{r ∨ ¬ s} "p"
#eval toString <| prop!{p ∧ (q ∨ r)}.substitute prop!{r ∨ ¬ s} "t"

#eval toString <| prop!{p}.substitute prop!{r} "p"
#eval toString <| prop!{p}.substitute prop!{r} "q"
#eval toString <| prop!{¬ p}.substitute prop!{q} "p"
#eval toString <| prop!{p ∧ q}.substitute prop!{r} "p"
#eval toString <| prop!{p ∧ q}.substitute prop!{r} "q"
#eval toString <| prop!{p ∨ q}.substitute prop!{r} "p"
#eval toString <| prop!{p → q}.substitute prop!{r} "p"
#eval toString <| prop!{p ↔ q}.substitute prop!{r} "q"
#eval toString <| prop!{¬ (p ∨ q)}.substitute prop!{r} "p"
#eval toString <| prop!{p ∧ (q ∨ r)}.substitute prop!{r ∨ ¬ s} "q"



/-
exercise 6
-/

-- On the right-hand side, Lean determines that `.tr` is `PropForm.tr`
-- because it is expecting a `PropForm` there.

-- Replace this with the real definition.
def LittoProp : Lit -> PropForm
  | .tr => .tr
  | .fls => .fls
  | .pos p => .var p
  | .neg p => .neg (.var p)

def ClausetoProp : Clause → PropForm
  | [] => .fls
  | x::[] => LittoProp x
  | x::xs => .disj (LittoProp x) (ClausetoProp xs)



def CnfForm.toPropForm (F : CnfForm) : PropForm :=
  match F with
  | [] => .tr
  | x::[] => ClausetoProp x
  | x::xs => .conj (ClausetoProp x) (CnfForm.toPropForm xs)

#eval toString cnf!{p q r, r -s t, q t}.toPropForm

#eval toString cnf!{}.toPropForm
#eval toString cnf!{p}.toPropForm
#eval toString cnf!{-p}.toPropForm
#eval toString cnf!{p q}.toPropForm
#eval toString cnf!{p, q}.toPropForm
#eval toString cnf!{p q, r}.toPropForm
#eval toString cnf!{p q, -r}.toPropForm
#eval toString cnf!{p q r}.toPropForm
#eval toString cnf!{p, -p}.toPropForm
#eval toString cnf!{p q, -q r}.toPropForm


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

def ClauseEval (x : Clause) (P : PropAssignment) : Bool :=
  match x with
  | [] => false
  | x::xs =>
      (match x with
      | Lit.tr => true
      | Lit.fls => false
      | Lit.pos s => P.eval s
      | Lit.neg s => !(P.eval s)) || ClauseEval xs P

-- Replace this with the real definition.
def CnfForm.eval (C : CnfForm) (P : PropAssignment) : Bool :=
  match C with
  | [] => true
  | x::xs => (ClauseEval x P) && (eval xs P)

#eval cnf!{p q r, r -s t, q t}.eval propassign!{-p, -q, -r, s, -t}

#eval cnf!{}.eval propassign!{}
#eval cnf!{p}.eval propassign!{p}
#eval cnf!{p}.eval propassign!{-p}
#eval cnf!{-p}.eval propassign!{p}
#eval cnf!{p q}.eval propassign!{p}
#eval cnf!{p q}.eval propassign!{-p, -q}
#eval cnf!{p, q}.eval propassign!{p, q}
#eval cnf!{p, q}.eval propassign!{p, -q}
#eval cnf!{p q}.eval propassign!{p, -q}
#eval cnf!{p, -p}.eval propassign!{p}
#eval cnf!{p q r, -q}.eval propassign!{p, q, r}


/-
exercise 8
-/

#check NnfForm
#check PropForm.toNnfForm

-- Replace this with the real definition.
inductive EnnfForm
  | lit  (l : Lit)       : EnnfForm
  | conj (A B : EnnfForm) : EnnfForm
  | disj (A B : EnnfForm) : EnnfForm
  | biImpl (A B : EnnfForm) : EnnfForm

namespace EnnfForm

-- Replace this with the real definition.
def toPropForm : EnnfForm → PropForm
  | .lit Lit.tr => PropForm.tr
  | .lit Lit.fls => PropForm.fls
  | .lit (Lit.pos p) => PropForm.var p
  | .lit (Lit.neg p) => .neg (PropForm.var p)
  | .conj A B => .conj (toPropForm A) (toPropForm B)
  | .disj A B => .disj (toPropForm A) (toPropForm B)
  | .biImpl A B => .biImpl (toPropForm A) (toPropForm B)

end EnnfForm

def EnnfForm.neg : EnnfForm → EnnfForm
  | .lit l    => lit l.negate
  | .conj A B => disj A.neg B.neg
  | .disj A B => conj A.neg B.neg
  | .biImpl A B => disj (conj A.neg B) (conj A B.neg)

namespace PropForm

-- Replace this with the real definition.
def toEnnfForm : PropForm → EnnfForm
  | PropForm.tr         => .lit Lit.tr
  | PropForm.fls         => .lit Lit.fls
  | PropForm.var p      => .lit (Lit.pos p)
  | PropForm.neg A      => (toEnnfForm A).neg
  | PropForm.conj A B   => (toEnnfForm A).conj (toEnnfForm B)
  | PropForm.disj A B   => (toEnnfForm A).disj (toEnnfForm B)
  | PropForm.impl A B   => ((toEnnfForm A).neg).disj (toEnnfForm B)
  | PropForm.biImpl A B => (toEnnfForm A).biImpl (toEnnfForm B)

end PropForm


#eval prop!{p}.toEnnfForm
#eval prop!{¬ p}.toEnnfForm
#eval prop!{p ∧ q}.toEnnfForm
#eval prop!{p ∨ q}.toEnnfForm
#eval prop!{p → q}.toEnnfForm
#eval prop!{p ↔ q}.toEnnfForm
#eval prop!{¬ (p ∧ q)}.toEnnfForm
#eval prop!{¬ (p ∨ q)}.toEnnfForm
#eval prop!{¬ (p → q)}.toEnnfForm
#eval prop!{¬ ((p ↔ q) ∨ r)}.toEnnfForm

#eval prop!{¬ ((p ↔ q ↔ r) ∨ s ↔ t)}.toEnnfForm
#eval toString <| prop!{¬ ((p ↔ q ↔ r) ∨ s ↔ t)}.toEnnfForm.toPropForm


#eval toString <| (prop!{p}).toEnnfForm.toPropForm
#eval toString <| (prop!{¬ p}).toEnnfForm.toPropForm
#eval toString <| (prop!{p ∧ q}).toEnnfForm.toPropForm
#eval toString <| (prop!{p ∨ q}).toEnnfForm.toPropForm
#eval toString <| (prop!{p → q}).toEnnfForm.toPropForm
#eval toString <| (prop!{p ↔ q}).toEnnfForm.toPropForm
#eval toString <| (prop!{¬ (p ∧ q)}).toEnnfForm.toPropForm
#eval toString <| (prop!{¬ (p ∨ q)}).toEnnfForm.toPropForm
#eval toString <| (prop!{¬ (p → q)}).toEnnfForm.toPropForm
#eval toString <| prop!{¬ ((p ↔ q ↔ r) ∨ s ↔ t)}.toEnnfForm.toPropForm
