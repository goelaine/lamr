import LAMR

/-
# Implementing the syntax of Propositional Logic

The textbook definitions are here:
https://avigad.github.io/lamr/propositional_logic.html#syntax
-/

namespace hidden

-- fix this

inductive PropForm
  | tr     : PropForm
  | fls     : PropForm
  | var    : String → PropForm
  | neg    : PropForm → PropForm
  | conj   : PropForm → PropForm → PropForm
  | disj   : PropForm → PropForm → PropForm
  | impl   : PropForm → PropForm → PropForm
  | biImpl : PropForm → PropForm → PropForm
  deriving Repr, DecidableEq, Inhabited

end hidden

#print PropForm

#check (PropForm.neg (PropForm.var "x"))

#check (PropForm.impl (PropForm.conj (PropForm.var "p") (PropForm.var "q")) (PropForm.var "r"))

#check PropForm.impl (.conj (.var "p") (.var "q")) (.var "r")

#check ((PropForm.var "p").conj (.var "q")).impl (.var "r")

section
open PropForm

#check (impl (conj (var "p") (var "q")) (var "r"))

#check ((var "p").conj (var "q")).impl (var "r")

end

def foo : PropForm := .impl (.conj (.var "p") (.var "q")) (.var "r")

#check (.impl (.conj (.var "p") (.var "q")) (.var "r") : PropForm)

#check prop!{p ∧ q → (r ∨ ¬ p) → q}
#check prop!{p ∧ q ∧ r → p}

def propExample := prop!{p ∧ q → r ∧ p ∨ ¬ s1 → s2}

#print propExample
#eval propExample
#eval toString propExample


/-
Some examples of structural recursion.
-/

namespace PropForm

def complexity : PropForm → Nat
  | var _ => 0
  | tr => 0
  | fls => 0
  | neg A => complexity A + 1
  | conj A B => complexity A + complexity B + 1
  | disj A B => complexity A + complexity B + 1
  | impl A B => complexity A + complexity B + 1
  | biImpl A B => complexity A + complexity B + 1

def depth : PropForm → Nat
  | var _ => 0
  | tr => 0
  | fls => 0
  | neg A => depth A + 1
  | conj A B => max (depth A) (depth B) + 1
  | disj A B => max (depth A) (depth B) + 1
  | impl A B => max (depth A) (depth B) + 1
  | biImpl A B => max (depth A) (depth B) + 1

-- fill in, return the set of variables

def vars' : PropForm → List String
  | .tr => []
  | .fls => []
  | .var x => [x]
  | .neg A => vars' A
  | .conj A B => (vars' A).union' (vars' B)
  | .disj A B => (vars' A).union' (vars' B)
  | .impl A B => (vars' A).union' (vars' B)
  | .biImpl A B => (vars' A).union' (vars' B)


def vars : PropForm → List String
  | .var x => [x]
  | .tr => []
  | .fls => []
  | .neg A => vars A
  | .conj A B => (vars A).union' (vars B)
  | .disj A B => (vars A).union' (vars B)
  | .impl A B => (vars A).union' (vars B)
  | .biImpl A B => (vars A).union' (vars B)

/-
def propExample := prop!{p ∧ q → r ∧ p ∨ ¬ s1 → s2}
-/

#eval complexity propExample
#eval depth propExample
#eval vars propExample

end PropForm

#eval PropForm.complexity propExample
#eval propExample.complexity


-- evaluation of propositional formulas

#check PropAssignment
#print PropAssignment

#check PropAssignment.eval

def assignExample := PropAssignment.mk [("q", true)]

#eval assignExample.eval "p"

def PropForm.eval (τ : PropAssignment) : PropForm → Bool
  | var s =>  τ.eval s -- fix this!!
  | tr => true
  | fls => false
  | neg A => !(eval τ A)
  | conj A B =>   (eval τ A) && (eval τ B)
  | disj A B =>   (eval τ A) || (eval τ B)
  | impl A B =>  !(eval τ A) || (eval τ B)
  | biImpl A B => (eval τ A) == (eval τ B)

/-
def propExample := prop!{(p ∧ q) → (((r ∧ p) ∨ ¬ s1) → s2)}
-/

#eval let τ := PropAssignment.mk [("p", true), ("q", true), ("r", true), ("s2", true)]
  propExample.eval τ

#check propassign!{p, -q, r}

#eval propExample.eval propassign!{p, -q, r}


-- determining satisfiability and validity

def allSublists : List α → List (List α)
  | [] => [[]]
  | a :: as =>
      let recval := allSublists as
      recval.map (a :: .) ++ recval

#eval propExample.vars
#eval allSublists propExample.vars

def allAssignments (A : PropForm) : List PropAssignment :=
  (allSublists A.vars).map (fun l => PropAssignment.mk (l.map (., true)))

#eval allAssignments propExample

def truthTable (A : PropForm) : List (List Bool × Bool) :=
  (allAssignments A).map (fun τ => (A.vars.map τ.eval, A.eval τ))

#eval truthTable propExample
#eval (truthTable propExample).filter (fun p => p.2)

-- how to determine satisfiability and validity?

def PropForm.isSat    (A : PropForm) := (truthTable A).filter (fun p =>  p.2) != []
def PropForm.isValid  (A : PropForm) := (truthTable A).filter (fun p => !p.2) == []

def PropForm.isSat'   (A : PropForm) := (truthTable A).any (fun p => p.2)
def PropForm.isValid' (A : PropForm) := (truthTable A).all (fun p => p.2)

#eval propExample.isValid
#eval propExample.isSat
#eval prop!{(p ∨ ¬ p)}.isValid


-- Negation Normal Form

namespace hidden

inductive Lit
  | tr  : Lit
  | fls  : Lit
  | pos : String → Lit
  | neg : String → Lit

inductive NnfForm
  | lit  (l : Lit)       : NnfForm
  | conj (A B : NnfForm) : NnfForm
  | disj (A B : NnfForm) : NnfForm


-- Converstion to NNF

/-
p ∧ (¬ q ∨ (r ∧ s))

¬ (p ∧ (¬ q ∨ (r ∧ s)))

¬ p ∨ (q ∧ (¬ r ∨ ¬ s))

-/

def Lit.negate : Lit → Lit
  | tr    => fls
  | fls    => tr
  | pos s => neg s
  | neg s => pos s

-- fill in

def NnfForm.neg : NnfForm → NnfForm
  | lit l    => lit l.negate
  | conj A B => disj A.neg B.neg
  | disj A B => conj A.neg B.neg

namespace NnfForm

def toNnfForm : PropForm → NnfForm
  | PropForm.tr         => lit Lit.tr
  | PropForm.fls         => lit Lit.fls
  | PropForm.var p      => lit (Lit.pos p)
  | PropForm.neg A      => (toNnfForm A).neg
  | PropForm.conj A B   => (toNnfForm A).conj (toNnfForm B)
  | PropForm.disj A B   => (toNnfForm A).disj (toNnfForm B)
  | PropForm.impl A B   => ((toNnfForm A).neg).disj (toNnfForm B)
  | PropForm.biImpl A B => ((toNnfForm A).neg.disj (toNnfForm B)).conj
                           ((toNnfForm B).neg.disj (toNnfForm A))

end NnfForm

/-
namespace PropForm

def toNnfForm : PropForm → NnfForm
  | tr         => NnfForm.lit Lit.tr
  | fls         => NnfForm.lit Lit.fls
  | var p      => NnfForm.lit (Lit.pos p)
  | neg A      => A.toNnfForm.neg
  | conj A B   => NnfForm.conj A.toNnfForm B.toNnfForm
  | disj A B   => NnfForm.disj A.toNnfForm B.toNnfForm
  | impl A B   => NnfForm.disj A.toNnfForm.neg B.toNnfForm
  | biImpl A B => NnfForm.conj (NnfForm.disj A.toNnfForm.neg B.toNnfForm)
                               (NnfForm.disj B.toNnfForm.neg A.toNnfForm)

end PropForm
-/

end hidden

#check nnf!{p ∧ q ∧ ((r ∧ ¬ q) ∨ ¬ p) ∨ q}

def propExample0 := prop!{p ∧ q → (r ∨ ¬ p) → q}
def propExample1 := prop!{p ∧ q ∧ r → p}
def propExample2 := prop!{p ∧ q → r ∧ p ∨ ¬ s1 → s2 }

#eval propExample0.toNnfForm
#eval propExample.toNnfForm
#eval toString propExample.toNnfForm

-- Conjunctive Normal Form

namespace hidden₂

def Clause := List Lit

def CnfForm := List Clause

end hidden₂

#print Lit
#print Clause
#print CnfForm

def exLit0 := lit!{ p }
def exLit1 := lit!{ -q }

#print exLit0
#print exLit1

def exClause0 := clause!{ p }
def exClause1 := clause!{ p -q r }
def exClause2 := clause!{ r -s }

#print exClause0
#print exClause1
#print exClause2

def exCnf0 := cnf!{
  p,
  -p q -r,
  -p q
}

def exCnf1 := cnf!{
  p -q,
  p q,
  -p -r,
  -p r
}

def exCnf2 := cnf!{
  p q,
  -p,
  -q
}

#print exCnf0
#print exCnf1
#print exCnf2

#eval toString exClause1
#eval toString exCnf2

#eval List.insert lit!{ r } exClause0

#eval exClause0.union' exClause1

#eval List.Union [exClause0, exClause1, exClause2]

#eval  (exCnf1.map exClause0.union' : CnfForm) |> toString

-- Conversion to CNF

namespace hidden₃

def CnfForm.conj (cnf1 cnf2 : CnfForm) : CnfForm :=
  cnf1.union' cnf2

def CnfForm.disj (cnf1 cnf2 : CnfForm) : CnfForm :=
  (cnf1.map (fun cls => cnf2.map cls.union')).Union

#eval cnf!{p, q, u -w}.disj cnf!{r1 r2, s1 s2, t1 t2 t3}
#eval cnf!{p, q, u -w}.disj cnf!{r1 r2, s1 s2, t1 t2 t3} |> toString

#eval [[1],[2],[3]].union' []


-- fill in

def NnfForm.toCnfForm : NnfForm → CnfForm
  | NnfForm.lit (Lit.pos s) => [ [Lit.pos s] ]
  | NnfForm.lit (Lit.neg s) => [ [Lit.neg s] ]
  | NnfForm.lit Lit.tr      => []
  | NnfForm.lit Lit.fls      => [ [] ]
  | NnfForm.conj A B        => (toCnfForm A).conj (toCnfForm B)
  | NnfForm.disj A B        => (toCnfForm A).disj (toCnfForm B)

def PropForm.toCnfForm (A : PropForm) : CnfForm := A.toNnfForm.toCnfForm

end hidden₃

#eval propExample.toCnfForm |> toString

#eval prop!{(p1 ∧ p2) ∨ (q1 ∧ q2)}.toCnfForm |> toString

#eval prop!{(p1 ∧ p2) ∨ (q1 ∧ q2) ∨ (r1 ∧ r2) ∨ (s1 ∧ s2)}.toCnfForm |> toString


-- Alternative conversion implementation

def CnfForm.disj' (cnf1 cnf2 : CnfForm) : CnfForm := Id.run do
  let mut out : CnfForm := []
  for c₁ in cnf1 do
    for c₂ in cnf2 do
      out := List.insert (c₁.union' c₂) out
  return out

#eval cnf!{p, q, u -w}.disj cnf!{r1 r2, s1 s2, t1 t2 t3}
#eval cnf!{p, q, u -w}.disj' cnf!{r1 r2, s1 s2, t1 t2 t3} |> toString
