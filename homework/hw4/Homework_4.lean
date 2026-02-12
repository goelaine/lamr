import LAMR

/-
Exercise 1.
-/

-- this may be helpful
def Lit.var : Lit → String
  | tr => ""
  | fls => ""
  | pos s => s
  | neg s => s

-- these may be helpful also
#check List.all
#check List.any
#check List.filter
#print PropAssignment
/-
Remember a `Clause` is a list of literals, so you can do this, for example.
-/
#eval let clause : Clause := [lit!{p}, lit!{-q}, lit!{r}]
      clause.any (fun l => l.var == "p")

namespace PropAssignment

-- relevant clause = not already true and has a variable in P
def relevant (P : PropAssignment) (x : Clause) : Bool :=
  not (List.any x (fun p => (match p with | Lit.tr => true | _ => false)))
  && (List.any x (fun p => List.any P (fun (q,_) => q == Lit.var p)))


def ClauseEval (P : PropAssignment) (x : Clause): Bool :=
  match x with
  | [] => false
  | x::xs =>
      (match x with
      | Lit.tr => true
      | Lit.fls => false
      | Lit.pos s => P.any (fun (l, t) => l==s && t=true) || ClauseEval P xs
      | Lit.neg s => P.any (fun (l, t) => l==s && t=false) || ClauseEval P xs
    )

-- ** Fill in this definition. **
def isAutarky (τ : PropAssignment) (Γ : CnfForm) : Bool :=
  let relevantClauses := List.filter (relevant τ) Γ
  List.all relevantClauses (ClauseEval τ)

-- for testing
#eval isAutarky [] cnf!{p q r, -p -q -r} == true
#eval isAutarky propassign!{p} cnf!{p q r, -p -q -r} == false
#eval isAutarky propassign!{p} cnf!{p q r, -q -r} == true
#eval isAutarky propassign!{p, -q} cnf!{p q r, -p -q -r} == true
#eval isAutarky propassign!{-q} cnf!{-p -q -r} == true
#eval isAutarky propassign!{-q} [] == true
#eval isAutarky (propassign!{p, q, -u, -r}) (cnf!{p q u -v, -u, -r, ⊥, ⊤}) == true
#eval isAutarky (propassign!{p, -q, v}) (cnf!{p q u -v, -u, u, -v}) == false
#eval isAutarky (propassign!{p, -q, v, w, a, b, c, d}) (cnf!{p q u -v, -u, u}) == true

-- ** Fill in this definition. **
def flatten (ls : CnfForm) :=
  match ls with
  | [] => []
  | x::xs => x.append (flatten xs)


def conflict (vars : List Lit) (x : Lit) :=
  match x with
  | Lit.pos x => List.all vars (fun p => match p with | Lit.neg s => s≠x | _ => true)
  | Lit.neg x => List.all vars (fun p => match p with | Lit.pos s => s≠x | _ => true)
  | _ => false

def getPure (Γ : CnfForm) : List Lit :=
  let allVars := flatten Γ
  List.filter (conflict allVars) allVars

-- for testing
def eqSets [BEq α] (k l : List α) : Bool :=
  k.all l.contains &&
  l.all k.contains
infix:40 " eqSets " => eqSets

#eval getPure cnf!{} eqSets []
#eval getPure cnf!{p} eqSets [lit!{p}]
#eval getPure cnf!{-p} eqSets [lit!{-p}]
#eval getPure cnf!{-p, p} eqSets []
#eval getPure cnf!{p, q} eqSets [lit!{p}, lit!{q}]
#eval getPure cnf!{p, q, -p} eqSets [lit!{q}]
#eval getPure cnf!{p, -q, -p} eqSets [lit!{-q}]
#eval getPure cnf!{q p, -q p, p} eqSets [lit!{p}]

end PropAssignment

/-
Exercise 2.
-/

-- ** Write this function. **
def rectangleConstraints (m n k : Nat) : CnfForm :=
  Id.run do
  let mut cnf : CnfForm := []
  for i in [1:n+1] do
    for j in [1:m+1] do
      let clause : Clause :=
        (List.range k).map fun c => Lit.pos s!"p_{i}_{j}_{c+1}"
      cnf := clause :: cnf
      for c in [1:k+1] do
        let atMostCol : List Clause :=
          (List.range (k-c)).map fun co => [Lit.neg s!"p_{i}_{j}_{co+c+1}", Lit.neg s!"p_{i}_{j}_{c}"]
        cnf := List.append atMostCol cnf
      for x in [i+1:n+1] do
        for y in [j+1:m+1] do
          let notEqCorn : List Clause :=
            (List.range k).map fun c => [Lit.neg s!"p_{i}_{j}_{c+1}",Lit.neg s!"p_{x}_{y}_{c+1}",Lit.neg s!"p_{x}_{j}_{c+1}",Lit.neg s!"p_{i}_{y}_{c+1}"]
          cnf := List.append notEqCorn cnf
  return cnf

/-
These should be satisfiable.
-/

#eval show IO Unit from do
  let (_, result) ← callCadical <| rectangleConstraints 10 10 3
  match result with
    | SatResult.Unsat _ => IO.println "unsat."
    | SatResult.Sat   τ => IO.println τ.toString

#eval show IO Unit from do
  let (_, result) ← callCadical <| rectangleConstraints 9 12 3
  match result with
    | SatResult.Unsat _ => IO.println "unsat."
    | SatResult.Sat   τ => IO.println τ.toString

/-
Decode the solutions.
-/

-- This may be helpful; it tests whether a literal is positive.
def Lit.isPos : Lit → Bool
  | pos s => true
  | _     => false

-- ** Write this part: interpret the positive literals as a rectangle. **
def decodeSolution (m n k: Nat) (τ : List Lit) : Except String (Array (Array Nat)) := do
  let mut s : Array (Array Nat) := Array.replicate m (Array.replicate n 0)
  -- use the literals to fill in the rectangle
  return s

def outputSolution (m n k : Nat) (τ : List Lit) : IO Unit :=
  let posLits := τ.filter Lit.isPos
  match decodeSolution m n k posLits with
    | Except.error s => IO.println s!"Error: {s}"
    | Except.ok rect =>
        for i in [:m] do
          for j in [:n] do
            IO.print s!"{rect[i]![j]!} "
          IO.println ""

-- Try it out.

#eval show IO Unit from do
  let (_, result) ← callCadical <| rectangleConstraints 10 10 3
  match result with
    | SatResult.Unsat _ => IO.println "unsat."
    | SatResult.Sat τ  => outputSolution 10 10 3 τ

#eval show IO Unit from do
  let (_, result) ← callCadical <| rectangleConstraints 9 12 3
  match result with
    | SatResult.Unsat _ => IO.println "unsat."
    | SatResult.Sat τ  => outputSolution 9 12 3 τ


/-
Exercise 3.
-/

namespace Resolution

/--
The resolution Step.
-/
def resolve (c₁ c₂ : Clause) (var : String) : Clause :=
  (c₁.erase (Lit.pos var)).union' (c₂.erase (Lit.neg var))

/--
A line of a resolution proof is either a hypothesis or the result of a
resolution step.
-/
inductive Step where
  | hyp (clause : Clause) : Step
  | res (var : String) (pos neg : Nat) : Step
deriving Inhabited, Repr

def Proof := Array Step deriving Inhabited, Repr

-- Ignore this: it is boilerplate to make the `p[i]` notation work.
instance : GetElem Proof Nat Step (fun xs i => i < xs.size) :=
  inferInstanceAs (GetElem (Array Step) _ _ _)

-- determines whether a proof is well-formed
def Proof.wellFormed (p : Proof) : Bool := Id.run do
  for i in [:p.size] do
    match p[i]! with
      | Step.hyp _ => continue
      | Step.res _ pos neg =>
          if i ≤ pos ∨ i ≤ neg then
            return false
  true

-- prints out the proof
def Proof.show (p : Proof) : IO Unit := do
  if ¬ p.wellFormed then
    IO.println "Proof is not well-formed."
    return
  let mut clauses : Array Clause := #[]
  for i in [:p.size] do
    match p[i]! with
      | Step.hyp c =>
          clauses := clauses.push c
          IO.println s!"{i}: hypothesis: {c}"
      | Step.res var pos neg =>
          let resolvent := resolve clauses[pos]! clauses[neg]! var
          clauses := clauses.push resolvent
          IO.println s!"{i}: resolve {pos}, {neg} on {var}: {resolvent}"

end Resolution

section
open Resolution

def example1 : Proof := #[
  .hyp clause!{p q}, -- 0
  .hyp clause!{-p},  -- 1
  .hyp clause!{-q},  -- 2
  .res "p" 0 1,      -- 3 q
  .res "q" 3 2       -- 4 ⊥
]

#eval example1.wellFormed
#eval example1.show

def example2 : Proof := #[
  .hyp clause!{p q r}, -- 0
  .hyp clause!{-p s},  -- 1
  .hyp clause!{-q s},  -- 2
  .hyp clause!{-r s},  -- 3
  .hyp clause!{-s},    -- 4
  .res "p" 0 1,        -- 5 q r s
  .res "q" 5 2,        -- 6 r s
  .res "r" 6 3,        -- 7 s
  .res "s" 7 4         -- 8 ⊥
]

#eval example2.wellFormed
#eval example2.show

-- ** Finish this to get a proof of ⊥.
def example3 : Proof := #[
  .hyp clause!{ p  q -r}, -- 0
  .hyp clause!{-p -q  r}, -- 1
  .hyp clause!{ q  r -s}, -- 2
  .hyp clause!{-q -r  s}, -- 3
  .hyp clause!{ p  r  s}, -- 4
  .hyp clause!{-p -r -s}, -- 5
  .hyp clause!{-p  q  s}, -- 6
  .hyp clause!{ p -q -s}, -- 7
  .res "p" 0 6, --8
  .res "q" 8 3, --9
  .res "q" 0 7, --10
  .res "p" 10 5, --11
  .res "p" 7 1, --12
  .res "q" 2 12, --13
  .res "q" 6 1, -- 14
  .res "p" 4 14, --15
  .res "s" 15 13, --16
  .res "s" 9 11, --17
  .res "r" 16 17
]

#eval example3.wellFormed
#eval example3.show

end
