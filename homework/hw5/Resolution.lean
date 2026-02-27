import LAMR
import LAMR.Examples.proof_systems_for_propositional_logic.resolution

/-
You can use these to evaluate clauses under a truth assignment in the exercises below.

Remember that `PropAssignment` is defined to be `List (String × Bool)` and that any variable `s` that is
not assigned is given the default value `false` by `τ.eval s`.
-/

def Lit.eval : Lit → PropAssignment → Bool
  | .pos s, τ => τ.eval s
  | .neg s, τ => !(τ.eval s)
  | .tr,    _ => true
  | .fls,    _ => false

def Clause.eval : Clause → PropAssignment → Bool
  | [], _      => false
  | l :: ls, τ => l.eval τ || (eval ls τ)

open Resolution

#print VerboseProof
#print VerboseStep
/-
A decision procedure for propositional logic that produces either a satisfying assignment or a proof
of unsatisfiability. You should start by reviewing the exmaples in the second import above.
-/

/--
Given a `VerboseProof` and a list of line numbers corresponding to the clauses of a CNF,
returns the first variable that appears in the CNF, or `none` if there aren't any.
-/
def getVar? (vp : VerboseProof) : List Nat → Option String
  | []      => none
  | c :: cs =>
    match vp[c]!.clause.getVar? with
      | some v => some v
      | none   => getVar? vp cs

/--
Given a `VerboseProof` and a list of line numbers corresponding to the clauses of a CNF, this sorts the clauses into
three lists: those that contain the variable, those that contain its negation, and the rest.
-/
def getPosNegClauseNums (vp : VerboseProof) (var : String) :
    List Nat → List Nat × List Nat × List Nat
  | [] => ([], [], [])
  | (c :: cs) =>
    let (pos, neg, rest) := getPosNegClauseNums vp var cs
    let clause := vp[c]!.clause
    if Lit.pos var ∈ clause then
      (c :: pos, neg, rest)
    else if Lit.neg var ∈ clause then
      (pos, c :: neg, rest)
    else
      (pos, neg, c :: rest)

/--
Our decision procedure should either return a satisfying assignment or a proof of unsatisfiability.
-/
inductive DecisionResult
  | sat (τ : PropAssignment) : DecisionResult
  | unsat (p : VerboseProof) : DecisionResult
deriving Repr, Inhabited

def DecisionResult.show : DecisionResult → IO Unit
  | .sat τ => do
      IO.println s!"Satisfiable: {τ}"
  | .unsat p => do
      IO.println s!"Refutation found:"
      p.show


/-
This procedure takes a `VerboseProof` and a list of line numbers corresponding to the clauses of a CNF. It either
produces a satisfying propositional assignment or extends the proof to a refutation of the CNF.

The algorithm is similar to that of `refute` from the import; the only difference is that it has to build the truth
assignment in the first case and build the proof in the second.

Remember that an element `vp : VerboseProof` is an array, so you can use array operations. Using
`do` notation, if `vp` is declared with `let mut`, then `vp  := vp.push x` adds `x` to the end of
`vp`. The value `vp.size` is the number of elements in the array, so that last element is
`vp.size - 1`. See `Proof.show` in the second import above for an example of a procedure that
builds a proof incrementally.
-/
partial def decide_aux (vp : VerboseProof) (cnf : List Nat) : DecisionResult :=
  -- ** Replace this with your code! **
  if cnf.any (fun i => vp[i]!.clause==[]) then  -- the empty clause
    .unsat vp
  else
    match getVar? vp cnf with
      | none     => .sat []
      | some var => Id.run do
          let (pos, neg, rest) := getPosNegClauseNums vp var cnf
          let mut cnfTrue := rest
          let mut vpTrue := vp
          for i in neg do
            vpTrue := vpTrue.push (VerboseStep.hyp (vpTrue[i]!.clause.erase (Lit.neg var)))
            cnfTrue := (vpTrue.size -1)::cnfTrue
          match decide_aux vpTrue cnfTrue with
          | .sat τ => .sat ((var, true)::τ)
          | .unsat _ =>
            let mut cnfFalse := rest
            let mut vpFalse := vp
            for i in pos do
              vpFalse := vpFalse.push (VerboseStep.hyp (vpFalse[i]!.clause.erase (Lit.pos var)))
              cnfFalse := (vpFalse.size -1)::cnfFalse
            match decide_aux vpFalse cnfFalse with
              | .sat τ => .sat ((var, false)::τ)
              | .unsat _ =>
                let mut new_clauses : List Nat := []
                let mut vp := vp
                for i in pos do
                  for j in neg do
                    let c₁ := vp[i]!.clause
                    let c₂ := vp[j]!.clause
                    let c := resolve c₁ c₂ var
                    if ¬ IsTautology c then
                      vp := vp.push (VerboseStep.res var i j c)
                      new_clauses := (vp.size -1)::new_clauses
                decide_aux vp (new_clauses ++ rest)

/--
This procedure puts it all together: it takes a CNF formula, adds them as hypotheses to a verbose
proof, and then calls the procedure above to decide it.
-/
def decide (cnf : CnfForm) : DecisionResult := Id.run do
  -- start by adding the hypotheses
  let vp : VerboseProof := cnf.toArray.map VerboseStep.hyp
  -- the initial cnf formula consists of the conjunction of the hypotheses
  let cnf_nums := List.range vp.size
  decide_aux vp cnf_nums

-- Try it out!
def example_unsat : CnfForm := cnf!{
   p  q -r,
  -p -q  r,
   q  r -s,
  -q -r  s,
   p  r  s,
  -p -r -s,
  -p  q  s,
   p -q -s
}

#eval decide example_unsat |>.show

def example_sat : CnfForm := cnf!{
   p  q -r,
  -p -q  r,
   q  r -s,
  -q -r  s,
   p  r  s,
  -p -r -s,
  -p  q  s
}

#eval decide example_sat |>.show

  --x  q -r,
  --x -p -q  r,
  --x  q  r -s,
  --x -q -r  s,
  --x  r  s,
  --x -p -r -s,
  --x -p  q  s

/-
Note: this method returns all the clauses derived in the search, whether or not they are
needed in a proof of ⊥.

As an exercise, you can write a procedure that trims a proof to that form.
-/
