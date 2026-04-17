import LAMR.Util.FirstOrder.Atp
open Std
open Lean (AssocList)

-- The parts you need to fill in are labeled "TODO".

/-
These helper functions may be useful.
-/

namespace Std.AssocList

def find! [BEq α] [Inhabited β] (a : α) (m : AssocList α β) : β :=
  match m.find? a with
    | some b => b
    | none   => default

end Std.AssocList

def getVal (s : String) (m : AssocList String Sexp) : Nat :=
  match evalNumConst (m.getD s) with
    | some n => n
    | none   => 0

/-
These examples may be helpful. See also the examples in the folder
Examples/using_smt_solvers.
-/

def smt_example_input :=
let xmin := "5"
let ymin := "7"
sexps!{
    (set-logic QF_LIA)
    (set-option :produce-models true)
    (declare-const x Int)
    (declare-const y Int)
    (declare-const z Int)
    (assert (<= {xmin} x))
    (assert (<= {ymin} y))
    (assert (<= (+ x y) z))
    (check-sat)
    (get-model)
  }

def smt_example : IO Unit := do
  -- turn on verbose output to see what is going on.
  let out ← callZ3 smt_example_input (verbose := true)
  match out with
  | Sexp.atom "sat" :: m :: _ =>
    IO.println "Model as an Sexpr"
    IO.println m
    IO.println ""
    let assocList := decodeModelConsts m
    IO.println "Model as an association list:"
    IO.println assocList
    let x := getVal "x" assocList
    let y := getVal "y" assocList
    let z := getVal "z" assocList
    IO.println ""
    IO.println s!"x := {x}, y := {y}, z := {z}"
  | ss =>
    IO.println "Not SAT. Solver output:"
    IO.println ss

#eval smt_example

-- There is also notation for splicing in another list of sexprs.

def smt_example_input2 : List Sexp := Id.run do
  let mut decls : Array Sexp := #[]
  for var in ["x", "y", "z"] do
    decls := decls.push sexp!{(declare-const {var} Int)}
  let xmin := "5"
  let ymin := "7"
  sexps!{
      (set-logic QF_LIA)
      (set-option :produce-models true)
      ...{decls.toList}
      (assert (<= {xmin} x))
      (assert (<= {ymin} y))
      (assert (<= (+ x y) z))
      (check-sat)
      (get-model)
    }

def smt_example2 : IO Unit := do
  let out ← callZ3 smt_example_input (verbose := false)
  match out with
  | Sexp.atom "sat" :: m :: _ =>
    let assocList := decodeModelConsts m
    let x := getVal "x" assocList
    let y := getVal "y" assocList
    let z := getVal "z" assocList
    IO.println s!"x := {x}, y := {y}, z := {z}"
  | ss =>
    IO.println "Not SAT. Solver output:"
    IO.println ss

#eval smt_example2

/-
Problem 1.
-/

-- TODO: Add the relevant constraints

def problem1_input :=
sexps!{
    (set-logic QF_NIA)
    (set-option :produce-models true)
    (declare-const f Int)
    (declare-const o Int)
    (declare-const s Int)
    (declare-const c Int)
    (declare-const l Int)
    (declare-const a Int)
    (declare-const m Int)
    (declare-const r Int)
    (check-sat)
    (get-model)
  }

-- TODO: call the solver and print out the answer

def problem1 : IO Unit := do
  let out ← callZ3 problem1_input (verbose := false)
  match out with
  | Sexp.atom "sat" :: m :: _ =>
    let assocList := decodeModelConsts m
    IO.println "Print solution here."
  | ss =>
    IO.println "Not SAT. Solver output:"
    IO.println ss

#eval problem1

/-
Problem 2.
-/

-- Here are some helper functions

def distinctSexp (consts : List String) : Sexp :=
  Sexp.expr <| [Sexp.atom "distinct"] ++ consts.map Sexp.atom

def multiAritySexp (op : String) (args : List Sexp): Sexp :=
  Sexp.expr <| (Sexp.atom op) :: args

def natConst (i : Nat) := s!"{i}"
def node (i : Nat) := s!"v{i}"
def edge (i : Nat) := s!"e{i}"

#eval distinctSexp [node 0, node 1, node 2]
#eval multiAritySexp "or" [sexp!{({node 0} = 0)}, sexp!{({node 0} = 1)}, sexp!{({node 0} = 2)}]
#eval sexp!{(assert {multiAritySexp "or" [sexp!{({node 0} = 0)}, sexp!{({node 0} = 1)}, sexp!{({node 0} = 2)}]})}

-- TODO: The constraints from part A.

def gracefulLabelingA (n : Nat) : Array Sexp := Id.run do
  let mut body : Array Sexp := #[]
  body

-- Do a reality check.

#eval gracefulLabelingA 9 |>.toList

-- TODO: the constraints from part B.

def gracefulLabelingB (n : Nat) : Array Sexp := Id.run do
  let mut body : Array Sexp := gracefulLabelingA n
  body

-- Another reality check.

#eval gracefulLabelingB 9 |>.toList

def gracefulLabelingProblem (n : Nat) : List Sexp :=
sexps!{
    (set-logic QF_LIA)
    (set-option :produce-models true)
    ...{ gracefulLabelingB n |>.toList }
    (check-sat)
    (get-model)
  }

-- TODO: call the solver and print out the solution.

def gracefulLabeling (n : Nat) : IO Unit := do
  let out ← callZ3 (gracefulLabelingProblem n) (verbose := false)
  match out with
  | Sexp.atom "sat" :: m :: _ =>
    IO.println "Print the solution here."
  | ss =>
    IO.println "Not SAT. Solver output:"
    IO.println ss

#eval gracefulLabeling 9

/-
Problem 3.
-/

-- More helper functions.

def xmin (i : Nat) := s!"xmin_{i}"
def xmax (i : Nat) := s!"xmax_{i}"
def ymin (i : Nat) := s!"ymin_{i}"
def ymax (i : Nat) := s!"ymax_{i}"

-- TODO: Define the list of constant declarations and assertions that say that
-- the almost squares of orders 1 to m cover the almost square of order n.

def AlmostToSmt (n m : Nat) : List Sexp := sexps!{()}

def String.ljust n s :=
  s ++ "".pushn ' ' (n - s.length)

-- TODO: Write a procedure to print it out

def printAlmostSquare (n m : Nat) (model : Sexp) : IO Unit := do
    IO.println ""

-- Call the SAT solver to construct the almost square.

#eval (do
  let cmds := AlmostToSmt 8 15
  -- Set `verbose := false` to hide SMT-LIB communications
  let out ← callZ3 cmds (verbose := true)
  match out with
  | Sexp.atom "sat" :: m :: _ =>
    IO.println <| decodeModelConsts m
    IO.println "SAT with assignment:"
    for (x, b) in decodeModelConsts m do
      IO.println s!"{x} ↦ {evalNumConst b |>.get!}"
    IO.println "\nResult:"
    printAlmostSquare 8 15 m
  | ss =>
    IO.println "Not SAT. Solver output:"
    IO.println ss

  : IO Unit)

-- TODO: Define the bitvector-based encoding.

def almostToSmtBv (n m : Nat) : List Sexp :=
sexps!{()}

-- Call the SAT solver to construct the result square.

#eval (do
  let cmds := almostToSmtBv 8 15
  -- Set `verbose := false` to hide SMT-LIB communications
  let out ← callZ3 cmds (verbose := true)
  match out with
  | Sexp.atom "sat" :: m :: _ =>
    IO.println "SAT with assignment:"
    for (x, b) in decodeModelConsts m do
      IO.println s!"{x} ↦ {evalNumConst b |>.get!}"
    IO.println "\nResult:"
    printAlmostSquare 8 15 m
  | ss =>
    IO.println "Not SAT. Solver output:"
    IO.println ss

  : IO Unit)
