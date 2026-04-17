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

    (declare-const fof Int)
    (declare-const scs Int)
    (declare-const lamr Int)
    (assert (= fof (+ (* 100 f) (* 10 o) f)))
    (assert (= scs (+ (* 100 s) (* 10 c) s)))
    (assert (= lamr (+ (* 1000 l) (* 100 a) (* 10 m) r)))


    (assert (distinct f o s c l a m r))

    (assert (and (<= 1 f) (>= 9 f)))
    (assert (and (<= 0 o) (>= 9 o)))
    (assert (and (<= 1 s) (>= 9 s)))
    (assert (and (<= 0 c) (>= 9 c)))
    (assert (and (<= 0 l) (>= 9 l)))
    (assert (and (<= 0 a) (>= 9 a)))
    (assert (and (<= 0 m) (>= 9 m)))
    (assert (and (<= 0 r) (>= 9 r)))

    (assert (= (* fof 9999) (* lamr scs)))
    (check-sat)
    (get-model)
  }

-- TODO: call the solver and print out the answer

def problem1 : IO Unit := do
  let out ← callZ3 problem1_input (verbose := false)
  match out with
  | Sexp.atom "sat" :: m :: _ =>
    let assocList := decodeModelConsts m
    let fof := getVal "fof" assocList
    let scs := getVal "scs" assocList
    let lamr := getVal "lamr" assocList
    IO.println s!"FOF := {fof}, SCS := {scs}, LAMR := {lamr}"
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
  let mut V : List String := []
  for i in [:n+1] do
    body := body.push sexp!{(declare-const {node i} Int)}
    body := body.push sexp!{(assert (and (<= 0 {node i}) (<= {node i} {natConst n})))}
    V := (node i)::V
  body := body.push sexp!{(assert {distinctSexp V})}

  let mut E : List String := []
  for i in [1:n+1] do
    body := body.push sexp!{(declare-const {edge (i)} Int)}
    body := body.push sexp!{(assert (and (<= 1 {edge i}) (<= {edge i} {natConst n})))}
    E := (edge (i))::E
    body := body.push sexp!{(assert (or (= {node (i-1)} (+ {node i} {edge i})) (= {node i} (+ {node (i-1)} {edge i}))))}
  body := body.push sexp!{(assert {distinctSexp E})}

  return body



-- Do a reality check.


#eval gracefulLabelingA 9 |>.toList

-- TODO: the constraints from part B.

def gracefulLabelingB (n : Nat) : Array Sexp := Id.run do
  let mut body : Array Sexp := gracefulLabelingA n
  for i in [:n+1] do
    let mut labelList : List Sexp := []
    for j in [:n+1] do
      labelList :=  (sexp!{(= {node j} {natConst i})})::labelList
    body := body.push sexp!{(assert {multiAritySexp "or" labelList})}

  for i in [1:n+1] do
    let mut labelList : List Sexp := []
    for j in [1:n+1] do
      labelList :=  (sexp!{(= {edge j} {natConst i})})::labelList
    body := body.push sexp!{(assert {multiAritySexp "or" labelList})}
  return body


-- Another reality check.

-- #eval multiAritySexp "or" [sexp!{({node 0} = 0)}, sexp!{({node 0} = 1)}, sexp!{({node 0} = 2)}]
-- #eval sexp!{(assert {multiAritySexp "or" [sexp!{({node 0} = 0)}, sexp!{({node 0} = 1)}, sexp!{({node 0} = 2)}]})}


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
    let assocList := decodeModelConsts m
    let mut res := s!"({toString (getVal (node 0) assocList)})"
    for i in [1:n+1] do
      res := res ++ s!"-{toString (getVal (edge i) assocList)}-({toString (getVal (node i) assocList)})"
    IO.println res
  | ss =>
    IO.println "Not SAT. Solver output:"
    IO.println ss

#eval gracefulLabeling 9

-- def problem1 : IO Unit := do
--   let out ← callZ3 problem1_input (verbose := false)
--   match out with
--   | Sexp.atom "sat" :: m :: _ =>
--     let assocList := decodeModelConsts m
--     let fof := getVal "fof" assocList
--     let scs := getVal "scs" assocList
--     let lamr := getVal "lamr" assocList
--     IO.println s!"FOF := {fof}, SCS := {scs}, LAMR := {lamr}"
--   | ss =>
--     IO.println "Not SAT. Solver output:"
--     IO.println ss

-- #eval problem1

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

def AlmostToSmt (m n : Nat) : List Sexp := Id.run do
  let mut body : List Sexp := []
  for i in [1:m+1] do
    let xmin := xmin i
    let xmax := xmax i
    let ymin := ymin i
    let ymax := ymax i

    body := (sexp!{(declare-const {xmin} Int)})::body
    body := (sexp!{(declare-const {xmax} Int)})::body
    body := (sexp!{(declare-const {ymin} Int)})::body
    body := (sexp!{(declare-const {ymax} Int)})::body

    body := (sexp!{(assert (and (<= 1 {xmin}) (<= {xmax} {natConst (n+1)}) (<= {xmin} {xmax})))})::body
    body := (sexp!{(assert (and (<= 1 {ymin}) (<= {ymax} {natConst (n)}) (<= {ymin} {ymax})))})::body
    body := (sexp!{(assert (and (>= {xmax} (+ {xmin} {natConst (i-1)})) (<= {xmax} (+ {xmin} {natConst i}))))})::body
    body := (sexp!{(assert (and (>= {ymax} (+ {ymin} {natConst (i-1)})) (<= {ymax} (+ {ymin} {natConst i}))))})::body

    body := (sexp!{(assert (= (+ (- {xmax} {xmin}) 1 (- {ymax} {ymin}) 1) {natConst (2*i+1)}))})::body

  for i in [1:m+1] do
    for j in [1:m+1] do
      if i<j then
        let xmini := xmin i
        let xmaxi := xmax i
        let ymini := ymin i
        let ymaxi := ymax i
        let xminj := xmin j
        let xmaxj := xmax j
        let yminj := ymin j
        let ymaxj := ymax j
        let mut ls : List Sexp := []
        ls := (sexp!{(<= {xmaxi} (- {xminj} 1))})::ls
        ls := (sexp!{(<= {xmaxj} (- {xmini} 1))})::ls
        ls := (sexp!{(<= {ymaxj} (- {ymini} 1))})::ls
        ls := (sexp!{(<= {ymaxi} (- {yminj} 1))})::ls

        body := (sexp!{(assert {multiAritySexp "or" ls})})::body

  return sexps!{
    (set-logic QF_LIA)
    (set-option :produce-models true)
    ...{body.reverse}
    (check-sat)
    (get-model)
  }


def String.ljust n s :=
  s ++ "".pushn ' ' (n - s.length)

-- TODO: Write a procedure to print it out

def printAlmostSquare (n m : Nat) (model : Sexp) : IO Unit := do
  IO.println ""
  let assocList := decodeModelConsts model

  let mut grid := Array.replicate m (Array.replicate (m+1) 0)
  for i in [1:n+1] do
    let xmin := getVal (xmin i) assocList
    let xmax := getVal (xmax i) assocList
    let ymin := getVal (ymin i) assocList
    let ymax := getVal (ymax i) assocList
    for r in [ymin:ymax+1] do
      for c in [xmin : xmax+1] do
        grid := grid.set! (r-1) (grid[r-1]!.set! (c-1) i)

  for r in [:m] do
    let mut res := ""
    for c in [:m+1] do
      res := res ++ (toString (grid[r]![c]!))
    IO.println res


-- Call the SAT solver to construct the almost square.
-- TIME: 15 seconds on inputs 100,200
#eval (do
  let cmds := AlmostToSmt 8 15
  -- Set `verbose := false` to hide SMT-LIB communications
  let out ← callZ3 cmds (verbose := false)
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


def bvConst (i : Nat) := toBVConst 16 i


def almostToSmtBv (m n : Nat) : List Sexp := Id.run do
  let mut body : List Sexp := []
  for i in [1:m+1] do
    let xmin := xmin i
    let xmax := xmax i
    let ymin := ymin i
    let ymax := ymax i

    body := (sexp!{(declare-const {xmin} (_ BitVec 16))})::body
    body := (sexp!{(declare-const {xmax} (_ BitVec 16))})::body
    body := (sexp!{(declare-const {ymin} (_ BitVec 16))})::body
    body := (sexp!{(declare-const {ymax} (_ BitVec 16))})::body

    body := (sexp!{(assert (and (bvsle #x0001 {xmin}) (bvsle {xmax} {bvConst (n+1)}) (bvsle {xmin} {xmax})))})::body
    body := (sexp!{(assert (and (bvsle #x0001 {ymin}) (bvsle {ymax} {bvConst (n)}) (bvsle {ymin} {ymax})))})::body
    body := (sexp!{(assert (and (bvsge {xmax} (bvadd {xmin} {bvConst (i-1)})) (bvsle {xmax} (bvadd {xmin} {bvConst i}))))})::body
    body := (sexp!{(assert (and (bvsge {ymax} (bvadd {ymin} {bvConst (i-1)})) (bvsle {ymax} (bvadd {ymin} {bvConst i}))))})::body

    body := (sexp!{(assert (= (bvadd (bvsub {xmax} {xmin}) (bvsub {ymax} {ymin})) {bvConst (2*i-1)}))})::body

  for i in [1:m+1] do
    for j in [i+1:m+1] do
      let xmini := xmin i
      let xmaxi := xmax i
      let ymini := ymin i
      let ymaxi := ymax i
      let xminj := xmin j
      let xmaxj := xmax j
      let yminj := ymin j
      let ymaxj := ymax j
      let mut ls : List Sexp := []
      ls := (sexp!{(bvslt {xmaxi} {xminj})})::ls
      ls := (sexp!{(bvslt {xmaxj} {xmini})})::ls
      ls := (sexp!{(bvslt {ymaxj} {ymini})})::ls
      ls := (sexp!{(bvslt {ymaxi} {yminj})})::ls

      body := (sexp!{(assert {multiAritySexp "or" ls})})::body

  return sexps!{
    (set-logic QF_BV)
    (set-option :produce-models true)
    ...{body.reverse}
    (check-sat)
    (get-model)
  }



-- Call the SAT solver to construct the result square.
-- TIME: 10 seconds on inputs 100,200
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
