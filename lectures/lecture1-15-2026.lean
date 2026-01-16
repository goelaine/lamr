import Mathlib.Tactic -- only used for some examples

/-

Remember:
- Course website is here: https://www.cs.cmu.edu/~mheule/15311-s26/
- Textbook is online here: https://avigad.github.io/lamr
- Github repository: https://github.com/avigad/lamr

Options:
- Install Lean and VS Code, and then use ctrl-shift-P "Lean 4: Project: Download Project ..."
- Use Lean in Codespaces (see repo)

Resources for using Lean:
- Lean 4 manual: https://lean-lang.org/learn/
- Functional Programming in Lean: https://lean-lang.org/functional_programming_in_lean/
- Theorem Proving in Lean: https://leanprover.github.io/theorem_proving_in_lean/
- Lean community website: https://leanprover-community.github.io/
- Lean Zulip channel: https://leanprover.zulipchat.com/

Lean is both a programming language and a proof assistant.

It is based on a foundational system known as *dependent type theory*.

In type theory,
- everything is an expression
- every expression has a type.

The type determines what sort of object it is.

There are:
- data types, `T : Type`
- objects, `t : T`
- propositions, `P : Prop`
- proofs, `p : P`

-/


-- every well-formed expression has a type
-- #check shows the type
#check 2 + 2
#check -5
#check [1, 2, 3]
#check #[1, 2, 3]
#check (1, 2, 3)
#check "hello world"
#check true
#check fun x => x + 1
#check fun x => if x = 1 then "yes" else "no"

-- types are expressions as well
-- all of type 'Type'
#check Nat
#check Int
#check List Nat
#check Array Nat
#check Nat × Nat × Nat
#check String
#check Bool
#check Nat → Nat
#check Nat → String

-- Lean can confirm the type of an expression
#check (2 + 2 : Nat)
#check ([1, 2, 3] : List Nat)


-- define new objects with the def command
def four : Nat := 2 + 2

def isOne (x : Nat) : String := if x = 1 then "yes" else "no"

-- using #print to show the definition
#check four
#print four

#check isOne
#print isOne


-- Lean may infer types from the context
def four' := 2 + 2

def isOne' x := if x = 1 then "yes" else "no"


-- Lean expressions can be evaluated with #eval
#eval four
#eval isOne 3
#eval isOne 1


-- evaluations can also have side effects,
-- which are generally related to system IO
#eval IO.println "Hello, world!"


-- some expressions in the proof system are propositions
#check 2 + 2 = 4
#check 2 + 2 < 5
#check isOne 3 = "no"
#check 2 + 2 < 5 ∧ isOne 3 = "no"


-- for example the statement of Fermat’s last theorem
def Fermat_statement : Prop :=
∀ a b c n : Nat, a * b * c ≠ 0 ∧ n > 2 → a^n + b^n ≠ c^n

-- to prove a proposition of type P, Lean requires
-- an expression p of type P. 2 + 2 = 4 is easy
theorem two_plus_two_is_four : 2 + 2 = 4 := rfl

-- example is a theorem without a name
example : 2 + 2 = 4 := rfl
-- rfl: reflexive

-- proving Fermat’s last theorem is considerably harder :)
theorem Fermat_last_theorem : Fermat_statement := sorry
-- sorry: like pass

-- a slightly harder example that will be explained later
def fsq (x : ℤ) := 3 * x^2 + 7

example : ∀ x, fsq x ≥ 7 := by
  -- intro x → introduces a generic x from ∀ x into the context
  intro x
  -- simp → simplify the goal using known definitions and lemmas
  simp [fsq]
  -- sq_nonneg = ∀ x : ℤ, 0 ≤ x^2
  -- exact → provide a specific proof term that exactly matches the goal.
  exact sq_nonneg x


/- Using Lean as a functional programming language -/

-- simply define functions and evaluate them
def foo n := 3 * n + 7

#eval foo 3
#eval foo (foo 3)

def bar n := foo (foo n) + 3

#eval bar 3
#eval bar (bar 3)


-- imperative style of programming using do notation
def printExample : IO Unit:= do
  IO.println "hello"
  IO.println "world"

#eval printExample


-- recursive definitions
def factorial : Nat → Nat
  | 0       => 1
  | (n + 1) => (n + 1) * factorial n

#eval factorial 10
#eval factorial 100



-- solution to the Towers of Hanoi problem
def hanoi (numDisks start finish aux : Nat) : IO Unit :=
  match numDisks with
  -- pure() -> return nothing in IO context. opposite of 'do'
  | 0     => pure ()
  | n + 1 => do
      hanoi n start aux finish
      IO.println s!"Move disk {n + 1} from peg {start} to peg {finish}"
      hanoi n aux finish start

#eval hanoi 7 1 2 3


-- define things by recursion on lists
def addNums : List Nat → Nat
  | []    => 0
  | a::as => a + addNums as

#eval addNums [0, 1, 2, 3, 4, 5, 6]


--  useful functions built into Lean’s library
#eval List.range 7

-- section ... end → creates a local namespace,
-- so definitions inside do not pollute the global namespace
section
open List
-- open List → allows you to use functions from the List module directly, e.g., range, map, foldl

#eval range 7
#eval addNums (range 7)
#eval map (fun x => x + 3) (range 7)
#eval foldl (. + .) 0 (range 7)

end


-- Lean also supports projection notation
-- like in OOP class
def myRange := List.range 7
#eval myRange.map fun x => x + 3


-- Everything inside is now called hidden.reverse, hidden.append, etc.
namespace hidden

def reverseAux : List α → List α → List α
  | [],   r => r
  | a::l, r => reverseAux l (a::r)

def reverse (as : List α) :List α :=
  reverseAux as []

-- protected allows projection notation?????????????????????????????????????
protected def append (as bs : List α) : List α :=
  reverseAux as.reverse bs

end hidden


-- partial keyword for if lean can't verify it terminates. now user's responsibility
-- to use it correctly
partial def my_gcd x y :=
  if y = 0 then x else my_gcd y (x % y)

#eval my_gcd 45 30
#eval my_gcd 37252 49824

-- it is possible to provide the termination argument
-- but this won't be need during the course
def term_gcd x y :=
  have (h : y > 0) : (x % y) < y := Nat.mod_lt _ h
  if y = 0 then x else my_gcd y (x % y)

/- It is ok to use partial for homework assignments -/

-- the famous Collatz map
def Collatz (n : Nat) : Nat :=
  if (n % 2) == 0 then n / 2 else 3 * n + 1

-- the conjecture states that this function terminates:
partial def terminate (n : Nat) : Nat :=
  if n <= 1 then n else terminate (Collatz n)

#eval terminate 278658758756956778

-- be careful not to write a bad recursion
partial def bad (n : Nat) : Nat := bad (n + 1)

-- apart from termination, it is important to write
-- efficient code when you evaluate it

-- inefficient definition of Fibonacci
def fib' : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib' (n + 1) + fib' n


-- more efficient
def fibAux : Nat → Nat × Nat
  | 0     => (0, 1)
  | n + 1 => let p := fibAux n
             (p.2, p.1 + p.2)

def fib n := (fibAux n).1

#eval (List.range 35).map fib




/- Inductive data types in Lean -/

inductive BinTree where
  | empty : BinTree
  | node  : BinTree → BinTree → BinTree
  deriving Repr, DecidableEq, Inhabited
  -- allows Lean to print values of BinTree, evaluate = using structural induction, give it a default value

open BinTree

-- provided by Repr
#eval node empty (node empty empty)

-- provided by DecidableEq
#eval empty == node empty empty  -- evaluates to false

--provided by Inhabited
#eval (default : BinTree)  -- BinTree.empty


-- the functions size and depth defined by structural recursion
def size : BinTree → Nat
  | empty    => 0
  | node a b => 1 + size a + size b

def depth : BinTree → Nat
  | empty    => 0
  | node a b => 1 + Nat.max (depth a) (depth b)

def example_tree := node (node empty empty)
                         (node empty
                               (node empty empty))

#eval size example_tree
#eval depth example_tree

-- Lean also supports match syntax
def nonempty (b : BinTree) : Nat :=
  match b with
  | empty    => 0
  | node _ _ => 1

#eval nonempty (node empty empty)

-- list is inductively defined
#print List

#print Option

-- use a match to determine the case
def bin_bar (n? : Option Nat) : Nat :=
  match n? with
  | some n => n
  | none   => 0

#eval bin_bar (some 5)
#eval bin_bar none

-- use getD to return a default value in case the input is none
#eval (some 5).getD 0
#eval none.getD 0



/-
Using Lean as an imperative programming language
-/

-- print the sum of the numbers up to i
-- 'mut' = mutable
def showSums : IO Unit := do
  let mut sum := 0
  for i in [0:100] do
    sum := sum + i
    IO.println s!"i: {i}, sum: {sum}"

#eval showSums

-- using a loop to compute a value
def isPrime (n : Nat) : Bool := Id.run do
  if n < 2 then false else
    for i in [2:n] do
      if n % i = 0 then
        return false
      if i * i > n then
        return true
    true

#eval (List.range 200).filter isPrime


def primes (n : Nat) : Array Nat := Id.run do
  let mut result := #[]
  for i in [2:n] do
    if isPrime i then
      result := result.push i
  result

#eval (primes 10000).size


def oops (n? : Option Nat) : IO Unit := do
  let some n := n? |
    IO.println "oops"
  IO.println n

#eval oops (some 2)
#eval oops none


def mulTable : Array (Array Nat) := Id.run do
  let mut table := #[]
  for i in [:10] do
    let mut row := #[]
    for j in [:10] do
      row := row.push ((i + 1) * (j + 1))
    table := table.push row
  table

#eval mulTable

def mulTable' : Array (Array Nat) := Id.run do
  let mut s : Array (Array Nat) := Array.replicate 10 (Array.replicate 10 0)
  for i in [:10] do
    for j in [:10] do
      s := s.set! i <| s[i]!.set! j ((i + 1) * (j + 1))
  s

#eval show IO Unit from do
  for i in [0:mulTable.size] do
    let row := mulTable[i]!
    for j in [0:row.size] do
      let numstr := toString (row[j]!)
      IO.print <| " ".pushn ' ' (3 - numstr.length)
      IO.print numstr
    IO.println ""
