namespace q1

  open List

  def divisors (n: Nat) : List Nat :=
    (range (n/2+1)).filter (fun x => n%x == 0)
  -- partial def helper (n ls i):=
  --   if i==0 then ls else
  --     (if (n%i)==0 then (helper n (i::ls) (i-1)) else (helper n ls (i-1)))

  -- def divisors (n : Nat) : List Nat :=
  --   helper n [] (n/2)

end q1

namespace q2
  partial def helper (n : Nat) (ls : List Nat) : Bool :=
    match (n, ls) with
    | (0,[])    => true
    | (n, a::ls) => if a>n then false else helper (n-a) ls
    | _ => false -- (0, ls) or (n, [])

  def perfect (n:Nat) : Bool := Id.run do
    let ls := q1.divisors n
    return helper n ls

  def perfectNums : Array Nat := Id.run do
    let mut table := #[]
    for i in [1:1000] do
      if perfect i then table := table.push i
    table

end q2

namespace q3
  def addOne (ls: List (List α)) (a : α) (acc : List (List α)) :=
    match ls with
    | []      => acc
    | b::ls   => (addOne ls a ((a::b)::acc))

  def helper (rem: List α) (acc : List (List α)) :=
    match rem with
    | []    => acc
    | a::ls => helper ls (acc.append (addOne acc a []))
    -- | a::ls => helper ls (acc.append (List.map (fun l => a::l) acc))

  def sublists : List α → List (List α)
  | []    => [[]]
  | ls => helper ls.reverse [[]]
end q3

namespace q4

  def hanoiAdj (numDisks A B C : Nat) : IO Unit :=
    match numDisks with
    | 0     => pure ()
    | n + 1 => do
        hanoiAdj n A B C
        IO.println s!"Move disk {n + 1} from peg {A} to peg {B}"
        hanoiAdj n C B A
        IO.println s!"Move disk {n + 1} from peg {B} to peg {C}"
        hanoiAdj n A B C
end q4

namespace q5
-- inductive List.{u} : Type u → Type u
-- number of parameters: 1
-- constructors:
-- List.nil : {α : Type u} → List α
-- List.cons : {α : Type u} → α → List α → List α
  inductive LBinTree (α : Type u) where
  | empty : LBinTree α
  | node (label : α) (L : LBinTree α) (R : LBinTree α) : LBinTree α
  deriving Repr, Inhabited

  open LBinTree

  def myTree := node (5 : Nat) (node (7 : Nat) empty (node 3 empty empty)) (node 6 (node 4 empty empty) (node 2 empty empty))

  def addNodes : LBinTree Nat → Nat
    | empty       => 0
    | node a L R  => a + addNodes R + addNodes L

  def toListInorder : LBinTree α → List α
    | empty       => []
    | node a L R  => ((toListInorder L).append (a::(toListInorder R)))

end q5


namespace q6

  def factorial : Nat → Nat
  | 0       => 1
  | (n + 1) => (n + 1) * factorial n

  partial def pascalRow n i (acc : String) := do
    let nFact := factorial n
    match i with
    | 0   =>  acc.append " 1"
    | i   =>  pascalRow n (i-1) ((acc.append " ").append (toString (nFact/(factorial i * factorial (n-i)))))


  def pascal (n : Nat) : IO Unit :=
    for i in [0:n] do
      IO.println s!"{i}:{pascalRow i i ""}"
end q6

-- q1
#eval q1.divisors 10
#eval q1.divisors 12


-- q2
#eval q2.perfectNums

-- q3
#eval q3.sublists [1,2,4,3]

-- q4
#eval q4.hanoiAdj 2 1 2 3

-- q5
#print q5.myTree
#eval q5.addNodes q5.myTree
#eval q5.toListInorder q5.myTree

-- q6
#eval q6.pascal 6
