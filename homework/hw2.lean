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
    -- | a::ls => helper ls (acc.append (addOne acc a []))
    | a::ls => helper ls (acc.append (List.map (fun l => a::l) acc))

  def sublists : List α → List (List α)
  | []    => [[]]
  | ls => helper ls.reverse [[]]
end q3

-- q1
#eval q1.divisors 10
#eval q1.divisors 12


-- q2
#eval q2.perfectNums

-- q3
#eval q3.sublists [1,2,3]
