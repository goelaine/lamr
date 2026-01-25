namespace q1

  partial def helper (n ls i):=
    if i==0 then ls else
      (if (n%i)==0 then (helper n (i::ls) (i-1)) else (helper n ls (i-1)))

  def divisors (n : Nat) : List Nat :=
    helper n [] (n/2)

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
    for i in [:1000] do
      if perfect i then table := table.push i
    table

end q2
