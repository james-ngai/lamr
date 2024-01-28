import LAMR

def map {α β : Type} (f : α → β) : List α → List β
  | [] => []
  | (h :: t) => f h :: map f t

def sum : List Nat → Nat
  | [] => 0
  | (h :: t) => h + sum t

def question1Helper : Nat -> (Nat → List Nat)
  | 0 => fun _ => []
  | (i + 1) => fun n => if n % (i + 1) = 0 then (i + 1) :: question1Helper i n else question1Helper i n

def question1 : Nat -> List Nat
  | 0 => []
  | (n+1) => question1Helper n (n+1)

#eval question1 100

def question2 (n : Nat) : Bool := n = sum (question1 n)

#eval question2 6

#eval (List.range 1000).filter question2

def question3 {α : Type} : List α → List (List α)
  | [] => [[]]
  | (h :: t) => map (List.cons h) (question3 t) ++ question3 t

#eval question3 [1,2,3]
#eval question3 [1,2,3,4]
-- exercise 1
-- -/

-- Consider a variation of the Towers of Hanoi puzzle where we assume the pegs A, B, and C are
-- in a row, and we are only allowed to transfer a disk to an adjacent peg, which is to say, moves
-- from A to C or vice-versa are ruled out. Convince yourself that the following algorithm works:
-- procedure hanoiAdj(n, A, B, C)
-- if n = 0 then
-- return
-- else
-- move n − 1 disks from A to C
-- move the last disk from A to B
-- move n − 1 disks from C to A
-- move the last disk from B to C
-- move n − 1 disks from A to C
-- end if
-- end procedure
-- Write a Lean program to output the list of moves req

def hanoiAdj (numPegs : Nat) (start aux finish : String) : IO Unit :=
  match numPegs with
  | 0 => pure ()
  | (n + 1) => do
    hanoiAdj n start aux finish
    IO.println s!"move disk from {start} to {aux}"
    hanoiAdj n finish aux start
    IO.println s!"move disk from {aux} to {finish}"
    hanoiAdj n start aux finish

#eval hanoiAdj 3 "A" "B" "C"
/-
exercise 2
-/

inductive LBinTree (α : Type)
  | empty : LBinTree α
  | node  : α -> LBinTree α → LBinTree α → LBinTree α
  /- fill in constructors here -/
  deriving Repr

open LBinTree

def myTree : LBinTree Nat := LBinTree.node 5 (LBinTree.node 7 LBinTree.empty (LBinTree.node 3 LBinTree.empty LBinTree.empty)) (LBinTree.node 6 (LBinTree.node 4 LBinTree.empty LBinTree.empty) (LBinTree.node 2 LBinTree.empty LBinTree.empty))

#eval myTree
-- #eval myTree

namespace LBinTree

def addNodes : LBinTree Nat → Nat
  | LBinTree.empty => 0
  | LBinTree.node n l r => n + addNodes l + addNodes r

#eval addNodes myTree
-- #eval addNodes myTree

def toListInorder : LBinTree α → List α
  | LBinTree.empty => []
  | LBinTree.node n l r => toListInorder l ++ [n] ++ toListInorder r

#eval toListInorder myTree
-- #eval toListInorder myTree

end LBinTree


/-
exercise 3
-/

def fact : Nat → Nat
  | 0 => 1
  | (n + 1) => (n + 1) * fact n

def choose (n : Nat) (k : Nat) : Nat :=
  fact n / (fact k * fact (n - k))

def pascal : Nat -> IO Unit
  | 0 => pure ()
  | (n+1) => do
    pascal n
    IO.print s!"{n}: "
    for i in [0:n+1] do
      IO.print s!"{choose n i} "
    IO.println "¬"


#eval pascal 6
