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
    hanoiAdj n aux finish start

#eval hanoiAdj 5 "A" "B" "C"

def hanoi (num_disks start finish aux: Nat) : IO Unit :=
  match num_disks with
  | 0 => pure ()
  | (n + 1) => do
    hanoi n start aux finish
    IO.println s!"move disk from {start} to {finish}"
    hanoi n aux finish start

#eval hanoi 10 1 2 3

/-
exercise 2
-/

inductive LBinTree (α : Type)
  /- fill in constructors here -/
  deriving Repr

open LBinTree

def myTree : LBinTree Nat :=
  sorry

-- #eval myTree

namespace LBinTree

def addNodes : LBinTree Nat → Nat := sorry

-- #eval addNodes myTree

def toListInorder : LBinTree α → List α := sorry

-- #eval toListInorder myTree

end LBinTree


/-
exercise 3
-/

def pascal (n : Nat) : IO Unit := sorry

-- #eval pascal 10
