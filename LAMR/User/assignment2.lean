import LAMR

def map {α β : Type} (f : α → β) : List α → List β
  | [] => []
  | (h :: t) => f h :: map f t

def filter {α : Type} (p : α → Bool) : List α → List α
  | [] => []
  | (h :: t) => if p h then h :: filter p t else filter p t

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

#eval filter question2 (List.range 1000)
-- exercise 1
-- -/

def hanoiAdj (numPegs : Nat) (start aux finish : String) : IO Unit :=
  sorry

-- #eval hanoiAdj 5 "A" "B" "C"


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
