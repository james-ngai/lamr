import LAMR

/-
Exercise 1.
-/

-- this may be helpful
def Lit.var : Lit → String
  | tr => ""
  | fls => ""
  | pos s => s
  | neg s => s

-- these may be helpful also
#check List.all
#check List.any
#check List.filter
#check List.contains

/-
Remember a `Clause` is a list of literals, so you can do this, for example.
-/
#eval let clause : Clause := [lit!{p}, lit!{-q}, lit!{r}]
      clause.any (fun l => l.var == "p")

#eval let clause : Clause := [lit!{p}, lit!{-q}, lit!{r}]
      clause.any (fun l => l.var == "p")

namespace PropAssignment

def propInClause : PropAssignment → Clause → Bool
  | [], _ => false
  | (string, _)::τ, clause => clause.any (fun l => l.var == string) || propInClause τ clause

def tauInProp : PropAssignment → Lit → Bool
  | [], _ => false
  | (string, _)::τ, l => l.var == string || tauInProp τ l

def Clause.eval : Clause → PropAssignment → Bool
  | [], _ => false
  | Lit.pos s::A, pa => ((tauInProp pa (Lit.pos s)) && pa.eval s) || eval A pa
  | Lit.neg s::A, pa => ((tauInProp pa (Lit.pos s)) && !(pa.eval s)) || eval A pa
  | Lit.tr::_, _ => true
  | Lit.fls::A, pa => eval A pa

-- Check if an individual literal is in the assignment

-- ** Fill in this definition. **
-- If a clause is not touched by assignment, proceed forward.
-- Else, if it is, it must evaluate to true
def isAutarky :  PropAssignment → CnfForm → Bool
  | _, [] => true
  | τ, x::xs => (( Clause.eval x τ) || !(propInClause τ x)) && isAutarky τ xs

def isinAssignment :  PropAssignment → CnfForm → List Clause
  | _, [] => []
  | τ, x::xs => if (propInClause τ x) then x::isinAssignment τ xs else isinAssignment τ xs

def isAssignmentTrue :  PropAssignment → CnfForm → List Clause
  | _, [] => []
  | τ, x::xs => if (Clause.eval x τ)  then x::isAssignmentTrue τ xs else isAssignmentTrue τ xs

#eval isinAssignment [] cnf!{p q r, -p -q -r}
#eval isinAssignment propassign!{p} cnf!{p q r, -p -q -r}
#eval isinAssignment propassign!{p} cnf!{p q r}
#eval isinAssignment propassign!{p} cnf!{-p q r}
#eval isinAssignment propassign!{p} cnf!{-p -q r}
#eval isinAssignment propassign!{p} cnf!{p q r, -q -r}
#eval isinAssignment propassign!{p, -q} cnf!{p q r, -p -q -r}
#eval isinAssignment propassign!{p, -q} cnf!{p q r, q, r, -r, r}
#eval isinAssignment propassign!{-q} cnf!{-p -q -r}

#eval isAssignmentTrue [] cnf!{p q r, -p -q -r}
#eval isAssignmentTrue propassign!{p} cnf!{p q r, -p -q -r}
#eval isAssignmentTrue propassign!{p} cnf!{p q r}
#eval isAssignmentTrue propassign!{p} cnf!{-p q r}
#eval isAssignmentTrue propassign!{p} cnf!{-p -q r}
#eval isAssignmentTrue propassign!{p} cnf!{p q r, -q -r}
#eval isAssignmentTrue propassign!{p, -q} cnf!{p q r, -p -q -r}
#eval isAssignmentTrue propassign!{p, -q} cnf!{p q r, q, r, -r, r}
#eval isAssignmentTrue propassign!{-q} cnf!{-p -q -r}


-- for testing
#eval isAutarky [] cnf!{p q r, -p -q -r} == true
#eval isAutarky propassign!{p} cnf!{p q r, -p -q -r} == false
#eval isAutarky propassign!{p} cnf!{p q r} == true
#eval isAutarky propassign!{p} cnf!{-p q r} == false
#eval isAutarky propassign!{p} cnf!{-p -q r} == false
#eval isAutarky propassign!{p} cnf!{p q r, -q -r} == true
#eval isAutarky propassign!{p, -q} cnf!{p q r, -p -q -r} == true
#eval isAutarky propassign!{-q} cnf!{-p -q -r} == true
#eval isAutarky propassign!{-q} [] == true
#eval isAutarky (propassign!{p, q, -u, -r}) (cnf!{p q u -v, -u, -r, ⊥, ⊤}) == true
#eval isAutarky (propassign!{p, -q, v}) (cnf!{p q u -v, -u, u, -v}) == false
#eval isAutarky (propassign!{p, -q, v}) (cnf!{p q u -v, -u, u, -v}) == false
#eval isAutarky (propassign!{p, -q, v, w, a, b, c, d}) (cnf!{p q u -v, -u, u}) == true


def listClauseLiterals : Clause → List Lit
  | [] => []
  | Lit.pos s::A => (Lit.pos s)::listClauseLiterals A
  | Lit.neg s::A => (Lit.neg s)::listClauseLiterals A
  | _::A => listClauseLiterals A

def listCNFLiterals : CnfForm → List Lit
  | [] => []
  | x::xs => listClauseLiterals x ++ listCNFLiterals xs

-- ** Fill in this definition. **
-- Return all pure literals. A pure literal is either always positive or always negative.
-- First go into the CnfForm and put every literal into a list
-- Then go through the list and check if the literal is in the list of pure literals
-- Put all literals (negative or postivie) into a list. THen apply n^2 algorithm to check if the literal is in the list of pure literals
def getPure (φ : CnfForm) : List Lit := Id.run do
  let allLiterals := listCNFLiterals φ
  let mut pureLiterals := allLiterals
  for l in allLiterals do
    for k in allLiterals do
      if l.var == k.var then
        match (l,k) with
          | (Lit.pos _, Lit.neg _) => pureLiterals := pureLiterals.filter (fun x => x.var != l.var)
          | (Lit.neg _, Lit.pos _) => pureLiterals := pureLiterals.filter (fun x => x.var != l.var)
          | _ => continue
  pureLiterals


-- Just maintain a list of
-- for testing
def eqSets [BEq α] (k l : List α) : Bool :=
  k.all l.contains &&
  l.all k.contains
infix:40 " eqSets " => eqSets

#eval getPure cnf!{} eqSets []
#eval getPure cnf!{p} eqSets [lit!{p}]
#eval getPure cnf!{-p} eqSets [lit!{-p}]
#eval getPure cnf!{-p, p} eqSets []
#eval getPure cnf!{p, q} eqSets [lit!{p}, lit!{q}]
#eval getPure cnf!{p, q, -p} eqSets [lit!{q}]
#eval getPure cnf!{p, -q, -p} eqSets [lit!{-q}]
#eval getPure cnf!{q p, -q p, p} eqSets [lit!{p}]

end PropAssignment

/-
Exercise 2.
-/

-- Part A) Write this function
def rectangleConstraints (m n k : Nat) : CnfForm :=
  []

/-
These should be satisfiable.
-/

#eval show IO Unit from do
  let (_, result) ← callCadical <| rectangleConstraints 10 10 3
  match result with
    | SatResult.Unsat _ => IO.println "unsat."
    | SatResult.Sat τ  => IO.println τ.toString

#eval show IO Unit from do
  let (_, result) ← callCadical <| rectangleConstraints 9 12 3
  match result with
    | SatResult.Unsat _ => IO.println "unsat."
    | SatResult.Sat τ  => IO.println τ.toString

/-
Decode the solutions.
-/

-- This may be helpful; it tests whether a literal is positive.
def Lit.isPos : Lit → Bool
  | pos s => true
  | _     => false

-- ** Write this part: interpret the positive literals as a rectangle. **
def decodeSolution (m n k: Nat) (τ : List Lit) : Except String (Array (Array Nat)) := do
  let mut s : Array (Array Nat) := mkArray m (mkArray n 0)
  -- use the literals to fill in the rectangle
  return s

def outputSolution (m n k : Nat) (τ : List Lit) : IO Unit :=
  let posLits := τ.filter Lit.isPos
  match decodeSolution m n k posLits with
    | Except.error s => IO.println s!"Error: {s}"
    | Except.ok rect =>
        for i in [:m] do
          for j in [:n] do
            IO.print s!"{rect[i]![j]!} "
          IO.println ""

-- Try it out.

#eval show IO Unit from do
  let (_, result) ← callCadical <| rectangleConstraints 10 10 3
  match result with
    | SatResult.Unsat _ => IO.println "unsat."
    | SatResult.Sat τ  => outputSolution 10 10 3 τ

#eval show IO Unit from do
  let (_, result) ← callCadical <| rectangleConstraints 9 12 3
  match result with
    | SatResult.Unsat _ => IO.println "unsat."
    | SatResult.Sat τ  => outputSolution 9 12 3 τ


/-
Exercise 3.
-/

namespace Resolution

/--
The resolution Step.
-/
def resolve (c₁ c₂ : Clause) (var : String) : Clause :=
  (c₁.erase (Lit.pos var)).union' (c₂.erase (Lit.neg var))

/--
A line of a resolution proof is either a hypothesis or the result of a
resolution step.
-/
inductive Step where
  | hyp (clause : Clause) : Step
  | res (var : String) (pos neg : Nat) : Step
deriving Inhabited

def Proof := Array Step deriving Inhabited

-- Ignore this: it is boilerplate to make `GetElem` work.
instance : GetElem Proof Nat Step (fun xs i => i < xs.size) :=
  inferInstanceAs (GetElem (Array Step) _ _ _)

-- determines whether a proof is well-formed
def Proof.wellFormed (p : Proof) : Bool := Id.run do
  for i in [:p.size] do
    match p[i]! with
      | Step.hyp _ => continue
      | Step.res _ pos neg =>
          if i ≤ pos ∨ i ≤ neg then
            return false
  true

-- prints out the proof
def Proof.show (p : Proof) : IO Unit := do
  if ¬ p.wellFormed then
    IO.println "Proof is not well-formed."
    return
  let mut clauses : Array Clause := #[]
  for i in [:p.size] do
    match p[i]! with
      | Step.hyp c =>
          clauses := clauses.push c
          IO.println s!"{i}: hypothesis: {c}"
      | Step.res var pos neg =>
          let resolvent := resolve clauses[pos]! clauses[neg]! var
          clauses := clauses.push resolvent
          IO.println s!"{i}: resolve {pos}, {neg} on {var}: {resolvent}"

end Resolution

section
open Resolution

def example1 : Proof := #[
  .hyp clause!{p q},
  .hyp clause!{-p},
  .hyp clause!{-q},
  .res "p" 0 1,
  .res "q" 3 2
]

#eval example1.wellFormed
#eval example1.show

def example2 : Proof := #[
  .hyp clause!{p q r},
  .hyp clause!{-p s},
  .hyp clause!{-q s},
  .hyp clause!{-r s},
  .hyp clause!{-s},
  .res "p" 0 1,
  .res "q" 5 2,
  .res "r" 6 3,
  .res "s" 7 4
]

#eval example2.wellFormed
#eval example2.show

-- ** Finish this to get a proof of ⊥.
def example3 : Proof := #[
  .hyp clause!{p q -r},
  .hyp clause!{-p -q r},
  .hyp clause!{q r -s},
  .hyp clause!{-q -r s},
  .hyp clause!{p r s},
  .hyp clause!{-p -r -s},
  .hyp clause!{-p q s},
  .hyp clause!{p -q -s}
]

#eval example3.wellFormed
#eval example3.show

end
