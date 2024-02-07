import LAMR.Util.Propositional

/-
The first midterm exam is a week from Monday. We'll say more
about it on Monday.

Assignment 3 has been graded.

(Jeremy won't be here b/c of the Jewish Holidays.)

Recap:
- CNF, DNF, and NNF
- Equivalence and equisatisfiability
- Implementing propositional logic in Lean.
-/

/-
# Implementing the syntax of Propositional Logic

The textbook definitions are here:
https://avigad.github.io/lamr/propositional_logic.html#syntax
-/

namespace hidden

inductive PropForm
| var : String → PropForm
| tr  : PropForm
| fls : PropForm
| neg : PropForm → PropForm
| conj : PropForm → PropForm → PropForm
| disj : PropForm → PropForm → PropForm
| impl : PropForm → PropForm → PropForm
| biImpl : PropForm → PropForm → PropForm
deriving Repr, DecidableEq, Inhabited

end hidden

#print PropForm

#check PropForm.tr
#check PropForm.var "x"
#check PropForm.conj PropForm.tr (PropForm.var "x")

open PropForm

#check conj tr (var "x")
#check (impl (conj (var "p") (var "q")) (var "r"))

#check prop!{p ∧ q → (r ∨ ¬ p) → q}
#check prop!{p ∧ q ∧ r → p}
#check prop!{p ∧ q → r}

def propExample := prop!{p ∧ q → r ∧ p ∨ ¬ s1 → s2 }

#print propExample
#eval propExample

#eval toString propExample

/-
Some examples of structural recursion.
-/

namespace PropForm

def complexity : PropForm → Nat
  | var _      => 0
  | tr         => 0
  | fls        => 0
  | neg A      => complexity A + 1
  | conj A B   => complexity A + complexity B + 1
  | disj A B   => complexity A + complexity B + 1
  | impl A B   => complexity A + complexity B + 1
  | biImpl A B => complexity A + complexity B + 1

def depth : PropForm → Nat
  | var _      => 0
  | tr         => 0
  | fls        => 0
  | neg A      => depth A + 1
  | conj A B   => max (depth A) (depth B) + 1
  | disj A B   => max (depth A) (depth B) + 1
  | impl A B   => max (depth A) (depth B) + 1
  | biImpl A B => max (depth A) (depth B) + 1

#eval depth prop!{(p ∨ q) ∧ (r ∨ ¬ s)}
#eval complexity prop!{(p ∨ q) ∧ (r ∨ ¬ s)}

def vars : PropForm → List String
  | var s      => [s]
  | tr         => []
  | fls        => []
  | neg A      => vars A
  | conj A B   => (vars A).union' (vars B)
  | disj A B   => (vars A).union' (vars B)
  | impl A B   => (vars A).union' (vars B)
  | biImpl A B => (vars A).union' (vars B)

#eval vars prop!{(p ∨ q) ∧ (p ∨ ¬ s)}

-- def propExample := prop!{p ∧ q → r ∧ p ∨ ¬ s1 → s2 }

#eval complexity propExample
#eval depth propExample
#eval vars propExample

end PropForm

#eval PropForm.complexity propExample
#eval propExample.complexity

#check PropAssignment
#check PropAssignment.eval

#eval propassign!{p, - q , r}.eval? "s"

def PropForm.eval (τ : PropAssignment) : PropForm → Bool
  | var s      => τ.eval s
  | tr         => true
  | fls        => false
  | neg A      => !eval τ A
  | conj A B   => eval τ A && eval τ B
  | disj A B   => eval τ A || eval τ B
  | impl A B   => !eval τ A || eval τ B
  | biImpl A B => eval τ A == eval τ B

-- def propExample := prop!{p ∧ q → r ∧ p ∨ ¬ s1 → s2 }

#eval let τ := PropAssignment.mk [("p", true), ("q", true), ("r", true)]
      propExample.eval τ

#eval let τ := PropAssignment.mk [("p", true), ("q", true), ("r", true)]
      prop!{p ∨ ¬ q}.eval τ

#check propassign!{p, - q, r}

#eval propExample.eval propassign!{p, q, r}

def allSublists : List α → List (List α)
  | [] => [[]]
  | a :: as =>
      let recval := allSublists as
      recval.map (a :: .) ++ recval

#eval allSublists [1, 2, 3]

-- def propExample := prop!{p ∧ q → r ∧ p ∨ ¬ s1 → s2 }

#eval allSublists propExample.vars

def List.toPropAssignment : List String → PropAssignment :=
fun l => PropAssignment.mk (l.map (., true))

#eval ["x", "y", "z"].toPropAssignment

def truthTable (A : PropForm) : List (List Bool × Bool) :=
  let vars := A.vars
  let assignments := (allSublists vars).map List.toPropAssignment
  let evalLine := fun v : PropAssignment => (vars.map v.eval, A.eval v)
  assignments.map evalLine

#eval truthTable propExample

#eval truthTable prop!{p ∧ q}

def PropForm.isValid (A : PropForm) : Bool :=
(truthTable A).all Prod.snd

def PropForm.isSat(A : PropForm) : Bool :=
(truthTable A).any Prod.snd

#eval propExample.isValid
#eval propExample.isSat
