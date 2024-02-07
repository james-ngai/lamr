import LAMR

/-
exercise 5
-/

-- you can test whether two strings are equal
#eval if "p" = "q" then "yes" else "no"

namespace PropForm

-- Just define base cases of assinging, then apply propForm and backpropogate up

-- Replace this with the real definition.
def substitute : PropForm → PropForm → String → PropForm
  | tr, _, _ => tr
  | fls, _, _ => fls
  | var str1, A, str2 => if str1 = str2 then A else var str1
  | neg A, B, str => neg (substitute A B str)
  | conj A B, C, str => conj (substitute A C str) (substitute B C str)
  | disj A B, C, str => disj (substitute A C str) (substitute B C str)
  | impl A B, C, str => impl (substitute A C str) (substitute B C str)
  | biImpl A B, C, str => biImpl (substitute A C str) (substitute B C str)

end PropForm

-- Putting the definition in the `PropForm` namespace means you can use the
-- "anonymous projection" notation below.

#eval toString <| prop!{p ∧ (q ∨ r)}.substitute prop!{r ∨ ¬ s} "q"
#eval toString <| prop!{p ∧ (q ∨ r)}.substitute prop!{r ∨ ¬ s} "p"
#eval toString <| prop!{p ∧ (q ∨ r)}.substitute prop!{r ∨ ¬ s} "t"


/-
exercise 6
-/

-- Surely just apply some recursion and then bam. There's some recursive rules to get this done
-- So remove all negations???
-- So the only unique thing about this problem is that it's a list. So it's actually trivial, just change of forms.
-- On the right-hand side, Lean determines that `.tr` is `PropForm.tr`
-- because it is expecting a `PropForm` there.

def Clause.toPropForm : Clause → PropForm
  | [] => .fls
  | Lit.tr::[] => .tr
  | Lit.fls::[] => .fls
  | Lit.pos s::[] => .var s
  | Lit.neg s::[] => .neg (.var s)
  | Lit.tr::A => .disj .tr (toPropForm A)
  | Lit.fls::A => .disj .fls (toPropForm A)
  | Lit.pos s::A => .disj (.var s) (toPropForm A)
  | Lit.neg s::A => .disj (.neg (.var s)) (toPropForm A)

def CnfForm.toPropForm : CnfForm → PropForm
  | [] => .fls
  | A::[] => A.toPropForm
  | A :: rest => PropForm.conj (A.toPropForm) (toPropForm rest)

#eval toString cnf!{p q r, r -s t, q t}.toPropForm
#eval toString cnf!{t u v, w x y d e f, f}.toPropForm


-- def cnfForm.toPropForm (F : CnfForm) : PropForm
--   | [] => PropForm.fls
--   | [[]] => PropForm.tr
--   | [[pos str]] => PropForm.var str
--   | [[neg str]] => PropForm.neg (var str)
--   | A :: B => A.toPropForm ∨ B.toPropForm

/-
exercise 7
-/

-- Remember the notation for propositional assignments.
#eval propassign!{p, q, -r}.eval "r"

-- Here are some operations on Booleans.
#eval true && false
#eval true || false
#eval !true

-- You will have to define auxiliary functions, like evaluation
-- for literals and clauses.

-- Rather than open the namespace explicitly, you can put the
-- function in the `CnfForm` namespace like this.
-- In the recursive call, refer to the function as just `eval`.

-- Replace this with the real definition.
def CnfForm.eval : CnfForm → PropAssignment → Bool
  | _, _      => true

#eval cnf!{p q r, r -s t, q t}.eval propassign!{-p, -q, -r, s, -t}


/-
exercise 8
-/

#check NnfForm
#check PropForm.toNnfForm

-- Replace this with the real definition.
inductive EnnfForm :=
  sorry

namespace EnnfForm

-- Replace this with the real definition.
def toPropForm : EnnfForm → PropForm
  | _ => sorry

end EnnfForm

namespace PropForm

-- Replace this with the real definition.
def toEnnfForm : PropForm → EnnfForm
  | _ => sorry

end PropForm

-- #eval prop!{¬ ((p ↔ q ↔ r) ∨ s ↔ t)}.toEnnfForm
-- #eval toString <| prop!{¬ ((p ↔ q ↔ r) ∨ s ↔ t)}.toEnnfForm.toPropForm
