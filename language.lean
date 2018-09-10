
structure Language := 
    language :: (relations : Type) (functions : Type ) (arityF :  functions →  nat) (arityR : relations → nat)

variable L : Language
universe u
inductive vector (α : Type) : nat → Type
| nil {} : vector 0
| cons   : Π {n}, α → vector n → vector (n+1)

inductive  term : Type
    | var : nat → term
    | apply: ∀ (f : L.functions ), (vector term (L.arityF f)) → term


inductive formula : Type 
    | equal : term L → term L → formula
    | atomic : ∀ r : L.relations, vector (term L) (L.arityR r) → formula
    | imp : formula → formula → formula
    | not : formula → formula → formula
    | forallF : nat → formula → formula

mutual def freeVars, freeVarsVec 
with freeVars : (term L) → list nat 
    | (term.var L n) := [n]
    | (term.apply f v) := freeVarsVec v
with freeVarsVec : Π {n}, vector (term L) n → list nat
    | 0 nil := []
    | (n+1) (vector.cons t v') := freeVars t ++ freeVarsVec v'



definition freeVarsFormula : formula L → list int := sorry


definition substitute : nat → formula L → formula L → formula L := sorry
    




