

structure Language := 
    language :: (relations : Type) (functions : Type ) (arityF :  functions →  nat) (arityR : relations → nat)

variable L : Language
universe u
inductive term : Type
    | var: nat → term
    | apply: ∀ (f : L.functions) (l : list term), term
 
def union : (list nat) → (list nat) → (list nat)
    | [] l := l
    | (list.cons a as) l := if a ∈ l then [a] ++ union as l else union as l
def remove : nat → list nat → list nat
    | _ [] := []
    | n (list.cons m ns) := if n = m then remove n ns else list.cons m (remove n ns)
mutual def well_formed_term, well_formed_term_list 
with well_formed_term : term L -> Prop
    | (term.var L _) := true
    | (term.apply f l) := ((L.arityF f) = list.length l) ∧ (well_formed_term_list l)
with well_formed_term_list : list (term L) → Prop
    | [] := true
    | (list.cons t ts) := (well_formed_term t) ∧ well_formed_term_list ts

inductive formula : Type 
    | equal : term L → term L → formula
    | atomic : ∀ r : L.relations, list (term L) → formula
    | imp : formula → formula → formula
    | not : formula → formula → formula
    | forallF : nat → formula → formula

def free_vars_term: (term L) → list nat 
    | (term.var L n) := [n]
    | (term.apply f []) := []
    | (term.apply f (t::ts)) := free_vars_term t ++ free_vars_term (term.apply f ts)

definition free_vars_formula : formula L → list nat 
    | (formula.equal t t' ) := union (free_vars_term L t) (free_vars_term L t')
    | (formula.atomic r []) := []
    | (formula.atomic r (list.cons t ts)) := union (free_vars_term L t) (free_vars_formula (formula.atomic r ts))
    | (formula.imp f f') := union (free_vars_formula f) (free_vars_formula f')
    | (formula.not f f') := union (free_vars_formula f) (free_vars_formula f')
    | (formula.forallF n f) := remove n (free_vars_formula f)

definition substitute : nat → formula L → formula L → formula L :=     




