module

public import Veir.IR.Attribute

namespace Veir.Data.SMT

open Veir.SMT

public section

/--
  The operational semantics of SMT terms are defined to be a symbolic AST.
  Terms are not indexed by their sort; `Term.sort?` computes the sort of a well-sorted term.
-/
inductive Term where
| bvConst (w : Nat) (value : Nat)
| bvVar (w : Nat) (name : String)
| bvAdd (lhs rhs : Term)
| bvNeg (operand : Term)
| eq (lhs rhs : Term)
deriving DecidableEq

/--
  The sort of a term, or `none` if the term is ill-sorted, e.g. adds bit-vectors of different
  widths or contains a constant that does not fit its width.
-/
def Term.sort? : Term → Option SortType
  | .bvConst w value => if value < 2 ^ w then some (.bv w) else none
  | .bvVar w _ => some (.bv w)
  | .bvAdd lhs rhs =>
    match lhs.sort?, rhs.sort? with
    | some (.bv w), some (.bv w') => if w = w' then some (.bv w) else none
    | _, _ => none
  | .bvNeg operand =>
    match operand.sort? with
    | some (.bv w) => some (.bv w)
    | _ => none
  | .eq lhs rhs =>
    match lhs.sort?, rhs.sort? with
    | some s, some s' => if s = s' then some .bool else none
    | _, _ => none

/-- Print a term in SMT-LIB syntax. -/
def Term.toString : Term → String
  | .bvConst w value => s!"(_ bv{value} {w})"
  | .bvVar _ name => name
  | .bvAdd lhs rhs => s!"(bvadd {lhs.toString} {rhs.toString})"
  | .bvNeg operand => s!"(bvneg {operand.toString})"
  | .eq lhs rhs => s!"(= {lhs.toString} {rhs.toString})"

instance : ToString Term where
  toString := Term.toString

end

end Veir.Data.SMT
