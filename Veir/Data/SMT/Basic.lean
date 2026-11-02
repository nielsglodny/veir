module

import Veir.ForLean

namespace Veir.SMT

public section

/--
  The `!smt.bool` sort, the type of Boolean SMT terms.
-/
structure BoolType where
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  The `!smt.bv<width>` sort, the type of bit-vector SMT terms of a given width.
-/
structure BvType where
  /-- The bit-vector width. -/
  width : Nat
deriving Inhabited, Repr, DecidableEq, Hashable

/--
  An SMT sort is either the Boolean sort or a bit-vector sort. Sorts are the
  types of the SMT dialect; they mirror MLIR's `!smt.bool` and `!smt.bv<width>`.
-/
abbrev SortType := BoolType ⊕ BvType

/-- The `!smt.bool` sort. -/
abbrev boolSort : SortType := .inl ⟨⟩

/-- The `!smt.bv<width>` sort. -/
abbrev bvSort (width : Nat) : SortType := .inr ⟨width⟩

/-- The width of a bit-vector sort, if this sort is one. -/
def SortType.bvWidth? : SortType → Option Nat
  | .inl _ => none
  | .inr bv => some bv.width

instance : Inhabited SortType where
  default := .inl default

instance : ToString SortType where
  toString
    | .inl _ => "!smt.bool"
    | .inr bv => s!"!smt.bv<{bv.width}>"

instance : Hashable SortType where
  hash
    | .inl boolTy => mixHash 0 (hash boolTy)
    | .inr bvTy => mixHash 1 (hash bvTy)

end

end Veir.SMT

namespace Veir.Data.SMT

open Veir.SMT

public section

/--
  The operational semantics of SMT terms are defined to be a symbolic AST.
-/
inductive Term : SortType → Type where
| bvConst {w : Nat} (value : BitVec w) : Term (.inr ⟨w⟩)
| bvVar {w : Nat} (name : String) : Term (.inr ⟨w⟩)
| bvAdd {w : Nat} (lhs rhs : Term (.inr ⟨w⟩)) : Term (.inr ⟨w⟩)
| bvNeg {w : Nat} (operand : Term (.inr ⟨w⟩)) : Term (.inr ⟨w⟩)
/-- `s` cannot be implicit, since it can't be inferred from the Boolean sort. -/
| eq (s : SortType) (lhs rhs : Term s) : Term (.inl ⟨⟩)
deriving Repr, BEq, Hashable, DecidableEq

instance : Inhabited (Term s) where
  default := match s with
    | .inl ⟨⟩ => .eq (bvSort 0) (.bvConst 0) (.bvConst 0)
    | .inr _ => .bvConst default

/-- Print a term in SMT-LIB syntax. -/
def Term.toString : (s : SortType) → Term s → String
  | .inr ⟨w⟩, .bvConst value => s!"(_ bv{value.toNat} {w})"
  | _, .bvVar name => name
  | _, .bvAdd lhs rhs => s!"(bvadd {Term.toString _ lhs} {Term.toString _ rhs})"
  | _, .bvNeg operand => s!"(bvneg {Term.toString _ operand})"
  | .inl _, .eq _ lhs rhs => s!"(= {Term.toString _ lhs} {Term.toString _ rhs})"

instance : ToString (Term s) where
  toString := Term.toString s

end

end Veir.Data.SMT
