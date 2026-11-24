module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic

meta import Veir.Meta.OpCode

open Veir.Data

namespace Veir

public section

@[opcodes]
inductive SMT where
| bv__add
| bv__neg
| eq
| not
| declare_fun
| assert
| check
| solver
| yield
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, implicit_reducible, properties_of]
def SMT.propertiesOf (op : SMT) : Type :=
match op with
| _ => Unit

def SMT.fromAttrDict
    (op : SMT) (_attrDict : Std.HashMap ByteArray Attribute) :
    Except String (SMT.propertiesOf op) := by
  cases op <;> exact .ok ()

def SMT.toAttrDict
    (_op : SMT) (_props : SMT.propertiesOf _op) :
    Std.HashMap ByteArray Attribute :=
  Std.HashMap.emptyWithCapacity 0

/-- Solver commands are not pure: they must neither be merged nor removed. -/
@[get_effects]
def SMT.getEffects
    (op : SMT) (_props : SMT.propertiesOf op) : MemoryEffects :=
  match op with
  | .declare_fun | .assert | .check | .solver => .unknown
  | .bv__add | .bv__neg | .eq | .not | .yield => .none

/-- SMT terms are symbolic, so poison never flows through an SMT operation. -/
def SMT.propagatesPoison (_op : SMT) : Bool :=
  false

def SMT.isConstantLike (_op : SMT) : Bool :=
  false

def SMT.hasSSADominance (_op : SMT) (_index : Nat) : Bool :=
  true

@[is_terminator]
def SMT.isTerminator (op : SMT) : Bool :=
  op = .yield

#generate_dialect SMT

instance : IsOpCode SMT where
  fromName := SMT.fromName
  name := SMT.name
  propertiesOf := SMT.propertiesOf
  fromAttrDict := SMT.fromAttrDict
  toAttrDict := SMT.toAttrDict

/-- The SMT sort named by a type attribute, if it is an SMT sort at all. -/
def TypeAttr.smtSort? (ty : TypeAttr) : Option SMT.SortType :=
  match ty.val with
  | .smtSortType sortType => some sortType
  | _ => none

/--
  Verify the local invariants of an `smt` operation in any operation-info type
  containing the `smt` dialect.

  `smt.bv.add` and `smt.bv.neg` preserve the sort of their operands, while
  `smt.eq` takes two terms of the same sort and produces an `!smt.bool`.
-/
@[expose]
def SMT.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo] [HasDialect OpInfo SMT]
    (opType : SMT) (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  match opType with
  | .bv__add => do
    op.verifyPlainOpCounts ctx opIn 2 1
    let lhsType := (op.getOperand! ctx.raw 0).getType! ctx.raw
    let rhsType := (op.getOperand! ctx.raw 1).getType! ctx.raw
    let some (.bv lhsWidth) := lhsType.smtSort?
      | throw s!"{instrName}: Expected operand 0 to have a bit-vector sort"
    let some (.bv rhsWidth) := rhsType.smtSort?
      | throw s!"{instrName}: Expected operand 1 to have a bit-vector sort"
    if lhsWidth ≠ rhsWidth then
      throw s!"{instrName}: Expected operands to have the same bit-vector width"
    op.verifyResultTypeMatches ctx lhsType
      s!"{instrName}: Expected result type to match operand type"
  | .bv__neg => do
    op.verifyPlainOpCounts ctx opIn 1 1
    let operandType := (op.getOperand! ctx.raw 0).getType! ctx.raw
    let some (.bv _) := operandType.smtSort?
      | throw s!"{instrName}: Expected operand 0 to have a bit-vector sort"
    op.verifyResultTypeMatches ctx operandType
      s!"{instrName}: Expected result type to match operand type"
  | .eq => do
    op.verifyPlainOpCounts ctx opIn 2 1
    let lhsType := (op.getOperand! ctx.raw 0).getType! ctx.raw
    let rhsType := (op.getOperand! ctx.raw 1).getType! ctx.raw
    if lhsType.smtSort?.isNone then
      throw s!"{instrName}: Expected operand 0 to have an SMT sort"
    if rhsType.smtSort?.isNone then
      throw s!"{instrName}: Expected operand 1 to have an SMT sort"
    let _ ← op.verifyOperandTypesMatch ctx 0 1
      s!"{instrName}: Expected operands to have the same sort"
    let expected : TypeAttr := TypeAttr.of SMT.SortType .bool
    op.verifyResultTypeMatches ctx expected
      s!"{instrName}: Expected result 0 to have type !smt.bool"
  /- Only Boolean free variables are supported so far. -/
  | .declare_fun => do
    op.verifyPlainOpCounts ctx opIn 0 1
    op.verifyResultTypeMatches ctx (TypeAttr.of SMT.SortType .bool)
      s!"{instrName}: Expected result 0 to have type !smt.bool"
  | .not | .assert | .check | .solver | .yield => pure ()

instance : HasOpInfo SMT where
  verifyLocalInvariants := SMT.verifyLocalInvariants
  getEffects := SMT.getEffects
  isConstantLike := SMT.isConstantLike
  propagatesPoison := SMT.propagatesPoison
  hasSSADominance := SMT.hasSSADominance
  isTerminator := SMT.isTerminator

end

end Veir
