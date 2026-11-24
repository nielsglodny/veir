module

public import Veir.Interpreter.CTree
public import Veir.Dialects.SMT.Oracle

public section

open CTree Std.Tactic.BVDecide

namespace Veir

/--
Interpret an `smt` operation on concrete values: a value of sort `!smt.bool` is a `Bool`.

The solver commands (`smt.declare_fun`, `smt.assert`, `smt.check`) only have a meaning in the body
of an `smt.solver`, which interprets them itself (`SMT.interpretSolver`).
-/
def SMT.interpretOpCTree {EIn : Type} {E : EIn → Type} [ErrorE -< E]
    (opType : SMT) (operands : Array RuntimeValue) (mem : MemoryState) :
    CTree E FreezeC (Array RuntimeValue × MemoryState × Option ControlFlowAction) :=
  match opType, operands.toList with
  | .not, [.smtBool x] => return (#[.smtBool !x], mem, none)
  | .eq, [.smtBool x, .smtBool y] => return (#[.smtBool (x == y)], mem, none)
  | .yield, _ => return (#[], mem, some (.return operands))
  | _, _ => fail

namespace SMT

/-!
# Semantics of `smt.solver`

The answer of `smt.check` depends on all values the free variables may take, so a solver body is
not run on values. Instead, it is run on formulas: `smt.declare_fun` is a fresh variable,
`smt.not` and `smt.eq` build formulas, and `smt.assert` adds its formula to the assertions. A check
decides the assertions so far (`satSolver`) and runs the region of its outcome.´

A body may only contain smt operations.
-/

abbrev SolverValue := RuntimeValue ⊕ BVLogicalExpr

structure SolverState where
  values : Std.HashMap ValuePtr SolverValue := {}
  numVars : Nat := 0
  assertions : BVLogicalExpr := .const true
  memory : MemoryState

variable {ctx : WfIRContext OpCode}

def SolverState.setResults (state : SolverState) (op : OperationPtr)
    (results : Array SolverValue) : SolverState :=
  { state with values := results.zipIdx.foldl (init := state.values) fun values (result, i) =>
      values.insert (.opResult (op.getResult i)) result }

/-- Interpret the operation `op` of a solver body: continue with the next operation, or return
the values that the body yields. -/
def interpretSolverOp (op : OperationPtr) (state : SolverState) :
    RegionTree ctx MemoryState ((OperationPtr × SolverState) ⊕ (Array RuntimeValue × MemoryState)) := do
  let some operands := (op.getOperands! ctx.raw).mapM (state.values[·]?) | fail
  let next (state : SolverState) : RegionTree ctx MemoryState _ := do
    let some nextOp := op.getNextOp! ctx.raw | fail
    return .inl (nextOp, state)
  match op.getOpType! ctx.raw, operands with
  | .smt .declare_fun, #[] =>
    let var := .literal (.getLsbD (.var state.numVars : BVExpr 1) 0)
    next ({ state with numVars := state.numVars + 1 }.setResults op #[.inr var])
  | .smt .not, #[.inr φ] => next (state.setResults op #[.inr (.not φ)])
  | .smt .eq, #[.inr φ, .inr ψ] => next (state.setResults op #[.inr (.gate .beq φ ψ)])
  | .smt .assert, #[.inr φ] => next { state with assertions := .gate .and state.assertions φ }
  | .smt .check, #[] =>
    let giveUp : FreezeC (.mk 1) ← CTree.choose (FreezeCIn.mk 1)
    /- The regions are for `sat`, `unknown`, and `unsat`. A proof of unsatisfiability is checked. -/
    let region := op.getRegion! ctx.raw <| if giveUp = 1 then 1 else
      match satSolver state.assertions with
      | some (.error _) => 0
      | some (.ok proof) => if Reflect.verifyBVExpr state.assertions proof then 2 else 1
      | none => 1
    if h : region.InBounds ctx.raw then
      let (memory, results) ← runRegion region #[] state.memory h
      next ({ state with memory }.setResults op (results.map .inl))
    else
      fail
  | .smt .yield, _ =>
    let some results := operands.mapM (·.getLeft?) | fail
    return .inr (results, state.memory)
  | _, _ => fail

def interpretSolver (regions : Array RegionPtr) (memory : MemoryState) :
    RegionTree ctx MemoryState (Array RuntimeValue × MemoryState × Option ControlFlowAction) := do
  let #[body] := regions | fail
  let some firstOp := (body.getFirstBlock! ctx.raw).bind (·.getFirstOp! ctx.raw) | fail
  let (results, memory) ← CTree.iter (fun (op, state) => interpretSolverOp op state)
    (firstOp, ({ memory } : SolverState))
  return (results, memory, none)

end SMT

end Veir
