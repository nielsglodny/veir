module

public import Std.Tactic.BVDecide
public import Lean.Meta.Tactic.BVDecide.LRAT.Cert
import Lean.Meta.Tactic.BVDecide.TacticContext

public section

open Lean Elab Meta.Tactic.BVDecide Std.Tactic.BVDecide Std.Sat

namespace Veir.SMT

/-- An answer of `bv_decide`'s SAT solver: a model (`.error`), or an LRAT proof of
unsatisfiability (`.ok`). -/
abbrev SatAnswer := Except (Array (Bool × Nat)) LratCert

/-- Run `bv_decide`'s SAT solver on `φ`, as `bv_decide` does. -/
def runSatSolver (φ : BVLogicalExpr) : IO SatAnswer :=
  IO.FS.withTempFile fun _ lratPath => do
    let run : TermElabM _ := do
      let ctx ← TacticContext.new lratPath {}
      runExternal (AIG.toCNF φ.bitblast.relabelNat) ctx.solver ctx.lratPath ctx.config.trimProofs
        ctx.config.timeout ctx.config.binaryProofs ctx.config.solverMode
    (run.run' { declName? := `Veir.SMT.runSatSolver }).run'.toIO' { fileName := "", fileMap := default }
      { env := ← mkEmptyEnvironment }

/- The interpreter evaluates the same check many times, as it unfolds the tree of the program. -/
private initialize answers : IO.Ref (Std.HashMap String (Option SatAnswer)) ← IO.mkRef {}

private unsafe def satSolverImpl (φ : BVLogicalExpr) : Option SatAnswer :=
  unsafeBaseIO do
    let key := toString φ
    if let some answer := (← answers.get)[key]? then
      return answer
    let answer := (← (runSatSolver φ).toBaseIO).toOption
    answers.modify (·.insert key answer)
    return answer

/-- The answer of `bv_decide`'s SAT solver, or `none` if it fails. In the logic, this is an
arbitrary function. -/
@[implemented_by satSolverImpl]
opaque satSolver (φ : BVLogicalExpr) : Option SatAnswer

end Veir.SMT
