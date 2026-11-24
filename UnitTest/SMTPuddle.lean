module

import Veir.PatternRewriter.Puddle.CTreeValidityTactics
import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.SMT.Interpreter
import all Veir.Dialects.SMT.OpInfo
import all Veir.GlobalOpInfo

/-! A rewrite of SMT terms, proved correct on their concrete semantics. -/

namespace SMTPuddleTest

open Veir Veir.Puddle

/-- `smt.not (smt.not x) → x` -/
private def notNot : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := TypeAttr)
      let x ← MatchProg.value ty
      let inner ← MatchProg.operation (.smt .not) #[x] #[ty]
      let _ ← MatchProg.root (.smt .not) #[inner.res[0]!] #[ty]
      return x)
    pure (fun x => x)

attribute [local puddle] Veir.CTree.interpretOp' CTree.CanInterpretTo SMT.interpretOpCTree

theorem notNot_valid : CTree.Pattern.Valid notNot := by
  unfold notNot
  simpPuddleValid
  simp [puddle]
  intro _ value
  cases value <;> simp_all

end SMTPuddleTest
