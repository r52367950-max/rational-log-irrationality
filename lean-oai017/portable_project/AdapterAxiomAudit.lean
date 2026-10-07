import DistinctMultiplicativeRigidity
import DistinctMultiplicativePersistent
import DistinctMultiplicativeJets
import DistinctMultiplicativeAmple
import DistinctMultiplicativeFibre
import DistinctMultiplicativeStatement
import RationalLogAnalytic
import OAIApproximationAdapter
import OAIFormalLogAdapter
import DistinctMultiplicativeContact
import DistinctMultiplicativeGlobal
import DistinctMultiplicativeDegree
import DistinctMultiplicativeExistence
import RationalLogParameters
import RationalLogArithmeticAssembly
import RationalLogMatrixBridge
import RationalLogGeometryParameters
import RationalLogAsymptotic
import RationalLogMain
import Lean.Util.CollectAxioms

/-! Enumerates every theorem in the new adapter namespaces and rejects any
transitive axiom outside Lean/mathlib's usual three foundational axioms. -/
set_option maxHeartbeats 0
run_cmd do
  let prefixes := #[
    "OAI.PiExponent.DistinctMultiplicative.",
    "OAI.PiExponent.DistinctMultiplicativeAmple.",
    "RationalLogOAI017.",
    "RationalLogReview.",
    "IrrationalityReview.RationalLogMatrixBridge.",
    "IrrationalityReview.RationalLogArithmeticAssembly.",
    "IrrationalityReview.OAIFormalLogAdapter."]
  let privateModules := #["_private.DistinctMultiplicativeContact.", "_private.DistinctMultiplicativeGlobal.", "_private.DistinctMultiplicativeDegree.", "_private.DistinctMultiplicativeExistence.", "_private.RationalLogParameters.", "_private.RationalLogArithmeticAssembly.", "_private.RationalLogMatrixBridge.", "_private.RationalLogGeometryParameters.", "_private.RationalLogAsymptotic.", "_private.RationalLogMain.", "_private.DistinctMultiplicativeRigidity.", "_private.DistinctMultiplicativeJets.", "_private.DistinctMultiplicativePersistent.", "_private.DistinctMultiplicativeAmple.", "_private.DistinctMultiplicativeFibre.", "_private.RationalLogAnalytic.", "_private.OAIFormalLogAdapter.", "_private.OAIApproximationAdapter."]
  let permitted := #[`propext, `Classical.choice, `Quot.sound]
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if info.isTheorem && (prefixes.any (fun p => name.toString.startsWith p) || privateModules.any (fun p => name.toString.startsWith p)) then
      let axioms ← Lean.collectAxioms name
      unless axioms.all (fun a => permitted.contains a) do
        Lean.throwError "unpermitted axioms in {name}: {axioms}"
      Lean.logInfo m!"ADAPTER_AXIOMS {name} {axioms}"
      count := count + 1
  Lean.logInfo m!"ADAPTER_THEOREM_COUNT {count}"
