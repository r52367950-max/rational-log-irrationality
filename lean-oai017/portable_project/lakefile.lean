import Lake
open Lake DSL
package OAI017ReviewDelivery where
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"
lean_lib OAI where
  roots := #[`OAI.NumberTheory.PiExponent.Statement]
  globs := #[`OAI.NumberTheory.PiExponent.+]
lean_lib SupportCore
@[default_target]
lean_lib OAI017Review where
  roots := #[`OAI017Review, `DistinctMultiplicativeRigidity, `DistinctMultiplicativePersistent, `DistinctMultiplicativeJets, `DistinctMultiplicativeAmple, `DistinctMultiplicativeFibre, `DistinctMultiplicativeStatement, `RationalLogAnalytic, `OAIApproximationAdapter, `OAIFormalLogAdapter, `DistinctMultiplicativeContact, `DistinctMultiplicativeGlobal, `DistinctMultiplicativeDegree, `DistinctMultiplicativeExistence, `RationalLogParameters, `RationalLogArithmeticAssembly, `RationalLogMatrixBridge, `RationalLogGeometryParameters, `RationalLogAsymptotic, `RationalLogMain, `Round2MainReference, `Round2MainTypeChecker, `AdapterAxiomAudit]
