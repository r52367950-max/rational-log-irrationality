import Lake
open Lake DSL
package RationalLogReviewDelivery
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"
@[default_target]
lean_lib RationalLogReview where
  roots := #[`RationalLogReview, `ParameterContradiction, `IntegerDeterminant, `Collision, `ApproximationBridge, `LaurentResidue, `GeometryNumerics, `RationalCenters, `AxiomAudit]
