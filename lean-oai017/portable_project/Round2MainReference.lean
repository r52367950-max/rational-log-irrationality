import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Independent statement of manuscript B's strict rational-logarithm bound.

This file imports no solution module and contains no asserted proof of the
target. It only defines the intended proposition using stock mathlib objects.
-/

set_option autoImplicit false

namespace RationalLogReview.MainReference

/-- Every positive rational base other than one has a strict eventual bound
for every exponent above two, for all integer numerators and positive natural
denominators. There is no geometric/interpolation assumption in this type. -/
def StrictRationalLogMain : Prop :=
  ∀ r : ℚ, 0 < r → r ≠ 1 →
    ∀ ν : ℝ, 2 < ν → ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 0 < q →
      ∀ p : ℤ, (q : ℝ) ^ (-ν) <
        |Real.log (r : ℝ) - (p : ℝ) / (q : ℝ)|

end RationalLogReview.MainReference

#print axioms RationalLogReview.MainReference.StrictRationalLogMain
