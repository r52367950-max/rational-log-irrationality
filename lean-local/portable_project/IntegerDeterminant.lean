import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Integer determinant arithmetic lemma

This verifies the elementary lower-bound mechanism, not the manuscript's
specific entry-clearing construction. Entry-clearing must separately furnish
an integer matrix and prove its nonzero determinant.
-/
namespace RationalLogReview

/-- A nonzero integer has real absolute value at least one. -/
theorem nonzero_integer_abs_ge_one (z : ℤ) (hz : z ≠ 0) :
    (1 : ℝ) ≤ |(z : ℝ)| := by
  have hpos : (0 : ℤ) < |z| := abs_pos.mpr hz
  have hge : (1 : ℤ) ≤ |z| := hpos
  exact_mod_cast hge

/-- The arithmetic premise of B: a nonzero integral determinant has
absolute value at least one, including after embedding into the reals. -/
theorem integer_matrix_det_abs_ge_one
    {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℤ) (hB : B.det ≠ 0) :
    (1 : ℝ) ≤ |(B.map (fun z : ℤ => (z : ℝ))).det| := by
  rw [← Int.cast_det]
  exact nonzero_integer_abs_ge_one B.det hB

/-- If clearing a determinant multiplies it by a positive factor, the
reciprocal factor is an exact lower bound. -/
theorem cleared_integer_lower_bound
    (z : ℤ) (hz : z ≠ 0) (factor x : ℝ) (hfactor : 0 < factor)
    (hclear : (z : ℝ) = factor * x) :
    1 / factor ≤ |x| := by
  have h := nonzero_integer_abs_ge_one z hz
  rw [hclear, abs_mul, abs_of_pos hfactor] at h
  apply (div_le_iff₀ hfactor).mpr
  nlinarith

#print axioms nonzero_integer_abs_ge_one
#print axioms integer_matrix_det_abs_ge_one
#print axioms cleared_integer_lower_bound
end RationalLogReview
