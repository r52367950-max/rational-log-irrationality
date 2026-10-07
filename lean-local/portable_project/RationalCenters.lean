import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic

/-! The actual geometric centers in B: distinct nonzero powers of a positive
rational base different from one. No interpolation hypothesis is used. -/
namespace RationalLogReview

theorem rational_power_centers_injective (r : ℚ) (hr : 0 < r) (hne : r ≠ 1) :
    Function.Injective (fun j : ℕ => r ^ j) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (pow_right_strictAnti₀ hr hlt).injective
  · exact (pow_right_strictMono₀ hgt).injective

theorem rational_power_centers_nonzero (r : ℚ) (hr : 0 < r) (j : ℕ) :
    r ^ j ≠ 0 := pow_ne_zero j (ne_of_gt hr)

theorem finite_rational_power_centers (r : ℚ) (hr : 0 < r) (hne : r ≠ 1) (K : ℕ) :
    Function.Injective (fun j : Fin K => r ^ (j : ℕ)) ∧
      (∀ j : Fin K, r ^ (j : ℕ) ≠ 0) := by
  refine ⟨?_, fun j => rational_power_centers_nonzero r hr j⟩
  intro i j hij
  exact Fin.ext (rational_power_centers_injective r hr hne hij)

#print axioms rational_power_centers_injective
#print axioms rational_power_centers_nonzero
#print axioms finite_rational_power_centers

end RationalLogReview
