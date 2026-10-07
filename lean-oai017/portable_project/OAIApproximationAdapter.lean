import OAI.NumberTheory.PiExponent.Approximation.Exponent

/-!
# Direct adapter to OAI017's original approximation endpoint

The import above is the original OAI017 module. In particular, `irrationalityExponent`
below always means `OAI.PiExponent.irrationalityExponent`, not the independent
extended-real definition from the first review project.

Original code reused:
* `OAI.PiExponent.EventualLowerBound` from `Statement.lean`;
* `OAI.PiExponent.eventualLowerBound_iff_integer`;
* `OAI.PiExponent.eventualLowerBound_of_not_unbounded_approximations`;
* `OAI.PiExponent.irrationalityExponent_eq_two_of_eventualLowerBound`.

This adapter supplies the additional irrationality argument for a generic real number,
then invokes OAI017's existing exponent theorem directly. The manuscript's geometric
interpolation and rational-base determinant estimates remain explicit hypotheses.
Nothing here proves those new hypotheses for logarithms.

OAI017's exponent is the real supremum of positive exponents admitting infinitely
many distinct reduced rational approximants, with strict inequality and nonzero error.
-/

set_option autoImplicit false

namespace RationalLogReview.OAIAdapter

open OAI.PiExponent

/-- Exact rational representations can have arbitrarily large unreduced denominators. -/
theorem rational_has_large_exact_representation (r : ℚ) (N : ℕ) :
    ∃ q : ℕ, N ≤ q ∧ 0 < q ∧ ∃ p : ℤ, (r : ℝ) = (p : ℝ) / (q : ℝ) := by
  let k : ℕ := N + 1
  have hk : 0 < k := Nat.zero_lt_succ N
  have hq : k ≤ r.den * k := by
    calc
      k = 1 * k := (one_mul k).symm
      _ ≤ r.den * k := Nat.mul_le_mul_right k r.pos
  refine ⟨r.den * k, (Nat.le_succ N).trans hq, Nat.mul_pos r.den_pos hk,
    r.num * (k : ℤ), ?_⟩
  rw [Int.cast_mul, Int.cast_natCast, Nat.cast_mul,
    mul_div_mul_right _ _ (by exact_mod_cast hk.ne')]
  exact Rat.cast_def r

/-- The ORIGINAL OAI eventual lower bound itself excludes rational x. OAI's generic
exponent theorem requests irrationality separately; this fills that interface. -/
theorem irrational_of_original_eventualLowerBound {x : ℝ}
    (hbound : OAI.PiExponent.EventualLowerBound x) : Irrational x := by
  rintro ⟨r, rfl⟩
  obtain ⟨Q, _, hQ⟩ := hbound 3 (by norm_num)
  obtain ⟨q, hqQ, hqpos, p, heq⟩ := rational_has_large_exact_representation r Q
  have herr := hQ p q hqQ
  rw [← heq, sub_self, abs_zero] at herr
  have hpos : 0 < (q : ℝ) ^ (-(3 : ℝ)) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hqpos) _
  exact (not_le_of_gt hpos) herr

/-- DIRECT reuse of the original OAI017 generic exponent theorem. There is no local
redefinition of irrationality exponent, good approximants, or the supremum argument. -/
theorem exponent_two_of_original_eventualLowerBound {x : ℝ}
    (hbound : OAI.PiExponent.EventualLowerBound x) :
    OAI.PiExponent.irrationalityExponent x = 2 := by
  exact OAI.PiExponent.irrationalityExponent_eq_two_of_eventualLowerBound
    (irrational_of_original_eventualLowerBound hbound) hbound

/-- The manuscript's strict lower bound with positive natural denominators. -/
def ManuscriptStrictBound (x : ℝ) : Prop :=
  ∀ ν : ℝ, 2 < ν → ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 0 < q →
    ∀ p : ℤ, (q : ℝ) ^ (-ν) < |x - (p : ℝ) / (q : ℝ)|

/-- Adapts the manuscript's strict bound to OAI017's original weak bound.
The enlarged threshold `max Q 2` supplies OAI's q ≥ 2 convention. -/
theorem original_eventualLowerBound_of_manuscript_strict {x : ℝ}
    (hbound : ManuscriptStrictBound x) : OAI.PiExponent.EventualLowerBound x := by
  intro ν hν
  obtain ⟨Q, hQ⟩ := hbound ν hν
  refine ⟨max Q 2, le_max_right _ _, ?_⟩
  intro p q hq
  exact (hQ q ((le_max_left Q 2).trans hq) (by omega) p).le

/-- The conditional rational-logarithm endpoint in OAI017's ORIGINAL exponent definition.
The unresolved manuscript input is explicitly the argument `hbound`. -/
theorem rational_logarithm_endpoint_from_manuscript_bound (r : ℚ)
    (hbound : ManuscriptStrictBound (Real.log (r : ℝ))) :
    Irrational (Real.log (r : ℝ)) ∧
      OAI.PiExponent.irrationalityExponent (Real.log (r : ℝ)) = 2 := by
  have hOAI := original_eventualLowerBound_of_manuscript_strict hbound
  exact ⟨irrational_of_original_eventualLowerBound hOAI,
    exponent_two_of_original_eventualLowerBound hOAI⟩

/-- The same endpoint from the ORIGINAL integer-denominator interface, using OAI017's
already-proved equivalence rather than another cast-conversion proof. -/
theorem rational_logarithm_endpoint_from_integer_bound (r : ℚ)
    (hbound : OAI.PiExponent.IntegerEventualLowerBound (Real.log (r : ℝ))) :
    OAI.PiExponent.irrationalityExponent (Real.log (r : ℝ)) = 2 := by
  exact exponent_two_of_original_eventualLowerBound
    ((OAI.PiExponent.eventualLowerBound_iff_integer (Real.log (r : ℝ))).mpr hbound)

/-- DIRECT reuse of OAI017's exclusion-of-unbounded-approximants theorem followed by
its original exponent endpoint. This is the exact contradiction interface of B. -/
theorem rational_logarithm_endpoint_from_no_unbounded_approximants (r : ℚ)
    (hbound : ∀ ν : ℝ, 2 < ν →
      ¬ ∀ Q : ℕ, ∃ (p : ℤ) (q : ℕ), Q ≤ q ∧
        |Real.log (r : ℝ) - (p : ℝ) / (q : ℝ)| ≤ (q : ℝ) ^ (-ν)) :
    OAI.PiExponent.irrationalityExponent (Real.log (r : ℝ)) = 2 := by
  exact exponent_two_of_original_eventualLowerBound
    (OAI.PiExponent.eventualLowerBound_of_not_unbounded_approximations hbound)

end RationalLogReview.OAIAdapter

/- Kernel dependency audit of the reused originals and the new adapters. -/
#print axioms OAI.PiExponent.eventualLowerBound_iff_integer
#print axioms OAI.PiExponent.two_mem_approximationExponents
#print axioms OAI.PiExponent.irrationalityExponent_eq_two_of_eventualLowerBound
#print axioms OAI.PiExponent.eventualLowerBound_of_not_unbounded_approximations
#print axioms RationalLogReview.OAIAdapter.rational_has_large_exact_representation
#print axioms RationalLogReview.OAIAdapter.irrational_of_original_eventualLowerBound
#print axioms RationalLogReview.OAIAdapter.exponent_two_of_original_eventualLowerBound
#print axioms RationalLogReview.OAIAdapter.original_eventualLowerBound_of_manuscript_strict
#print axioms RationalLogReview.OAIAdapter.rational_logarithm_endpoint_from_manuscript_bound
#print axioms RationalLogReview.OAIAdapter.rational_logarithm_endpoint_from_integer_bound
#print axioms RationalLogReview.OAIAdapter.rational_logarithm_endpoint_from_no_unbounded_approximants
