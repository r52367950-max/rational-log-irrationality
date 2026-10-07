import Mathlib.RingTheory.LaurentSeries

/-!
# The Laurent-series obstruction in Lemma 3.1 of Theorem A

This file proves the actual formal Laurent-series coefficient statement used in
the final step of Lemma 3.1: the coefficient of `X⁻¹` in a formal derivative is
zero. It does not formalize the extension of derivations, field traces, or the
whole finitely generated field / Kähler differential argument.

The definitions below use mathlib's `LaurentSeries` and `derivative`, rather than
an axiomatized model or an assumed residue formula.
-/

namespace IrrationalityReview

open HahnSeries
open scoped LaurentSeries

variable {R V : Type*} [Semiring R] [AddCommGroup V] [Module R V]

/-- The residue of `f dX` is the coefficient of `X⁻¹` in `f`. -/
def residue (f : LaurentSeries V) : V := f.coeff (-1)

/-- Every formal derivative has zero residue. No characteristic hypothesis is
needed for this necessary condition. -/
theorem residue_derivative_zero (f : LaurentSeries V) :
    residue (LaurentSeries.derivative R f) = 0 := by
  simp [residue, LaurentSeries.derivative_apply]

/-- A Laurent series of nonzero residue has no Laurent-series antiderivative. -/
theorem derivative_ne_of_residue_ne_zero (f g : LaurentSeries V)
    (hg : residue g ≠ 0) : LaurentSeries.derivative R f ≠ g := by
  intro h
  apply hg
  rw [← h]
  exact residue_derivative_zero f

/-- In particular, a nonzero multiple of `X⁻¹` is not a formal derivative. -/
theorem derivative_ne_simple_pole (f : LaurentSeries V) (c : V) (hc : c ≠ 0) :
    LaurentSeries.derivative R f ≠ single (-1) c := by
  apply derivative_ne_of_residue_ne_zero
  simpa [residue] using hc

/-- Equivalent existential formulation, matching the contradiction in the
manuscript: there is no formal primitive of `c/X` when `c ≠ 0`. -/
theorem no_primitive_simple_pole (c : V) (hc : c ≠ 0) :
    ¬ ∃ f : LaurentSeries V,
      LaurentSeries.derivative R f = single (-1) c := by
  rintro ⟨f, hf⟩
  exact derivative_ne_simple_pole f c hc hf

section CharacteristicZero

variable {K : Type*} [Field K] [CharZero K]

/-- The coefficient notation `single (-1) c` is exactly the algebraic expression
`c/X` in the Laurent-series field. -/
theorem constant_div_X_eq_simple_pole (c : K) :
    (HahnSeries.C c : LaurentSeries K) / single 1 1 = single (-1) c := by
  rw [HahnSeries.C_apply, div_eq_mul_inv,
    ← RatFunc.single_inv (1 : ℤ) (one_ne_zero : (1 : K) ≠ 0),
    HahnSeries.single_mul_single]
  simp

/-- The contradiction remains valid when the nonzero residue is the positive
degree of a finite extension, as in the trace step of the manuscript. -/
theorem no_primitive_positive_degree (e : ℕ) (he : 0 < e) :
    ¬ ∃ f : LaurentSeries K,
      LaurentSeries.derivative K f = single (-1) (e : K) := by
  exact no_primitive_simple_pole (e : K) (Nat.cast_ne_zero.mpr (Nat.ne_of_gt he))

omit [CharZero K] in
/-- The logarithmic derivative of the actual Laurent monomial `a Xⁿ` is `n/X`. -/
theorem logarithmic_derivative_monomial (n : ℤ) (a : K) (ha : a ≠ 0) :
    LaurentSeries.derivative K (single n a) / single n a = single (-1) (n : K) := by
  rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_single,
    Ring.choose_one_right, zsmul_eq_mul, div_eq_mul_inv,
    ← RatFunc.single_inv n ha, HahnSeries.single_mul_single]
  simp [show n - 1 + -n = (-1 : ℤ) by omega, ha]

/-- Thus the logarithmic differential of a monomial of nonzero order cannot be
the differential of any Laurent series. -/
theorem derivative_ne_logarithmic_monomial (f : LaurentSeries K)
    (n : ℤ) (hn : n ≠ 0) (a : K) (ha : a ≠ 0) :
    LaurentSeries.derivative K f ≠
      LaurentSeries.derivative K (single n a) / single n a := by
  rw [logarithmic_derivative_monomial n a ha]
  exact derivative_ne_simple_pole f (n : K) (Int.cast_ne_zero.mpr hn)

/-- Formal integration with constant term chosen to be zero. This construction
does not integrate an `X⁻¹` term; division by zero gives coefficient zero there. -/
noncomputable def primitive (f : LaurentSeries K) : LaurentSeries K :=
  ofSuppBddBelow (fun n : ℤ => f.coeff (n - 1) / (n : K))
    (forallLTEqZero_supp_BddBelow _ (f.order + 1)
      (fun n hn => by
        rw [coeff_eq_zero_of_lt_order (show n - 1 < f.order by omega), zero_div]))

omit [CharZero K] in
@[simp] theorem primitive_coeff (f : LaurentSeries K) (n : ℤ) :
    (primitive f).coeff n = f.coeff (n - 1) / (n : K) := rfl

/-- In characteristic zero, zero residue is also sufficient for a formal
Laurent-series antiderivative. -/
theorem derivative_primitive (f : LaurentSeries K) (hf : residue f = 0) :
    LaurentSeries.derivative K (primitive f) = f := by
  ext n
  simp only [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff,
    Ring.choose_one_right, primitive_coeff, Nat.cast_one, add_sub_cancel_right, zsmul_eq_mul]
  by_cases hn : n + 1 = 0
  · have hn' : n = -1 := by omega
    simpa [hn, hn', residue] using hf.symm
  · have hcast : ((n + 1 : ℤ) : K) ≠ 0 := Int.cast_ne_zero.mpr hn
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hcast]

/-- Exact characterization of the image of the formal derivative. -/
theorem exists_primitive_iff_residue_zero (f : LaurentSeries K) :
    (∃ g : LaurentSeries K, LaurentSeries.derivative K g = f) ↔ residue f = 0 := by
  constructor
  · rintro ⟨g, rfl⟩
    exact residue_derivative_zero g
  · intro hf
    exact ⟨primitive f, derivative_primitive f hf⟩

omit [CharZero K] in
/-- Constants have derivative zero. -/
theorem derivative_constant_zero (a : K) :
    LaurentSeries.derivative K (HahnSeries.C a : LaurentSeries K) = 0 := by
  simp [HahnSeries.C_apply, LaurentSeries.derivative_apply]

/-- In characteristic zero the constant Laurent series are the entire kernel
of the formal derivative. -/
theorem eq_constant_of_derivative_zero (f : LaurentSeries K)
    (hf : LaurentSeries.derivative K f = 0) :
    f = HahnSeries.C (f.coeff 0) := by
  ext n
  by_cases hn : n = 0
  · simp [hn, HahnSeries.C_apply]
  · have hcoeff := congrArg (fun g : LaurentSeries K => g.coeff (n - 1)) hf
    have hmul : (n : K) * f.coeff n = 0 := by
      simpa [LaurentSeries.derivative_apply, Ring.choose_one_right, zsmul_eq_mul] using hcoeff
    have hz : f.coeff n = 0 :=
      (mul_eq_zero.mp hmul).resolve_left (Int.cast_ne_zero.mpr hn)
    simp [HahnSeries.C_apply, hn, hz]

/-- A second exact statement about the derivative: its kernel is precisely the
embedded coefficient field. -/
theorem derivative_zero_iff_constant (f : LaurentSeries K) :
    LaurentSeries.derivative K f = 0 ↔ ∃ a : K, f = HahnSeries.C a := by
  constructor
  · intro hf
    exact ⟨f.coeff 0, eq_constant_of_derivative_zero f hf⟩
  · rintro ⟨a, rfl⟩
    exact derivative_constant_zero a

end CharacteristicZero

end IrrationalityReview

-- Kernel dependency checks. The successful compile output should contain no
-- `sorryAx` and no project-specific axioms.
#print axioms IrrationalityReview.residue_derivative_zero
#print axioms IrrationalityReview.derivative_ne_of_residue_ne_zero
#print axioms IrrationalityReview.derivative_ne_simple_pole
#print axioms IrrationalityReview.no_primitive_simple_pole
#print axioms IrrationalityReview.constant_div_X_eq_simple_pole
#print axioms IrrationalityReview.no_primitive_positive_degree
#print axioms IrrationalityReview.logarithmic_derivative_monomial
#print axioms IrrationalityReview.derivative_ne_logarithmic_monomial
#print axioms IrrationalityReview.primitive_coeff
#print axioms IrrationalityReview.derivative_primitive
#print axioms IrrationalityReview.exists_primitive_iff_residue_zero
#print axioms IrrationalityReview.derivative_constant_zero
#print axioms IrrationalityReview.eq_constant_of_derivative_zero
#print axioms IrrationalityReview.derivative_zero_iff_constant
