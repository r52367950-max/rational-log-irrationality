import OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction
import OAI.NumberTheory.PiExponent.Approximation.GenericNormalRigidity
import OAI.NumberTheory.PiExponent.Geometry.CurveCenters

/-!
Actual reuse of OAI017's geometric library at openai/math commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a.

The new center configuration is `(y_j, c_j)` with injective `y_j`, rather than
the original `(1, c_j)` with each additive coordinate injective. The lemmas
below implement its new constant-fiber consequence using the original
function-field obstruction, generic normal-rigidity theorem, and valuation
center interface. They do not assume additive-coordinate injectivity.

The weighted transverse-multiplicity estimate remains an explicit `hupper`
input. This file does not claim the full separated interpolation theorem.
-/

namespace OAI.PiExponent.DistinctMultiplicative

noncomputable section
open scoped BigOperators
open Module MvPolynomial NormalBasisRigidity

section FunctionField

variable {C E : Type*} [Field C] [CharZero C] [IsAlgClosed C]
  [Field E] [Algebra C E] [Algebra.EssFiniteType C E]

/-- The entire function-field logarithmic obstruction, reused from OAI017,
not merely its Laurent-series residue calculation. -/
theorem exact_logarithmic_differential_forces_constant (x y : E)
    (h : KaehlerDifferential.D C E x =
      y⁻¹ • KaehlerDifferential.D C E y) :
    ∃ c : C, y = algebraMap C E c := by
  obtain ⟨c, hc⟩ := OAI.PiExponent.constant_of_logarithmic_differential x y h
  exact ⟨c, hc.symm⟩

/-- Convert the weighted comparison and its strict opposite for the largest
differing positive index into the original generic normal-rigidity theorem.
The multiplicative coordinate is arbitrary and nonzero; it is not fixed to 1.
-/
theorem zeroth_constant_of_weighted_normal_comparison
    {m : ℕ}
    (φ : MvPolynomial (Fin (m + 1)) C →ₐ[C] E)
    (Q : Ideal (MvPolynomial (Fin (m + 1)) C))
    (hker : ∀ p, φ p = 0 ↔ p ∈ Q) (hQ : Q ≠ ⊥)
    (hy : φ (X (0 : Fin (m + 1))) ≠ 0)
    (w v : Fin (m + 1) → ℝ) (comparison : ℝ)
    (hupper : ∀ A B : Finset (Fin (m + 1)),
      IsNormalBasis (K := E)
        (fun j => (polynomialTangent φ Q).mkQ (Pi.basisFun E _ j)) A →
      IsNormalBasis (K := E)
        (fun j => (polynomialTangent φ Q).mkQ
          (frameBasis m (φ (X 0)) hy j)) B →
      (∏ j ∈ A, w j) ≤ comparison * (∏ j ∈ B, v j))
    (hseparation : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparison * (∏ j ∈ B, v j) < ∏ j ∈ A, w j) :
    ∃ c : C, φ (X (0 : Fin (m + 1))) = algebraMap C E c := by
  obtain ⟨c, hc⟩ := OAI.PiExponent.constant_zeroth_coordinate_of_generic_normal_separation
    φ Q hker hQ hy (by
      intro A B hA hB i hi0 hiA hiB hagree
      exact weighted_normalBasis_exclusion
        (fun j => (polynomialTangent φ Q).mkQ (Pi.basisFun E _ j))
        (fun j => (polynomialTangent φ Q).mkQ (frameBasis m (φ (X 0)) hy j))
        w v comparison hupper hseparation A B hA hB i hi0 hiA hiB hagree)
  refine ⟨c, ?_⟩
  have hzero := (hker _).mpr hc
  simpa only [map_sub, MvPolynomial.algHom_C, sub_eq_zero] using hzero

end FunctionField

section Centers

variable {E J : Type*} [Field E] [Algebra ℂ E] {m : ℕ}

/-- Centers with freely varying nonzero multiplicative coordinate. -/
def centers (y : J → ℂ) (c : J → Fin m → ℂ) :
    J → Fin (m + 1) → ℂ := fun j => Fin.cases (y j) (c j)

@[simp] theorem centers_zero (y : J → ℂ) (c : J → Fin m → ℂ) (j : J) :
    centers y c j 0 = y j := rfl

@[simp] theorem centers_succ (y : J → ℂ) (c : J → Fin m → ℂ)
    (j : J) (i : Fin m) : centers y c j i.succ = c j i := by
  simp only [centers, Fin.cases_succ]

/-- Unlike the original theorem, injectivity is required only for the
multiplicative coordinate. Additive coordinates can coincide arbitrarily.
This is the new reason a constant-Y curve meets at most one center. -/
theorem center_index_unique_of_constant_y
    (z : Fin (m + 1) → E) (y : J → ℂ) (c : J → Fin m → ℂ)
    (hy : Function.Injective y) (a : ℂ)
    (hz : z 0 = algebraMap ℂ E a)
    (j l : J) (p q : CurveValuationCenter.NormalizedPlace ℂ E)
    (hp : CurveCenters.Centered z (centers y c j) p)
    (hq : CurveCenters.Centered z (centers y c l) q) : j = l := by
  apply hy
  exact (hp.constant_coordinate 0 a hz).symm.trans
    (hq.constant_coordinate 0 a hz)

/-- All centered branches of a constant-Y curve belong to one center,
even when the selected branches lie at different normalized places. -/
theorem all_centered_branches_have_one_index
    (z : Fin (m + 1) → E) (y : J → ℂ) (c : J → Fin m → ℂ)
    (hy : Function.Injective y) (a : ℂ)
    (hz : z 0 = algebraMap ℂ E a)
    (j₀ : J) (p₀ : CurveValuationCenter.NormalizedPlace ℂ E)
    (hp₀ : CurveCenters.Centered z (centers y c j₀) p₀) :
    ∀ (j : J) (p : CurveValuationCenter.NormalizedPlace ℂ E),
      CurveCenters.Centered z (centers y c j) p → j = j₀ := by
  intro j p hp
  exact center_index_unique_of_constant_y z y c hy a hz j j₀ p p₀ hp hp₀

end Centers

#print axioms exact_logarithmic_differential_forces_constant
#print axioms zeroth_constant_of_weighted_normal_comparison
#print axioms center_index_unique_of_constant_y
#print axioms all_centered_branches_have_one_index

end

end OAI.PiExponent.DistinctMultiplicative
