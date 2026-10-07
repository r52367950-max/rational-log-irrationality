import OAI.NumberTheory.PiExponent.LocalAlgebra.FibreContact
import OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateContactBound

/-! The one-center final fiber inequality with an arbitrary constant Y.
The genuine contact-sum estimate is reused from OAI017. The contact function
μ is explicitly required to be the ordinary additive contact on the fiber;
the new logarithmic branch/contact identification is a separate obligation.
-/

namespace OAI.PiExponent.DistinctMultiplicative

noncomputable section
open scoped BigOperators
open CurveValuationCenter WeightedPolynomialPole

variable {E : Type*} [Field E] [Algebra ℂ E]

theorem coordinatePole_constant {m : ℕ}
    (p : NormalizedPlace ℂ E) (w : Fin (m + 1) → ℚ)
    (a : ℂ) (x : Fin m → E) :
    coordinatePole p.valuation
      (Fin.cases (algebraMap ℂ E a) x : Fin (m + 1) → E) w =
      coordinatePole p.valuation x (fun i => w i.succ) := by
  have h0 : coordinateOrder p.valuation (algebraMap ℂ E a) = 0 :=
    CurveContactSum.coordinateOrder_constant_eq_zero p a
  have he : (fun i : Fin (m + 1) =>
      (coordinateOrder p.valuation
        ((Fin.cases (algebraMap ℂ E a) x : Fin (m + 1) → E) i) : ℚ)) =
      Fin.cases 0 (fun i => (coordinateOrder p.valuation (x i) : ℚ)) := by
    funext i
    cases i using Fin.cases <;> simp [h0]
  unfold coordinatePole
  rw [he]
  exact FibreContact.weightedPole_zero_cons w _

/-- Every constant multiplicative coordinate contributes zero pole degree,
so OAI017's Y=1 fiber degree identity extends to arbitrary constants. -/
theorem weightedDegree_constant {m : ℕ}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (w : Fin (m + 1) → ℚ) (a : ℂ) (x : Fin m → E) :
    CurveContactSum.weightedDegree hfinite
      (Fin.cases (algebraMap ℂ E a) x : Fin (m + 1) → E) w =
      CurveContactSum.weightedDegree hfinite x (fun i => w i.succ) := by
  have he : CurveContactSum.weightedPoleDivisor hfinite
      (Fin.cases (algebraMap ℂ E a) x : Fin (m + 1) → E) w =
      CurveContactSum.weightedPoleDivisor hfinite x (fun i => w i.succ) := by
    ext p
    exact coordinatePole_constant p w a x
  unfold CurveContactSum.weightedDegree
  rw [he]

/-- Actual single-center contact inequality, with no additive-coordinate
injectivity and no second volume condition. It is the final contradiction in
A once the new logarithmic contact equals ordinary contact on constant Y.
-/
theorem single_center_fibre_curve_inequality {m : ℕ}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (a : ℂ) (x : Fin m → E) (c : Fin m → ℂ)
    (w v : Fin (m + 1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (hratio : ∀ i : Fin m, (1 + sigma) * (w i.succ : ℝ) < v i.succ)
    (i : Fin m) (hne : x i - algebraMap ℂ E (c i) ≠ 0)
    (S : Finset (NormalizedPlace ℂ E))
    (hc : ∀ p ∈ S, CurveCenters.Centered x c p)
    (hres : ∀ p ∈ S,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring p)))
    (μ : NormalizedPlace ℂ E → ℝ)
    (hμ : ∀ p (hp : p ∈ S), letI := hres p hp;
      μ p = (PlaceCenteredBranch.ordinaryContact p x c (hc p hp)
        ⟨i, sub_ne_zero.mp hne⟩ (fun j => v j.succ) : ℝ)) :
    (1 + sigma) * (∑ p ∈ S, μ p) ≤
      CurveContactSum.weightedDegree hfinite
        (Fin.cases (algebraMap ℂ E a) x : Fin (m + 1) → E) w := by
  rw [weightedDegree_constant]
  have hcoord := CoordinateContactBound.coordinate_contact_sum_le hfinite x c
    (fun j => w j.succ) (fun j => v j.succ) (fun j => hw j.succ)
    (fun j => hv j.succ) i hne S hc hres μ hμ
  by_contra h
  have hexcess := lt_of_not_ge h
  have hsum : 0 < ∑ p ∈ S, μ p := by
    have hn := CurveContactSum.weightedDegree_nonneg hfinite x (fun j => w j.succ)
    have hs : 0 < 1 + sigma := by linarith
    exact (mul_pos_iff_of_pos_left hs).mp (lt_of_le_of_lt hn hexcess)
  have hwi : (0 : ℝ) < w i.succ := by exact_mod_cast hw i.succ
  have hb := mul_lt_mul_of_pos_left hexcess hwi
  have hr := mul_lt_mul_of_pos_right (hratio i) hsum
  nlinarith

#print axioms weightedDegree_constant
#print axioms single_center_fibre_curve_inequality

end

end OAI.PiExponent.DistinctMultiplicative
