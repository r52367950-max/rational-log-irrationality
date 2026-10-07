import OAI.NumberTheory.PiExponent.Geometry.CurveFieldRigidity
import DistinctMultiplicativeRigidity

/-!
New-center adaptation of the actual OAI017 persistent-component and weighted
transverse-multiplicity machinery. The zeroth center need not equal 1.

The separation constant below is the upstream `comparisonConstant` (its
rectangular estimate), not the sharper factorial constant claimed in A-r2.
Thus this module handles sufficiently more separated weights and does not
claim to machine-check A-r2's particular displayed explicit lower bounds.
-/

namespace OAI.PiExponent.DistinctMultiplicative

noncomputable section
open scoped BigOperators
open Filter
open PiExponentApprox PersistentWeightComparison CurveCenters CurveValuationCenter

variable {E : Type*} [Field E] [Algebra ℂ E]

/-- Actual persistent derivative vanishing plus the original multiplicity
comparison forces Y to equal the arbitrary nonzero center's Y coordinate.
No independent generic-normal comparison is postulated here: it is obtained
by invoking the upstream `logarithmic_persistent_comparison` proof.
-/
theorem persistent_derivatives_force_center_y {m : ℕ}
    (x : Fin (m + 1) → E) (a : Fin (m + 1) → ℂ) (ha : a 0 ≠ 0)
    (p : NormalizedPlace ℂ E) (hp : Centered x a p)
    (hheight : (CurveFieldRigidity.coordinateKernel x).height ≤ m)
    (rho : Fin (m + 1) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma N : ℝ) (hsigma : 0 < sigma) (hN : 0 < N)
    (hrect : UniformRectangles (m + 1) cost (sigma / ((m : ℝ) + 2)) N)
    (F : FramePolynomial m) (hF0 : F ≠ 0)
    (hF : HasWeightedDegreeLE (fun i => (rho i : ℝ)) N F)
    (hvanish : ∀ word : List (Fin (m + 1)), frameWordCost cost word ≤ sigma * N →
      MvPolynomial.aeval x (polynomialFrameWord m word F) = 0)
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m sigma * (∏ j ∈ B, cost j) < ∏ j ∈ A, (rho j : ℝ)) :
    x 0 = algebraMap ℂ E (a 0) := by
  have hx0 : x 0 ≠ 0 := by
    intro hz
    have hc := hp.constant_coordinate 0 0 (by simpa using hz)
    exact ha hc.symm
  have hY : MvPolynomial.X (0 : Fin (m + 1)) ∉
      CurveFieldRigidity.coordinateKernel x := by
    simpa only [CurveFieldRigidity.mem_coordinateKernel, MvPolynomial.aeval_X] using hx0
  have hbound : ((m : ℝ) + 2) * ((sigma / ((m : ℝ) + 2)) * N) = sigma * N := by
    have hm : (m : ℝ) + 2 ≠ 0 := by positivity
    field_simp
  obtain ⟨c, hc⟩ := CurveComponentRigidity.coordinate_constant_of_persistent_comparison
    (fun i => (rho i : ℝ)) cost (comparisonConstant m sigma)
    ((sigma / ((m : ℝ) + 2)) * N) (fun i => (hcost i).le) (by positivity)
    F hF0 (CurveFieldRigidity.coordinateKernel x) inferInstance hheight hY
    (fun word hword => hvanish word (by simpa only [hbound] using hword))
    (logarithmic_persistent_comparison rho hrho cost hcost sigma N hsigma hN hrect
      F hF (CurveFieldRigidity.coordinateKernel x) hY) hseparated
  have hxc : x 0 = algebraMap ℂ E c := by
    simpa only [CurveFieldRigidity.mem_coordinateKernel, map_sub, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C, sub_eq_zero] using hc
  have hca := hp.constant_coordinate 0 c hxc
  simpa only [hca] using hxc

/-- This new distinct-multiplicative-center consequence directly removes the
original second, additive-fiber persistence argument and its volume condition.
-/
theorem persistent_derivatives_at_most_one_center {m : ℕ} {J : Type*}
    (x : Fin (m + 1) → E) (y : J → ℂ) (c : J → Fin m → ℂ)
    (hy : Function.Injective y) (hy0 : ∀ j, y j ≠ 0)
    (j l : J) (p q : NormalizedPlace ℂ E)
    (hp : Centered x (centers y c j) p) (hq : Centered x (centers y c l) q)
    (hheight : (CurveFieldRigidity.coordinateKernel x).height ≤ m)
    (rho : Fin (m + 1) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma N : ℝ) (hsigma : 0 < sigma) (hN : 0 < N)
    (hrect : UniformRectangles (m + 1) cost (sigma / ((m : ℝ) + 2)) N)
    (F : FramePolynomial m) (hF0 : F ≠ 0)
    (hF : HasWeightedDegreeLE (fun i => (rho i : ℝ)) N F)
    (hvanish : ∀ word : List (Fin (m + 1)), frameWordCost cost word ≤ sigma * N →
      MvPolynomial.aeval x (polynomialFrameWord m word F) = 0)
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ k, i < k → (k ∈ A ↔ k ∈ B)) →
      comparisonConstant m sigma * (∏ k ∈ B, cost k) < ∏ k ∈ A, (rho k : ℝ)) :
    j = l := by
  have hY := persistent_derivatives_force_center_y x (centers y c j) (hy0 j)
    p hp hheight rho hrho cost hcost sigma N hsigma hN hrect F hF0 hF hvanish hseparated
  exact center_index_unique_of_constant_y x y c hy (y j) hY j l p q hp hq

/-- The technical rectangular cutoff condition is automatic for sufficiently
large N, by the original uniform-cutoff theorem. This version no longer asks
the caller to prove `hrect` or a positivity hypothesis separately for each N.
-/
theorem eventually_persistent_derivatives_at_most_one_center {m : ℕ} {J : Type*}
    (x : Fin (m + 1) → E) (y : J → ℂ) (c : J → Fin m → ℂ)
    (hy : Function.Injective y) (hy0 : ∀ j, y j ≠ 0)
    (j l : J) (p q : NormalizedPlace ℂ E)
    (hp : Centered x (centers y c j) p) (hq : Centered x (centers y c l) q)
    (hheight : (CurveFieldRigidity.coordinateKernel x).height ≤ m)
    (rho : Fin (m + 1) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ k, i < k → (k ∈ A ↔ k ∈ B)) →
      comparisonConstant m sigma * (∏ k ∈ B, cost k) < ∏ k ∈ A, (rho k : ℝ)) :
    ∀ᶠ N : ℝ in atTop, ∀ F : FramePolynomial m, F ≠ 0 →
      HasWeightedDegreeLE (fun i => (rho i : ℝ)) N F →
      (∀ word : List (Fin (m + 1)), frameWordCost cost word ≤ sigma * N →
        MvPolynomial.aeval x (polynomialFrameWord m word F) = 0) → j = l := by
  filter_upwards [eventually_uniformRectangles (m + 1) cost hcost
      (sigma / ((m : ℝ) + 2)) (by positivity),
    eventually_gt_atTop (0 : ℝ)] with N hrect hN
  intro F hF0 hF hvanish
  exact persistent_derivatives_at_most_one_center x y c hy hy0 j l p q hp hq
    hheight rho hrho cost hcost sigma N hsigma hN hrect F hF0 hF hvanish hseparated

#print axioms persistent_derivatives_force_center_y
#print axioms persistent_derivatives_at_most_one_center
#print axioms eventually_persistent_derivatives_at_most_one_center

end

end OAI.PiExponent.DistinctMultiplicative
