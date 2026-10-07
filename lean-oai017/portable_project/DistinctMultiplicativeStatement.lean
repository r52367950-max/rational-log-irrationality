import DistinctMultiplicativeJets

/-!
A precise formal statement of A-r2, using the actual new logarithmic jet map
and the original OAI017 weighted polynomial / rational packet definitions.

This file defines propositions. It deliberately does not declare A as an
axiom, does not contain `sorry`, and does not supply a proof of the full
statement. The complete proof of this target is now provided in
DistinctMultiplicativeExistence.lean; this file keeps only the definitions.
-/

namespace OAI.PiExponent.DistinctMultiplicative

noncomputable section
open Filter

/-- Source monomials have inclusive weighted degree at most H. -/
def WeightedPolynomialsAt (m : ℕ) (W : Fin (m + 1) → ℚ) (H : ℚ) :=
  {P : PiExponentApprox.FramePolynomial m //
    WeightedSliceDegree.SupportBound (fun i => (W i : ℝ)) (H : ℝ) P}

/-- Target coefficients retain the strict weight inequality weight < H. -/
def packetMapAt {m K : ℕ} (W V : Fin (m + 1) → ℚ) (H : ℚ)
    (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) :
    WeightedPolynomialsAt m W H →
      (Fin K → JetGeometry.RationalCoefficientPacket (R := ℂ) V H) :=
  fun P j => JetGeometry.rationalCoefficientPacket V H
    (formalJetAt (y j) (c j) P.val)

/-- The divisibility scale is chosen from the weights before the centers.
The threshold on n may depend on the complete center family.
-/
def EventualDistinctMultiplicativeInterpolation (m K : ℕ)
    (W V : Fin (m + 1) → ℚ) : Prop :=
  ∃ R : ℕ, 0 < R ∧
    (∀ i, ∃ a : ℕ, 0 < a ∧ (a : ℚ) * W i = (R : ℚ)) ∧
    (∀ i, ∃ a : ℕ, 0 < a ∧ (a : ℚ) * V i = (R : ℚ)) ∧
    ∀ (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ),
      (∀ j, y j ≠ 0) → Function.Injective y →
      ∀ᶠ n : ℕ in atTop,
        Function.Surjective (packetMapAt W V ((n : ℚ) * (R : ℚ)) y c)

/-- A bound for coordinate i can inspect only earlier positive weights. -/
def SuccessiveLowerBounds (m : ℕ) :=
  (i : Fin m) → (Fin i.val → ℚ) → ℚ

def ExceedsSuccessiveBounds {m : ℕ} (b : SuccessiveLowerBounds m)
    (x : Fin m → ℚ) : Prop :=
  ∀ i, b i (fun j => x ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) < x i

/-- Theorem A's full existence and independence quantifiers.

The first two coordinates w₀,v₀ and the ratio θ are fixed before selecting
the successive bounds. Those bounds are fixed before the positive weights;
R is fixed from all the weights before selecting any centers. The final
eventual threshold is allowed to depend on the centers.

The theorem concerns all sufficiently separated weights. A-r2's optional
specific displayed bounds (1.4) would require an additional theorem and are
not silently identified with the larger upstream comparison constant.
-/
def SeparatedDistinctMultiplicativeInterpolationStatement : Prop :=
  ∀ (m K : ℕ), 0 < m → 0 < K →
    ∀ (w₀ v₀ theta : ℚ), 0 < w₀ → 0 < v₀ → 0 < theta → theta < 1 →
      (K : ℚ) * (w₀ / v₀) * theta ^ m < 1 →
      ∃ b : SuccessiveLowerBounds m,
        ∀ (x : Fin m → ℚ), (∀ i, 0 < x i) → ExceedsSuccessiveBounds b x →
          EventualDistinctMultiplicativeInterpolation m K
            (Fin.cases w₀ x) (Fin.cases v₀ (fun i => x i / theta))

#check packetMapAt
#check EventualDistinctMultiplicativeInterpolation
#check SeparatedDistinctMultiplicativeInterpolationStatement

end

end OAI.PiExponent.DistinctMultiplicative
