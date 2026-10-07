import OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivityComplete
import OAI.NumberTheory.PiExponent.Ampleness.BlowupAmpleTwist
import OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin
import OAI.NumberTheory.PiExponent.Ampleness.NumericalAmplenessTheorem
import OAI.NumberTheory.PiExponent.Jets.JetGeometry

/-!
Generic, genuinely geometric adapters to the pinned OAI017 development.

These declarations do NOT assume all multiplicative centers equal 1. They do NOT
claim to prove the distinct-center interpolation theorem: the curve-degree
hypothesis, construction of its compact ideal, and the comparison between its
global sections and polynomial logarithmic jets remain explicit obligations.
There are no new axioms or `sorry` declarations here.
-/

namespace OAI.PiExponent.DistinctMultiplicativeAmple

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open OAI.PiExponentSeshadri.Geometry
open OAI.PiExponent.NumericalAmpleness
open OAI.PiExponent.BlowupJetSurjectivity
open OAI.PiExponent.GeometrySupport

/-- A positive uniform margin on the actual ordinary blowup gives eventual
surjectivity of abstract ideal-jet restriction. No center coordinates occur. -/
theorem eventual_jetRestriction_surjective_of_uniform_curve_margin
    {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (I : X.IdealSheafData) (A : LineBundle X)
    (H : LineBundle (OAI.PiExponentSeshadri.BlowupGluing.scheme I))
    (hH : H.IsAmple) (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ C : IntegralCurve (OAI.PiExponentSeshadri.BlowupGluing.scheme I),
      ε * (curveDegree
        (OAI.PiExponentSeshadri.BlowupGluing.projection I ≫ p) H C : ℝ) ≤
        (curveDegree
          (OAI.PiExponentSeshadri.BlowupGluing.projection I ≫ p)
          (blowupBundle I A) C : ℝ)) :
    ∃ N, ∀ n, N ≤ n → Function.Surjective (jetRestriction I A n) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have hample : (blowupBundle I A).IsAmple :=
    isAmple_of_uniform_curve_margin
      (OAI.PiExponentSeshadri.BlowupGluing.projection I ≫ p)
      H (blowupBundle I A) hH ε hε hmargin
  exact eventual_blowup_jetRestriction_surjective p I A hample

/-- Theorem A's geometric endgame, with the precise remaining degree inequality
as a hypothesis. The ambient compactification is any proper integral complex
scheme, and the center ideal is arbitrary with proper support. -/
theorem eventual_jetRestriction_surjective_of_nonnegative_curve_degree
    {X : Scheme.{0}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (I : X.IdealSheafData) (hI : I.support ≠ ⊤)
    (A : LineBundle X) (hA : A.IsAmple)
    (σ : ℝ) (hσ : 0 < σ)
    (hn : ∀ C : IntegralCurve (OAI.PiExponentSeshadri.BlowupGluing.scheme I),
      0 ≤ (curveDegree
        (OAI.PiExponentSeshadri.BlowupGluing.projection I ≫ p)
        (A.pullback (OAI.PiExponentSeshadri.BlowupGluing.projection I)) C : ℝ) +
        (1 + σ) * (curveDegree
          (OAI.PiExponentSeshadri.BlowupGluing.projection I ≫ p)
          (OAI.PiExponentSeshadri.BlowupGluing.exceptionalLineBundle I) C : ℝ)) :
    ∃ N, ∀ n, N ≤ n → Function.Surjective (jetRestriction I A n) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let L := A.pullback (OAI.PiExponentSeshadri.BlowupGluing.projection I)
  let J := OAI.PiExponentSeshadri.BlowupGluing.exceptionalLineBundle I
  obtain ⟨a, ha, hample⟩ :=
    OAI.PiExponentSeshadri.BlowupGluing.exists_ample_exceptional_power_gt_one
      I hI A hA
  have hmargin : ∀ C : IntegralCurve (OAI.PiExponentSeshadri.BlowupGluing.scheme I),
      OAI.PiExponent.BlowupCurveMargin.marginCoefficient a σ *
        (curveDegree
          (OAI.PiExponentSeshadri.BlowupGluing.projection I ≫ p)
          ((L.pow a).tensor J) C : ℝ) ≤
        (curveDegree
          (OAI.PiExponentSeshadri.BlowupGluing.projection I ≫ p)
          (L.tensor J) C : ℝ) := by
    intro C
    exact OAI.PiExponent.BlowupCurveMargin.margin_of_nonnegative_degree
      (OAI.PiExponentSeshadri.BlowupGluing.projection I ≫ p)
      L J a ha hample σ hσ C (hn C)
  have hLJ : (L.tensor J).IsAmple :=
    isAmple_of_uniform_curve_margin
      (OAI.PiExponentSeshadri.BlowupGluing.projection I ≫ p)
      ((L.pow a).tensor J) (L.tensor J) hample
      (OAI.PiExponent.BlowupCurveMargin.marginCoefficient a σ)
      (OAI.PiExponent.BlowupCurveMargin.marginCoefficient_pos ha hσ) hmargin
  have hblowup : (blowupBundle I A).IsAmple :=
    OAI.PiExponent.AmpleIso.isAmple_of_sheaf_iso (L.tensor J)
      (blowupBundle I A) (moduleTensorComm L.sheaf J.sheaf) hLJ
  exact eventual_blowup_jetRestriction_surjective p I A hblowup

/-- Transport the actual scheme-theoretic jet restriction to simultaneous formal
coefficient packets. In a distinct-center application, `α` is the weighted
polynomial space and `f a j` is its logarithmic expansion at `(y_j,c_j)`.

The two surjective presentations and the commuting-square equality are explicit
remaining obligations. In particular, this declaration does not conceal the
construction of the centers, their local ideals, or the polynomial degree bound.
-/
theorem formalCoefficientPackets_surjective_of_jetRestriction
    {X : Scheme.{0}} {ι J α : Type}
    (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ)
    (v : ι → ℚ) (hv : ∀ i, 0 ≤ v i)
    (e : ι → ℕ) (H : ℚ) (he : ∀ i, H ≤ (e i : ℚ) * v i)
    (f : α → J → MvPowerSeries ι ℂ)
    (P : α → GlobalSections X (modulePow X A.sheaf n))
    (hP : Function.Surjective P)
    (q : GlobalSections X ((moduleTwistFunctor A n).obj (jetQuotient (I ^ n))) →
      J → (MvPowerSeries ι ℂ ⧸ ((JetGeometry.coordinatePowerIdeal (R := ℂ) e) ^ n)))
    (hq : Function.Surjective q)
    (hcompat : ∀ a, q (jetRestriction I A n (P a)) =
      fun j => Ideal.Quotient.mk ((JetGeometry.coordinatePowerIdeal (R := ℂ) e) ^ n)
        (f a j))
    (hjet : Function.Surjective (jetRestriction I A n)) :
    Function.Surjective (fun a j =>
      JetGeometry.rationalCoefficientPacket v (n * H) (f a j)) := by
  apply JetGeometry.rationalCoefficientPackets_surjective_of_coordinatePowerIdeal
    v hv e H he n f
  intro packets
  obtain ⟨s, hs⟩ := hq packets
  obtain ⟨r, hr⟩ := hjet s
  obtain ⟨a, ha⟩ := hP r
  refine ⟨a, ?_⟩
  change (fun j => Ideal.Quotient.mk
    ((JetGeometry.coordinatePowerIdeal (R := ℂ) e) ^ n) (f a j)) = packets
  rw [← hcompat a, ha, hr, hs]

end

end OAI.PiExponent.DistinctMultiplicativeAmple

#print axioms OAI.PiExponent.DistinctMultiplicativeAmple.eventual_jetRestriction_surjective_of_uniform_curve_margin
#print axioms OAI.PiExponent.DistinctMultiplicativeAmple.eventual_jetRestriction_surjective_of_nonnegative_curve_degree
#print axioms OAI.PiExponent.DistinctMultiplicativeAmple.formalCoefficientPackets_surjective_of_jetRestriction
