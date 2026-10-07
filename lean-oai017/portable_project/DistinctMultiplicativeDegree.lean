import DistinctMultiplicativeGlobal
import DistinctMultiplicativeContact
import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree
import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizedDegreeTransfer
import OAI.NumberTheory.PiExponent.Geometry.AdmissibleCurveCoordinates
import OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupMargin
import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism

/-! Actual ideal/contact/degree comparison at distinct multiplicative centers.
All ideals below are the concrete ideals constructed by Global, and all
contacts are the actual normalized logarithmic contacts constructed by Contact.
-/

namespace OAI.PiExponent.DistinctMultiplicative.Degree

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped BigOperators
open OAI.PiExponentSeshadri.Geometry
open OAI.PiExponent.ExceptionalCurveDegree
open CurveNormalizationModel CurveValuationCenter CurvePlaceCenter
open Global

variable {m : ℕ}

section Algebra
variable {A : Type} [CommRing A] [Algebra ℂ A]

theorem aeval_scaleY_inverse (y : ℂ) (z : Fin (m + 1) → A) :
    (MvPolynomial.aeval z).comp (scaleY y⁻¹) =
      MvPolynomial.aeval
        (Fin.cases (algebraMap ℂ A y⁻¹ * z 0) (fun i => z i.succ)) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero => simp
  | succ i => simp

theorem map_powerIdealAt_aeval (y : ℂ) (hy : y ≠ 0) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ) (z : Fin (m + 1) → A) :
    (powerIdealAt y c T e).map (MvPolynomial.aeval z).toRingHom =
      LogarithmicContactIdeal.logarithmicIdeal c
        (algebraMap ℂ A y⁻¹ * z 0) (fun i => z i.succ) T e := by
  rw [powerIdealAt_eq_map_inverse y hy, Ideal.map_map]
  have h : (MvPolynomial.aeval z).toRingHom.comp (scaleY y⁻¹).toRingHom =
      (MvPolynomial.aeval
        (Fin.cases (algebraMap ℂ A y⁻¹ * z 0) (fun i => z i.succ))).toRingHom :=
    congrArg AlgHom.toRingHom (aeval_scaleY_inverse y z)
  rw [h]
  exact CompactJetPolynomial.map_powerIdeal_aeval c T e
    (algebraMap ℂ A y⁻¹ * z 0) (fun i => z i.succ)

variable [IsLocalRing A]
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

theorem map_polynomialIdealAt_eq_selected {K : ℕ}
    (y : Fin K → ℂ) (hy0 : ∀ j, y j ≠ 0) (hy : Function.Injective y)
    (c : Fin K → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (z : Fin (m + 1) → A) (k : Fin K)
    (hY : CurveLocalOrder.residueAugmentation ℂ A (z 0) = y k) :
    (polynomialIdealAt y c T e).map (MvPolynomial.aeval z).toRingHom =
      LogarithmicContactIdeal.logarithmicIdeal (c k)
        (algebraMap ℂ A (y k)⁻¹ * z 0) (fun i => z i.succ) T e := by
  classical
  unfold polynomialIdealAt
  change Ideal.mapHom (MvPolynomial.aeval z).toRingHom _ = _
  rw [map_prod]
  simp only [Ideal.mapHom_apply, map_powerIdealAt_aeval _ (hy0 _)]
  apply Finset.prod_eq_single k
  · intro j _ hjk
    rw [Ideal.one_eq_top]
    apply JetProductLocalization.logarithmicIdeal_eq_top_of_residue_ne
    rintro ⟨h1, _⟩
    rw [map_mul, CurveLocalOrder.residueAugmentation_algebraMap, hY] at h1
    have h := congrArg (fun a : ℂ => y j * a) h1
    simp only [← mul_assoc, mul_inv_cancel₀ (hy0 j), one_mul, mul_one] at h
    exact hjk (hy h.symm)
  · simp

end Algebra

variable {X Y : Scheme.{0}}

theorem localIdeal_compactIdealAt {A : Type} [CommRing A]
    {K : Type} [Fintype K] (y : K → ℂ) (c : K → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (j : CompactLogJetIdeal.affineSpace m ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (φ : PiExponentApprox.FramePolynomial m →+* A) :
    localIdeal (compactIdealAt y c T e j)
      (Spec.map (CommRingCat.ofHom φ) ≫ j) =
        (polynomialIdealAt y c T e).map φ := by
  unfold localIdeal
  rw [Scheme.IdealSheafData.comap_comp, restrict_compactIdealAt]
  exact localIdeal_specIdeal _ φ

theorem centered_of_closedPoint_eqAt
    {E : Type} [Field E] [Algebra ℂ E]
    (p : NormalizedPlace ℂ E) (z : Fin (m + 1) → E)
    (y : ℂ) (c : Fin m → ℂ)
    (j : CompactLogJetIdeal.affineSpace m ⟶ X) [IsOpenImmersion j]
    (q : Spec (CommRingCat.of (PlaceValuationRing.ring p)) ⟶ X)
    (hgeneric : Spec.map (CommRingCat.ofHom
        (algebraMap (PlaceValuationRing.ring p) E)) ≫ q =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (hclosed : q (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) =
      j (centerPointAt y c)) : CurveCenters.Centered z (Global.centerAt y c) p := by
  have hr : Set.range q ⊆ Set.range j := by
    rintro _ ⟨r, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint r).map q.continuous).mem_open
      j.isOpenEmbedding.isOpen_range (hclosed ▸ Set.mem_range_self (centerPointAt y c))
  let g := IsOpenImmersion.lift j q hr
  have hg : g ≫ j = q := IsOpenImmersion.lift_fac j q hr
  let φ : PiExponentApprox.FramePolynomial m →+* PlaceValuationRing.ring p :=
    (Spec.preimage g).hom
  have hgφ : Spec.map (CommRingCat.ofHom φ) = g := Spec.map_preimage g
  have hcomp : CommRingCat.ofHom φ ≫
      CommRingCat.ofHom (algebraMap (PlaceValuationRing.ring p) E) =
      CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, hgφ]
    apply (cancel_mono j).mp
    rw [Category.assoc, hg]
    exact hgeneric
  have hgc : g (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) =
      centerPointAt y c := by
    apply j.isOpenEmbedding.injective
    change (g ≫ j) (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) = _
    rw [hg, hclosed]
  have hcomap : PrimeSpectrum.comap φ (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) =
      centerPointAt y c := by
    change (Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint _) = _
    rw [hgφ, hgc]
  intro i
  let P : PiExponentApprox.FramePolynomial m :=
    MvPolynomial.X i - MvPolynomial.C (Global.centerAt y c i)
  have hmem : φ P ∈ IsLocalRing.maximalIdeal (PlaceValuationRing.ring p) := by
    change P ∈ (PrimeSpectrum.comap φ (IsLocalRing.closedPoint _)).asIdeal
    rw [hcomap]
    change P ∈ WeightedBezout.pointIdeal (Global.centerAt y c)
    rw [WeightedBezout.mem_pointIdeal]
    simp [P]
  have hpos := p.valuation.toValuation.mem_maximalIdeal_iff.mp hmem
  have heval := congrArg
    (fun h : CommRingCat.of (PiExponentApprox.FramePolynomial m) ⟶ CommRingCat.of E => h P)
    hcomp
  change algebraMap (PlaceValuationRing.ring p) E (φ P) = MvPolynomial.aeval z P at heval
  change 0 < p.valuation (algebraMap (PlaceValuationRing.ring p) E (φ P)) at hpos
  rw [heval] at hpos
  simpa [P] using hpos

section Curve
variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

theorem map_powerIdealAt_eq_top_of_transcendental
    (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (he : ∀ i, 0 < e i) (z : Fin (m + 1) → E)
    (hz : ∃ i, Transcendental ℂ (z i)) :
    (powerIdealAt y c T e).map (MvPolynomial.aeval z).toRingHom = ⊤ := by
  let φ := (MvPolynomial.aeval (R := ℂ) z).toRingHom
  rcases ((powerIdealAt y c T e).map φ).eq_bot_or_top with hb | ht
  · have hle : powerIdealAt y c T e ≤ RingHom.ker φ := by
      apply Ideal.map_le_iff_le_comap.mp
      simpa using hb.le
    have hr := (Ideal.IsPrime.radical_le_iff (RingHom.ker_isPrime φ)).mpr hle
    rw [radical_powerIdealAt y c T e he] at hr
    obtain ⟨i, hi⟩ := hz
    have hx : MvPolynomial.X i - MvPolynomial.C (Global.centerAt y c i) ∈
        WeightedBezout.pointIdeal (Global.centerAt y c) := by
      rw [WeightedBezout.mem_pointIdeal]
      simp
    have hv := hr hx
    change MvPolynomial.aeval z
      (MvPolynomial.X i - MvPolynomial.C (Global.centerAt y c i)) = 0 at hv
    simp only [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, sub_eq_zero] at hv
    exact (hi (hv ▸ isAlgebraic_algebraMap (A := E) (Global.centerAt y c i))).elim
  · exact ht

theorem compactIdealAt_comap_ne_bot_of_generic {K : ℕ}
    (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (he : ∀ i, 0 < e i)
    (j : CompactLogJetIdeal.affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (g : parameterCurve f hf ⟶ X) (z : Fin (m + 1) → E)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hgeneric : parameterCurveGenericPoint f hf ≫ g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j) :
    (compactIdealAt y c T e j).comap g ≠ ⊥ := by
  have htop : localIdeal (compactIdealAt y c T e j)
      (parameterCurveGenericPoint f hf ≫ g) = ⊤ := by
    rw [hgeneric, localIdeal_compactIdealAt]
    unfold polynomialIdealAt
    change Ideal.mapHom (MvPolynomial.aeval z).toRingHom _ = _
    rw [map_prod]
    have ht : ∀ k : Fin K, (powerIdealAt (y k) (c k) T e).map
        (MvPolynomial.aeval z).toRingHom = ⊤ :=
      fun k => map_powerIdealAt_eq_top_of_transcendental (y k) (c k) T e he z hz
    simp only [Ideal.mapHom_apply, ht]
    rw [← Ideal.one_eq_top]
    exact Finset.prod_const_one
  intro hzero
  have hb : localIdeal (compactIdealAt y c T e j)
      (parameterCurveGenericPoint f hf ≫ g) = ⊥ := by
    simp only [localIdeal, Scheme.IdealSheafData.comap_comp, hzero,
      Scheme.IdealSheafData.comap_bot]
    exact Ideal.map_bot
  exact bot_ne_top (hb.symm.trans htop)

theorem centerMorphism_eq_centeredLiftAt [X.IsSeparated]
    (j : CompactLogJetIdeal.affineSpace m ⟶ X)
    (g : parameterCurve f hf ⟶ X) (z : Fin (m + 1) → E)
    (hgeneric : parameterCurveGenericPoint f hf ≫ g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (p : NormalizedPlace ℂ E) (y : ℂ) (c : Fin m → ℂ)
    (hc : CurveCenters.Centered z (Global.centerAt y c) p) :
    centerMorphism f hf p ≫ g =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.aeval (PlaceCenteredBranch.lift p z (Global.centerAt y c) hc)).toRingHom) ≫ j := by
  apply centerMorphism_comp_eq_of_generic f hf p g
  rw [hgeneric, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro P
  exact PlaceCenteredBranch.lift_aeval p z (Global.centerAt y c) hc P

theorem localIdealAt_length_eq_logContactAt [X.IsSeparated]
    {K : ℕ} (y : Fin K → ℂ) (hy0 : ∀ j, y j ≠ 0) (hy : Function.Injective y)
    (c : Fin K → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 < v i)
    (R : ℚ) (he : ∀ i, v i * (e i : ℚ) = R)
    (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (j : CompactLogJetIdeal.affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (g : parameterCurve f hf ⟶ X) (z : Fin (m + 1) → E)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hgeneric : parameterCurveGenericPoint f hf ≫ g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring p))]
    (k : Fin K) (hcenter : CurveCenters.Centered z (Global.centerAt (y k) (c k)) p) :
    ((Module.length (PlaceValuationRing.ring p)
      ((PlaceValuationRing.ring p) ⧸
        localIdeal (compactIdealAt y c T e j) (centerMorphism f hf p ≫ g))).toNat : ℚ) =
      R * logContactAt p (y k) (hy0 k) z (c k) hcenter
        (CurveCenters.Centered.exists_nonzero_difference z _ hz) v := by
  let a := PlaceCenteredBranch.lift p z (Global.centerAt (y k) (c k)) hcenter
  rw [centerMorphism_eq_centeredLiftAt f hf j g z hgeneric p (y k) (c k) hcenter,
    localIdeal_compactIdealAt,
    map_polynomialIdealAt_eq_selected y hy0 hy c T e a k
      (PlaceCenteredBranch.lift_residue p z (Global.centerAt (y k) (c k)) hcenter 0)]
  have hi : LogarithmicContactIdeal.logarithmicIdeal (c k)
      (algebraMap ℂ (PlaceValuationRing.ring p) (y k)⁻¹ * a 0) (fun i => a i.succ) T e =
      localLogIdealAt p (y k) (hy0 k) z (c k) hcenter T e := by
    simp only [localLogIdealAt, normalized_lift_zero, normalized_lift_succ]
    rfl
  rw [hi]
  exact localLogIdealAt_colength_eq_contact p (y k) (hy0 k) z (c k) hcenter
    (CurveCenters.Centered.exists_nonzero_difference z _ hz) v hv T hT R e he

theorem compactIdealAt_degree_eq_neg_contact_sum [X.IsSeparated]
    {K : ℕ} (y : Fin K → ℂ) (hy0 : ∀ k, y k ≠ 0) (hy : Function.Injective y)
    (c : Fin K → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 < v i)
    (R : ℚ) (he : ∀ i, v i * (e i : ℚ) = R)
    (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (j : CompactLogJetIdeal.affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (pX : X ⟶ Spec (CommRingCat.of ℂ)) [IsSeparated pX]
    (hj : j ≫ pX = CompactLogJetIdeal.structureMap m)
    (π : Y ⟶ X) (J : LineBundle Y) (ι : J.sheaf ⟶ PiExponentSeshadri.Frames.O Y)
    (hJ : PresentsPullbackIdeal (compactIdealAt y c T e j) π J ι)
    (g : parameterCurve f hf ⟶ Y) (z : Fin (m + 1) → E)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hgeneric : parameterCurveGenericPoint f hf ≫ g ≫ π =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring p)))
    (hfinite : ∀ t : E, Transcendental ℂ t →
      FiniteDimensional (IntermediateField.adjoin ℂ {t}) E) :
    ((eulerCharacteristic (parameterCurveStructureMap f hf) 1 (J.pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℚ) =
      -R * ∑ p ∈ placesAt hfinite z y c hz,
        familyContactAt hres hfinite z y hy0 c hz v p := by
  classical
  let I := compactIdealAt y c T e j
  have hg : I.comap (g ≫ π) ≠ ⊥ :=
    compactIdealAt_comap_ne_bot_of_generic f hf y c T e hepos j (g ≫ π) z hz hgeneric
  let D := idealDivisor f hf I π J ι hJ g hg
  let P := placesAt hfinite z y c hz
  have hzero (p : NormalizedPlace ℂ E) (hp : p ∉ P) : D p = 0 := by
    have havoid : (centerMorphism f hf p ≫ g ≫ π)
        (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) ∉ I.support := by
      intro hmem
      change _ ∈ ((compactIdealAt y c T e j).support : Set X) at hmem
      rw [support_compactIdealAt y c T e hepos j pX hj] at hmem
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hmem
      obtain ⟨a, ha⟩ := hk
      have hap : pointAt (y k) (c k) a = centerPointAt (y k) (c k) := by
        have h := Set.mem_range_self (f := pointAt (y k) (c k)) a
        rw [range_pointAt] at h
        exact h
      have hclosed : (centerMorphism f hf p ≫ g ≫ π)
          (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) =
          j (centerPointAt (y k) (c k)) :=
        ha.symm.trans (congrArg j hap)
      have hfield : Spec.map (CommRingCat.ofHom
          (algebraMap (PlaceValuationRing.ring p) E)) ≫
          (centerMorphism f hf p ≫ g ≫ π) =
          Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j := by
        rw [← Category.assoc, centerMorphism_generic]
        exact hgeneric
      apply hp
      exact (mem_placesAt hfinite z y c hz p).mpr
        ⟨k, centered_of_closedPoint_eqAt p z (y k) (c k) j _ hfield hclosed⟩
    change idealDivisor f hf I π J ι hJ g hg p = 0
    rw [idealDivisor_apply, localIdeal_eq_top_of_not_mem I _ havoid]
    simp
  have hsupport : D.support ⊆ P := by
    intro p hp
    by_contra h
    exact (Finsupp.mem_support_iff.mp hp) (hzero p h)
  have hvalue (p : NormalizedPlace ℂ E) (hp : p ∈ P) :
      (D p : ℚ) = R * familyContactAt hres hfinite z y hy0 c hz v p := by
    letI := hres p
    have hp' : p ∈ placesAt hfinite z y c hz := hp
    let k := centerAtIndex hfinite z y c hz p hp
    have hcenter := centeredAt hfinite z y c hz p hp
    have h := localIdealAt_length_eq_logContactAt f hf y hy0 hy c T e v hv R he hT
      j (g ≫ π) z hz hgeneric p k hcenter
    change (idealDivisor f hf I π J ι hJ g hg p : ℚ) = _
    rw [idealDivisor_apply]
    simpa only [familyContactAt, dite_eq_left hp', I, k] using h
  have hsum : D.sum (fun _ n => (n : ℚ)) =
      R * ∑ p ∈ P, familyContactAt hres hfinite z y hy0 c hz v p := by
    rw [D.sum_of_support_subset hsupport (fun _ n => (n : ℚ)) (by simp)]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p hp => hvalue p hp)
  have hd := degree_eq_neg_idealDivisor_sum f hf I π J ι hJ g hg
  have hdq : ((eulerCharacteristic (parameterCurveStructureMap f hf) 1 (J.pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℚ) =
      -D.sum (fun _ n => (n : ℚ)) := by
    simpa only [Int.cast_neg, Finsupp.sum, Int.cast_sum, Int.cast_natCast] using
      congrArg (fun a : ℤ => (a : ℚ)) hd
  rw [hsum] at hdq
  simpa only [neg_mul, P] using hdq

end Curve

open OAI.PiExponent.NumericalAmpleness
open CurveImageAffineCoordinates

/-- An actual normalization model of a noncontracted curve in the blowup.
It contains geometric data and equations, with no degree or interpolation
assertion among its fields.
-/
structure ModelData {B X : Scheme.{0}} (pB : B ⟶ CompactLogJetIdeal.base)
    (π : B ⟶ X) (j : CompactLogJetIdeal.affineSpace m ⟶ X)
    (C : IntegralCurve B) where
  E : Type
  [field : Field E]
  [algebra : Algebra ℂ E]
  [essFiniteType : Algebra.EssFiniteType ℂ E]
  coordinates : Fin (m + 1) → E
  coordinates_generate : IntermediateField.adjoin ℂ (Set.range coordinates) = ⊤
  trdeg_one : Algebra.trdeg ℂ E = 1
  parameter : E
  parameter_transcendental : Transcendental ℂ parameter
  [parameterFinite : FiniteDimensional (IntermediateField.adjoin ℂ {parameter}) E]
  normalization : parameterCurve parameter parameter_transcendental ⟶ C.scheme
  [normalizationFinite : IsFinite normalization]
  normalization_over : normalization ≫ C.embedding ≫ pB =
    parameterCurveStructureMap parameter parameter_transcendental
  chart : C.scheme.Opens
  chart_nonempty : chart ≠ ⊥
  [chartIso : IsIso (normalization ∣_ chart)]
  generic_coordinates : parameterCurveGenericPoint parameter parameter_transcendental ≫
      (normalization ≫ C.embedding ≫ π) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval coordinates).toRingHom) ≫ j

theorem exists_modelData {B X : Scheme.{0}}
    (pX : X ⟶ CompactLogJetIdeal.base) [IsProper pX]
    (π : B ⟶ X) [IsProper π]
    (j : CompactLogJetIdeal.affineSpace m ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ pX = CompactLogJetIdeal.structureMap m)
    (I : X.IdealSheafData) (hπ : IsBlowup I π)
    (hclosed : ∀ x : X, x ∈ I.support → IsClosed ({x} : Set X))
    (C : IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x})
    (hm : ∃ c : C.scheme, (C.embedding ≫ π) c ∈ j.opensRange) :
    Nonempty (ModelData (π ≫ pX) π j C) := by
  classical
  let pB := π ≫ pX
  let IC := CurveBlowupImage.imageCurve π C hn
  let sourceStructure := C.embedding ≫ pB
  let imageStructure := IC.embedding ≫ pX
  letI sourceAlgebra : Algebra ℂ C.scheme.functionField :=
    IntegralAffineOpenDimension.functionFieldAlgebra sourceStructure
  letI imageAlgebra : Algebra ℂ IC.scheme.functionField :=
    IntegralAffineOpenDimension.functionFieldAlgebra imageStructure
  let U := I.support.compl
  letI : IsIso (π ∣_ U) := CurveBlowupImage.blowup_restrict_isIso hπ
  have hU : ∃ a : C.scheme, (C.embedding ≫ π) a ∈ U :=
    CurveBlowupImage.exists_image_outside_closed_points (C.embedding ≫ π)
      I.support hclosed hn
  let iso := CurveBlowupImage.imageFunctionFieldIso π C hn U hU
  have hiso := CurveBlowupImage.imageFunctionFieldIso_generic π C hn U hU
  let equiv : IC.scheme.functionField ≃ₐ[ℂ] C.scheme.functionField :=
    fieldAlgEquiv imageStructure sourceStructure iso (by
      simpa only [imageStructure, sourceStructure, pB, Category.assoc] using
        congrArg (fun h => h ≫ pX) hiso)
  let AP := affinePart IC.embedding j
  let presentation := affinePresentation IC.embedding j
  have hmeet : ∃ a : IC.scheme, IC.embedding a ∈ j.opensRange := by
    obtain ⟨a, ha⟩ := hm
    refine ⟨CurveBlowupImage.imageMap π C hn a, ?_⟩
    change IC.embedding (CurveBlowupImage.imageMap π C hn a) ∈ j.opensRange
    dsimp only [IC]
    simpa only [← Scheme.Hom.comp_apply, CurveBlowupImage.imageMap_comp] using ha
  letI : Nonempty AP.1 := affinePart_nonempty _ _ hmeet
  let iz := CurveImageAffineCoordinates.coordinates AP presentation
  let z : Fin (m + 1) → C.scheme.functionField := equiv ∘ iz
  have ho := affinePresentation_over pX IC.embedding j hj
  obtain ⟨ht, hd, hgen⟩ := CurveImageAffineCoordinates.field_properties
    imageStructure IC.dimension AP presentation ho
  letI := ht
  obtain ⟨heft, htrdeg, hzgen⟩ :=
    transport_field_properties equiv iz hd hgen
  letI := heft
  let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ C.scheme.functionField htrdeg
  obtain ⟨i, hi⟩ := CurveInequality.nonconstant_coordinates z hzgen htrdeg
  let f := z i
  have hf : Transcendental ℂ f := hi
  letI := hfinite f hf
  have hzmap : Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℂ) z).toRingHom) ≫ j =
      C.scheme.fromSpecStalk (genericPoint C.scheme) ≫ C.embedding ≫ π := by
    have himage := CurveImageAffineCoordinates.coordinates_generic_map
      imageStructure AP presentation ho j IC.embedding (affinePresentation_comp _ _)
    have he : (MvPolynomial.aeval (R := ℂ) z).toRingHom =
        iso.hom.hom.comp (MvPolynomial.aeval (R := ℂ) iz).toRingHom := by
      apply congrArg AlgHom.toRingHom
        (show MvPolynomial.aeval (R := ℂ) z =
          equiv.toAlgHom.comp (MvPolynomial.aeval (R := ℂ) iz) from ?_)
      apply MvPolynomial.algHom_ext
      intro l
      simp only [MvPolynomial.aeval_X, AlgHom.comp_apply]
      rfl
    rw [he, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc]
    rw [show Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℂ) iz).toRingHom) ≫ j =
      IC.scheme.fromSpecStalk (genericPoint IC.scheme) ≫ IC.embedding from himage]
    exact hiso
  obtain ⟨g, hg, hgeneric, hgfinite, W, hW, hWiso⟩ :=
    CurveNormalizationMorphism.exists_intrinsic_normalization_morphism
      sourceStructure C.dimension f hf
  letI := hgfinite
  letI := hWiso
  have hWne : W ≠ ⊥ := by
    intro he
    simp only [he, Opens.mem_bot] at hW
  have hc : parameterCurveGenericPoint f hf ≫ (g ≫ C.embedding ≫ π) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j := by
    rw [← Category.assoc, ← Category.assoc, hgeneric]
    exact hzmap.symm
  exact ⟨{ E := C.scheme.functionField
           field := inferInstance
           algebra := inferInstance
           essFiniteType := heft
           coordinates := z
           coordinates_generate := hzgen
           trdeg_one := htrdeg
           parameter := f
           parameter_transcendental := hf
           parameterFinite := inferInstance
           normalization := g
           normalizationFinite := hgfinite
           normalization_over := hg
           chart := W
           chart_nonempty := hWne
           chartIso := hWiso
           generic_coordinates := hc }⟩

namespace Weighted
open Global.Weighted
open OAI.PiExponentSeshadri.BlowupGluing

variable (w v : Fin (m + 1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)

theorem center_point_isClosed {K : ℕ} (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ)
    (x : compactification w v hw hv)
    (hx : x ∈ (centerIdeal w v hw hv y c).support) :
    IsClosed ({x} : Set (compactification w v hw hv)) := by
  change x ∈ ((centerIdeal w v hw hv y c).support : Set _) at hx
  rw [centerIdeal_support] at hx
  obtain ⟨k, z, rfl⟩ := Set.mem_iUnion.mp hx
  let q := pointAt (y k) (c k) ≫ chart w v hw hv
  letI : IsClosedImmersion q := CompactJetIdeal.section_isClosedImmersion
    (structureMorphism w v hw hv) q (by
      dsimp [q]
      rw [Category.assoc, chart_over, pointAt_section])
  have he : Set.range q = {q z} := by
    ext x
    constructor
    · rintro ⟨z', rfl⟩
      exact congrArg q (Subsingleton.elim z' z)
    · rintro rfl
      exact ⟨z, rfl⟩
  rw [← he]
  exact q.isClosedEmbedding.isClosed_range

theorem nonnegative_separated_curve_degrees {K : ℕ}
    (y : Fin K → ℂ) (hy0 : ∀ j, y j ≠ 0) (hy : Function.Injective y)
    (c : Fin K → Fin m → ℂ) (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ) * (1 + 3 * (sigma : ℝ)) ^ (m + 1) *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      PersistentWeightComparison.comparisonConstant m sigma *
        (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
    (hratio : ∀ i : Fin m, (1 + (sigma : ℝ)) * (w i.succ : ℝ) < v i.succ) :
    NonnegativeSeparatedCurveDegrees w v hw hv y c (sigma : ℝ) := by
  classical
  let I := centerIdeal w v hw hv y c
  let π := projection I
  let p := π ≫ structureMorphism w v hw hv
  let L := hyperplane w v hw hv
  let A := L.pullback π
  let J := exceptionalLineBundle I
  letI : IsProper p := inferInstance
  letI : CompactSpace (compactification w v hw hv) :=
    QuasiCompact.compactSpace_of_compactSpace (structureMorphism w v hw hv)
  obtain ⟨a, ha, hH⟩ := exists_ample_exceptional_power_gt_one I
    (centerIdeal_support_ne_top w v hw hv y hy0 c) L (hyperplane_ample w v hw hv)
  let H := (A.pow a).tensor J
  change H.IsAmple at hH
  intro C
  change 0 ≤ (curveDegree p A C : ℝ) +
    (1 + (sigma : ℝ)) * (curveDegree p J C : ℝ)
  obtain ⟨ht, hp⟩ := BlowupCurveMargin.curve_degree_laws p H hH C
  by_cases hc : ∃ x, Set.range (C.embedding ≫ π) ⊆ ({x} : Set _)
  · obtain ⟨x, hx⟩ := hc
    have hA := ConstantPullbackDegree.curveDegree_eq_zero_of_contracted p L π C x hx
    have hpos := curveDegree_pos_of_ample p H hH C
    change 0 < curveDegree p ((A.pow a).tensor J) C at hpos
    rw [ht, hp, hA, mul_zero, zero_add] at hpos
    rw [hA]
    have hJ : (0 : ℝ) ≤ curveDegree p J C := by exact_mod_cast hpos.le
    exact add_nonneg (by norm_num) (mul_nonneg (by exact_mod_cast (show (0 : ℚ) ≤ 1 + sigma by linarith)) hJ)
  · by_cases hm : ∃ q : C.scheme, (C.embedding ≫ π) q ∈ (chart w v hw hv).opensRange
    · obtain ⟨r⟩ := exists_modelData (structureMorphism w v hw hv) π
        (chart w v hw hv) (chart_over w v hw hv) I (isBlowup I)
        (center_point_isClosed w v hw hv y c) C hc hm
      letI := r.field
      letI := r.algebra
      letI := r.essFiniteType
      letI := r.parameterFinite
      letI := r.normalizationFinite
      letI := r.chartIso
      let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ r.E r.trdeg_one
      let hres := PlaceLocalRing.residue_integral r.trdeg_one.le
      let hz := CurveInequality.nonconstant_coordinates r.coordinates
        r.coordinates_generate r.trdeg_one
      let S : ℝ := ∑ q ∈ placesAt hfinite r.coordinates y c hz,
        (familyContactAt hres hfinite r.coordinates y hy0 c hz v q : ℝ)
      let D : ℝ := CurveContactSum.weightedDegree hfinite r.coordinates w
      have hcoord : parameterCurveGenericPoint r.parameter r.parameter_transcendental ≫
          (r.normalization ≫ C.embedding ≫ π) =
          CurveMonomialMap.genericMonomialMap (exponents w v hw hv)
            (constantIndex w v hw hv) ((scale w v hw hv).exponents_constant hw)
            (coordinateIndex w v hw hv) ((scale w v hw hv).exponents_coordinate hw)
            r.coordinates := by
        have heval : (MvPolynomial.aeval r.coordinates).toRingHom =
            MvPolynomial.eval₂Hom (algebraMap ℂ r.E) r.coordinates := by
          apply RingHom.ext
          intro P
          exact MvPolynomial.aeval_def r.coordinates P
        simpa only [CurveMonomialMap.genericMonomialMap, chart, heval] using
          r.generic_coordinates
      have hA : (curveDegree p A C : ℝ) = ((scale w v hw hv).radius : ℝ) * D := by
        exact CurveNormalizedDegreeTransfer.weighted_curveDegree
          (exponents w v hw hv) r.coordinates (constantIndex w v hw hv)
          ((scale w v hw hv).exponents_constant hw)
          (coordinateIndex w v hw hv) ((scale w v hw hv).exponents_coordinate hw)
          p H hH C r.parameter r.parameter_transcendental r.normalization
          r.normalization_over r.chart r.chart_nonempty π hcoord w hw
          (by exact_mod_cast (scale w v hw hv).radius_pos)
          (scale w v hw hv).degreePowers (scale w v hw hv).degreePowers_eq
          ((scale w v hw hv).pureIndex hw)
          ((scale w v hw hv).exponents_pure hw) ((scale w v hw hv).budget hw) hfinite
      have hJ : (curveDegree p J C : ℝ) = -((scale w v hw hv).radius : ℝ) * S := by
        have hd := CurveNormalizedDegreeTransfer.curveDegree_eq_normalized p H hH C
          r.parameter r.parameter_transcendental r.normalization r.normalization_over
          r.chart r.chart_nonempty J
        have hn := compactIdealAt_degree_eq_neg_contact_sum r.parameter r.parameter_transcendental
          y hy0 hy c (logCutoff v hv) (scale w v hw hv).jetPowers
          (scale w v hw hv).jetPowers_pos v hv (scale w v hw hv).radius
          (scale w v hw hv).jetPowers_eq (logCutoff_strict v hv)
          (chart w v hw hv) (structureMorphism w v hw hv) (chart_over w v hw hv)
          π J (exceptionalInclusion I) (exceptional_presents I)
          (r.normalization ≫ C.embedding) r.coordinates hz
          (by simpa only [Category.assoc] using r.generic_coordinates) hres hfinite
        have hn' := congrArg (fun q : ℚ => (q : ℝ)) hn
        simp only [Rat.cast_intCast, Rat.cast_neg, Rat.cast_mul, Rat.cast_sum] at hn'
        exact (congrArg (fun q : ℤ => (q : ℝ)) hd).trans hn'
      have hb : (1 + (sigma : ℝ)) * S ≤ D := weighted_curve_inequality_at
        r.coordinates y hy0 hy c r.coordinates_generate r.trdeg_one
        w v hw hv sigma hsigma hvol hseparated hratio
      rw [hA, hJ]
      have hR : (0 : ℝ) ≤ (scale w v hw hv).radius := by
        exact_mod_cast (scale w v hw hv).radius_pos.le
      have hb' := mul_le_mul_of_nonneg_left hb hR
      nlinarith
    · have havoid : ∀ q : C.scheme, (C.embedding ≫ π) q ∉ I.support := by
        intro q hq
        exact hm ⟨q, centerIdeal_support_subset_chart w v hw hv y c hq⟩
      have hJ := BlowupCurveMargin.curveDegree_zero_of_frame p J C
        (InvertibleIdealAway.pullbackIsoOfAvoids I π J (exceptionalInclusion I)
          (exceptional_presents I) C.embedding havoid)
      have hpos := curveDegree_pos_of_ample p H hH C
      change 0 < curveDegree p ((A.pow a).tensor J) C at hpos
      rw [ht, hp, hJ, add_zero] at hpos
      have ha' : (0 : ℤ) < a := by exact_mod_cast (Nat.zero_lt_of_lt ha)
      have hA := (mul_pos_iff_of_pos_left ha').mp hpos
      rw [hJ]
      simpa using (show (0 : ℝ) ≤ curveDegree p A C by exact_mod_cast hA.le)

include hw hv in
theorem eventual_interpolation_of_separated_weights (K : ℕ) (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ) * (1 + 3 * (sigma : ℝ)) ^ (m + 1) *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      PersistentWeightComparison.comparisonConstant m sigma *
        (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
    (hratio : ∀ i : Fin m, (1 + (sigma : ℝ)) * (w i.succ : ℝ) < v i.succ) :
    EventualDistinctMultiplicativeInterpolation m K w v := by
  apply Global.Weighted.eventual_interpolation_of_curve_degrees w v hw hv K
    (sigma : ℝ) (by exact_mod_cast hsigma)
  intro y c hy0 hy
  exact nonnegative_separated_curve_degrees w v hw hv y hy0 hy c sigma hsigma
    hvol hseparated hratio

end Weighted

#print axioms localIdealAt_length_eq_logContactAt
#print axioms compactIdealAt_degree_eq_neg_contact_sum
#print axioms exists_modelData
#print axioms Weighted.eventual_interpolation_of_separated_weights

end
end OAI.PiExponent.DistinctMultiplicative.Degree
