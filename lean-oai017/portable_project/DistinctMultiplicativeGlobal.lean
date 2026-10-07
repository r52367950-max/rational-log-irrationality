import DistinctMultiplicativeStatement
import DistinctMultiplicativeAmple
import OAI.NumberTheory.PiExponent.Jets.AffineJetPackets
import OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientInterface
import OAI.NumberTheory.PiExponent.Jets.AffineJetPolynomial
import OAI.NumberTheory.PiExponent.Approximation.WeightedGlobalSectionBound
import OAI.NumberTheory.PiExponent.Ampleness.WeightedProjectiveAmple
import OAI.NumberTheory.PiExponent.Ampleness.WeightedAffineFrame

/-!
Actual algebraic center ideals and the global-section endgame for A-r2.
The definitions here use the literal logarithmic jet map at arbitrary nonzero
multiplicative centers. No interpolation statement is introduced as an axiom.
The final geometric curve-degree condition remains visible until the new
curve-contact proof has been identified with degrees on this blowup.
-/

namespace OAI.PiExponent.DistinctMultiplicative.Global

noncomputable section
open AlgebraicGeometry CategoryTheory Filter
open scoped BigOperators
open OAI.PiExponentSeshadri.Geometry
open OAI.PiExponent.GeometrySupport
open OAI.PiExponent.NumericalAmpleness
open OAI.PiExponent.CompactJetPolynomial
open OAI.PiExponent.CompactLogJetIdeal

variable {m : ℕ}

/-- The actual affine center, including its multiplicative coordinate. -/
def centerAt (y : ℂ) (c : Fin m → ℂ) : Fin (m + 1) → ℂ := Fin.cases y c

private theorem scaleY_comp_inverse (y : ℂ) (hy : y ≠ 0) :
    (scaleY y).comp (scaleY y⁻¹) =
      AlgHom.id ℂ (PiExponentApprox.FramePolynomial m) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero =>
    simp only [AlgHom.comp_apply, scaleY_Y, map_mul, MvPolynomial.algHom_C,
      MvPolynomial.algebraMap_eq, AlgHom.id_apply]
    rw [← mul_assoc, ← MvPolynomial.C_mul]
    simp [hy]
  | succ i => simp

theorem scaleY_surjective (y : ℂ) (hy : y ≠ 0) :
    Function.Surjective (scaleY (m := m) y) := by
  intro P
  exact ⟨scaleY y⁻¹ P, AlgHom.congr_fun (scaleY_comp_inverse y hy) P⟩

theorem eval_centerAt_scaleY (y : ℂ) (c : Fin m → ℂ) :
    (MvPolynomial.aeval (center c)).comp (scaleY y) =
      MvPolynomial.aeval (centerAt y c) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero => simp [center, centerAt]
  | succ i => simp [center, centerAt]

/-- Pulling back the original pure-power ideal through Y ↦ yY gives the
algebraic local ideal in the coordinates Y/y-1, Xi-ci-G(Y/y-1).
-/
def powerIdealAt (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) : Ideal (PiExponentApprox.FramePolynomial m) :=
  (powerIdeal c (logPolynomials T) e).comap (scaleY y).toRingHom

theorem powerIdealAt_eq_map_inverse (y : ℂ) (hy : y ≠ 0) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ) :
    powerIdealAt y c T e =
      (powerIdeal c (logPolynomials T) e).map (scaleY y⁻¹).toRingHom := by
  ext P
  change scaleY y P ∈ powerIdeal c (logPolynomials T) e ↔ _
  rw [Ideal.mem_map_iff_of_surjective (scaleY y⁻¹).toRingHom
    (scaleY_surjective y⁻¹ (inv_ne_zero hy))]
  constructor
  · intro hP
    refine ⟨scaleY y P, hP, ?_⟩
    have h := AlgHom.congr_fun (scaleY_comp_inverse (m := m) y⁻¹ (inv_ne_zero hy)) P
    simpa using h
  · rintro ⟨Q, hQ, rfl⟩
    have h := AlgHom.congr_fun (scaleY_comp_inverse (m := m) y hy) Q
    change scaleY y (scaleY y⁻¹ Q) = Q at h
    change scaleY y (scaleY y⁻¹ Q) ∈ powerIdeal c (logPolynomials T) e
    rw [h]
    exact hQ

/-- These are the polynomial coordinates actually used for the new centers. -/
def coordinatesAt (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ)
    (i : Fin (m + 1)) : PiExponentApprox.FramePolynomial m :=
  scaleY y⁻¹ (coordinates c (logPolynomials T) i)

@[simp] theorem coordinatesAt_zero (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ) :
    coordinatesAt y c T 0 = MvPolynomial.C y⁻¹ * MvPolynomial.X 0 - 1 := by
  simp [coordinatesAt, coordinates]

@[simp] theorem coordinatesAt_succ (y : ℂ) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (i : Fin m) :
    coordinatesAt y c T i.succ = MvPolynomial.X i.succ - MvPolynomial.C (c i) -
      Polynomial.aeval (MvPolynomial.C y⁻¹ * MvPolynomial.X 0 - 1)
        (logPolynomials T i) := by
  simp only [coordinatesAt, coordinates, PiExponent.AlgebraicJetPackets.inverseTriangularMap_X_succ,
    map_sub, scaleY_X, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
    ← Polynomial.aeval_algHom_apply, scaleY_Y, map_one]

theorem powerIdealAt_eq_span (y : ℂ) (hy : y ≠ 0) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ) :
    powerIdealAt y c T e = Ideal.span (Set.range (fun i => coordinatesAt y c T i ^ e i)) := by
  rw [powerIdealAt_eq_map_inverse y hy, powerIdeal, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  exact map_pow (scaleY y⁻¹) (coordinates c (logPolynomials T) i) (e i)

theorem radical_powerIdealAt (y : ℂ) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ) (he : ∀ i, 0 < e i) :
    (powerIdealAt y c T e).radical =
      OAI.PiExponent.WeightedBezout.pointIdeal (centerAt y c) := by
  rw [powerIdealAt, ← Ideal.comap_radical,
    radical_powerIdeal c (logPolynomials T) (logPolynomials_eval_zero T) e he]
  ext P
  change MvPolynomial.aeval (center c) (scaleY y P) = 0 ↔
    MvPolynomial.aeval (centerAt y c) P = 0
  rw [← AlgHom.comp_apply, eval_centerAt_scaleY]

def pointAt (y : ℂ) (c : Fin m → ℂ) :
    base ⟶ affineSpace m :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (centerAt y c)).toRingHom)

def centerPointAt (y : ℂ) (c : Fin m → ℂ) :
    PrimeSpectrum (PiExponentApprox.FramePolynomial m) :=
  ⟨OAI.PiExponent.WeightedBezout.pointIdeal (centerAt y c), inferInstance⟩

theorem pointAt_section (y : ℂ) (c : Fin m → ℂ) :
    pointAt y c ≫ structureMap m = 𝟙 base := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap ℂ (coordinateRing m)) ≫
      CommRingCat.ofHom (MvPolynomial.aeval (centerAt y c)).toRingHom =
      𝟙 (CommRingCat.of ℂ) := by
    ext a
    simp
  rw [h, Spec.map_id]

theorem range_pointAt (y : ℂ) (c : Fin m → ℂ) :
    Set.range (pointAt y c) = {centerPointAt y c} := by
  change Set.range (PrimeSpectrum.comap
    (MvPolynomial.aeval (centerAt y c)).toRingHom) = _
  rw [range_comap_of_surjective _ _ (by
    intro a
    exact ⟨MvPolynomial.C a, by simp⟩)]
  exact PrimeSpectrum.zeroLocus_eq_singleton
    (PiExponent.WeightedBezout.pointIdeal (centerAt y c))

theorem zeroLocus_powerIdealAt (y : ℂ) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ) (he : ∀ i, 0 < e i) :
    PrimeSpectrum.zeroLocus (powerIdealAt y c T e : Set _) =
      {centerPointAt y c} := by
  rw [← PrimeSpectrum.zeroLocus_radical, radical_powerIdealAt y c T e he]
  exact PrimeSpectrum.zeroLocus_eq_singleton _

theorem formalJetAt_mem_weighted_of_mem_pow
    (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (P : PiExponentApprox.FramePolynomial m) (hP : P ∈ powerIdealAt y c T e ^ n) :
    formalJetAt y c P ∈ JetGeometry.rationalWeightedIdeal v hv (n * R) := by
  apply formalJet_mem_weighted_of_mem_pow c T e v hv hT R he n (scaleY y P)
  exact Ideal.le_comap_pow (scaleY y).toRingHom n hP

theorem formalJetAt_packet_surjective (y : ℂ) (hy : y ≠ 0)
    (c : Fin m → ℂ) (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    Function.Surjective (fun P : PiExponentApprox.FramePolynomial m =>
      JetGeometry.rationalCoefficientPacket v H (formalJetAt y c P)) := by
  intro packet
  obtain ⟨Q, hQ⟩ := PiExponent.AlgebraicJetPackets.formalJet_packet_surjective c v hv H packet
  obtain ⟨P, hP⟩ := scaleY_surjective y hy Q
  exact ⟨P, by simpa [formalJetAt, hP] using hQ⟩

theorem powerIdealAt_pairwise_isCoprime {J : Type*}
    (y : J → ℂ) (hy : Function.Injective y) (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ) (he : ∀ i, 0 < e i) :
    Pairwise (fun j k => IsCoprime (powerIdealAt (y j) (c j) T e)
      (powerIdealAt (y k) (c k) T e)) := by
  intro j k hjk
  have hp : IsCoprime
      (PiExponent.WeightedBezout.pointIdeal (centerAt (y j) (c j)))
      (PiExponent.WeightedBezout.pointIdeal (centerAt (y k) (c k))) := by
    apply Ideal.isCoprime_of_isMaximal
    intro heq
    have hcent := PiExponent.JetPowerIdealCoprime.pointIdeal_injective heq
    have hY : y j = y k := by simpa [centerAt] using congrFun hcent 0
    exact hjk (hy hY)
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply Ideal.radical_eq_top.mp
  rw [Ideal.radical_sup, radical_powerIdealAt _ _ T e he,
    radical_powerIdealAt _ _ T e he, hp.sup_eq, Ideal.radical_top]

def polynomialIdealAt {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) : Ideal (PiExponentApprox.FramePolynomial m) :=
  ∏ j, powerIdealAt (y j) (c j) T e

theorem polynomialIdealAt_pow_le {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (n : ℕ) (j : J) :
    polynomialIdealAt y c T e ^ n ≤ powerIdealAt (y j) (c j) T e ^ n := by
  classical
  apply pow_le_pow_left'
  exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ j))

theorem formalJetAt_packet_eq_of_sub_mem_pow
    (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (P Q : PiExponentApprox.FramePolynomial m)
    (hPQ : P - Q ∈ powerIdealAt y c T e ^ n) :
    JetGeometry.rationalCoefficientPacket v (n * R) (formalJetAt y c P) =
      JetGeometry.rationalCoefficientPacket v (n * R) (formalJetAt y c Q) := by
  apply (PiExponent.FormalLogTruncation.rationalCoefficientPacket_eq_iff
    v hv (n * R) _ _).mpr
  simpa only [map_sub] using formalJetAt_mem_weighted_of_mem_pow
    y c T e v hv hT R he n (P - Q) hPQ

/-- Unrestricted affine polynomial packets are independently constructed by
the Chinese remainder theorem on the actual distinct multiplicative centers.
This assertion imposes no weighted source bound and therefore does not assume A.
-/
theorem formalJetAt_packets_surjective {J : Type*} [Fintype J]
    (y : J → ℂ) (hy0 : ∀ j, y j ≠ 0) (hy : Function.Injective y)
    (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 < v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ) :
    Function.Surjective (fun P : PiExponentApprox.FramePolynomial m => fun j =>
      JetGeometry.rationalCoefficientPacket v (n * R)
        (formalJetAt (y j) (c j) P)) := by
  classical
  intro packets
  choose P hP using fun j => formalJetAt_packet_surjective
    (y j) (hy0 j) (c j) v hv (n * R) (packets j)
  have hcop : Pairwise (fun j k => IsCoprime
      (powerIdealAt (y j) (c j) T e ^ n)
      (powerIdealAt (y k) (c k) T e ^ n)) :=
    fun j k hjk => (powerIdealAt_pairwise_isCoprime y hy c T e hepos hjk).pow
  obtain ⟨Q, hQ⟩ := Ideal.exists_forall_sub_mem_ideal hcop P
  refine ⟨Q, ?_⟩
  funext j
  exact (formalJetAt_packet_eq_of_sub_mem_pow (y j) (c j) T e v
    (fun i => (hv i).le) hT R he n Q (P j) (hQ j)).trans (hP j)

theorem packets_surjective_of_polynomialIdealAt_quotient
    {α J : Type*} [Fintype J]
    (y : J → ℂ) (hy0 : ∀ j, y j ≠ 0) (hy : Function.Injective y)
    (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 < v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (f : α → PiExponentApprox.FramePolynomial m)
    (hf : Function.Surjective (fun a =>
      Ideal.Quotient.mk (polynomialIdealAt y c T e ^ n) (f a))) :
    Function.Surjective (fun a j => JetGeometry.rationalCoefficientPacket v (n * R)
      (formalJetAt (y j) (c j) (f a))) := by
  intro packets
  obtain ⟨P, hP⟩ := formalJetAt_packets_surjective
    y hy0 hy c T e hepos v hv hT R he n packets
  obtain ⟨a, ha⟩ := hf (Ideal.Quotient.mk _ P)
  have hdiff : f a - P ∈ polynomialIdealAt y c T e ^ n := Ideal.Quotient.eq.mp ha
  refine ⟨a, ?_⟩
  funext j
  exact (formalJetAt_packet_eq_of_sub_mem_pow (y j) (c j) T e v
    (fun i => (hv i).le) hT R he n (f a) P
    (polynomialIdealAt_pow_le y c T e n j hdiff)).trans (congrFun hP j)

theorem zeroLocus_finset_prod_powerIdealAt {J : Type*} (s : Finset J)
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (he : ∀ i, 0 < e i) :
    PrimeSpectrum.zeroLocus
      (((∏ j ∈ s, powerIdealAt (y j) (c j) T e) :
        Ideal (PiExponentApprox.FramePolynomial m)) : Set _) =
      (fun j => centerPointAt (y j) (c j)) '' (s : Set J) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, PrimeSpectrum.zeroLocus_mul,
      zeroLocus_powerIdealAt (y j) (c j) T e he, ih]
    simp

def affineIdealAt {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) : (affineSpace m).IdealSheafData :=
  OAI.PiExponentSeshadri.IdealPullback.specIdeal (polynomialIdealAt y c T e)

theorem support_affineIdealAt {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (he : ∀ i, 0 < e i) :
    ((affineIdealAt y c T e).support : Set (affineSpace m)) =
      ⋃ j, Set.range (pointAt (y j) (c j)) := by
  rw [affineIdealAt, support_specIdeal]
  have hz := zeroLocus_finset_prod_powerIdealAt Finset.univ y c T e he
  change PrimeSpectrum.zeroLocus
    (polynomialIdealAt y c T e : Set (PiExponentApprox.FramePolynomial m)) = _
  rw [show PrimeSpectrum.zeroLocus
    (polynomialIdealAt y c T e : Set (PiExponentApprox.FramePolynomial m)) =
    Set.range (fun j => centerPointAt (y j) (c j)) by simpa [polynomialIdealAt] using hz]
  simp only [range_pointAt]
  ext p
  constructor
  · rintro ⟨j, rfl⟩
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_singleton _⟩
  · intro hp
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp
    exact ⟨j, (Set.mem_singleton_iff.mp hj).symm⟩

def compactIdealAt {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) {X : Scheme} (j : affineSpace m ⟶ X) :
    X.IdealSheafData :=
  PiExponent.CompactJetIdeal.extend (affineIdealAt y c T e) j

theorem restrict_compactIdealAt {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) {X : Scheme}
    (j : affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j] :
    (compactIdealAt y c T e j).comap j = affineIdealAt y c T e :=
  PiExponent.CompactJetIdeal.restrict_extend _ j

theorem support_compactIdealAt {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (he : ∀ i, 0 < e i)
    {X : Scheme} (j : affineSpace m ⟶ X) [QuasiCompact j]
    (π : X ⟶ base) [IsSeparated π] (hπ : j ≫ π = structureMap m) :
    ((compactIdealAt y c T e j).support : Set X) =
      ⋃ a, Set.range (pointAt (y a) (c a) ≫ j) := by
  rw [compactIdealAt, PiExponent.CompactJetIdeal.support_extend (affineIdealAt y c T e)
    j π (fun a => pointAt (y a) (c a)) (fun a => by
      rw [Category.assoc, hπ, pointAt_section]) (support_affineIdealAt y c T e he),
    support_affineIdealAt y c T e he, Set.image_iUnion]
  congr 1
  funext a
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]

theorem formalPackets_surjective_of_jetRestrictionAt
    {X : Scheme} {J : Type} [Fintype J]
    (y : J → ℂ) (hy0 : ∀ j, y j ≠ 0) (hy : Function.Injective y)
    (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 < v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (j : affineSpace m ⟶ X) [IsOpenImmersion j]
    (I : X.IdealSheafData) (A : LineBundle X)
    (frame : PiExponent.AffineJetCoefficientInterface.Frame j A)
    (hI : I.comap j = affineIdealAt y c T e)
    (hs : ((I ^ n).support : Set X) ⊆ j.opensRange)
    (hjet : Function.Surjective (PiExponent.BlowupJetSurjectivity.jetRestriction I A n)) :
    Function.Surjective (fun s : PiExponent.AffineJetCoefficientInterface.Sections A n =>
      fun k => JetGeometry.rationalCoefficientPacket v (n * R)
        (formalJetAt (y k) (c k)
          (PiExponent.AffineJetCoefficientInterface.coefficient j A n frame s))) := by
  apply packets_surjective_of_polynomialIdealAt_quotient
    y hy0 hy c T e hepos v hv hT R he n
    (PiExponent.AffineJetCoefficientInterface.coefficient j A n frame)
  exact PiExponent.AffineJetPolynomial.polynomialQuotient_surjective_of_jetRestriction
    I A n j frame (polynomialIdealAt y c T e) hI hs hjet

namespace Weighted

variable (W V : Fin (m + 1) → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)

def scale : PiExponent.WeightedGeometryScale.Scale W V :=
  PiExponent.WeightedGeometryScale.chooseScale W V hW hV

abbrev Index := (scale W V hW hV).Index
abbrev exponents : Index W V hW hV → Fin (m + 1) →₀ ℕ :=
  (scale W V hW hV).exponents
abbrev constantIndex : Index W V hW hV :=
  (scale W V hW hV).constantIndex hW
abbrev coordinateIndex : Fin (m + 1) → Index W V hW hV :=
  (scale W V hW hV).coordinateIndex hW

instance index_nonempty : Nonempty (Index W V hW hV) :=
  ⟨constantIndex W V hW hV⟩

abbrev compactification : Scheme :=
  Proj (PiExponent.WeightedCompactification.imageGrade (R := ℂ) (exponents W V hW hV))

def structureMorphism : compactification W V hW hV ⟶ base :=
  PiExponent.WeightedCompactification.projection (exponents W V hW hV)

instance structure_proper : IsProper (structureMorphism W V hW hV) := by
  dsimp [structureMorphism]
  infer_instance

def chart : affineSpace m ⟶ compactification W V hW hV :=
  PiExponent.WeightedCompactification.affineChartMap (exponents W V hW hV)
    (constantIndex W V hW hV) ((scale W V hW hV).exponents_constant hW)
    (coordinateIndex W V hW hV) ((scale W V hW hV).exponents_coordinate hW)

instance chart_openImmersion : IsOpenImmersion (chart W V hW hV) := by
  dsimp [chart]
  infer_instance

instance compactification_nonempty : Nonempty (compactification W V hW hV) :=
  ⟨chart W V hW hV
    ⟨PiExponent.WeightedBezout.pointIdeal (0 : Fin (m + 1) → ℂ), inferInstance⟩⟩

instance compactification_integral : IsIntegral (compactification W V hW hV) := by
  infer_instance

instance compactification_locallyNoetherian :
    IsLocallyNoetherian (compactification W V hW hV) :=
  LocallyOfFiniteType.isLocallyNoetherian (structureMorphism W V hW hV)

instance chart_quasiCompact : QuasiCompact (chart W V hW hV) := by infer_instance

theorem chart_over : chart W V hW hV ≫ structureMorphism W V hW hV = structureMap m :=
  PiExponent.CurveMonomialMap.affineChartMap_projection (exponents W V hW hV)
    (constantIndex W V hW hV) ((scale W V hW hV).exponents_constant hW)
    (coordinateIndex W V hW hV) ((scale W V hW hV).exponents_coordinate hW)

def hyperplane : LineBundle (compactification W V hW hV) :=
  PiExponent.WeightedCompactification.lineBundle (exponents W V hW hV)

theorem hyperplane_ample : (hyperplane W V hW hV).IsAmple :=
  PiExponent.WeightedCompactification.lineBundle_ample (exponents W V hW hV)

def logCutoff : Fin m → ℕ :=
  (PiExponent.WeightedGeometryScale.exists_log_cutoff V (hV 0)).choose

theorem logCutoff_strict (i : Fin m) :
    V i.succ < (logCutoff V hV i : ℚ) * V 0 :=
  (PiExponent.WeightedGeometryScale.exists_log_cutoff V (hV 0)).choose_spec i

def centerIdeal {K : ℕ} (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) :
    (compactification W V hW hV).IdealSheafData :=
  compactIdealAt y c (logCutoff V hV) (scale W V hW hV).jetPowers (chart W V hW hV)

theorem centerIdeal_restrict {K : ℕ} (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) :
    (centerIdeal W V hW hV y c).comap (chart W V hW hV) =
      affineIdealAt y c (logCutoff V hV) (scale W V hW hV).jetPowers :=
  restrict_compactIdealAt _ _ _ _ _

theorem centerIdeal_support {K : ℕ} (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) :
    ((centerIdeal W V hW hV y c).support : Set (compactification W V hW hV)) =
      ⋃ k, Set.range (pointAt (y k) (c k) ≫ chart W V hW hV) :=
  support_compactIdealAt _ _ _ _ (scale W V hW hV).jetPowers_pos _
    (structureMorphism W V hW hV) (chart_over W V hW hV)

theorem centerIdeal_support_subset_chart {K : ℕ}
    (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) :
    ((centerIdeal W V hW hV y c).support : Set (compactification W V hW hV)) ⊆
      (chart W V hW hV).opensRange := by
  rw [centerIdeal_support]
  intro x hx
  obtain ⟨k, z, rfl⟩ := Set.mem_iUnion.mp hx
  exact ⟨pointAt (y k) (c k) z, rfl⟩

theorem affineFrame_exists :
    Nonempty (PiExponent.AffineJetCoefficientInterface.Frame
      (chart W V hW hV) (hyperplane W V hW hV)) := by
  exact PiExponent.WeightedAffineFrame.affineFrame_nonempty (R := ℂ)
    (exponents W V hW hV) (constantIndex W V hW hV)
    ((scale W V hW hV).exponents_constant hW)
    (coordinateIndex W V hW hV) ((scale W V hW hV).exponents_coordinate hW)

theorem eventual_section_supportBound :
    PiExponent.ProjectiveCoefficientBound.EventualBound
      (chart W V hW hV) (hyperplane W V hW hV)
      (fun i => (W i : ℝ)) (scale W V hW hV).radius := by
  apply PiExponent.WeightedGlobalSectionBound.eventual_supportBound (K := ℂ)
    (exponents W V hW hV) (constantIndex W V hW hV)
    ((scale W V hW hV).exponents_constant hW)
    (coordinateIndex W V hW hV) ((scale W V hW hV).exponents_coordinate hW)
    (fun i => (W i : ℝ)) (scale W V hW hV).radius
  intro i
  have hi := (scale W V hW hV).budget hW i
  have hi' : (∑ j, (W j : ℝ) * ((exponents W V hW hV i) j : ℝ)) ≤
      (scale W V hW hV).radius := by exact_mod_cast hi
  simpa [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_comm] using hi'

def origin : affineSpace m :=
  ⟨PiExponent.WeightedBezout.pointIdeal (0 : Fin (m + 1) → ℂ), inferInstance⟩

theorem origin_ne_centerPointAt (y : ℂ) (hy : y ≠ 0) (c : Fin m → ℂ) :
    origin (m := m) ≠ centerPointAt y c := by
  intro h
  have hx : MvPolynomial.X (0 : Fin (m + 1)) ∈ (origin (m := m)).asIdeal := by
    change MvPolynomial.aeval (0 : Fin (m + 1) → ℂ) (MvPolynomial.X 0) = 0
    simp
  rw [h] at hx
  change MvPolynomial.aeval (centerAt y c) (MvPolynomial.X 0) = 0 at hx
  exact hy (by simpa [centerAt] using hx)

theorem centerIdeal_support_ne_top {K : ℕ}
    (y : Fin K → ℂ) (hy0 : ∀ k, y k ≠ 0) (c : Fin K → Fin m → ℂ) :
    (centerIdeal W V hW hV y c).support ≠ ⊤ := by
  have havoid : chart W V hW hV (origin (m := m)) ∉
      (centerIdeal W V hW hV y c).support := by
    change chart W V hW hV (origin (m := m)) ∉
      ((centerIdeal W V hW hV y c).support : Set _)
    rw [centerIdeal_support]
    intro h
    obtain ⟨k, z, hz⟩ := Set.mem_iUnion.mp h
    have ho : pointAt (y k) (c k) z = origin (m := m) :=
      (chart W V hW hV).isOpenEmbedding.injective hz
    have hc : pointAt (y k) (c k) z = centerPointAt (y k) (c k) := by
      apply Set.mem_singleton_iff.mp
      erw [← range_pointAt]
      exact ⟨z, rfl⟩
    exact origin_ne_centerPointAt (y k) (hy0 k) (c k) (ho.symm.trans hc)
  intro h
  exact havoid (by rw [h]; trivial)

/-- The comparison of actual global sections with the bounded polynomial
source and actual logarithmic target is proved here, not left as a surjective
presentation hypothesis. Only scheme-theoretic jet restriction is an input.
-/
theorem eventual_packetMapAt_surjective_of_eventual_jetRestriction {K : ℕ}
    (y : Fin K → ℂ) (hy0 : ∀ k, y k ≠ 0) (hy : Function.Injective y)
    (c : Fin K → Fin m → ℂ)
    (hjet : ∀ᶠ n : ℕ in atTop, Function.Surjective
      (PiExponent.BlowupJetSurjectivity.jetRestriction
        (centerIdeal W V hW hV y c) (hyperplane W V hW hV) n)) :
    ∀ᶠ n : ℕ in atTop, Function.Surjective
      (packetMapAt W V ((n : ℚ) * (scale W V hW hV).radius) y c) := by
  obtain ⟨N, hN⟩ := eventual_section_supportBound W V hW hV
  obtain ⟨frame⟩ := affineFrame_exists W V hW hV
  filter_upwards [hjet, eventually_ge_atTop N] with n hn hnN
  have hs : (((centerIdeal W V hW hV y c) ^ n).support :
      Set (compactification W V hW hV)) ⊆
      ((chart W V hW hV).opensRange : Set (compactification W V hW hV)) := by
    cases n with
    | zero => simp
    | succ n => simpa using centerIdeal_support_subset_chart W V hW hV y c
  have he : ∀ i, ((scale W V hW hV).radius : ℚ) ≤
      ((scale W V hW hV).jetPowers i : ℚ) * V i := by
    intro i
    rw [mul_comm, (scale W V hW hV).jetPowers_eq]
  have hp := formalPackets_surjective_of_jetRestrictionAt
    y hy0 hy c (logCutoff V hV) (scale W V hW hV).jetPowers
    (scale W V hW hV).jetPowers_pos V hV
    (fun i => (logCutoff_strict V hV i).le) (scale W V hW hV).radius he n
    (chart W V hW hV) (centerIdeal W V hW hV y c) (hyperplane W V hW hV)
    frame (centerIdeal_restrict W V hW hV y c) hs hn
  intro packets
  obtain ⟨s, hs⟩ := hp packets
  let P := PiExponent.AffineJetCoefficientInterface.coefficient
    (chart W V hW hV) (hyperplane W V hW hV) n frame s
  have hP : WeightedSliceDegree.SupportBound (fun i => (W i : ℝ))
      (((n : ℚ) * (scale W V hW hV).radius : ℚ) : ℝ) P := by
    simpa only [Rat.cast_mul, Rat.cast_natCast] using hN n hnN frame s
  exact ⟨⟨P, hP⟩, hs⟩

def blowupStructure {K : ℕ} (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) :=
  OAI.PiExponentSeshadri.BlowupGluing.projection (centerIdeal W V hW hV y c) ≫
    structureMorphism W V hW hV

/-- A concrete final obligation expressed on the constructed blowup.
Unlike an interpolation hypothesis, it is solely a curve-degree inequality.
-/
def NonnegativeSeparatedCurveDegrees {K : ℕ}
    (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) (σ : ℝ) : Prop :=
  ∀ C : IntegralCurve
      (OAI.PiExponentSeshadri.BlowupGluing.scheme (centerIdeal W V hW hV y c)),
    0 ≤ (curveDegree (blowupStructure W V hW hV y c)
      ((hyperplane W V hW hV).pullback
        (OAI.PiExponentSeshadri.BlowupGluing.projection (centerIdeal W V hW hV y c))) C : ℝ) +
      (1 + σ) * (curveDegree (blowupStructure W V hW hV y c)
        (OAI.PiExponentSeshadri.BlowupGluing.exceptionalLineBundle
          (centerIdeal W V hW hV y c)) C : ℝ)

theorem eventual_packetMapAt_surjective_of_curve_degrees {K : ℕ}
    (y : Fin K → ℂ) (hy0 : ∀ k, y k ≠ 0) (hy : Function.Injective y)
    (c : Fin K → Fin m → ℂ) (σ : ℝ) (hσ : 0 < σ)
    (hn : NonnegativeSeparatedCurveDegrees W V hW hV y c σ) :
    ∀ᶠ n : ℕ in atTop, Function.Surjective
      (packetMapAt W V ((n : ℚ) * (scale W V hW hV).radius) y c) := by
  apply eventual_packetMapAt_surjective_of_eventual_jetRestriction W V hW hV y hy0 hy c
  obtain ⟨N, hN⟩ := DistinctMultiplicativeAmple.eventual_jetRestriction_surjective_of_nonnegative_curve_degree
    (structureMorphism W V hW hV) (centerIdeal W V hW hV y c)
    (centerIdeal_support_ne_top W V hW hV y hy0 c)
    (hyperplane W V hW hV) (hyperplane_ample W V hW hV) σ hσ hn
  exact eventually_atTop.mpr ⟨N, hN⟩

/-- The common integer scale precedes all center families. The threshold in n
is then allowed to depend on the centers, exactly as in Theorem A.
-/
theorem eventual_interpolation_of_curve_degrees (K : ℕ) (σ : ℝ) (hσ : 0 < σ)
    (hn : ∀ (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ),
      (∀ k, y k ≠ 0) → Function.Injective y →
        NonnegativeSeparatedCurveDegrees W V hW hV y c σ) :
    EventualDistinctMultiplicativeInterpolation m K W V := by
  refine ⟨(scale W V hW hV).radius, (scale W V hW hV).radius_pos, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(scale W V hW hV).degreePowers i, (scale W V hW hV).degreePowers_pos i,
      by rw [mul_comm, (scale W V hW hV).degreePowers_eq]⟩
  · intro i
    exact ⟨(scale W V hW hV).jetPowers i, (scale W V hW hV).jetPowers_pos i,
      by rw [mul_comm, (scale W V hW hV).jetPowers_eq]⟩
  · intro y c hy0 hy
    exact eventual_packetMapAt_surjective_of_curve_degrees W V hW hV
      y hy0 hy c σ hσ (hn y c hy0 hy)

end Weighted

#print axioms formalJetAt_packets_surjective
#print axioms formalPackets_surjective_of_jetRestrictionAt
#print axioms Weighted.eventual_packetMapAt_surjective_of_eventual_jetRestriction
#print axioms Weighted.eventual_interpolation_of_curve_degrees

end
end OAI.PiExponent.DistinctMultiplicative.Global
