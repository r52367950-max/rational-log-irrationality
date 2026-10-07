import DistinctMultiplicativeJets
import DistinctMultiplicativePersistent
import DistinctMultiplicativeFibre
import OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch
import OAI.NumberTheory.PiExponent.Cohomology.CurveDerivativeVanishing
import OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal
import OAI.NumberTheory.PiExponent.Geometry.CurveInequalityIntrinsic

/-! Actual local logarithmic contact and curve bridges at arbitrary nonzero
multiplicative centers. A single center is normalized by Y ↦ a⁻¹Y; the
polynomial is simultaneously replaced by `scaleY a P`. -/

namespace OAI.PiExponent.DistinctMultiplicative

noncomputable section
open scoped BigOperators
open Filter Topology
open PiExponentApprox CurveValuationCenter CurveCenters PlaceValuationRing

theorem scaleY_mul {m : ℕ} (a b : ℂ) (P : FramePolynomial m) :
    scaleY a (scaleY b P) = scaleY (a * b) P := by
  have h : (scaleY (m := m) a).comp (scaleY b) = scaleY (a * b) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases with
    | zero => simp [map_mul, mul_assoc, mul_comm, mul_left_comm]
    | succ i => simp
  exact AlgHom.congr_fun h P

theorem scaleY_inv_left {m : ℕ} (a : ℂ) (ha : a ≠ 0) (P : FramePolynomial m) :
    scaleY a⁻¹ (scaleY a P) = P := by
  rw [scaleY_mul, inv_mul_cancel₀ ha, scaleY_one, AlgHom.id_apply]

theorem scaleY_inv_right {m : ℕ} (a : ℂ) (ha : a ≠ 0) (P : FramePolynomial m) :
    scaleY a (scaleY a⁻¹ P) = P := by
  rw [scaleY_mul, mul_inv_cancel₀ ha, scaleY_one, AlgHom.id_apply]

theorem scaleY_polynomialFrameWord {m : ℕ} (a : ℂ)
    (word : List (Fin (m + 1))) (P : FramePolynomial m) :
    scaleY a (polynomialFrameWord m word P) =
      polynomialFrameWord m word (scaleY a P) := by
  induction word with
  | nil => rfl
  | cons i word ih =>
      rw [polynomialFrameWord_cons, scaleY_polynomialFrame, ih]
      rfl

theorem aeval_scaleY {A : Type*} [CommRing A] [Algebra ℂ A] {m : ℕ}
    (a : ℂ) (z : Fin (m + 1) → A) (P : FramePolynomial m) :
    MvPolynomial.aeval z (scaleY a P) =
      MvPolynomial.aeval
        (Fin.cases (algebraMap ℂ A a * z 0) (fun i => z i.succ)) P := by
  have h : (MvPolynomial.aeval z).comp (scaleY a) =
      MvPolynomial.aeval
        (Fin.cases (algebraMap ℂ A a * z 0) (fun i => z i.succ)) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases <;> simp
  exact AlgHom.congr_fun h P

variable {E : Type*} [Field E] [Algebra ℂ E]

def normalizeCoordinates {m : ℕ} (a : ℂ) (z : Fin (m + 1) → E) :
    Fin (m + 1) → E :=
  Fin.cases (algebraMap ℂ E a⁻¹ * z 0) (fun i => z i.succ)

@[simp] theorem normalizeCoordinates_zero {m : ℕ} (a : ℂ)
    (z : Fin (m + 1) → E) :
    normalizeCoordinates a z 0 = algebraMap ℂ E a⁻¹ * z 0 := rfl

@[simp] theorem normalizeCoordinates_succ {m : ℕ} (a : ℂ)
    (z : Fin (m + 1) → E) (i : Fin m) :
    normalizeCoordinates a z i.succ = z i.succ := rfl

theorem aeval_normalize_scaleY {m : ℕ} (a : ℂ) (ha : a ≠ 0)
    (z : Fin (m + 1) → E) (P : FramePolynomial m) :
    MvPolynomial.aeval (normalizeCoordinates a z) (scaleY a P) =
      MvPolynomial.aeval z P := by
  have h : (MvPolynomial.aeval (normalizeCoordinates a z)).comp (scaleY a) =
      MvPolynomial.aeval z := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases with
    | zero =>
        simp only [AlgHom.comp_apply, scaleY_Y, map_mul, MvPolynomial.aeval_C,
          MvPolynomial.aeval_X, normalizeCoordinates_zero]
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
    | succ i => simp
  exact AlgHom.congr_fun h P

theorem centered_normalize {m : ℕ} (a : ℂ) (ha : a ≠ 0)
    (z : Fin (m + 1) → E) (c : Fin m → ℂ) (p : NormalizedPlace ℂ E)
    (hc : Centered z (Fin.cases a c) p) :
    Centered (normalizeCoordinates a z) (Fin.cases 1 c) p := by
  intro i
  cases i using Fin.cases with
  | zero =>
      have he : algebraMap ℂ E a⁻¹ * z 0 - algebraMap ℂ E 1 =
          algebraMap ℂ E a⁻¹ * (z 0 - algebraMap ℂ E a) := by
        rw [mul_sub, ← map_mul, inv_mul_cancel₀ ha]
      change 0 < p.valuation (algebraMap ℂ E a⁻¹ * z 0 - algebraMap ℂ E 1)
      rw [he, p.valuation.map_mul,
        CurveProductFormula.valuation_constant_eq_zero p _ (inv_ne_zero ha), zero_add]
      exact hc 0
  | succ i => simpa only [normalizeCoordinates_succ, Fin.cases_succ] using hc i.succ

theorem normalize_nonconstant {m : ℕ} (a : ℂ) (ha : a ≠ 0)
    (z : Fin (m + 1) → E) (c : Fin m → ℂ)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E ((Fin.cases a c : Fin (m + 1) → ℂ) i)) :
    ∃ i, normalizeCoordinates a z i ≠
      algebraMap ℂ E ((Fin.cases 1 c : Fin (m + 1) → ℂ) i) := by
  obtain ⟨i, hi⟩ := hnc
  cases i using Fin.cases with
  | zero =>
      refine ⟨0, ?_⟩
      intro hz
      apply hi
      have h := congrArg (fun q : E => algebraMap ℂ E a * q) hz
      simp only [normalizeCoordinates_zero, Fin.cases_zero, map_one,
        ← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, one_mul, mul_one] at h
      exact h
  | succ i => exact ⟨i.succ, by simpa only [normalizeCoordinates_succ, Fin.cases_succ] using hi⟩

variable (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]

def logContactAt {m : ℕ} (a : ℂ) (ha : a ≠ 0)
    (z : Fin (m + 1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases a c) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E ((Fin.cases a c : Fin (m + 1) → ℂ) i))
    (v : Fin (m + 1) → ℚ) : ℚ :=
  PlaceCenteredBranch.logContact p (normalizeCoordinates a z) c
    (centered_normalize a ha z c p hc) (normalize_nonconstant a ha z c hnc) v

theorem logContactAt_pos {m : ℕ} (a : ℂ) (ha : a ≠ 0)
    (z : Fin (m + 1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases a c) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E ((Fin.cases a c : Fin (m + 1) → ℂ) i))
    (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 < v i) :
    0 < logContactAt p a ha z c hc hnc v := by
  exact PlaceCenteredBranch.logContact_pos p _ c _ _ v hv

theorem logWord_field_order_lower_at {m : ℕ} (a : ℂ) (ha : a ≠ 0)
    (z : Fin (m + 1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases a c) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E ((Fin.cases a c : Fin (m + 1) → ℂ) i))
    (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (F : FramePolynomial m)
    (hf : formalJetAt a c F ∈ JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m + 1)))
    (hne : MvPolynomial.aeval z (polynomialFrameWord m word F) ≠ 0) :
    logContactAt p a ha z c hc hnc v * (H - (word.map v).sum) ≤
      (WeightedPolynomialPole.coordinateOrder p.valuation
        (MvPolynomial.aeval z (polynomialFrameWord m word F)) : ℚ) := by
  have he : MvPolynomial.aeval (normalizeCoordinates a z)
      (polynomialFrameWord m word (scaleY a F)) =
      MvPolynomial.aeval z (polynomialFrameWord m word F) := by
    rw [← scaleY_polynomialFrameWord, aeval_normalize_scaleY a ha]
  have hn : MvPolynomial.aeval (normalizeCoordinates a z)
      (polynomialFrameWord m word (scaleY a F)) ≠ 0 := he ▸ hne
  have hb := PlaceCenteredBranch.logWord_field_order_lower p
    (normalizeCoordinates a z) c (centered_normalize a ha z c p hc)
    (normalize_nonconstant a ha z c hnc) v hv H (scaleY a F) hf word hn
  simpa only [he, logContactAt] using hb

theorem normalize_constant_y {m : ℕ} (a : ℂ) (ha : a ≠ 0) (x : Fin m → E) :
    normalizeCoordinates a (Fin.cases (algebraMap ℂ E a) x) = Fin.cases 1 x := by
  funext i
  cases i using Fin.cases with
  | zero => simp only [normalizeCoordinates_zero, Fin.cases_zero, ← map_mul,
      inv_mul_cancel₀ ha, map_one]
  | succ i => rfl

theorem logContactAt_constant_y {m : ℕ} (a : ℂ) (ha : a ≠ 0)
    (x : Fin m → E) (c : Fin m → ℂ)
    (hc : Centered (Fin.cases (algebraMap ℂ E a) x) (Fin.cases a c) p)
    (hnc : ∃ i : Fin (m + 1),
      (Fin.cases (algebraMap ℂ E a) x : Fin (m + 1) → E) i ≠
        algebraMap ℂ E ((Fin.cases a c : Fin (m + 1) → ℂ) i))
    (v : Fin (m + 1) → ℚ) :
    logContactAt p a ha (Fin.cases (algebraMap ℂ E a) x) c hc hnc v =
      PlaceCenteredBranch.ordinaryContact p x c (fun i => hc i.succ)
        (by
          obtain ⟨i, hi⟩ := hnc
          cases i using Fin.cases with
          | zero => exact (hi rfl).elim
          | succ i => exact ⟨i, hi⟩) (fun i => v i.succ) := by
  have hcn : Centered (Fin.cases (1 : E) x) (Fin.cases (1 : ℂ) c) p := by
    simpa only [normalize_constant_y a ha x] using
      centered_normalize a ha (Fin.cases (algebraMap ℂ E a) x) c p hc
  have hnn : ∃ i : Fin (m + 1), (Fin.cases (1 : E) x : Fin (m + 1) → E) i ≠
      algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m + 1) → ℂ) i) := by
    simpa only [normalize_constant_y a ha x] using
      normalize_nonconstant a ha (Fin.cases (algebraMap ℂ E a) x) c hnc
  simpa only [logContactAt, normalize_constant_y a ha x] using
    PlaceCenteredBranch.logContact_one p x c hcn hnn v

theorem logContactAt_congr_coordinates {m : ℕ} (a : ℂ) (ha : a ≠ 0)
    (z t : Fin (m + 1) → E) (c : Fin m → ℂ) (hzt : z = t)
    (hz : Centered z (Fin.cases a c) p)
    (hnz : ∃ i, z i ≠ algebraMap ℂ E ((Fin.cases a c : Fin (m + 1) → ℂ) i))
    (ht : Centered t (Fin.cases a c) p)
    (hnt : ∃ i, t i ≠ algebraMap ℂ E ((Fin.cases a c : Fin (m + 1) → ℂ) i))
    (v : Fin (m + 1) → ℚ) :
    logContactAt p a ha z c hz hnz v = logContactAt p a ha t c ht hnt v := by
  subst t
  rfl

def localLogIdealAt {m : ℕ} (a : ℂ) (ha : a ≠ 0)
    (z : Fin (m + 1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases a c) p) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) : Ideal (ring p) :=
  let q := normalizeCoordinates a z
  let hq := centered_normalize a ha z c p hc
  LogarithmicContactIdeal.logarithmicIdeal c
    (PlaceCenteredBranch.lift p q (Fin.cases 1 c) hq 0)
    (fun i => PlaceCenteredBranch.lift p q (Fin.cases 1 c) hq i.succ) T e

theorem normalized_lift_zero {m : ℕ} (a : ℂ) (ha : a ≠ 0)
    (z : Fin (m + 1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases a c) p) :
    PlaceCenteredBranch.lift p (normalizeCoordinates a z) (Fin.cases 1 c)
      (centered_normalize a ha z c p hc) 0 =
      algebraMap ℂ (ring p) a⁻¹ * PlaceCenteredBranch.lift p z (Fin.cases a c) hc 0 := by
  apply Subtype.ext
  rfl

theorem normalized_lift_succ {m : ℕ} (a : ℂ) (ha : a ≠ 0)
    (z : Fin (m + 1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases a c) p) (i : Fin m) :
    PlaceCenteredBranch.lift p (normalizeCoordinates a z) (Fin.cases 1 c)
      (centered_normalize a ha z c p hc) i.succ =
      PlaceCenteredBranch.lift p z (Fin.cases a c) hc i.succ := rfl

theorem localLogIdealAt_colength_eq_contact {m : ℕ}
    (a : ℂ) (ha : a ≠ 0) (z : Fin (m + 1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases a c) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E ((Fin.cases a c : Fin (m + 1) → ℂ) i))
    (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 < v i)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (R : ℚ) (e : Fin (m + 1) → ℕ) (he : ∀ i, v i * (e i : ℚ) = R) :
    ((Module.length (ring p) ((ring p) ⧸ localLogIdealAt p a ha z c hc T e)).toNat : ℚ) =
      R * logContactAt p a ha z c hc hnc v := by
  let q := normalizeCoordinates a z
  let hq := centered_normalize a ha z c p hc
  let hn := normalize_nonconstant a ha z c hnc
  exact LogarithmicContactIdeal.logarithmicIdeal_colength_eq_contact v hv c
    (PlaceCenteredBranch.lift p q (Fin.cases 1 c) hq 0)
    (fun i => PlaceCenteredBranch.lift p q (Fin.cases 1 c) hq i.succ)
    (PlaceCenteredBranch.lift_residue p q (Fin.cases 1 c) hq 0)
    (fun i => PlaceCenteredBranch.lift_residue p q (Fin.cases 1 c) hq i.succ)
    (PlaceCenteredBranch.logLift_nonconstant p q c hq hn) T hT R e he

omit [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))] in
def placesAt {m K : ℕ}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m + 1) → E) (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) : Finset (NormalizedPlace ℂ E) :=
  centerPlaces z (centers y c) hz hfinite

omit [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))] in
theorem mem_placesAt {m K : ℕ}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m + 1) → E) (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (q : NormalizedPlace ℂ E) :
    q ∈ placesAt hfinite z y c hz ↔ ∃ j : Fin K, Centered z (centers y c j) q :=
  mem_centerPlaces z (centers y c) hz hfinite q

omit [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))] in
def centerAtIndex {m K : ℕ}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m + 1) → E) (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i))
    (q : NormalizedPlace ℂ E) (hq : q ∈ placesAt hfinite z y c hz) : Fin K :=
  Classical.choose ((mem_placesAt hfinite z y c hz q).mp hq)

omit [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))] in
theorem centeredAt {m K : ℕ}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m + 1) → E) (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i))
    (q : NormalizedPlace ℂ E) (hq : q ∈ placesAt hfinite z y c hz) :
    Centered z (centers y c (centerAtIndex hfinite z y c hz q hq)) q :=
  Classical.choose_spec ((mem_placesAt hfinite z y c hz q).mp hq)

omit [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))] in
def familyContactAt {m K : ℕ}
    (hres : ∀ q : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring q)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m + 1) → E) (y : Fin K → ℂ) (hy0 : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ) (hz : ∃ i, Transcendental ℂ (z i))
    (v : Fin (m + 1) → ℚ) (q : NormalizedPlace ℂ E) : ℚ := by
  classical
  letI := hres q
  exact if hq : q ∈ placesAt hfinite z y c hz then
    logContactAt q (y (centerAtIndex hfinite z y c hz q hq)) (hy0 _)
      z (c (centerAtIndex hfinite z y c hz q hq))
      (centeredAt hfinite z y c hz q hq)
      (Centered.exists_nonzero_difference z _ hz) v
  else 0

omit [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))] in
theorem familyContactAt_pos {m K : ℕ}
    (hres : ∀ q : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring q)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m + 1) → E) (y : Fin K → ℂ) (hy0 : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ) (hz : ∃ i, Transcendental ℂ (z i))
    (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 < v i)
    (q : NormalizedPlace ℂ E) (hq : q ∈ placesAt hfinite z y c hz) :
    0 < familyContactAt hres hfinite z y hy0 c hz v q := by
  letI := hres q
  simpa only [familyContactAt, dite_eq_left hq] using
    logContactAt_pos q (y (centerAtIndex hfinite z y c hz q hq)) (hy0 _)
      z (c (centerAtIndex hfinite z y c hz q hq))
      (centeredAt hfinite z y c hz q hq)
      (Centered.exists_nonzero_difference z _ hz) v hv

omit [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))] in
theorem familyContactAt_nonneg {m K : ℕ}
    (hres : ∀ q : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring q)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m + 1) → E) (y : Fin K → ℂ) (hy0 : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ) (hz : ∃ i, Transcendental ℂ (z i))
    (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 < v i) (q : NormalizedPlace ℂ E) :
    0 ≤ familyContactAt hres hfinite z y hy0 c hz v q := by
  by_cases hq : q ∈ placesAt hfinite z y c hz
  · exact (familyContactAt_pos hres hfinite z y hy0 c hz v hv q hq).le
  · simp only [familyContactAt, dite_eq_right hq, le_refl]

omit [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))] in
theorem familyLogWord_order_lower {m K : ℕ}
    (hres : ∀ q : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring q)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m + 1) → E) (y : Fin K → ℂ) (hy0 : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ) (hz : ∃ i, Transcendental ℂ (z i))
    (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (F : FramePolynomial m)
    (hjet : ∀ j, formalJetAt (y j) (c j) F ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m + 1)))
    (hne : MvPolynomial.aeval z (polynomialFrameWord m word F) ≠ 0)
    (q : NormalizedPlace ℂ E) (hq : q ∈ placesAt hfinite z y c hz) :
    familyContactAt hres hfinite z y hy0 c hz v q * (H - (word.map v).sum) ≤
      (WeightedPolynomialPole.coordinateOrder q.valuation
        (MvPolynomial.aeval z (polynomialFrameWord m word F)) : ℚ) := by
  letI := hres q
  simpa only [familyContactAt, dite_eq_left hq] using
    logWord_field_order_lower_at q (y (centerAtIndex hfinite z y c hz q hq)) (hy0 _)
      z (c (centerAtIndex hfinite z y c hz q hq)) (centeredAt hfinite z y c hz q hq)
      (Centered.exists_nonzero_difference z _ hz) v hv H F (hjet _) word hne

#print axioms logWord_field_order_lower_at
#print axioms logContactAt_constant_y
#print axioms localLogIdealAt_colength_eq_contact
#print axioms familyLogWord_order_lower

omit [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))] in
theorem logarithmic_words_vanish_at {m K : ℕ}
    (hres : ∀ q : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring q)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m + 1) → E) (y : Fin K → ℂ) (hy0 : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ) (hz : ∃ i, Transcendental ℂ (z i))
    (w v : Fin (m + 1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma) (N : ℕ) (hN : 0 < N)
    (F : FramePolynomial m) (hF : HasWeightedDegreeLE (fun i => (w i : ℝ)) N F)
    (hjet : ∀ j, formalJetAt (y j) (c j) F ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) ((1 + 3 * sigma) * N))
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1 + (sigma : ℝ)) * ∑ q ∈ placesAt hfinite z y c hz,
        (familyContactAt hres hfinite z y hy0 c hz v q : ℝ)) :
    ∀ word : List (Fin (m + 1)),
      frameWordCost (fun i => (v i : ℝ)) word ≤ (sigma : ℝ) * N →
        MvPolynomial.aeval z (polynomialFrameWord m word F) = 0 := by
  intro word hword
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsigR : (0 : ℝ) < sigma := by exact_mod_cast hsigma
  have hcost : (word.map v).sum ≤ sigma * N := by
    change (word.map (fun i => (v i : ℝ))).sum ≤ (sigma : ℝ) * N at hword
    rw [← CurveDerivativeVanishing.cast_word_cost v word] at hword
    exact_mod_cast hword
  have hdegree : ∀ d ∈ (polynomialFrameWord m word F).support,
      Finsupp.weight (fun i => (w i : ℝ)) d ≤ (N : ℝ) := by
    apply (FrameEquationFamily.hasWeightedDegreeLE_iff_supportBound _ _ _).mp
    exact hF.polynomialFrameWord (fun i => by exact_mod_cast (hw i).le) word
  have hsum : 0 ≤ ∑ q ∈ placesAt hfinite z y c hz,
      (familyContactAt hres hfinite z y hy0 c hz v q : ℝ) := by
    apply Finset.sum_nonneg
    intro q hq
    exact_mod_cast familyContactAt_nonneg hres hfinite z y hy0 c hz v hv q
  apply CurveContactSum.polynomial_eq_zero_of_excess_contact hfinite z w hw
    (N : ℝ) ((1 + 2 * (sigma : ℝ)) * N) hNR.le (polynomialFrameWord m word F) hdegree
    (placesAt hfinite z y c hz) (fun q => (familyContactAt hres hfinite z y hy0 c hz v q : ℝ))
  · intro hne q hq
    have hret : (1 + 2 * sigma) * (N : ℚ) ≤
        (1 + 3 * sigma) * N - (word.map v).sum := by nlinarith
    have hlocal := familyLogWord_order_lower hres hfinite z y hy0 c hz v hv
      ((1 + 3 * sigma) * N) F hjet word hne q hq
    have hq' := (mul_le_mul_of_nonneg_left hret
      (familyContactAt_nonneg hres hfinite z y hy0 c hz v hv q)).trans hlocal
    have hr : (familyContactAt hres hfinite z y hy0 c hz v q : ℝ) *
        ((1 + 2 * (sigma : ℝ)) * N) ≤
        (WeightedPolynomialPole.coordinateOrder q.valuation
          (MvPolynomial.aeval z (polynomialFrameWord m word F)) : ℝ) := by
      exact_mod_cast hq'
    simpa only [mul_comm] using hr
  · calc
      (N : ℝ) * CurveContactSum.weightedDegree hfinite z w <
          N * ((1 + (sigma : ℝ)) * ∑ q ∈ placesAt hfinite z y c hz,
            (familyContactAt hres hfinite z y hy0 c hz v q : ℝ)) :=
        mul_lt_mul_of_pos_left hexcess hNR
      _ = (1 + (sigma : ℝ)) * (N * ∑ q ∈ placesAt hfinite z y c hz,
          (familyContactAt hres hfinite z y hy0 c hz v q : ℝ)) := by ring
      _ ≤ (1 + 2 * (sigma : ℝ)) * (N * ∑ q ∈ placesAt hfinite z y c hz,
          (familyContactAt hres hfinite z y hy0 c hz v q : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hNR.le hsum)
      _ = _ := by ring

omit [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))] in
theorem excess_implies_zeroth_center {m K : ℕ}
    (hres : ∀ q : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring q)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m + 1) → E) (y : Fin K → ℂ) (hy0 : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ) (hz : ∃ i, Transcendental ℂ (z i))
    (hheight : (CurveFieldRigidity.coordinateKernel z).height ≤ m)
    (w v : Fin (m + 1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ) * (1 + 3 * (sigma : ℝ)) ^ (m + 1) *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      PersistentWeightComparison.comparisonConstant m sigma *
        (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1 + (sigma : ℝ)) * ∑ q ∈ placesAt hfinite z y c hz,
        (familyContactAt hres hfinite z y hy0 c hz v q : ℝ)) :
    ∃ j : Fin K, z 0 = algebraMap ℂ E (y j) := by
  have hvR (i : Fin (m + 1)) : (0 : ℝ) < v i := by exact_mod_cast hv i
  have hsR : (0 : ℝ) < sigma := by exact_mod_cast hsigma
  have haux := eventually_exists_auxiliaryPolynomialAt_nat w v hw hv K
    (a := 1 + 3 * sigma) (by positivity) (by simpa using hvol) y c
  have hrect := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (PersistentWeightComparison.eventually_uniformRectangles (m + 1)
      (fun i => (v i : ℝ)) hvR ((sigma : ℝ) / ((m : ℝ) + 2)) (by positivity))
  obtain ⟨N, hauxN, hrectN, hN⟩ :=
    (haux.and (hrect.and (eventually_gt_atTop (0 : ℕ)))).exists
  obtain ⟨F, hF0, hF, hjet⟩ := hauxN
  have hwords := logarithmic_words_vanish_at hres hfinite z y hy0 c hz
    w v hw hv sigma hsigma N hN F hF hjet hexcess
  have hS : (placesAt hfinite z y c hz).Nonempty := by
    by_contra h
    have he : placesAt hfinite z y c hz = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [he, Finset.sum_empty, mul_zero] at hexcess
    exact (not_lt_of_ge (CurveContactSum.weightedDegree_nonneg hfinite z w)) hexcess
  obtain ⟨q, hq⟩ := hS
  let j := centerAtIndex hfinite z y c hz q hq
  refine ⟨j, ?_⟩
  exact persistent_derivatives_force_center_y z (centers y c j) (hy0 j) q
    (centeredAt hfinite z y c hz q hq) hheight w hw (fun i => (v i : ℝ)) hvR
    sigma N hsR (by exact_mod_cast hN) hrectN F hF0 hF hwords hseparated

#print axioms logarithmic_words_vanish_at
#print axioms excess_implies_zeroth_center

omit [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))] in
theorem no_excess_of_constant_y {m K : ℕ}
    (hres : ∀ q : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring q)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m + 1) → E) (y : Fin K → ℂ) (hy0 : ∀ j, y j ≠ 0)
    (hy : Function.Injective y) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i))
    (w v : Fin (m + 1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hratio : ∀ i : Fin m, (1 + (sigma : ℝ)) * (w i.succ : ℝ) < v i.succ)
    (j0 : Fin K) (hj0 : z 0 = algebraMap ℂ E (y j0)) :
    ¬ CurveContactSum.weightedDegree hfinite z w <
      (1 + (sigma : ℝ)) * ∑ q ∈ placesAt hfinite z y c hz,
        (familyContactAt hres hfinite z y hy0 c hz v q : ℝ) := by
  intro hexcess
  let x : Fin m → E := fun i => z i.succ
  let S := placesAt hfinite z y c hz
  let μ := fun q => (familyContactAt hres hfinite z y hy0 c hz v q : ℝ)
  have hez : z = Fin.cases (algebraMap ℂ E (y j0)) x := by
    funext i
    cases i using Fin.cases with
    | zero => exact hj0
    | succ i => rfl
  have hcenters : ∀ q (hq : q ∈ S), centerAtIndex hfinite z y c hz q hq = j0 := by
    intro q hq
    apply hy
    exact ((centeredAt hfinite z y c hz q hq).constant_coordinate 0 (y j0) hj0).symm
  have hfull : ∀ q ∈ S, Centered z (Fin.cases (y j0) (c j0)) q := by
    intro q hq i
    have hh := centeredAt hfinite z y c hz q hq i
    cases i using Fin.cases with
    | zero => simpa only [centers_zero, Fin.cases_zero, hcenters q hq] using hh
    | succ i => simpa only [centers_succ, Fin.cases_succ, hcenters q hq] using hh
  have hcenter : ∀ q ∈ S, Centered x (c j0) q := by
    intro q hq i
    exact hfull q hq i.succ
  have hnc : ∃ i, x i ≠ algebraMap ℂ E (c j0 i) := by
    obtain ⟨i, hi⟩ := Centered.exists_nonzero_difference z (Fin.cases (y j0) (c j0)) hz
    cases i using Fin.cases with
    | zero => exact (hi hj0).elim
    | succ i => exact ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hnc
  have hμ : ∀ q (hq : q ∈ S), letI := hres q;
      μ q = (PlaceCenteredBranch.ordinaryContact q x (c j0) (hcenter q hq)
        ⟨i, hi⟩ (fun k => v k.succ) : ℝ) := by
    intro q hq
    letI := hres q
    have hp : q ∈ placesAt hfinite z y c hz := hq
    have hfirst : familyContactAt hres hfinite z y hy0 c hz v q =
        logContactAt q (y j0) (hy0 j0) z (c j0) (hfull q hq)
          (Centered.exists_nonzero_difference z _ hz) v := by
      simp only [familyContactAt, dite_eq_left hp, hcenters q hp]
    have hcz : Centered (Fin.cases (algebraMap ℂ E (y j0)) x)
        (Fin.cases (y j0) (c j0)) q := hez ▸ hfull q hq
    have hncz : ∃ k : Fin (m + 1),
        (Fin.cases (algebraMap ℂ E (y j0)) x : Fin (m + 1) → E) k ≠
          algebraMap ℂ E ((Fin.cases (y j0) (c j0) : Fin (m + 1) → ℂ) k) :=
      hez ▸ Centered.exists_nonzero_difference z _ hz
    have hsecond := logContactAt_congr_coordinates q (y j0) (hy0 j0) z
      (Fin.cases (algebraMap ℂ E (y j0)) x) (c j0) hez (hfull q hq)
      (Centered.exists_nonzero_difference z _ hz) hcz hncz v
    have hthird := logContactAt_constant_y q (y j0) (hy0 j0) x (c j0) hcz hncz v
    exact congrArg (fun r : ℚ => (r : ℝ)) (hfirst.trans (hsecond.trans hthird))
  have hb := single_center_fibre_curve_inequality hfinite (y j0) x (c j0)
    w v hw hv sigma (by exact_mod_cast hsigma) hratio i (sub_ne_zero.mpr hi)
    S hcenter (fun q _ => hres q) μ hμ
  rw [← hez] at hb
  exact (not_lt_of_ge hb) hexcess

omit [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))] in
theorem weighted_curve_inequality_at_of_model {m K : ℕ}
    (hres : ∀ q : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring q)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m + 1) → E) (y : Fin K → ℂ) (hy0 : ∀ j, y j ≠ 0)
    (hy : Function.Injective y) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hheight : (CurveFieldRigidity.coordinateKernel z).height ≤ m)
    (w v : Fin (m + 1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ) * (1 + 3 * (sigma : ℝ)) ^ (m + 1) *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      PersistentWeightComparison.comparisonConstant m sigma *
        (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
    (hratio : ∀ i : Fin m, (1 + (sigma : ℝ)) * (w i.succ : ℝ) < v i.succ) :
    (1 + (sigma : ℝ)) * ∑ q ∈ placesAt hfinite z y c hz,
      (familyContactAt hres hfinite z y hy0 c hz v q : ℝ) ≤
        CurveContactSum.weightedDegree hfinite z w := by
  by_contra h
  have hexcess := lt_of_not_ge h
  obtain ⟨j0, hj0⟩ := excess_implies_zeroth_center hres hfinite z y hy0 c hz hheight
    w v hw hv sigma hsigma hvol hseparated hexcess
  exact no_excess_of_constant_y hres hfinite z y hy0 hy c hz
    w v hw hv sigma hsigma hratio j0 hj0 hexcess

omit [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))] in
theorem weighted_curve_inequality_at [Algebra.EssFiniteType ℂ E] {m K : ℕ}
    (z : Fin (m + 1) → E) (y : Fin K → ℂ) (hy0 : ∀ j, y j ≠ 0)
    (hy : Function.Injective y) (c : Fin K → Fin m → ℂ)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1)
    (w v : Fin (m + 1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ) * (1 + 3 * (sigma : ℝ)) ^ (m + 1) *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      PersistentWeightComparison.comparisonConstant m sigma *
        (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
    (hratio : ∀ i : Fin m, (1 + (sigma : ℝ)) * (w i.succ : ℝ) < v i.succ) :
    let hres := PlaceLocalRing.residue_integral htrdeg.le
    let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
    let hz := CurveInequality.nonconstant_coordinates z hgen htrdeg
    (1 + (sigma : ℝ)) * ∑ q ∈ placesAt hfinite z y c hz,
      (familyContactAt hres hfinite z y hy0 c hz v q : ℝ) ≤
        CurveContactSum.weightedDegree hfinite z w := by
  dsimp only
  exact weighted_curve_inequality_at_of_model
    (PlaceLocalRing.residue_integral htrdeg.le)
    (CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg)
    z y hy0 hy c (CurveInequality.nonconstant_coordinates z hgen htrdeg)
    (CurvePrimeHeight.kernel_height_succ_le z hgen htrdeg)
    w v hw hv sigma hsigma hvol hseparated hratio

#print axioms no_excess_of_constant_y
#print axioms weighted_curve_inequality_at

end
end OAI.PiExponent.DistinctMultiplicative
