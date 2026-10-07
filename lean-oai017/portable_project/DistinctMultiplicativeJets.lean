import OAI.NumberTheory.PiExponent.Jets.FormalAuxiliaryJet
import OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree

/-!
Formal logarithmic jets at arbitrary multiplicative centers, built by actual
composition with the pinned OAI017 `FormalLogJet.formalJet` implementation.
The source theorem fixes the multiplicative center to 1. Here it is `y`.
-/

namespace OAI.PiExponent.DistinctMultiplicative

noncomputable section
open scoped BigOperators
open Filter Topology

/-- Rescale only the multiplicative polynomial variable. -/
def scaleY {m : ℕ} (y : ℂ) :
    PiExponentApprox.FramePolynomial m →ₐ[ℂ] PiExponentApprox.FramePolynomial m :=
  MvPolynomial.aeval (Fin.cases
    (MvPolynomial.C y * MvPolynomial.X (0 : Fin (m + 1)))
    (fun i : Fin m => MvPolynomial.X i.succ))

@[simp] theorem scaleY_Y {m : ℕ} (y : ℂ) :
    scaleY y (MvPolynomial.X (0 : Fin (m + 1))) =
      MvPolynomial.C y * MvPolynomial.X 0 := by
  simp [scaleY]

@[simp] theorem scaleY_X {m : ℕ} (y : ℂ) (i : Fin m) :
    scaleY y (MvPolynomial.X i.succ) = MvPolynomial.X i.succ := by
  simp [scaleY]

theorem scaleY_one {m : ℕ} :
    scaleY (m := m) 1 = AlgHom.id ℂ (PiExponentApprox.FramePolynomial m) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero => simp
  | succ i => simp

/-- The original support-budget theorem proves that rescaling Y does not
increase any source weighted degree, without assuming anything about y. -/
theorem scaleY_supportBound {m : ℕ} (y : ℂ) (w : Fin (m + 1) → ℝ)
    (H : ℝ) (P : PiExponentApprox.FramePolynomial m)
    (hP : WeightedSliceDegree.SupportBound w H P) :
    WeightedSliceDegree.SupportBound w H (scaleY y P) := by
  apply WeightedSliceDegree.supportBound_aeval w w _ _ H P hP
  intro i
  cases i using Fin.cases with
  | zero =>
      simpa only [Fin.cases_zero, zero_add] using
        (WeightedSliceDegree.supportBound_C w y).mul
          (WeightedSliceDegree.supportBound_X w (0 : Fin (m + 1)))
  | succ i =>
      simpa only [Fin.cases_succ] using
        WeightedSliceDegree.supportBound_X w i.succ

/-- Literal reuse of OAI017's formal logarithm and its jet algebra map.
It evaluates P at Y=y(1+t) and Xi=c_i+u_i+log(1+t).
-/
def formalJetAt {m : ℕ} (y : ℂ) (c : Fin m → ℂ) :
    PiExponentApprox.FramePolynomial m →ₐ[ℂ] MvPowerSeries (Fin (m + 1)) ℂ :=
  (FormalLogJet.formalJet c).comp (scaleY y)

@[simp] theorem formalJetAt_Y {m : ℕ} (y : ℂ) (c : Fin m → ℂ) :
    formalJetAt y c (MvPolynomial.X (0 : Fin (m + 1))) =
      MvPowerSeries.C y * (1 + MvPowerSeries.X 0) := by
  simp [formalJetAt, MvPowerSeries.algebraMap_apply]

@[simp] theorem formalJetAt_X {m : ℕ} (y : ℂ) (c : Fin m → ℂ) (i : Fin m) :
    formalJetAt y c (MvPolynomial.X i.succ) =
      MvPowerSeries.C (c i) + MvPowerSeries.X i.succ + FormalLogJet.formalLog m := by
  simp [formalJetAt]

@[simp] theorem formalJetAt_one {m : ℕ} (c : Fin m → ℂ)
    (P : PiExponentApprox.FramePolynomial m) :
    formalJetAt 1 c P = FormalLogJet.formalJet c P := by
  simp only [formalJetAt, scaleY_one, AlgHom.comp_apply, AlgHom.id_apply]

theorem scaleY_polynomialFrame_X {m : ℕ} (y : ℂ) (i j : Fin (m + 1)) :
    scaleY y (PiExponentApprox.polynomialFrame m i (MvPolynomial.X j)) =
      PiExponentApprox.polynomialFrame m i (scaleY y (MvPolynomial.X j)) := by
  classical
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero =>
          simp [PiExponentApprox.polynomialFrame_zero,
            PiExponentApprox.logarithmicDerivation_apply, MvPolynomial.pderiv_X,
            MvPolynomial.pderiv_mul] <;> ring
      | succ j =>
          simp [PiExponentApprox.polynomialFrame_zero,
            PiExponentApprox.logarithmicDerivation_apply, MvPolynomial.pderiv_X,
            Pi.single_apply]
  | succ i =>
      rw [PiExponentApprox.polynomialFrame_pos m i.succ (Fin.succ_ne_zero i)]
      cases j using Fin.cases with
      | zero => simp [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X]
      | succ j => simp [MvPolynomial.pderiv_X, Pi.single_apply]

/-- Rescaling commutes with the original logarithmic polynomial frame. -/
theorem scaleY_polynomialFrame {m : ℕ} (y : ℂ) (i : Fin (m + 1))
    (P : PiExponentApprox.FramePolynomial m) :
    scaleY y (PiExponentApprox.polynomialFrame m i P) =
      PiExponentApprox.polynomialFrame m i (scaleY y P) := by
  exact FormalLogJet.derivation_map_of_X (scaleY y)
    (PiExponentApprox.polynomialFrame m i) (PiExponentApprox.polynomialFrame m i)
    (scaleY_polynomialFrame_X y i) P

/-- The original frame-to-jet differential identity is preserved at y(1+t). -/
theorem formalJetAt_polynomialFrame {m : ℕ} (y : ℂ) (c : Fin m → ℂ)
    (i : Fin (m + 1)) (P : PiExponentApprox.FramePolynomial m) :
    formalJetAt y c (PiExponentApprox.polynomialFrame m i P) =
      FormalJetDerivatives.jetFrame m i (formalJetAt y c P) := by
  change FormalLogJet.formalJet c (scaleY y (PiExponentApprox.polynomialFrame m i P)) = _
  rw [scaleY_polynomialFrame, FormalLogJet.formalJet_polynomialFrame]
  rfl

theorem formalJetAt_polynomialFrameWord {m : ℕ} (y : ℂ) (c : Fin m → ℂ)
    (word : List (Fin (m + 1))) (P : PiExponentApprox.FramePolynomial m) :
    formalJetAt y c (PiExponentApprox.polynomialFrameWord m word P) =
      FormalJetDerivatives.jetFrameWord m word (formalJetAt y c P) := by
  induction word with
  | nil => rfl
  | cons i word ih =>
      rw [PiExponentApprox.polynomialFrameWord_cons, formalJetAt_polynomialFrame, ih]
      rfl

/-- The original weighted derivative-cost estimate now applies to the new
actual logarithmic jet map, so this is not just a renamed evaluation map. -/
theorem formalJetAt_polynomialFrameWord_vanishing {m : ℕ}
    (y : ℂ) (c : Fin m → ℂ) (v : Fin (m + 1) → ℚ)
    (hv : ∀ i, 0 ≤ v i) (H : ℚ) (P : PiExponentApprox.FramePolynomial m)
    (hP : formalJetAt y c P ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (word : List (Fin (m + 1))) :
    formalJetAt y c (PiExponentApprox.polynomialFrameWord m word P) ∈
      JetGeometry.rationalWeightedIdeal v hv (H - (word.map v).sum) := by
  rw [formalJetAt_polynomialFrameWord]
  exact FormalJetDerivatives.jetFrameWord_mem_rationalWeightedIdeal
    v hv H (formalJetAt y c P) hP word

def formalJetEvaluationAt {m : ℕ} (K : ℕ)
    (V : Fin (m + 1) → ℝ) (H : ℝ)
    (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) :
    PiExponentApprox.FramePolynomial m →ₗ[ℂ]
      ((Fin K × ↥(strictWeightedSimplex V H)) → ℂ) :=
  LinearMap.pi (fun ρ =>
    (MvPowerSeries.coeff (InterpolationMatrix.exponentVector ρ.2.val)).comp
      (formalJetAt (y ρ.1) (c ρ.1)).toLinearMap)

/-- New-center auxiliary polynomial existence, obtained by supplying the new
actual evaluation map to OAI017's already proved dimension/counting theorem.
No injectivity of any coordinates is needed for this homogeneous count.
-/
theorem eventually_exists_auxiliaryPolynomialAt {m : ℕ}
    (W V : Fin (m + 1) → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (K : ℕ) {a : ℝ} (ha : 0 < a)
    (hvol : (K : ℝ) * a ^ (m + 1) * (∏ i, (W i : ℝ)) /
      (∏ i, (V i : ℝ)) < 1)
    (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) :
    ∀ᶠ N : ℝ in atTop, ∃ P : PiExponentApprox.FramePolynomial m, P ≠ 0 ∧
      PiExponentApprox.HasWeightedDegreeLE (fun i => (W i : ℝ)) N P ∧
      ∀ j d, Finsupp.weight (fun i => (V i : ℝ)) d < a * N →
        MvPowerSeries.coeff d (formalJetAt (y j) (c j) P) = 0 := by
  filter_upwards [OAI.PiExponent.eventually_exists_auxiliaryPolynomial W V hW hV K ha hvol]
    with N hN
  obtain ⟨P, hP, hw, he⟩ :=
    hN (formalJetEvaluationAt K (fun i => (V i : ℝ)) (a * N) y c)
  refine ⟨P, hP, hw, ?_⟩
  intro j d hd
  have hmem : (fun i => d i) ∈ strictWeightedSimplex (fun i => (V i : ℝ)) (a * N) := by
    apply (mem_strictWeightedSimplex (fun i => by exact_mod_cast hV i)).mpr
    simpa [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_comm] using hd
  have hh := congrFun he (j, ⟨(fun i => d i), hmem⟩)
  have hd' : InterpolationMatrix.exponentVector (fun i => d i) = d := by ext i; rfl
  simpa [formalJetEvaluationAt, hd'] using hh

theorem eventually_exists_auxiliaryPolynomialAt_nat {m : ℕ}
    (W V : Fin (m + 1) → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (K : ℕ) {a : ℚ} (ha : 0 < a)
    (hvol : (K : ℝ) * (a : ℝ) ^ (m + 1) * (∏ i, (W i : ℝ)) /
      (∏ i, (V i : ℝ)) < 1)
    (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) :
    ∀ᶠ N : ℕ in atTop, ∃ P : PiExponentApprox.FramePolynomial m, P ≠ 0 ∧
      PiExponentApprox.HasWeightedDegreeLE (fun i => (W i : ℝ)) N P ∧
      ∀ j, formalJetAt (y j) (c j) P ∈
        JetGeometry.rationalWeightedIdeal V (fun i => le_of_lt (hV i)) (a * N) := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_exists_auxiliaryPolynomialAt W V hW hV K
      (by exact_mod_cast ha) hvol y c)
  filter_upwards [h] with N hN
  obtain ⟨P, hP, hw, hv⟩ := hN
  refine ⟨P, hP, hw, ?_⟩
  intro j d hd
  apply hv j d
  have hcast : ((Finsupp.weight V d : ℚ) : ℝ) < (a : ℝ) * (N : ℝ) := by
    exact_mod_cast hd
  simpa [Finsupp.weight_eq_sum, nsmul_eq_mul] using hcast

/-- Transport simultaneous pure-power quotient interpolation to the actual
new logarithmic coefficient packets using the original rational-weighted
packet theorem. This explicitly records the remaining quotient-surjectivity
input, rather than postulating the full interpolation theorem.
-/
theorem new_packets_surjective_of_power_quotients
    {m : ℕ} {α J : Type*}
    (y : J → ℂ) (c : J → Fin m → ℂ)
    (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (e : Fin (m + 1) → ℕ) (H : ℚ)
    (he : ∀ i, H ≤ (e i : ℚ) * v i) (n : ℕ)
    (P : α → PiExponentApprox.FramePolynomial m)
    (hquotient : Function.Surjective (fun a j =>
      Ideal.Quotient.mk
        ((JetGeometry.coordinatePowerIdeal e :
          Ideal (MvPowerSeries (Fin (m + 1)) ℂ)) ^ n)
        (formalJetAt (y j) (c j) (P a)))) :
    Function.Surjective (fun a j =>
      JetGeometry.rationalCoefficientPacket v (n * H)
        (formalJetAt (y j) (c j) (P a))) := by
  exact JetGeometry.rationalCoefficientPackets_surjective_of_coordinatePowerIdeal
    v hv e H he n (fun a j => formalJetAt (y j) (c j) (P a)) hquotient

#print axioms scaleY_supportBound
#print axioms formalJetAt_Y
#print axioms formalJetAt_X
#print axioms formalJetAt_one
#print axioms scaleY_polynomialFrame
#print axioms formalJetAt_polynomialFrameWord_vanishing
#print axioms eventually_exists_auxiliaryPolynomialAt_nat
#print axioms new_packets_surjective_of_power_quotients

end

end OAI.PiExponent.DistinctMultiplicative
