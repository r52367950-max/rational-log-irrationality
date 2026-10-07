import RationalLogArithmeticAssembly
import DistinctMultiplicativeStatement
import OAI.NumberTheory.PiExponent.Approximation.FormalMatrixSurjectivity

/-!
The actual arbitrary-center logarithmic packet map is converted to the
literal finite coefficient matrix and a nonzero full-row minor. This proves
the algebraic interface required for B; it does not assume such a minor.
-/

namespace IrrationalityReview.RationalLogMatrixBridge

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.FormalMatrixBridge
open OAI.PiExponent.DistinctMultiplicative
open IrrationalityReview.OAIFormalLogAdapter
open IrrationalityReview.RationalLogArithmeticAssembly

noncomputable section
set_option maxHeartbeats 1200000

def truncatedFormalJetAt {m : ℕ} (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ) :
    OAI.PiExponentApprox.FramePolynomial m →ₐ[ℂ] MvPowerSeries (Fin (m+1)) ℂ :=
  (FormalLogTruncation.truncatedFormalJet c T).comp (scaleY y)

theorem scaleY_monomial {m : ℕ} (y : ℂ) (e : Fin (m+1) → ℕ) (z : ℂ) :
    scaleY y (MvPolynomial.monomial (InterpolationMatrix.exponentVector e) z) =
      MvPolynomial.C (y ^ e 0) *
        MvPolynomial.monomial (InterpolationMatrix.exponentVector e) z := by
  classical
  rw [scaleY, MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [InterpolationMatrix.exponentVector_apply, Fin.cases_zero, Fin.cases_succ,
    MvPolynomial.algebraMap_eq, mul_pow, ← map_pow]
  ring

theorem centeredEntry_eq_coeff_truncatedFormalJetAt {m : ℕ}
    (y : ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ) (j : ℕ)
    (b e : Fin (m+1) → ℕ) (z : ℂ) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (truncatedFormalJetAt y (fun i => (j : ℂ) * r i) T
        (MvPolynomial.monomial (InterpolationMatrix.exponentVector e) z)) =
      centeredEntry y r (fun i => InterpolationMatrix.truncatedLog (T i))
        j (b 0) (fun i => b i.succ) (e 0) (fun i => e i.succ) * z := by
  have hC : (FormalLogTruncation.truncatedFormalJet (fun i => (j : ℂ) * r i) T)
      (MvPolynomial.C (y ^ e 0)) = MvPowerSeries.C (y ^ e 0) := by
    change (FormalLogTruncation.truncatedFormalJet (fun i => (j : ℂ) * r i) T)
      (algebraMap ℂ (OAI.PiExponentApprox.FramePolynomial m) (y ^ e 0)) = _
    rw [AlgHom.commutes, ← MvPowerSeries.c_eq_algebraMap]
  rw [truncatedFormalJetAt, AlgHom.comp_apply, scaleY_monomial,
    map_mul, hC, MvPowerSeries.coeff_C_mul,
    coeff_truncatedFormalJet, literalJetSubstitution_monomial]
  simp only [MvPolynomial.coeff_C_mul, Polynomial.coeff_C_mul, exponentVector_tail,
    InterpolationMatrix.exponentVector_apply, centeredEntry_eq_original_entry,
    InterpolationMatrix.entry]
  ring

def centeredMatrix {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ) (w : Fin m → ℝ) (H : ℝ)
    (y : Fin K → ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ) :
    Matrix (InterpolationMatrix.Row K v0 θ w H) (InterpolationMatrix.Column w0 w H) ℂ :=
  fun ρ c => centeredEntry (y ρ.1) r (fun i => InterpolationMatrix.truncatedLog (T i))
    ρ.1.val (ρ.2.1 0) (fun i => ρ.2.1 i.succ) (c.1 0) (fun i => c.1 i.succ)

theorem centeredMatrix_mulVec_eq_coeff {m : ℕ}
    (K : ℕ) (w0 v0 θ : ℝ) (w : Fin m → ℝ) (H : ℝ)
    (y : Fin K → ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (x : InterpolationMatrix.Column w0 w H → ℂ)
    (ρ : InterpolationMatrix.Row K v0 θ w H) :
    (centeredMatrix K w0 v0 θ w H y r T).mulVecLin x ρ =
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector ρ.2.val)
        (truncatedFormalJetAt (y ρ.1) (fun i => (ρ.1.val : ℂ) * r i) T
          (polynomialOfCoefficients
            (realWeightedSimplex (InterpolationMatrix.columnWeights w0 w) H) x)) := by
  classical
  change (∑ c, centeredMatrix K w0 v0 θ w H y r T ρ c * x c) = _
  change _ = MvPowerSeries.coeff (InterpolationMatrix.exponentVector ρ.2.val)
    (truncatedFormalJetAt (y ρ.1) (fun i => (ρ.1.val : ℂ) * r i) T
      (∑ c : InterpolationMatrix.Column w0 w H,
        MvPolynomial.monomial (InterpolationMatrix.exponentVector c.val) (x c)))
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl (fun c _ =>
    (centeredEntry_eq_coeff_truncatedFormalJetAt _ _ _ _ _ _ _).symm)

theorem centered_formal_packets_surjective_iff_truncated {m : ℕ} {α J : Type*}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (y : J → ℂ) (c : J → Fin m → ℂ) (P : α → OAI.PiExponentApprox.FramePolynomial m) :
    Function.Surjective (fun a j => JetGeometry.rationalCoefficientPacket v H
      (formalJetAt (y j) (c j) (P a))) ↔
    Function.Surjective (fun a j => JetGeometry.rationalCoefficientPacket v H
      (truncatedFormalJetAt (y j) (c j) T (P a))) := by
  let tail := fun i => FormalLogTruncation.logTail (T i)
  let ht := fun i => FormalLogTruncation.logTail_constantCoeff (T i)
  let e := FormalLogTruncation.shiftEquiv tail ht
  have hw : ∀ i, (tail i).toMvPowerSeries (0 : Fin (m+1)) ∈
      JetGeometry.rationalWeightedIdeal v hv (v i.succ) :=
    fun i => FormalLogTruncation.logTail_mem_rationalWeightedIdeal v hv (T i) (v i.succ) (hT i)
  have he : ∀ f ∈ JetGeometry.rationalWeightedIdeal v hv H,
      e f ∈ JetGeometry.rationalWeightedIdeal v hv H :=
    fun f hf => (FormalLogTruncation.shiftEquiv_mem_iff tail ht v hv hw H f).mpr hf
  have hi : ∀ f ∈ JetGeometry.rationalWeightedIdeal v hv H,
      e.symm f ∈ JetGeometry.rationalWeightedIdeal v hv H := by
    intro f hf
    apply (FormalLogTruncation.shiftEquiv_mem_iff tail ht v hv hw H (e.symm f)).mp
    change e (e.symm f) ∈ JetGeometry.rationalWeightedIdeal v hv H
    simpa only [AlgEquiv.apply_symm_apply] using hf
  have hh := FormalLogTruncation.packets_surjective_comp_equiv_iff v hv H e he hi
    (fun a j => FormalLogTruncation.truncatedFormalJet (c j) T (scaleY (y j) (P a)))
  simpa only [e, tail, ht, FormalLogTruncation.shiftEquiv_apply,
    FormalLogTruncation.shiftMap_truncatedFormalJet,
    formalJetAt, truncatedFormalJetAt, AlgHom.comp_apply] using hh

theorem centeredMatrix_surjective_of_rational_packets {m : ℕ} {α : Type*}
    (K : ℕ) (w0 v0 θ : ℝ) (w : Fin m → ℝ) (H : ℚ)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (V : Fin (m+1) → ℚ) (hV : ∀ i, 0 < V i)
    (hrow : ∀ i, (V i : ℝ) = InterpolationMatrix.rowWeights v0 θ w i)
    (y : Fin K → ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (P : α → OAI.PiExponentApprox.FramePolynomial m)
    (hdegree : ∀ a, OAI.PiExponentApprox.HasWeightedDegreeLE
      (InterpolationMatrix.columnWeights w0 w) (H : ℝ) (P a))
    (hpacket : Function.Surjective (fun a j => JetGeometry.rationalCoefficientPacket V H
      (truncatedFormalJetAt (y j) (fun i => (j.val : ℂ) * r i) T (P a)))) :
    Function.Surjective (centeredMatrix K w0 v0 θ w (H : ℝ) y r T).mulVecLin := by
  classical
  have hrow' : (fun i => (V i : ℝ)) = InterpolationMatrix.rowWeights v0 θ w := funext hrow
  have hW : ∀ i, 0 < InterpolationMatrix.columnWeights w0 w i := fun i => Fin.cases hw0 hw i
  intro target
  let e := rationalJetIndexEquiv V hV H
  let z : Fin K → JetGeometry.RationalCoefficientPacket (R := ℂ) V H :=
    fun j d => target (j, ⟨(e d).val, by simpa only [← hrow'] using (e d).property⟩)
  obtain ⟨a, ha⟩ := hpacket z
  let x : InterpolationMatrix.Column w0 w (H : ℝ) → ℂ :=
    fun c => (P a).coeff (InterpolationMatrix.exponentVector c.val)
  refine ⟨x, ?_⟩
  funext ρ
  rw [centeredMatrix_mulVec_eq_coeff]
  change MvPowerSeries.coeff (InterpolationMatrix.exponentVector ρ.2.val)
    (truncatedFormalJetAt (y ρ.1) (fun i => (ρ.1.val : ℂ) * r i) T
      (polynomialOfCoefficients
        (realWeightedSimplex (InterpolationMatrix.columnWeights w0 w) (H : ℝ))
        (fun c => (P a).coeff (InterpolationMatrix.exponentVector c.val)))) = target ρ
  rw [polynomialOfCoefficients_of_weighted _ hW _ (P a) (hdegree a)]
  let b : ↥(strictWeightedSimplex (fun i => (V i : ℝ)) (H : ℝ)) :=
    ⟨ρ.2.val, by simpa only [hrow'] using ρ.2.property⟩
  have hh := congrFun (congrFun ha ρ.1) (e.symm b)
  change MvPowerSeries.coeff (e.symm b).val
    (truncatedFormalJetAt (y ρ.1) (fun i => (ρ.1.val : ℂ) * r i) T (P a)) =
      z ρ.1 (e.symm b) at hh
  simpa only [e, rationalJetIndexEquiv_symm_val, b, z, Equiv.apply_symm_apply] using hh

theorem centeredMatrix_surjective_of_formal_packets {m : ℕ} {α : Type*}
    (K : ℕ) (w0 v0 θ : ℝ) (w : Fin m → ℝ) (H : ℚ)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (V : Fin (m+1) → ℚ) (hV : ∀ i, 0 < V i)
    (hrow : ∀ i, (V i : ℝ) = InterpolationMatrix.rowWeights v0 θ w i)
    (y : Fin K → ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hT : ∀ i, V i.succ ≤ (T i : ℚ) * V 0)
    (P : α → OAI.PiExponentApprox.FramePolynomial m)
    (hdegree : ∀ a, OAI.PiExponentApprox.HasWeightedDegreeLE
      (InterpolationMatrix.columnWeights w0 w) (H : ℝ) (P a))
    (hpacket : Function.Surjective (fun a j => JetGeometry.rationalCoefficientPacket V H
      (formalJetAt (y j) (fun i => (j.val : ℂ) * r i) (P a)))) :
    Function.Surjective (centeredMatrix K w0 v0 θ w (H : ℝ) y r T).mulVecLin := by
  apply centeredMatrix_surjective_of_rational_packets K w0 v0 θ w H hw0 hw V hV hrow y r T P hdegree
  exact (centered_formal_packets_surjective_iff_truncated V (fun i => (hV i).le)
    H T hT y (fun j : Fin K => fun i => (j.val : ℂ) * r i) P).mp hpacket

theorem nonzero_centered_minor_of_actual_packet_surjective {m : ℕ}
    (K : ℕ) (w0 v0 θ : ℝ) (w : Fin m → ℝ) (H : ℚ)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (W V : Fin (m+1) → ℚ) (hV : ∀ i, 0 < V i)
    (hsource : ∀ i, (W i : ℝ) = InterpolationMatrix.columnWeights w0 w i)
    (hrow : ∀ i, (V i : ℝ) = InterpolationMatrix.rowWeights v0 θ w i)
    (y : Fin K → ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hT : ∀ i, V i.succ ≤ (T i : ℚ) * V 0)
    (hpacket : Function.Surjective (packetMapAt W V H y
      (fun j : Fin K => fun i => (j.val : ℂ) * r i))) :
    ∃ selection : InterpolationMatrix.Row K v0 θ w (H : ℝ) →
        InterpolationMatrix.Column w0 w (H : ℝ),
      Function.Injective selection ∧
        ((centeredMatrix K w0 v0 θ w (H : ℝ) y r T).submatrix id selection).det ≠ 0 := by
  apply InterpolationMatrix.exists_full_row_minor_of_surjective
  apply centeredMatrix_surjective_of_formal_packets K w0 v0 θ w H hw0 hw V hV hrow y r T hT
    (fun P : WeightedPolynomialsAt m W H => P.val)
  · intro P d hd
    have hp := P.property d hd
    change Finsupp.weight (fun i => (W i : ℝ)) d ≤ (H : ℝ) at hp
    simpa only [Finsupp.weight_eq_sum, nsmul_eq_mul, hsource,
      OAI.PiExponentApprox.monomialWeight, mul_comm] using hp
  · exact hpacket

theorem rationalBase_nonzero_centeredSelectedMinor {m : ℕ}
    (K : ℕ) (w0 v0 θ F : ℝ) (H : ℚ) (A B : ℤ)
    (p : Fin m → ℤ) (q : Fin m → ℕ)
    (hw0 : 0 < w0) (hq : ∀ i, 2 ≤ q i)
    (W V : Fin (m+1) → ℚ) (hV : ∀ i, 0 < V i)
    (hsource : ∀ i, (W i : ℝ) = InterpolationMatrix.columnWeights w0 (MatrixArithmetic.logWeights q) i)
    (hrow : ∀ i, (V i : ℝ) = InterpolationMatrix.rowWeights v0 θ (MatrixArithmetic.logWeights q) i)
    (hT : ∀ i, V i.succ ≤ (MatrixArithmetic.truncationOrders q F v0 i : ℚ) * V 0)
    (hpacket : Function.Surjective (packetMapAt W V H
      (fun j : Fin K => ((A : ℂ) / (B : ℂ)) ^ j.val)
      (fun j : Fin K => fun i => (j.val : ℂ) * ((p i : ℂ) / (q i : ℂ))))) :
    ∃ selection : InterpolationMatrix.Row K v0 θ (MatrixArithmetic.logWeights q) (H : ℝ) →
        InterpolationMatrix.Column w0 (MatrixArithmetic.logWeights q) (H : ℝ),
      Function.Injective selection ∧
        (centeredSelectedMinor K w0 v0 θ F (H : ℝ) A B p q selection).det ≠ 0 := by
  obtain ⟨selection, hinj, hdet⟩ := nonzero_centered_minor_of_actual_packet_surjective
    K w0 v0 θ (MatrixArithmetic.logWeights q) H hw0
    (fun i => MatrixArithmetic.ceil_log_weight_pos (hq i)) W V hV hsource hrow
    (fun j : Fin K => ((A : ℂ) / (B : ℂ)) ^ j.val)
    (fun i => (p i : ℂ) / (q i : ℂ)) (MatrixArithmetic.truncationOrders q F v0) hT hpacket
  exact ⟨selection, hinj, hdet⟩

/-- The truncation condition used by the exact packet equivalence follows
from the elementary ceiling budget and `1 ≤ F*θ`. -/
theorem truncationOrders_satisfy_packet_weight {m : ℕ}
    (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (F v0 θ : ℝ)
    (hv0 : 0 < v0) (hθ : 0 < θ) (hFθ : 1 ≤ F * θ)
    (V : Fin (m+1) → ℚ)
    (hrow : ∀ i, (V i : ℝ) = InterpolationMatrix.rowWeights v0 θ (MatrixArithmetic.logWeights q) i) :
    ∀ i, V i.succ ≤ (MatrixArithmetic.truncationOrders q F v0 i : ℚ) * V 0 := by
  intro i
  have hw := MatrixArithmetic.ceil_log_weight_pos (hq i)
  have ht : F * MatrixArithmetic.logWeights q i ≤
      (MatrixArithmetic.truncationOrders q F v0 i : ℝ) * v0 := by
    apply (div_le_iff₀ hv0).mp
    exact Nat.le_ceil (F * MatrixArithmetic.logWeights q i / v0)
  have hfirst : MatrixArithmetic.logWeights q i / θ ≤ F * MatrixArithmetic.logWeights q i := by
    apply (div_le_iff₀ hθ).mpr
    have hm := mul_le_mul_of_nonneg_left hFθ hw.le
    change MatrixArithmetic.logWeights q i * 1 ≤
      MatrixArithmetic.logWeights q i * (F * θ) at hm
    simpa only [mul_one, one_mul, mul_comm, mul_left_comm, mul_assoc] using hm
  have hreal : (V i.succ : ℝ) ≤
      (MatrixArithmetic.truncationOrders q F v0 i : ℝ) * (V 0 : ℝ) := by
    rw [hrow i.succ, hrow 0]
    exact hfirst.trans ht
  exact_mod_cast hreal

/-- The complete finite arithmetic half of B: actual A packet surjectivity
produces a nonzero actual minor with the derived normalized lower estimate. -/
theorem actualPacket_exists_arithmetic_minor {m : ℕ}
    (K : ℕ) (w0 v0 θ F wmin : ℝ) (H : ℚ) (A B : ℤ)
    (p : Fin m → ℤ) (q : Fin m → ℕ)
    (hB : 0 < B) (hq : ∀ i, 2 ≤ q i) (hK : 0 < K)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (hθ : 0 < θ) (hF : 0 ≤ F)
    (hH : 0 < H) (hmin : 0 < wmin) (hwmin : ∀ i, wmin ≤ MatrixArithmetic.logWeights q i)
    (hFθ : 1 ≤ F * θ) (W V : Fin (m+1) → ℚ) (hV : ∀ i, 0 < V i)
    (hsource : ∀ i, (W i : ℝ) = InterpolationMatrix.columnWeights w0 (MatrixArithmetic.logWeights q) i)
    (hrow : ∀ i, (V i : ℝ) = InterpolationMatrix.rowWeights v0 θ (MatrixArithmetic.logWeights q) i)
    (hpacket : Function.Surjective (packetMapAt W V H
      (fun j : Fin K => ((A : ℂ) / (B : ℂ)) ^ j.val)
      (fun j : Fin K => fun i => (j.val : ℂ) * ((p i : ℂ) / (q i : ℂ))))) :
    ∃ selection : InterpolationMatrix.Row K v0 θ (MatrixArithmetic.logWeights q) (H : ℝ) →
        InterpolationMatrix.Column w0 (MatrixArithmetic.logWeights q) (H : ℝ),
      Function.Injective selection ∧
      (centeredSelectedMinor K w0 v0 θ F (H : ℝ) A B p q selection).det ≠ 0 ∧
      -(1 - MatrixArithmetic.meanRowWeight K v0 θ q (H : ℝ)) -
        (Arithmetic.lcmConstant * F * m / v0 +
          (Arithmetic.lcmConstant * m + θ) / wmin +
          ((K - 1 : ℕ) : ℝ) * Real.log (B : ℝ) / w0) ≤
        Real.log ‖(centeredSelectedMinor K w0 v0 θ F (H : ℝ) A B p q selection).det‖ /
          ((Fintype.card (InterpolationMatrix.Row K v0 θ (MatrixArithmetic.logWeights q) (H : ℝ)) : ℝ) *
            (H : ℝ)) := by
  obtain ⟨selection, hinj, hdet⟩ := rationalBase_nonzero_centeredSelectedMinor
    K w0 v0 θ F H A B p q hw0 hq W V hV hsource hrow
    (truncationOrders_satisfy_packet_weight q hq F v0 θ hv0 hθ hFθ V hrow) hpacket
  refine ⟨selection, hinj, hdet, ?_⟩
  exact centeredSelectedMinor_arithmetic_lower_bound_common_error A B p q hB hq hK
    hw0 hv0 hθ hF (by exact_mod_cast hH) hmin hwmin selection hdet

end
end IrrationalityReview.RationalLogMatrixBridge

#print axioms IrrationalityReview.RationalLogMatrixBridge.scaleY_monomial
#print axioms IrrationalityReview.RationalLogMatrixBridge.centeredEntry_eq_coeff_truncatedFormalJetAt
#print axioms IrrationalityReview.RationalLogMatrixBridge.centeredMatrix_mulVec_eq_coeff
#print axioms IrrationalityReview.RationalLogMatrixBridge.centered_formal_packets_surjective_iff_truncated
#print axioms IrrationalityReview.RationalLogMatrixBridge.centeredMatrix_surjective_of_rational_packets
#print axioms IrrationalityReview.RationalLogMatrixBridge.centeredMatrix_surjective_of_formal_packets
#print axioms IrrationalityReview.RationalLogMatrixBridge.nonzero_centered_minor_of_actual_packet_surjective
#print axioms IrrationalityReview.RationalLogMatrixBridge.rationalBase_nonzero_centeredSelectedMinor
#print axioms IrrationalityReview.RationalLogMatrixBridge.truncationOrders_satisfy_packet_weight
#print axioms IrrationalityReview.RationalLogMatrixBridge.actualPacket_exists_arithmetic_minor
