import OAIFormalLogAdapter

/-!
Actual Theorem B arithmetic at rational-power multiplicative centers.
This file derives the normalized lower estimate from the actual entries,
original OAI Gaussian-integer clearing, and the original LCM bound.
-/

namespace IrrationalityReview.RationalLogArithmeticAssembly

open scoped BigOperators
open OAI.PiExponent
open OAIFormalLogAdapter

noncomputable section

set_option maxHeartbeats 1200000

def centeredSelectedMinor {m : ℕ} (K : ℕ) (w0 v0 θ F H : ℝ)
    (A B : ℤ) (p : Fin m → ℤ) (q : Fin m → ℕ)
    (selection : InterpolationMatrix.Row K v0 θ (MatrixArithmetic.logWeights q) H →
      InterpolationMatrix.Column w0 (MatrixArithmetic.logWeights q) H) :
    Matrix (InterpolationMatrix.Row K v0 θ (MatrixArithmetic.logWeights q) H)
      (InterpolationMatrix.Row K v0 θ (MatrixArithmetic.logWeights q) H) ℂ :=
  centeredRationalMatrix A B p q (MatrixArithmetic.truncationOrders q F v0)
    (fun ρ => ρ.1.val) (fun ρ => ρ.2.1 0) (fun ρ i => ρ.2.1 i.succ)
    (fun σ => (selection σ).1 0) (fun σ i => (selection σ).1 i.succ)

def baseCost {m K : ℕ} {w0 v0 θ H : ℝ} (B : ℤ) (q : Fin m → ℕ)
    (selection : InterpolationMatrix.Row K v0 θ (MatrixArithmetic.logWeights q) H →
      InterpolationMatrix.Column w0 (MatrixArithmetic.logWeights q) H) : ℝ :=
  ∑ σ, (((K - 1) * (selection σ).1 0 : ℕ) : ℝ) * Real.log (B : ℝ)

theorem log_baseColumnScale {m : ℕ} (B : ℤ) (K h : ℕ)
    (q : Fin m → ℕ) (hB : 0 < B) (hq : ∀ i, 0 < q i) (α : Fin m → ℕ) :
    Real.log (baseColumnScale B K h q α) =
      (((K - 1) * h : ℕ) : ℝ) * Real.log (B : ℝ) +
        ∑ i, (α i : ℝ) * Real.log (q i) := by
  rw [baseColumnScale, Real.log_mul (pow_ne_zero _ (by exact_mod_cast hB.ne'))
    (MatrixArithmetic.columnScale_pos hq α).ne', Real.log_pow,
    MatrixArithmetic.log_columnScale hq]

theorem baseCost_le {m K : ℕ} {w0 v0 θ H : ℝ} (B : ℤ)
    (q : Fin m → ℕ) (hB : 0 < B) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (selection : InterpolationMatrix.Row K v0 θ (MatrixArithmetic.logWeights q) H →
      InterpolationMatrix.Column w0 (MatrixArithmetic.logWeights q) H) :
    baseCost B q selection ≤
      (Fintype.card (InterpolationMatrix.Row K v0 θ (MatrixArithmetic.logWeights q) H) : ℝ) *
        H * ((K - 1 : ℕ) : ℝ) * Real.log (B : ℝ) / w0 := by
  have hlog : 0 ≤ Real.log (B : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (by omega : (1 : ℤ) ≤ B)
  have hw : ∀ i, 0 < MatrixArithmetic.logWeights q i :=
    fun i => MatrixArithmetic.ceil_log_weight_pos (hq i)
  have hcost (σ : InterpolationMatrix.Row K v0 θ (MatrixArithmetic.logWeights q) H) :
      (((K - 1) * (selection σ).1 0 : ℕ) : ℝ) * Real.log (B : ℝ) ≤
        H * ((K - 1 : ℕ) : ℝ) * Real.log (B : ℝ) / w0 := by
    have hb := InterpolationMatrix.column_weight_le hw0 hw (selection σ)
    have hs : 0 ≤ ∑ i, MatrixArithmetic.logWeights q i *
        ((selection σ).1 i.succ : ℝ) :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hw i).le (Nat.cast_nonneg _))
    have hc : ((selection σ).1 0 : ℝ) ≤ H / w0 := by
      apply (le_div_iff₀ hw0).mpr
      nlinarith only [hb, hs]
    have hmult := mul_le_mul_of_nonneg_right hc
      (mul_nonneg (Nat.cast_nonneg (K - 1)) hlog)
    calc
      _ = ((selection σ).1 0 : ℝ) *
          (((K - 1 : ℕ) : ℝ) * Real.log (B : ℝ)) := by push_cast; ring
      _ ≤ (H / w0) * (((K - 1 : ℕ) : ℝ) * Real.log (B : ℝ)) := hmult
      _ = _ := by ring
  calc
    baseCost B q selection ≤ ∑ _σ : InterpolationMatrix.Row K v0 θ
        (MatrixArithmetic.logWeights q) H,
        H * ((K - 1 : ℕ) : ℝ) * Real.log (B : ℝ) / w0 :=
      Finset.sum_le_sum (fun σ _ => hcost σ)
    _ = _ := by simp; ring

theorem centeredSelectedMinor_clearing_bound {m K : ℕ} {w0 v0 θ F H : ℝ}
    (A B : ℤ) (p : Fin m → ℤ) (q : Fin m → ℕ)
    (hB : 0 < B) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (selection : InterpolationMatrix.Row K v0 θ (MatrixArithmetic.logWeights q) H →
      InterpolationMatrix.Column w0 (MatrixArithmetic.logWeights q) H)
    (hdet : (centeredSelectedMinor K w0 v0 θ F H A B p q selection).det ≠ 0) :
    -(Fintype.card (InterpolationMatrix.Row K v0 θ (MatrixArithmetic.logWeights q) H) : ℝ) *
      Real.log (MatrixArithmetic.denominator q (MatrixArithmetic.truncationOrders q F v0) H) -
      MatrixArithmetic.columnCost q selection - baseCost B q selection +
        MatrixArithmetic.rowCost K v0 θ q H ≤
      Real.log ‖(centeredSelectedMinor K w0 v0 θ F H A B p q selection).det‖ := by
  have hqpos : ∀ i, 0 < q i := fun i => lt_of_lt_of_le (by decide) (hq i)
  have hw : ∀ i, 0 < MatrixArithmetic.logWeights q i :=
    fun i => MatrixArithmetic.ceil_log_weight_pos (hq i)
  have hc := centeredRationalMatrix_arithmetic_lower_bound
    (ι := InterpolationMatrix.Row K v0 θ (MatrixArithmetic.logWeights q) H) A B K hB p q
    (MatrixArithmetic.truncationOrders q F v0) (fun i => ⌊H / MatrixArithmetic.logWeights q i⌋₊)
    hqpos (fun ρ => ρ.1.val) (fun ρ => ρ.2.1 0) (fun ρ i => ρ.2.1 i.succ)
    (fun σ => (selection σ).1 0) (fun σ i => (selection σ).1 i.succ)
    (fun ρ => ρ.1.isLt)
    (fun σ => MatrixArithmetic.column_coordinate_le_floor hw0 hw (selection σ)) hdet
  simp only [MatrixArithmetic.log_rowScale hqpos, log_baseColumnScale B K _ q hB hqpos,
    Finset.sum_neg_distrib, Finset.sum_add_distrib, sub_neg_eq_add] at hc
  change -(Fintype.card (InterpolationMatrix.Row K v0 θ (MatrixArithmetic.logWeights q) H) : ℝ) *
      Real.log (MatrixArithmetic.denominator q (MatrixArithmetic.truncationOrders q F v0) H) +
      (∑ ρ : InterpolationMatrix.Row K v0 θ (MatrixArithmetic.logWeights q) H,
        ∑ i, (ρ.2.1 i.succ : ℝ) * Real.log (q i)) -
      ((∑ σ, (((K - 1) * (selection σ).1 0 : ℕ) : ℝ) * Real.log (B : ℝ)) +
        (∑ σ, ∑ i, ((selection σ).1 i.succ : ℝ) * Real.log (q i))) ≤
      Real.log ‖(centeredSelectedMinor K w0 v0 θ F H A B p q selection).det‖ at hc
  dsimp only [MatrixArithmetic.columnCost, MatrixArithmetic.rowCost, baseCost]
  linarith only [hc]

theorem centeredSelectedMinor_arithmetic_lower_bound {m K : ℕ} {w0 v0 θ F H wmin : ℝ}
    (A B : ℤ) (p : Fin m → ℤ) (q : Fin m → ℕ)
    (hB : 0 < B) (hq : ∀ i, 2 ≤ q i) (hK : 0 < K)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (hθ : 0 < θ) (hF : 0 ≤ F)
    (hH : 0 < H) (hmin : 0 < wmin) (hwmin : ∀ i, wmin ≤ MatrixArithmetic.logWeights q i)
    (selection : InterpolationMatrix.Row K v0 θ (MatrixArithmetic.logWeights q) H →
      InterpolationMatrix.Column w0 (MatrixArithmetic.logWeights q) H)
    (hdet : (centeredSelectedMinor K w0 v0 θ F H A B p q selection).det ≠ 0) :
    -(1 - MatrixArithmetic.meanRowWeight K v0 θ q H) -
      (Arithmetic.lcmConstant * F * m / v0 +
        Arithmetic.lcmConstant * ∑ i, 1 / MatrixArithmetic.logWeights q i + θ / wmin +
        ((K - 1 : ℕ) : ℝ) * Real.log (B : ℝ) / w0) ≤
      Real.log ‖(centeredSelectedMinor K w0 v0 θ F H A B p q selection).det‖ /
        ((Fintype.card (InterpolationMatrix.Row K v0 θ (MatrixArithmetic.logWeights q) H) : ℝ) * H) := by
  have hw : ∀ i, 0 < MatrixArithmetic.logWeights q i :=
    fun i => MatrixArithmetic.ceil_log_weight_pos (hq i)
  have hM : 0 < (Fintype.card (InterpolationMatrix.Row K v0 θ
      (MatrixArithmetic.logWeights q) H) : ℝ) := by
    exact_mod_cast MatrixArithmetic.actual_row_card_pos hK hv0 hθ hH hw
  let M : ℝ := Fintype.card (InterpolationMatrix.Row K v0 θ (MatrixArithmetic.logWeights q) H)
  let db : ℝ := ((K - 1 : ℕ) : ℝ) * Real.log (B : ℝ) / w0
  let D : ℝ := Real.log (MatrixArithmetic.denominator q (MatrixArithmetic.truncationOrders q F v0) H)
  let E : ℝ := Arithmetic.lcmConstant * F * m / v0 +
    Arithmetic.lcmConstant * ∑ i, 1 / MatrixArithmetic.logWeights q i
  have hclear := centeredSelectedMinor_clearing_bound A B p q hB hq hw0 selection hdet
  have hb := baseCost_le B q hB hq hw0 selection
  have hclear' : -M * (D + H * db) - MatrixArithmetic.columnCost q selection +
      MatrixArithmetic.rowCost K v0 θ q H ≤
      Real.log ‖(centeredSelectedMinor K w0 v0 θ F H A B p q selection).det‖ := by
    have hb' : baseCost B q selection ≤ M * H * db := by
      dsimp [M, db]
      convert hb using 1; ring
    calc
      _ = -M * D - MatrixArithmetic.columnCost q selection - M * H * db +
          MatrixArithmetic.rowCost K v0 θ q H := by ring
      _ ≤ -M * D - MatrixArithmetic.columnCost q selection - baseCost B q selection +
          MatrixArithmetic.rowCost K v0 θ q H := by linarith only [hb']
      _ ≤ _ := hclear
  have hden : D + H * db ≤ H * (E + db) := by
    have hd := MatrixArithmetic.log_denominator_le F v0 H hF hv0 hH hw
    dsimp [D, E]
    linarith
  have hrow : M * H * MatrixArithmetic.meanRowWeight K v0 θ q H -
      M * H * (θ / wmin) ≤ MatrixArithmetic.rowCost K v0 θ q H := by
    have hr := MatrixArithmetic.all_row_log_cost_lower (K := K) (H := H)
      q hq hv0 hθ hmin hwmin
    change MatrixArithmetic.rowWeightedSum K v0 θ q H -
      M * H * θ / wmin ≤ MatrixArithmetic.rowCost K v0 θ q H at hr
    have he : M * H * MatrixArithmetic.meanRowWeight K v0 θ q H =
        MatrixArithmetic.rowWeightedSum K v0 θ q H := by
      unfold MatrixArithmetic.meanRowWeight
      dsimp [M]
      field_simp [(mul_pos hM hH).ne']
    rw [he]
    simpa only [mul_div_assoc] using hr
  have hn := Arithmetic.normalized_arithmetic_bound M H
    (MatrixArithmetic.meanRowWeight K v0 θ q H) (E + db) (θ / wmin) (D + H * db)
    (MatrixArithmetic.columnCost q selection) (MatrixArithmetic.rowCost K v0 θ q H)
    (Real.log ‖(centeredSelectedMinor K w0 v0 θ F H A B p q selection).det‖)
    hM hH hclear' hden (MatrixArithmetic.selected_column_log_cost_le q hq hw0 selection) hrow
  dsimp [M, E, db] at hn
  convert hn using 1; ring

theorem reciprocal_logWeights_sum_le {m : ℕ} (q : Fin m → ℕ) (wmin : ℝ)
    (hmin : 0 < wmin) (hwmin : ∀ i, wmin ≤ MatrixArithmetic.logWeights q i) :
    (∑ i, 1 / MatrixArithmetic.logWeights q i) ≤ (m : ℝ) / wmin := by
  calc
    _ ≤ ∑ _i : Fin m, 1 / wmin := Finset.sum_le_sum (fun i _ =>
      one_div_le_one_div_of_le hmin (hwmin i))
    _ = _ := by simp [div_eq_mul_inv]

theorem centeredSelectedMinor_arithmetic_lower_bound_common_error
    {m K : ℕ} {w0 v0 θ F H wmin : ℝ}
    (A B : ℤ) (p : Fin m → ℤ) (q : Fin m → ℕ)
    (hB : 0 < B) (hq : ∀ i, 2 ≤ q i) (hK : 0 < K)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (hθ : 0 < θ) (hF : 0 ≤ F)
    (hH : 0 < H) (hmin : 0 < wmin) (hwmin : ∀ i, wmin ≤ MatrixArithmetic.logWeights q i)
    (selection : InterpolationMatrix.Row K v0 θ (MatrixArithmetic.logWeights q) H →
      InterpolationMatrix.Column w0 (MatrixArithmetic.logWeights q) H)
    (hdet : (centeredSelectedMinor K w0 v0 θ F H A B p q selection).det ≠ 0) :
    -(1 - MatrixArithmetic.meanRowWeight K v0 θ q H) -
      (Arithmetic.lcmConstant * F * m / v0 +
        (Arithmetic.lcmConstant * m + θ) / wmin +
        ((K - 1 : ℕ) : ℝ) * Real.log (B : ℝ) / w0) ≤
      Real.log ‖(centeredSelectedMinor K w0 v0 θ F H A B p q selection).det‖ /
        ((Fintype.card (InterpolationMatrix.Row K v0 θ (MatrixArithmetic.logWeights q) H) : ℝ) * H) := by
  have hb := centeredSelectedMinor_arithmetic_lower_bound A B p q
    hB hq hK hw0 hv0 hθ hF hH hmin hwmin selection hdet
  have he : Arithmetic.lcmConstant * (∑ i, 1 / MatrixArithmetic.logWeights q i) + θ / wmin ≤
      (Arithmetic.lcmConstant * m + θ) / wmin := by
    calc
      _ ≤ Arithmetic.lcmConstant * ((m : ℝ) / wmin) + θ / wmin :=
        add_le_add (mul_le_mul_of_nonneg_left
          (reciprocal_logWeights_sum_le q wmin hmin hwmin) Arithmetic.lcmConstant_pos.le) le_rfl
      _ = _ := by ring
  linarith only [hb, he]

end
end IrrationalityReview.RationalLogArithmeticAssembly

#print axioms IrrationalityReview.RationalLogArithmeticAssembly.log_baseColumnScale
#print axioms IrrationalityReview.RationalLogArithmeticAssembly.baseCost_le
#print axioms IrrationalityReview.RationalLogArithmeticAssembly.centeredSelectedMinor_clearing_bound
#print axioms IrrationalityReview.RationalLogArithmeticAssembly.centeredSelectedMinor_arithmetic_lower_bound
#print axioms IrrationalityReview.RationalLogArithmeticAssembly.reciprocal_logWeights_sum_le
#print axioms IrrationalityReview.RationalLogArithmeticAssembly.centeredSelectedMinor_arithmetic_lower_bound_common_error
