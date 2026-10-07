import RationalLogAnalytic
import OAIFormalLogAdapter
import RationalLogParameters
import RationalLogArithmeticAssembly
import RationalLogMatrixBridge
import OAI.NumberTheory.PiExponent.Approximation.MatrixCounting
import OAI.NumberTheory.PiExponent.Analysis.TranslationCountLimit

/-! Actual rational-logarithm analytic aggregate and H-asymptotic assembly.
No determinant estimate, counting asymptotic, or vanishing remainder is assumed.
Only literal finite data and elementary positive-weight/approximation budgets
are inputs. The interpolation geometry is kept as a separate eventual
surjectivity premise for the final contradiction. -/

namespace RationalLogReview.Analytic
open scoped BigOperators Topology
open Filter MvPolynomial OAI.PiExponent

structure Data (nu : ℝ) where
  r : ℚ
  r_pos : 0 < r
  m : ℕ
  K : ℕ
  K_pos : 1 ≤ K
  w0 : ℚ
  v0 : ℚ
  theta : ℚ
  A : ℚ
  w0_pos : 0 < (w0 : ℝ)
  v0_pos : 0 < (v0 : ℝ)
  theta_pos : 0 < (theta : ℝ)
  A_pos : 0 < (A : ℝ)
  eta : ℝ
  F0 : ℝ
  wstar : ℝ
  R0 : ℝ
  eta_pos : 0 < eta
  F0_pos : 0 < F0
  wstar_pos : 0 < wstar
  R0_pos : 0 < R0
  p : Fin m → ℤ
  q : Fin m → ℕ
  q_two_le : ∀ i, 2 ≤ q i
  approximations : ∀ i, |Real.log (r : ℝ) - (p i : ℝ) / q i| ≤ (q i : ℝ) ^ (-nu)
  wstar_lower : ∀ i, wstar ≤ MatrixArithmetic.logWeights q i
  radius_budget : 4 * (‖(Real.log (r : ℝ) : ℂ)‖ + 1) ≤ R0

noncomputable def collisionConstant : ℝ := Real.log 2 / 4
theorem collisionConstant_pos : 0 < collisionConstant :=
  div_pos (Real.log_pos (by norm_num)) (by norm_num)

abbrev Row {nu : ℝ} (d : Data nu) (H : ℝ) :=
  InterpolationMatrix.Row d.K d.v0 d.theta (MatrixArithmetic.logWeights d.q) H
abbrev Column {nu : ℝ} (d : Data nu) (H : ℝ) :=
  InterpolationMatrix.Column d.w0 (MatrixArithmetic.logWeights d.q) H

noncomputable def rationalCenters {nu : ℝ} (d : Data nu) : Fin d.m → ℂ :=
  fun i => (d.p i : ℂ) / (d.q i : ℂ)

noncomputable def actualMatrix {nu : ℝ} (d : Data nu) (H : ℝ) :
    Matrix (Row d H) (Column d H) ℂ :=
  fun row col => ((d.r : ℂ) ^ row.1.val) ^ (col.1 0) *
    InterpolationMatrix.entry (rationalCenters d)
      (fun i => InterpolationMatrix.truncatedLog (MatrixArithmetic.truncationOrders d.q d.F0 d.v0 i))
      row.1.val (row.2.1 0) (fun i => row.2.1 i.succ) (col.1 0) (fun i => col.1 i.succ)

noncomputable def actualMinor {nu : ℝ} (d : Data nu) (H : ℝ)
    (selection : Row d H → Column d H) : Matrix (Row d H) (Row d H) ℂ :=
  (actualMatrix d H).submatrix id selection
noncomputable def actualMean {nu : ℝ} (d : Data nu) (H : ℝ) : ℝ :=
  MatrixArithmetic.meanRowWeight d.K d.v0 d.theta d.q H
noncomputable def actualRowCount {nu : ℝ} (d : Data nu) (H : ℝ) : ℕ :=
  Fintype.card (Row d H)
noncomputable def lowIndexCount {nu : ℝ} (d : Data nu) (H : ℝ) : ℕ :=
  (realWeightedSimplex (MatrixArithmetic.logWeights d.q) ((d.A : ℝ) * H)).card
noncomputable def collisionRate {nu : ℝ} (d : Data nu) (H : ℝ) : ℝ :=
  collisionConstant * d.eta ^ 2 * (actualRowCount d H : ℝ) / (H * (lowIndexCount d H : ℝ))
noncomputable def collisionLimit {nu : ℝ} (d : Data nu) : ℝ :=
  collisionConstant * (d.eta ^ 2 * (d.K : ℝ) * (d.theta : ℝ) ^ d.m /
    (((d.m : ℝ) + 1) * (d.v0 : ℝ) * (d.A : ℝ) ^ d.m))
noncomputable def translationError {nu : ℝ} (d : Data nu) : ℝ :=
  nu / d.F0 + Real.log 2 / d.v0 +
    (Real.log 4 + Real.log (2 * (d.K : ℝ)) + nu) / d.wstar
noncomputable def holomorphicError {nu : ℝ} (d : Data nu) : ℝ :=
  (d.R0 * d.K) / d.w0 + Real.log (2 * (d.R0 * d.K)) / d.wstar + Real.log 2 / d.v0
noncomputable def analyticError {nu : ℝ} (d : Data nu) : ℝ :=
  translationError d + holomorphicError d

noncomputable def fixedWeights {nu : ℝ} (d : Data nu) : Fin d.m → ℝ :=
  MatrixArithmetic.logWeights (d.q)

abbrev Transverse {nu : ℝ} (d : Data nu) (H : ℝ) :=
  ↥(MatrixTranslation.transverseIndices (fixedWeights d) H)

noncomputable def beta {nu : ℝ} (d : Data nu) {H : ℝ} (r : Row d H) : Fin d.m →₀ ℕ :=
  InterpolationMatrix.exponentVector (fun i => r.2.1 i.succ)

abbrev RowChoice {nu : ℝ} (d : Data nu) (H : ℝ) (r : Row d H) :=
  RowTranslation.RowChoices (MatrixTranslation.transverseIndices (fixedWeights d) H)
    (beta d r) (r.2.1 0)

abbrev ChoiceFamily {nu : ℝ} (d : Data nu) (H : ℝ) :=
  ∀ r : Row d H, RowChoice d H r

noncomputable def indexWeight {nu : ℝ} (d : Data nu) {H : ℝ} (a : Transverse d H) : ℝ :=
  MatrixTranslationBounds.weight (fixedWeights d) (fun i => a.1 i)

noncomputable def rowWeight {nu : ℝ} (d : Data nu) {H : ℝ} (r : Row d H) : ℝ :=
  MatrixTranslationBounds.weight (fixedWeights d) (fun i => beta d r i)

noncomputable def choiceScalar {nu : ℝ} (d : Data nu) {H : ℝ}
    (r : Row d H) (t : RowChoice d H r) : ℂ :=
  RowTranslation.rowScalar
    (fun i => (r.1.val : ℂ) *
      (rationalCenters d i - (Real.log (d.r : ℝ) : ℂ)))
    (fun i => RowTranslation.tail
      (MatrixArithmetic.truncationOrders (d.q) d.F0 d.v0 i) (PowerSeries.log ℂ))
    (beta d r) t.1.1 t.2.1 t.2.2

noncomputable def choiceMatrix {nu : ℝ} (d : Data nu) {H : ℝ}
    (selection : Row d H → Column d H) (f : ChoiceFamily d H) : Matrix (Row d H) (Row d H) ℂ :=
  fun r c => PowerSeries.coeff (r.2.1 0 - (f r).2.2)
    ((RationalLogOAI017.rationalPeriodMonomial ((d.r : ℂ) ^ r.1.val) r.1.val (Real.log (d.r : ℝ) : ℂ)
      ((selection c).1 0) (fun i => (selection c).1 i.succ)).coeff (f r).1.1)

theorem fixedWeights_pos {nu : ℝ} (d : Data nu) (i : Fin d.m) :
    0 < fixedWeights d i := MatrixArithmetic.ceil_log_weight_pos (d.q_two_le i)

theorem fixedWeights_lower {nu : ℝ} (d : Data nu) (i : Fin d.m) :
    d.wstar ≤ fixedWeights d i := d.wstar_lower i

theorem fixedWeights_one_le {nu : ℝ} (d : Data nu) (i : Fin d.m) :
    1 ≤ fixedWeights d i := by
  have hn : 0 < ⌈Real.log (d.q i)⌉₊ := by
    exact_mod_cast MatrixArithmetic.ceil_log_weight_pos (d.q_two_le i)
  change 1 ≤ (⌈Real.log (d.q i)⌉₊ : ℝ)
  exact_mod_cast Nat.succ_le_of_lt hn

theorem rowOrder_le {nu : ℝ} (d : Data nu) {H : ℝ} (r : Row d H) :
    (r.2.1 0 : ℝ) ≤ H / (d.v0 : ℝ) := by
  have hr := InterpolationMatrix.row_weight_lt d.v0_pos d.theta_pos (fixedWeights_pos d) r
  have hs : 0 ≤ (∑ i, fixedWeights d i * (r.2.1 i.succ : ℝ)) / (d.theta : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (fixedWeights_pos d i).le (Nat.cast_nonneg _))
      d.theta_pos.le
  apply (le_div_iff₀ d.v0_pos).mpr
  nlinarith

theorem indexWeight_nonneg {nu : ℝ} (d : Data nu) {H : ℝ} (a : Transverse d H) :
    0 ≤ indexWeight d a := by
  unfold indexWeight MatrixTranslationBounds.weight
  exact Finset.sum_nonneg fun i _ => mul_nonneg (fixedWeights_pos d i).le (Nat.cast_nonneg _)

theorem indexWeight_le {nu : ℝ} (d : Data nu) {H : ℝ} (a : Transverse d H) :
    indexWeight d a ≤ H :=
  (MatrixTranslation.mem_transverseIndices (fixedWeights d) H (fixedWeights_pos d) a.1).mp a.2

theorem norm_choiceScalar_le {nu : ℝ} (d : Data nu) (hnu : 0 ≤ nu)
    {H : ℝ} (r : Row d H) (t : RowChoice d H r) :
    ‖choiceScalar d r t‖ ≤ Real.exp
      (-nu * (indexWeight d t.1 - rowWeight d r) + H * translationError d) := by
  have hk : ((t.2.2 : ℕ) : ℝ) ≤ H / (d.v0 : ℝ) := by
    apply le_trans _ (rowOrder_le d r)
    exact_mod_cast Nat.le_of_lt_succ t.2.2.isLt
  have hT : ∀ i, 1 ≤ MatrixArithmetic.truncationOrders d.q d.F0 d.v0 i :=
    fun i => MatrixTranslationBounds.truncationOrder_pos d.F0_pos d.v0_pos (fixedWeights_pos d i)
  have hTw : ∀ i, d.F0 * fixedWeights d i ≤
      (d.v0 : ℝ) * MatrixArithmetic.truncationOrders d.q d.F0 d.v0 i :=
    fun _ => MatrixTranslationBounds.truncationOrder_budget d.v0_pos
  have hb := RationalLogOAI017.rational_log_rowScalar_bound
    (Real.log (d.r : ℝ)) nu d.p d.q
    (MatrixArithmetic.truncationOrders d.q d.F0 d.v0) r.1.val d.K
    (beta d r) t.1.1 t.2.1 t.2.2 (fixedWeights d) H d.wstar d.v0 d.F0
    hnu d.K_pos r.1.isLt.le (fun i => (by decide : 1 ≤ 2).trans (d.q_two_le i))
    d.approximations (fun _ => rfl) d.wstar_pos d.v0_pos d.F0_pos
    (fixedWeights_lower d) (indexWeight_le d t.1) hk hT hTw
  simpa only [choiceScalar, indexWeight, rowWeight, translationError, rationalCenters,
    Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_intCast,
    Complex.ofReal_natCast] using hb

theorem rowWeight_le_indexWeight_of_ne_zero {nu : ℝ} (d : Data nu)
    {H : ℝ} (r : Row d H) (t : RowChoice d H r) (ht : choiceScalar d r t ≠ 0) :
    rowWeight d r ≤ indexWeight d t.1 := by
  have h := RowTranslation.rowScalar_ne_zero_le _ _ _ _ _ _ ht
  unfold rowWeight indexWeight MatrixTranslationBounds.weight
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by exact_mod_cast h i)
    (fixedWeights_pos d i).le

theorem actualRowCount_pos {nu : ℝ} (d : Data nu) {H : ℝ} (hH : 0 < H) :
    0 < actualRowCount d H :=
  MatrixArithmetic.actual_row_card_pos (lt_of_lt_of_le Nat.zero_lt_one d.K_pos) d.v0_pos d.theta_pos hH
    (fixedWeights_pos d)

theorem sum_rowWeight_eq {nu : ℝ} (d : Data nu) {H : ℝ} (hH : 0 < H) :
    (∑ r : Row d H, rowWeight d r) = (actualRowCount d H : ℝ) * H * actualMean d H := by
  have hM : (actualRowCount d H : ℝ) ≠ 0 := by exact_mod_cast (actualRowCount_pos d hH).ne'
  unfold actualMean MatrixArithmetic.meanRowWeight
  change (∑ r : Row d H, rowWeight d r) = (actualRowCount d H : ℝ) * H *
    (MatrixArithmetic.rowWeightedSum d.K d.v0 d.theta (d.q) H /
      ((actualRowCount d H : ℝ) * H))
  rw [mul_div_cancel₀ _ (mul_ne_zero hM hH.ne')]
  unfold MatrixArithmetic.rowWeightedSum rowWeight MatrixTranslationBounds.weight beta fixedWeights
  simp only [InterpolationMatrix.exponentVector_apply, mul_comm]

theorem low_transverse_capacity {nu : ℝ} (d : Data nu) (H : ℝ) :
    (((Finset.univ : Finset (Transverse d H)).filter
      (fun A => indexWeight d A ≤ (d.A : ℝ) * H)).card : ℝ) ≤ lowIndexCount d H := by
  classical
  let f : {A : Transverse d H // indexWeight d A ≤ (d.A : ℝ) * H} →
      ↥(MatrixTranslation.transverseIndices (fixedWeights d) ((d.A : ℝ) * H)) :=
    fun A => ⟨A.1.1, (MatrixTranslation.mem_transverseIndices _ _ (fixedWeights_pos d) _).mpr A.2⟩
  have hinj : Function.Injective f := by
    intro A B h
    apply Subtype.ext
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    simpa only [f] using hh
  have hh := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_subtype] at hh
  have hc : Fintype.card ↥(MatrixTranslation.transverseIndices (fixedWeights d)
      ((d.A : ℝ) * H)) = lowIndexCount d H := by
    simp only [Fintype.card_coe, MatrixTranslation.card_transverseIndices]
    rfl
  rw [hc] at hh
  exact_mod_cast hh

theorem lowIndexCount_pos {nu : ℝ} (d : Data nu) {H : ℝ} (hH : 0 < H) :
    0 < lowIndexCount d H := by
  apply Finset.card_pos.mpr
  refine ⟨fun _ => 0, ?_⟩
  apply (mem_realWeightedSimplex (fixedWeights_pos d)).mpr
  simp only [Nat.cast_zero, mul_zero, Finset.sum_const_zero]
  exact mul_nonneg d.A_pos.le hH.le

theorem norm_scalar_product_le {nu : ℝ} (d : Data nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (f : ChoiceFamily d H) :
    ‖∏ r, choiceScalar d r (f r)‖ ≤ Real.exp
      (-nu * ((∑ r, indexWeight d (f r).1) - (actualRowCount d H : ℝ) * H * actualMean d H) +
        (actualRowCount d H : ℝ) * H * translationError d) := by
  rw [norm_prod]
  apply (Finset.prod_le_prod₀ (fun r _ => norm_nonneg _) (fun r _ => norm_choiceScalar_le d hnu r (f r))).trans
  rw [← Real.exp_sum]
  apply le_of_eq
  congr 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, sum_rowWeight_eq d hH]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, actualRowCount]
  ring_nf

theorem norm_choiceMatrix_le {nu : ℝ} (d : Data nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    ‖(choiceMatrix d selection f).det‖ ≤ Real.exp
      (-(Real.log 2 / 4) * (∑ A : Transverse d H,
        (Collision.multiplicity Finset.univ (fun r => (f r).1) A : ℝ) ^ 2) +
        (actualRowCount d H : ℝ) * H *
          (holomorphicError d + Collision.collisionRemainder (actualRowCount d H) H)) := by
  have horders : ((∑ r : Row d H, (r.2.1 0 - ((f r).2.2 : ℕ)) : ℕ) : ℝ) ≤
      (Fintype.card (Row d H) : ℝ) * H / (d.v0 : ℝ) := by
    rw [Nat.cast_sum]
    calc
      _ ≤ ∑ r : Row d H, H / (d.v0 : ℝ) := by
        apply Finset.sum_le_sum
        intro r _
        exact le_trans (by exact_mod_cast Nat.sub_le (r.2.1 0) ((f r).2.2 : ℕ)) (rowOrder_le d r)
      _ = _ := by simp; ring_nf
  let R : NNReal := ⟨d.R0 * d.K, mul_nonneg d.R0_pos.le (Nat.cast_nonneg _)⟩
  have hR1 : 1 ≤ (R : ℝ) := by
    have hK : (1 : ℝ) ≤ d.K := by exact_mod_cast d.K_pos
    have hR0 : 4 ≤ d.R0 := by nlinarith [d.radius_budget, norm_nonneg (Real.log (d.r : ℝ) : ℂ)]
    change 1 ≤ d.R0 * d.K
    nlinarith
  have hc := RationalLogOAI017.rational_log_center_radius_budget d.K
    (fun r : Row d H => r.1.val) (Real.log (d.r : ℝ) : ℂ) d.R0 d.K_pos
    (fun r => r.1.isLt) d.radius_budget
  have hb := RationalLogOAI017.rational_log_coefficient_determinant_bound d.r d.r_pos
    (fun r => (f r).1) (fun A : Transverse d H => A.1)
    (fun r => r.1.val) (fun r => r.2.1 0 - ((f r).2.2 : ℕ))
    (fun c => (selection c).1 0) (fun c i => (selection c).1 i.succ)
    (fixedWeights d) R hR1 hH d.w0_pos d.wstar_pos (fixedWeights_lower d)
    (fun c => InterpolationMatrix.column_weight_le d.w0_pos (fixedWeights_pos d) (selection c))
    hc horders
  convert! hb using 1

theorem norm_actual_summand_le {nu : ℝ} (d : Data nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    ‖(∏ r, choiceScalar d r (f r)) * (choiceMatrix d selection f).det‖ ≤
    Real.exp ((actualRowCount d H : ℝ) * H *
      (analyticError d + Collision.collisionRemainder (actualRowCount d H) H +
        max (-collisionRate d H)
          (-nu * ((d.A : ℝ) * (1 - d.eta) - actualMean d H)))) := by
  classical
  by_cases hs : (∏ r, choiceScalar d r (f r)) = 0
  · simp [hs, Real.exp_nonneg]
  have hmono : (actualRowCount d H : ℝ) * H * actualMean d H ≤ ∑ r, indexWeight d (f r).1 := by
    rw [← sum_rowWeight_eq d hH]
    apply Finset.sum_le_sum
    intro r _
    apply rowWeight_le_indexWeight_of_ne_zero d r (f r)
    exact Finset.prod_ne_zero_iff.mp hs r (Finset.mem_univ r)
  have hb := DeterminantAnalyticBound.translated_summand_bound
    (fun r => (f r).1) (fun A : Transverse d H => indexWeight d A)
    (∏ r, choiceScalar d r (f r)) (choiceMatrix d selection f).det
    hH d.A_pos.le d.eta_pos.le hnu collisionConstant_pos.le
    (by exact_mod_cast lowIndexCount_pos d hH)
    (indexWeight_nonneg d) hmono (low_transverse_capacity d H)
    (norm_scalar_product_le d hnu hH f) (norm_choiceMatrix_le d hH selection f)
  convert! hb using 1
  congr 1
  unfold analyticError collisionRate collisionConstant actualRowCount
  ring_nf

theorem actual_minor_expansion {nu : ℝ} (d : Data nu) {H : ℝ}
    (selection : Row d H → Column d H) :
    (actualMinor d H selection).det =
      ∑ f : ChoiceFamily d H, (∏ r, choiceScalar d r (f r)) * (choiceMatrix d selection f).det := by
  classical
  have hp : ∀ r c : Row d H,
      (RationalLogOAI017.rationalPeriodMonomial ((d.r : ℂ) ^ r.1.val) r.1.val (Real.log (d.r : ℝ) : ℂ)
        ((selection c).1 0) (fun i => (selection c).1 i.succ)).support ⊆
        MatrixTranslation.transverseIndices (fixedWeights d) H := by
    intro r c
    apply IrrationalityReview.OAIFormalLogAdapter.centeredPeriodMonomial_support_subset _ _ _ _ _ _ _ (fixedWeights_pos d)
    have hc := InterpolationMatrix.column_weight_le d.w0_pos (fixedWeights_pos d) (selection c)
    have hz : 0 ≤ (d.w0 : ℝ) * ((selection c).1 0 : ℝ) :=
      mul_nonneg d.w0_pos.le (Nat.cast_nonneg _)
    linarith
  have he := RationalLogOAI017.rational_det_matrix_translation
    (fun r : Row d H => (d.r : ℂ) ^ r.1.val)
    (rationalCenters d)
    (MatrixArithmetic.truncationOrders (d.q) d.F0 d.v0)
    (fun r : Row d H => r.1.val) (fun r => r.2.1 0) (Real.log (d.r : ℝ) : ℂ)
    (fun r i => r.2.1 i.succ) (fun c => (selection c).1 0)
    (fun c i => (selection c).1 i.succ) (MatrixTranslation.transverseIndices (fixedWeights d) H) hp
  convert! he using 1

theorem card_choiceFamily_le {nu : ℝ} (d : Data nu) (H : ℝ) :
    Fintype.card (ChoiceFamily d H) ≤ translationTermCount d.m d.v0 H ^ actualRowCount d H := by
  classical
  rw [Fintype.card_pi]
  calc
    _ ≤ ∏ _r : Row d H, translationTermCount d.m d.v0 H := by
      apply Finset.prod_le_prod
      intro r _
      exact MatrixTranslation.row_term_count (fixedWeights d) H d.v0
        (fixedWeights_one_le d)
        (beta d r) (r.2.1 0) (rowOrder_le d r)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, actualRowCount]

noncomputable def analyticRemainder {nu : ℝ} (d : Data nu) (H : ℝ) : ℝ :=
  Collision.collisionRemainder (actualRowCount d H) H +
    Real.log (translationTermCount d.m d.v0 H : ℝ) / H

theorem actual_minor_analytic_bound {nu : ℝ} (d : Data nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (selection : Row d H → Column d H)
    (hne : (actualMinor d H selection).det ≠ 0) :
    Real.log ‖(actualMinor d H selection).det‖ / ((actualRowCount d H : ℝ) * H) ≤
      analyticError d + analyticRemainder d H +
        max (-collisionRate d H)
          (-nu * ((d.A : ℝ) * (1 - d.eta) - actualMean d H)) := by
  have hQ : (0 : ℝ) < translationTermCount d.m d.v0 H := by
    unfold translationTermCount
    positivity
  have hc : (Fintype.card (ChoiceFamily d H) : ℝ) ≤
      (translationTermCount d.m d.v0 H : ℝ) ^ actualRowCount d H := by
    exact_mod_cast card_choiceFamily_le d H
  have hb := DeterminantAnalyticBound.log_norm_sum_le
    (fun f : ChoiceFamily d H => (∏ r, choiceScalar d r (f r)) * (choiceMatrix d selection f).det)
    (actualMinor d H selection).det (actualRowCount_pos d hH) hH hQ hc
    (actual_minor_expansion d selection) hne (norm_actual_summand_le d hnu hH selection)
  convert! hb using 1
  unfold analyticRemainder
  ring

theorem tendsto_analyticRemainder {nu : ℝ} (d : Data nu) :
    Tendsto (analyticRemainder d) atTop (𝓝 0) := by
  have hv : 0 < d.v0 := by exact_mod_cast d.v0_pos
  have ht : 0 < d.theta := by exact_mod_cast d.theta_pos
  have hcount := MatrixCounting.tendsto_rowCount_normalized d.K d.v0 d.theta
    (d.q) hv ht (d.q_two_le)
  have hlead : 0 < (d.K : ℝ) * (d.theta : ℝ) ^ d.m /
      (((d.m + 1).factorial : ℝ) * (d.v0 : ℝ) *
        ∏ i, MatrixArithmetic.logWeights (d.q) i) := by
    apply div_pos
    · apply mul_pos
      · exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one d.K_pos
      · exact pow_pos d.theta_pos _
    · apply mul_pos
      · exact mul_pos (by positivity) d.v0_pos
      · exact Finset.prod_pos (fun i _ => fixedWeights_pos d i)
  have hr := tendsto_collisionRemainder_of_normalized_pow
    (M := actualRowCount d) hcount hlead
  have hq := tendsto_log_translationTermCount_div d.m d.v0_pos
  convert! hr.add hq using 1
  norm_num

theorem actualMean_bounds {nu : ℝ} (d : Data nu) (H : ℝ) (hH : 0 < H) :
    0 ≤ actualMean d H ∧ actualMean d H ≤ (d.theta : ℝ) :=
  ⟨MatrixArithmetic.meanRowWeight_nonneg _ _ _ _ hH.le,
    MatrixArithmetic.meanRowWeight_le_theta d.q d.q_two_le
      (Nat.zero_lt_of_lt d.K_pos) d.v0_pos d.theta_pos hH⟩

theorem tendsto_collisionRate {nu : ℝ} (d : Data nu) :
    Tendsto (collisionRate d) atTop (𝓝 (collisionLimit d)) := by
  have hv : 0 < d.v0 := by exact_mod_cast d.v0_pos
  have ht : 0 < d.theta := by exact_mod_cast d.theta_pos
  have hA : 0 < d.A := by exact_mod_cast d.A_pos
  have hh := MatrixCounting.tendsto_collisionRatio d.K d.v0 d.theta d.A d.q
    hv ht hA d.q_two_le collisionConstant d.eta
  have he : collisionConstant * d.eta ^ 2 * (d.K : ℝ) * (d.theta : ℝ) ^ d.m /
      (((d.m : ℝ) + 1) * (d.v0 : ℝ) * (d.A : ℝ) ^ d.m) = collisionLimit d := by
    unfold collisionLimit
    ring
  rw [he] at hh
  exact hh

/-- The full normalized analytic aggregate, with an explicitly constructed
vanishing remainder. No target bound or limit is an input hypothesis. -/
theorem analytic_aggregate {nu : ℝ} (d : Data nu) (hnu : 0 ≤ nu) :
    ∃ error : ℝ → ℝ, Tendsto error atTop (𝓝 0) ∧
      ∀ᶠ H : ℝ in atTop, ∀ selection : Row d H → Column d H,
        (actualMinor d H selection).det ≠ 0 →
        Real.log ‖(actualMinor d H selection).det‖ / ((actualRowCount d H : ℝ) * H) ≤
          analyticError d + error H + max (-collisionRate d H)
            (-nu * ((d.A : ℝ) * (1 - d.eta) - actualMean d H)) := by
  refine ⟨analyticRemainder d, tendsto_analyticRemainder d, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  exact fun selection hne => actual_minor_analytic_bound d hnu hH selection hne

/-- The analytic data are constructed from the already proved parameter and
successive-approximation selection. None of the analytic/counting conclusions
is a field of the selected data. -/
noncomputable def ofSelected (r : ℚ) (hr : 0 < r) {nu Lambda c : ℝ}
    (d : Parameters.SelectedParameters (Real.log (r : ℝ)) nu Lambda c
      (Parameters.baseRadius r) (Parameters.denominatorHeight r)) : Data nu := {
  r := r, r_pos := hr, m := d.m, K := d.K, K_pos := d.K_pos,
  w0 := d.w0, v0 := d.v0, theta := d.base.theta, A := d.base.A,
  w0_pos := d.w0_pos, v0_pos := d.v0_pos, theta_pos := d.base.theta_pos,
  A_pos := d.base.A_pos, eta := d.base.eta, eta_pos := d.base.eta_pos,
  F0 := d.F0, F0_pos := d.F0_pos, wstar := d.wstar, wstar_pos := d.wstar_pos,
  R0 := Parameters.baseRadius r,
  R0_pos := lt_of_lt_of_le zero_lt_one (Parameters.baseRadius_bounds r).1,
  p := fun i => d.p i.val, q := fun i => d.q i.val,
  q_two_le := fun i => (d.approximations i.val).1,
  approximations := fun i => (d.approximations i.val).2,
  wstar_lower := by
    intro i
    change d.wstar ≤ (⌈Real.log (d.q i.val)⌉₊ : ℝ)
    rw [← d.w_log i.val]
    exact d.wstar_lower i,
  radius_budget := by
    rw [Complex.norm_real]
    exact (Parameters.baseRadius_bounds r).2.le
}

theorem analyticError_ofSelected (r : ℚ) (hr : 0 < r) {nu Lambda c : ℝ}
    (d : Parameters.SelectedParameters (Real.log (r : ℝ)) nu Lambda c
      (Parameters.baseRadius r) (Parameters.denominatorHeight r)) :
    analyticError (ofSelected r hr d) = d.analyticError := by
  unfold analyticError translationError holomorphicError
    Parameters.SelectedParameters.analyticError Parameters.SelectedParameters.translationError
    Parameters.SelectedParameters.holomorphicError
  dsimp only [ofSelected]
  simp only [mul_assoc]
  ring

theorem collisionLimit_ofSelected (r : ℚ) (hr : 0 < r) {nu Lambda : ℝ}
    (d : Parameters.SelectedParameters (Real.log (r : ℝ)) nu Lambda collisionConstant
      (Parameters.baseRadius r) (Parameters.denominatorHeight r)) :
    collisionLimit (ofSelected r hr d) = d.collisionLimit := rfl

/-- The literal analytic minor is the independently denominator-cleared
arithmetic minor, using the canonical numerator and denominator of r. -/
theorem actualMinor_eq_centeredSelectedMinor {nu : ℝ} (d : Data nu) (H : ℝ)
    (selection : Row d H → Column d H) :
    actualMinor d H selection =
      IrrationalityReview.RationalLogArithmeticAssembly.centeredSelectedMinor
        d.K d.w0 d.v0 d.theta d.F0 H d.r.num (d.r.den : ℤ) d.p d.q selection := by
  ext row col
  simp only [actualMinor, actualMatrix, Matrix.submatrix_apply, id_eq,
    IrrationalityReview.RationalLogArithmeticAssembly.centeredSelectedMinor,
    IrrationalityReview.OAIFormalLogAdapter.centeredRationalMatrix,
    IrrationalityReview.OAIFormalLogAdapter.centeredEntry_eq_original_entry,
    Rat.cast_def, Int.cast_natCast]
  rfl

noncomputable def arithmeticError {nu : ℝ} (d : Data nu) : ℝ :=
  Arithmetic.lcmConstant * d.F0 * d.m / d.v0 +
    Arithmetic.lcmConstant * (∑ i, 1 / fixedWeights d i) + (d.theta : ℝ) / d.wstar +
    ((d.K : ℝ) - 1) * Real.log (d.r.den : ℝ) / d.w0

/-- The normalized arithmetic lower estimate is derived from actual entry
clearing; the extra rational-base denominator loss is retained. -/
theorem actual_minor_arithmetic_lower_bound {nu : ℝ} (d : Data nu)
    (H : ℝ) (hH : 0 < H) (selection : Row d H → Column d H)
    (hdet : (actualMinor d H selection).det ≠ 0) :
    -(1 - actualMean d H) - arithmeticError d ≤
      Real.log ‖(actualMinor d H selection).det‖ / ((actualRowCount d H : ℝ) * H) := by
  have hB : (0 : ℤ) < (d.r.den : ℤ) := by exact_mod_cast d.r.pos
  have hdet' : (IrrationalityReview.RationalLogArithmeticAssembly.centeredSelectedMinor
      d.K d.w0 d.v0 d.theta d.F0 H d.r.num (d.r.den : ℤ) d.p d.q selection).det ≠ 0 := by
    rw [← actualMinor_eq_centeredSelectedMinor d H selection]
    exact hdet
  have hb := IrrationalityReview.RationalLogArithmeticAssembly.centeredSelectedMinor_arithmetic_lower_bound
    d.r.num (d.r.den : ℤ) d.p d.q hB d.q_two_le (Nat.zero_lt_of_lt d.K_pos)
    d.w0_pos d.v0_pos d.theta_pos d.F0_pos.le hH d.wstar_pos
    (fixedWeights_lower d) selection hdet'
  rw [← actualMinor_eq_centeredSelectedMinor d H selection] at hb
  have hK : ((d.K - 1 : ℕ) : ℝ) = (d.K : ℝ) - 1 := by
    rw [Nat.cast_sub d.K_pos, Nat.cast_one]
  simpa only [actualMean, arithmeticError, actualRowCount, fixedWeights,
    Int.cast_natCast, hK] using hb

theorem arithmeticError_ofSelected (r : ℚ) (hr : 0 < r) {nu : ℝ}
    (d : Parameters.SelectedParameters (Real.log (r : ℝ)) nu Arithmetic.lcmConstant collisionConstant
      (Parameters.baseRadius r) (Parameters.denominatorHeight r)) :
    arithmeticError (ofSelected r hr d) = d.arithmeticError := by
  unfold arithmeticError fixedWeights MatrixArithmetic.logWeights
    Parameters.SelectedParameters.arithmeticError Parameters.denominatorHeight
  dsimp only [ofSelected]
  simp_rw [← d.w_log]
  rfl

/-- All analytic, arithmetic, cardinality and limiting estimates have been
discharged. The only input is cofinal surjectivity of the literal rational-base
weighted matrix, which is the interpolation/geometry conclusion of A. -/
theorem selected_contradiction_of_cofinal_interpolation
    (r : ℚ) (hr : 0 < r) (nu : ℝ) (hnu : 2 < nu)
    (d : Parameters.SelectedParameters (Real.log (r : ℝ)) nu Arithmetic.lcmConstant collisionConstant
      (Parameters.baseRadius r) (Parameters.denominatorHeight r))
    (hgeometry : ∀ L : ℝ, ∃ H : ℝ, L ≤ H ∧
      Function.Surjective (actualMatrix (ofSelected r hr d) H).mulVecLin) : False := by
  classical
  apply d.contradiction_of_cofinal_bounds hnu
    (analyticRemainder (ofSelected r hr d)) (collisionRate (ofSelected r hr d))
    (tendsto_analyticRemainder (ofSelected r hr d))
  · rw [← collisionLimit_ofSelected r hr d]
    exact tendsto_collisionRate (ofSelected r hr d)
  · intro L
    obtain ⟨H, hLH, hsurj⟩ := hgeometry (max L 1)
    have hH : 0 < H := lt_of_lt_of_le zero_lt_one ((le_max_right L 1).trans hLH)
    obtain ⟨selection, _hinj, hdet⟩ :=
      InterpolationMatrix.exists_full_row_minor_of_surjective
        (actualMatrix (ofSelected r hr d) H) hsurj
    have hdet' : (actualMinor (ofSelected r hr d) H selection).det ≠ 0 := hdet
    have hb := actualMean_bounds (ofSelected r hr d) H hH
    have hl := actual_minor_arithmetic_lower_bound (ofSelected r hr d) H hH selection hdet'
    have hu := actual_minor_analytic_bound (ofSelected r hr d) (by linarith) hH selection hdet'
    rw [arithmeticError_ofSelected r hr d] at hl
    rw [analyticError_ofSelected r hr d] at hu
    exact ⟨H, (le_max_left L 1).trans hLH,
      actualMean (ofSelected r hr d) H,
      Real.log ‖(actualMinor (ofSelected r hr d) H selection).det‖ /
        ((actualRowCount (ofSelected r hr d) H : ℝ) * H), hb.1, hb.2, hl, hu⟩

def CofinalActualInterpolation (r : ℚ) (hr : 0 < r) : Prop :=
  ∀ nu : ℝ, 2 < nu →
    ∀ d : Parameters.SelectedParameters (Real.log (r : ℝ)) nu Arithmetic.lcmConstant collisionConstant
      (Parameters.baseRadius r) (Parameters.denominatorHeight r),
      ∀ L : ℝ, ∃ H : ℝ, L ≤ H ∧
        Function.Surjective (actualMatrix (ofSelected r hr d) H).mulVecLin

/-- B is fully formalized conditional solely on its actual interpolation
input. Neither target determinant estimates nor any counts/limits are inputs. -/
theorem rational_log_endpoint_of_cofinal_interpolation
    (r : ℚ) (hr : 0 < r) (hgeometry : CofinalActualInterpolation r hr) :
    OAIAdapter.ManuscriptStrictBound (Real.log (r : ℝ)) ∧
      Irrational (Real.log (r : ℝ)) ∧
      OAI.PiExponent.irrationalityExponent (Real.log (r : ℝ)) = 2 := by
  apply Parameters.rational_log_endpoint_of_selected_contradictions r
    Arithmetic.lcmConstant collisionConstant Arithmetic.lcmConstant_pos collisionConstant_pos
  intro nu hnu d
  exact selected_contradiction_of_cofinal_interpolation r hr nu hnu d (hgeometry nu hnu d)

noncomputable def sourceWeights {nu : ℝ} (d : Data nu) : Fin (d.m + 1) → ℚ :=
  Fin.cases d.w0 (MatrixCounting.rationalLogWeights d.q)

noncomputable def targetWeights {nu : ℝ} (d : Data nu) : Fin (d.m + 1) → ℚ :=
  Fin.cases d.v0 (fun i => MatrixCounting.rationalLogWeights d.q i / d.theta)

theorem sourceWeights_cast {nu : ℝ} (d : Data nu) (i : Fin (d.m + 1)) :
    (sourceWeights d i : ℝ) =
      InterpolationMatrix.columnWeights d.w0 (MatrixArithmetic.logWeights d.q) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp [sourceWeights, InterpolationMatrix.columnWeights]

theorem targetWeights_cast {nu : ℝ} (d : Data nu) (i : Fin (d.m + 1)) :
    (targetWeights d i : ℝ) =
      InterpolationMatrix.rowWeights d.v0 d.theta (MatrixArithmetic.logWeights d.q) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp [targetWeights, InterpolationMatrix.rowWeights]

theorem targetWeights_pos {nu : ℝ} (d : Data nu) (i : Fin (d.m + 1)) :
    0 < targetWeights d i := by
  have hv : 0 < d.v0 := by exact_mod_cast d.v0_pos
  have ht : 0 < d.theta := by exact_mod_cast d.theta_pos
  exact Fin.cases hv
    (fun j => div_pos (MatrixCounting.rationalLogWeights_pos d.q d.q_two_le j) ht) i

/-- Actual A input at the explicitly constructed weighted rational-log data.
It is cofinal surjectivity of the genuine new formal logarithmic packet map,
not an assumed minor, determinant bound, cardinality estimate or limit. -/
def CofinalPacketInterpolation (r : ℚ) (hr : 0 < r) : Prop :=
  ∀ nu : ℝ, 2 < nu →
    ∀ d : Parameters.SelectedParameters (Real.log (r : ℝ)) nu Arithmetic.lcmConstant collisionConstant
      (Parameters.baseRadius r) (Parameters.denominatorHeight r),
      ∀ L : ℝ, ∃ H : ℚ, L ≤ (H : ℝ) ∧
        Function.Surjective (DistinctMultiplicative.packetMapAt
          (sourceWeights (ofSelected r hr d)) (targetWeights (ofSelected r hr d)) H
          (fun j : Fin d.K => (r : ℂ) ^ j.val)
          (fun j : Fin d.K => fun i => (j.val : ℂ) * ((d.p i.val : ℂ) / (d.q i.val : ℂ))))

theorem selected_contradiction_of_cofinal_packets
    (r : ℚ) (hr : 0 < r) (nu : ℝ) (hnu : 2 < nu)
    (d : Parameters.SelectedParameters (Real.log (r : ℝ)) nu Arithmetic.lcmConstant collisionConstant
      (Parameters.baseRadius r) (Parameters.denominatorHeight r))
    (hgeometry : ∀ L : ℝ, ∃ H : ℚ, L ≤ (H : ℝ) ∧
      Function.Surjective (DistinctMultiplicative.packetMapAt
        (sourceWeights (ofSelected r hr d)) (targetWeights (ofSelected r hr d)) H
        (fun j : Fin d.K => (r : ℂ) ^ j.val)
        (fun j : Fin d.K => fun i => (j.val : ℂ) * ((d.p i.val : ℂ) / (d.q i.val : ℂ))))) : False := by
  classical
  let a := ofSelected r hr d
  apply d.contradiction_of_cofinal_bounds hnu
    (analyticRemainder a) (collisionRate a)
    (tendsto_analyticRemainder a)
  · rw [← collisionLimit_ofSelected r hr d]
    exact tendsto_collisionRate a
  · intro L
    obtain ⟨H, hLH, hpacket⟩ := hgeometry (max L 1)
    have hHr : (0 : ℝ) < H := lt_of_lt_of_le zero_lt_one ((le_max_right L 1).trans hLH)
    have hH : 0 < H := by exact_mod_cast hHr
    have hFtheta : 1 ≤ a.F0 * (a.theta : ℝ) := by
      change 1 ≤ d.F0 * (d.base.theta : ℝ)
      have hf := (div_lt_iff₀ d.base.theta_pos).mp d.F0_large
      linarith
    have hT := IrrationalityReview.RationalLogMatrixBridge.truncationOrders_satisfy_packet_weight
      a.q a.q_two_le a.F0 a.v0 a.theta
      a.v0_pos a.theta_pos hFtheta (targetWeights a)
      (targetWeights_cast a)
    obtain ⟨selection, _hinj, hdet⟩ :=
      IrrationalityReview.RationalLogMatrixBridge.rationalBase_nonzero_centeredSelectedMinor
        a.K a.w0 a.v0 a.theta a.F0 H a.r.num (a.r.den : ℤ)
        a.p a.q a.w0_pos a.q_two_le
        (sourceWeights a) (targetWeights a)
        (targetWeights_pos a) (sourceWeights_cast a)
        (targetWeights_cast a) hT
        (by simpa only [a, ofSelected, Rat.cast_def, Int.cast_natCast] using hpacket)
    have hdet' : (actualMinor a (H : ℝ) selection).det ≠ 0 := by
      rw [actualMinor_eq_centeredSelectedMinor a (H : ℝ) selection]
      exact hdet
    have hb := actualMean_bounds a (H : ℝ) hHr
    have hl := actual_minor_arithmetic_lower_bound a (H : ℝ) hHr selection hdet'
    have hu := actual_minor_analytic_bound a (by linarith) hHr selection hdet'
    rw [arithmeticError_ofSelected r hr d] at hl
    rw [analyticError_ofSelected r hr d] at hu
    exact ⟨(H : ℝ), (le_max_left L 1).trans hLH,
      actualMean a (H : ℝ),
      Real.log ‖(actualMinor a (H : ℝ) selection).det‖ /
        ((actualRowCount a (H : ℝ) : ℝ) * (H : ℝ)), hb.1, hb.2, hl, hu⟩

/-- The final B endpoint uses only the actual A packet interpolation input. -/
theorem rational_log_endpoint_of_cofinal_packets
    (r : ℚ) (hr : 0 < r) (hgeometry : CofinalPacketInterpolation r hr) :
    OAIAdapter.ManuscriptStrictBound (Real.log (r : ℝ)) ∧
      Irrational (Real.log (r : ℝ)) ∧
      OAI.PiExponent.irrationalityExponent (Real.log (r : ℝ)) = 2 := by
  apply Parameters.rational_log_endpoint_of_selected_contradictions r
    Arithmetic.lcmConstant collisionConstant Arithmetic.lcmConstant_pos collisionConstant_pos
  intro nu hnu d
  exact selected_contradiction_of_cofinal_packets r hr nu hnu d (hgeometry nu hnu d)

end RationalLogReview.Analytic

#print axioms RationalLogReview.Analytic.norm_actual_summand_le
#print axioms RationalLogReview.Analytic.actual_minor_expansion
#print axioms RationalLogReview.Analytic.card_choiceFamily_le
#print axioms RationalLogReview.Analytic.actual_minor_analytic_bound
#print axioms RationalLogReview.Analytic.tendsto_analyticRemainder
#print axioms RationalLogReview.Analytic.tendsto_collisionRate
#print axioms RationalLogReview.Analytic.analytic_aggregate
#print axioms RationalLogReview.Analytic.ofSelected
#print axioms RationalLogReview.Analytic.analyticError_ofSelected
#print axioms RationalLogReview.Analytic.collisionLimit_ofSelected
#print axioms RationalLogReview.Analytic.actualMinor_eq_centeredSelectedMinor
#print axioms RationalLogReview.Analytic.actual_minor_arithmetic_lower_bound
#print axioms RationalLogReview.Analytic.arithmeticError_ofSelected
#print axioms RationalLogReview.Analytic.selected_contradiction_of_cofinal_interpolation
#print axioms RationalLogReview.Analytic.rational_log_endpoint_of_cofinal_interpolation
#print axioms RationalLogReview.Analytic.sourceWeights_cast
#print axioms RationalLogReview.Analytic.targetWeights_cast
#print axioms RationalLogReview.Analytic.targetWeights_pos
#print axioms RationalLogReview.Analytic.selected_contradiction_of_cofinal_packets
#print axioms RationalLogReview.Analytic.rational_log_endpoint_of_cofinal_packets
