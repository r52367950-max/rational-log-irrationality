import OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic
import OAI.NumberTheory.PiExponent.Analysis.AnalyticDeterminantCollision
import OAI.NumberTheory.PiExponent.Analysis.DeterminantAnalyticBound
import OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds

/-!
# Rational-base adapter to the genuine OAI017 analytic formalization

Upstream: openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a.
This file imports the proved OAI modules, not ComparatorChallenges/PiExponent.

The new feature is the factor y^h for a center with exp(center) = y,
which replaces the upstream period-specific condition exp(center) = 1.
The Taylor collision and entire monomial bound are reused directly.
-/

namespace RationalLogOAI017

open scoped BigOperators
open MvPolynomial
open OAI.PiExponent

/-- Convert an approximation to any real logarithm into the exponential
error bound required by the generic upstream row-scalar theorem. -/
theorem rational_log_error_exp (ω ν : ℝ) (p : ℤ) (q j K : ℕ)
    (hν : 0 ≤ ν) (hq : 1 ≤ q) (hK : 1 ≤ K) (hj : j ≤ K)
    (happrox : |ω - (p : ℝ) / q| ≤ (q : ℝ) ^ (-ν)) :
    ‖(j : ℂ) * (((p : ℝ) / q - ω : ℝ) : ℂ)‖ ≤
      Real.exp ((Real.log (2 * (K : ℝ)) + ν) - ν * (⌈Real.log q⌉₊ : ℝ)) := by
  have hjR : (j : ℝ) ≤ (K : ℝ) := by exact_mod_cast hj
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  have hqpow : 0 ≤ (q : ℝ) ^ (-ν) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h2K : 0 < 2 * (K : ℝ) := by
    have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    linarith
  have hsmall : ‖(j : ℂ) * (((p : ℝ) / q - ω : ℝ) : ℂ)‖ ≤
      2 * (K : ℝ) * (q : ℝ) ^ (-ν) := by
    rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
    have ha : |(p : ℝ) / q - ω| ≤ (q : ℝ) ^ (-ν) := by
      simpa only [abs_sub_comm] using happrox
    calc
      _ ≤ (K : ℝ) * |(p : ℝ) / q - ω| :=
        mul_le_mul_of_nonneg_right hjR (abs_nonneg _)
      _ ≤ (K : ℝ) * (q : ℝ) ^ (-ν) := mul_le_mul_of_nonneg_left ha hK0
      _ ≤ _ := by nlinarith [mul_nonneg hK0 hqpow]
  calc
    _ ≤ 2 * (K : ℝ) * (q : ℝ) ^ (-ν) := hsmall
    _ ≤ 2 * (K : ℝ) *
        (Real.exp ν * Real.exp (-ν * (⌈Real.log q⌉₊ : ℝ))) :=
      mul_le_mul_of_nonneg_left (rpow_neg_le_exp_ceil_log ν hν hq) h2K.le
    _ = _ := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_log h2K]
      ring

/-- B's scalar saving (6), using the proved generic OAI017 row-scalar
estimate and the logarithm-specific approximation-error adapter above. -/
theorem rational_log_rowScalar_bound {m : ℕ}
    (ω ν : ℝ) (p : Fin m → ℤ) (q T : Fin m → ℕ) (j K : ℕ)
    (β A : Fin m →₀ ℕ) (d : ∀ i, Fin (A i - β i + 1)) (k : ℕ)
    (w : Fin m → ℝ) (H ws v F : ℝ)
    (hν : 0 ≤ ν) (hK : 1 ≤ K) (hj : j ≤ K)
    (hq : ∀ i, 1 ≤ q i)
    (happrox : ∀ i, |ω - (p i : ℝ) / q i| ≤ (q i : ℝ) ^ (-ν))
    (hwlog : ∀ i, w i = (⌈Real.log (q i)⌉₊ : ℝ))
    (hws : 0 < ws) (hv : 0 < v) (hF : 0 < F)
    (hw : ∀ i, ws ≤ w i)
    (hA : MatrixTranslationBounds.weight w (fun i => A i) ≤ H)
    (hk : (k : ℝ) ≤ H / v) (hT : ∀ i, 1 ≤ T i)
    (hTw : ∀ i, F * w i ≤ v * T i) :
    ‖RowTranslation.rowScalar
      (fun i => (j : ℂ) * (((p i : ℝ) / q i - ω : ℝ) : ℂ))
      (fun i => RowTranslation.tail (T i) (PowerSeries.log ℂ)) β A d k‖ ≤
      Real.exp (-ν * (MatrixTranslationBounds.weight w (fun i => A i) -
        MatrixTranslationBounds.weight w (fun i => β i)) +
        H * (ν / F + Real.log 2 / v +
          (Real.log 4 + Real.log (2 * (K : ℝ)) + ν) / ws)) := by
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hC : 0 ≤ Real.log (2 * (K : ℝ)) + ν :=
    add_nonneg (Real.log_nonneg (by linarith)) hν
  have heps : ∀ i,
      ‖(j : ℂ) * (((p i : ℝ) / q i - ω : ℝ) : ℂ)‖ ≤
        Real.exp ((Real.log (2 * (K : ℝ)) + ν) - ν * w i) := by
    intro i
    rw [hwlog i]
    exact rational_log_error_exp ω ν (p i) (q i) j K hν (hq i) hK hj (happrox i)
  have hb := MatrixTranslationBounds.norm_rowScalar_exp_weight_difference
    (fun i => (j : ℂ) * (((p i : ℝ) / q i - ω : ℝ) : ℂ)) T β A d k w
    (Real.log (2 * (K : ℝ)) + ν) ν H ws v F
    hC hν hws hv hF hw hA hk hT hTw heps
  simpa only [add_assoc] using hb

theorem rational_log_center_radius_budget {ι : Type*}
    (K : ℕ) (j : ι → ℕ) (ω : ℂ) (R0 : ℝ)
    (hK : 1 ≤ K) (hj : ∀ r, j r < K)
    (hR0 : 4 * (‖ω‖ + 1) ≤ R0) :
    ∀ r, ‖(j r : ℂ) * ω‖ + 3 / 4 ≤ R0 * (K : ℝ) / 2 := by
  intro r
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hjK : (j r : ℝ) ≤ (K : ℝ) := by exact_mod_cast (Nat.le_of_lt (hj r))
  have hprod := mul_le_mul_of_nonneg_right hR0 hK0
  have hjprod := mul_le_mul_of_nonneg_right hjK (norm_nonneg ω)
  have hKnorm := mul_nonneg hK0 (norm_nonneg ω)
  rw [norm_mul, Complex.norm_natCast]
  nlinarith [hprod, hjprod, hKnorm]

theorem rational_log_row_order_budget {ι : Type*} [Fintype ι]
    (ell : ι → ℕ) (H v0 : ℝ)
    (hell : ∀ r, (ell r : ℝ) ≤ H / v0) :
    ((∑ r, ell r : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) * H / v0 := by
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ _r : ι, H / v0 := Finset.sum_le_sum (fun r _ => hell r)
    _ = _ := by simp; ring

/-- The full Y factor at a multiplicative center y. -/
noncomputable def rationalPeriodMonomial {m : ℕ}
    (y : ℂ) (j : ℕ) (ω : ℂ) (h : ℕ) (a : Fin m → ℕ) :
    MvPolynomial (Fin m) (PowerSeries ℂ) :=
  C (PowerSeries.C (y ^ h)) * MatrixTranslation.periodMonomial j ω h a

/-- The corresponding truncated rational additive-center image. -/
noncomputable def rationalFormalMonomialImage {m : ℕ}
    (y : ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (j h : ℕ) (a : Fin m → ℕ) :
    MvPolynomial (Fin m) (PowerSeries ℂ) :=
  C (PowerSeries.C (y ^ h)) * MatrixTranslation.formalMonomialImage r T j h a

theorem rationalPeriodMonomial_shift {m : ℕ}
    (y : ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (j : ℕ) (ω : ℂ) (h : ℕ) (a : Fin m → ℕ) :
    RowTranslation.shift
      (fun i => PowerSeries.C ((j : ℂ) * (r i - ω)) +
        RowTranslation.tail (T i) (PowerSeries.log ℂ))
      (rationalPeriodMonomial y j ω h a) =
      rationalFormalMonomialImage y r T j h a := by
  unfold rationalPeriodMonomial rationalFormalMonomialImage
  rw [map_mul, RowTranslation.shift_C, MatrixTranslation.periodMonomial_shift]

theorem rationalFormalMonomialImage_coeff {m : ℕ}
    (y : ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (j s : ℕ) (b : Fin m → ℕ) (h : ℕ) (a : Fin m → ℕ) :
    PowerSeries.coeff s ((rationalFormalMonomialImage y r T j h a).coeff
      (InterpolationMatrix.exponentVector b)) =
      y ^ h * InterpolationMatrix.entry r
        (fun i => InterpolationMatrix.truncatedLog (T i)) j s b h a := by
  simp only [rationalFormalMonomialImage, MvPolynomial.coeff_C_mul,
    PowerSeries.coeff_C_mul, MatrixTranslation.formalMonomialImage_coeff]

/-- Exact finite row translation with the rational-base factor retained.
This directly adapts B's equation (5); the base may be any complex y. -/
theorem rational_matrix_entry_translation {m : ℕ}
    (y : ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (j s : ℕ) (ω : ℂ) (b : Fin m → ℕ) (h : ℕ) (a : Fin m → ℕ)
    (S : Finset (Fin m →₀ ℕ))
    (hp : (rationalPeriodMonomial y j ω h a).support ⊆ S) :
    y ^ h * InterpolationMatrix.entry r
      (fun i => InterpolationMatrix.truncatedLog (T i)) j s b h a =
      ∑ A ∈ S, ∑ d : (∀ i, Fin (A i - (InterpolationMatrix.exponentVector b) i + 1)),
        ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal s,
          RowTranslation.rowScalar (fun i => (j : ℂ) * (r i - ω))
            (fun i => RowTranslation.tail (T i) (PowerSeries.log ℂ))
            (InterpolationMatrix.exponentVector b) A d kl.1 *
            PowerSeries.coeff kl.2 ((rationalPeriodMonomial y j ω h a).coeff A) := by
  rw [← rationalFormalMonomialImage_coeff y r T j s b h a,
    ← rationalPeriodMonomial_shift y r T j ω h a]
  exact RowTranslation.exact_row_identity _ _ _ _ S hp s

/-- Reindex the finite translation by the original proved choice type. -/
theorem rational_matrix_entry_translation_choices {m : ℕ}
    (y : ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (j s : ℕ) (ω : ℂ) (b : Fin m → ℕ) (h : ℕ) (a : Fin m → ℕ)
    (S : Finset (Fin m →₀ ℕ))
    (hp : (rationalPeriodMonomial y j ω h a).support ⊆ S) :
    y ^ h * InterpolationMatrix.entry r
      (fun i => InterpolationMatrix.truncatedLog (T i)) j s b h a =
      ∑ t : RowTranslation.RowChoices S (InterpolationMatrix.exponentVector b) s,
        RowTranslation.rowScalar (fun i => (j : ℂ) * (r i - ω))
          (fun i => RowTranslation.tail (T i) (PowerSeries.log ℂ))
          (InterpolationMatrix.exponentVector b) t.1.1 t.2.1 t.2.2 *
          PowerSeries.coeff (s - t.2.2) ((rationalPeriodMonomial y j ω h a).coeff t.1.1) := by
  classical
  rw [rational_matrix_entry_translation y r T j s ω b h a S hp, Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type]
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range]

/-- B's full finite determinant translation, with arbitrary multiplicative
center y_i. Multilinearity is reused from the actual OAI017 theorem. -/
theorem rational_det_matrix_translation
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (y : ι → ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (j s : ι → ℕ) (ω : ℂ) (b : ι → Fin m → ℕ)
    (h : ι → ℕ) (a : ι → Fin m → ℕ) (S : Finset (Fin m →₀ ℕ))
    (hp : ∀ i c, (rationalPeriodMonomial (y i) (j i) ω (h c) (a c)).support ⊆ S) :
    Matrix.det (fun i c => (y i) ^ (h c) * InterpolationMatrix.entry r
      (fun k => InterpolationMatrix.truncatedLog (T k)) (j i) (s i) (b i) (h c) (a c)) =
      ∑ f : (∀ i, RowTranslation.RowChoices S (InterpolationMatrix.exponentVector (b i)) (s i)),
        (∏ i, RowTranslation.rowScalar (fun k => (j i : ℂ) * (r k - ω))
          (fun k => RowTranslation.tail (T k) (PowerSeries.log ℂ))
          (InterpolationMatrix.exponentVector (b i)) (f i).1.1 (f i).2.1 (f i).2.2) *
          Matrix.det (fun i c => PowerSeries.coeff (s i - (f i).2.2)
            ((rationalPeriodMonomial (y i) (j i) ω (h c) (a c)).coeff (f i).1.1)) := by
  have he : (fun i c => (y i) ^ (h c) * InterpolationMatrix.entry r
      (fun k => InterpolationMatrix.truncatedLog (T k)) (j i) (s i) (b i) (h c) (a c)) =
      (fun i c => ∑ t : RowTranslation.RowChoices S (InterpolationMatrix.exponentVector (b i)) (s i),
        RowTranslation.rowScalar (fun k => (j i : ℂ) * (r k - ω))
          (fun k => RowTranslation.tail (T k) (PowerSeries.log ℂ))
          (InterpolationMatrix.exponentVector (b i)) t.1.1 t.2.1 t.2.2 *
          PowerSeries.coeff (s i - t.2.2)
            ((rationalPeriodMonomial (y i) (j i) ω (h c) (a c)).coeff t.1.1)) := by
    funext i c
    exact rational_matrix_entry_translation_choices (y i) r T (j i) (s i) ω
      (b i) (h c) (a c) S (hp i c)
  rw [he]
  exact MatrixTranslation.det_dependent_row_sum _ _

/-- Generalize the upstream exp(center)=1 bridge to exp(center)=y. -/
theorem rational_periodFunction_eq_exponentialMonomial
    (y b center : ℂ) (h d : ℕ) (hcenter : Complex.exp center = y)
    {z : ℂ} (hz : ‖z‖ < 1) :
    PeriodAnalytic.periodFunction (y ^ h * b) center h d z =
      AnalyticCollision.exponentialMonomial b (h : ℂ) d
        (center + Complex.log (1 + z)) := by
  have hz0 : 1 + z ≠ 0 := by
    intro heq
    have heq' : z = -1 := by linear_combination heq
    simp [heq'] at hz
  unfold PeriodAnalytic.periodFunction AnalyticCollision.exponentialMonomial
  rw [Complex.exp_nat_mul, Complex.exp_add, hcenter, Complex.exp_log hz0, mul_pow]
  ring

/-- The rational-base coefficient is precisely the analytic row test.
Thus the generic OAI collision theorem applies to the translated rows. -/
theorem rationalPeriodMonomial_coeff_eq_rowTest {m : ℕ}
    (y : ℂ) (j h ell : ℕ) (ω : ℂ) (a : Fin m → ℕ) (A : Fin m →₀ ℕ)
    (hcenter : Complex.exp ((j : ℂ) * ω) = y) :
    PowerSeries.coeff ell ((rationalPeriodMonomial y j ω h a).coeff A) =
      AnalyticCollision.rowTest ell (fun t =>
        PeriodAnalytic.columnFunction h a A ((j : ℂ) * ω + Complex.log (1 + t))) := by
  have hseries : (rationalPeriodMonomial y j ω h a).coeff A =
      PeriodAnalytic.periodSeries
        (y ^ h * ((∏ i, (a i).choose (A i) : ℕ) : ℂ))
        ((j : ℂ) * ω) h (∑ i : Fin m, (a i - A i)) := by
    simp only [rationalPeriodMonomial, MvPolynomial.coeff_C_mul,
      MatrixTranslation.periodMonomial_coeff, PeriodAnalytic.periodSeries,
      MatrixTranslation.periodCoordinate, map_mul, map_natCast]
    ring
  rw [hseries, ← PeriodAnalytic.rowTest_periodFunction_eq_coeff]
  apply PeriodAnalytic.rowTest_congr_sphere
  intro t ht
  apply rational_periodFunction_eq_exponentialMonomial _ _ _ _ _ hcenter
  have hn : ‖t‖ = (1 / 2 : ℝ) := by
    simpa only [Metric.mem_sphere, dist_zero_right] using ht
  rw [hn]
  norm_num

/-- The actual multiplicative center for a positive rational logarithm. -/
theorem positive_rational_exp_log_center (r : ℚ) (hr : 0 < r) (j : ℕ) :
    Complex.exp ((j : ℂ) * (Real.log (r : ℝ) : ℂ)) = (r : ℂ) ^ j := by
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  rw [Complex.exp_nat_mul, ← Complex.ofReal_exp, Real.exp_log hrR]
  norm_cast

/-- Specialization to B's actual rational base; the center identity is
proved above and is no longer an input assumption. -/
theorem rational_log_periodMonomial_coeff_eq_rowTest {m : ℕ}
    (r : ℚ) (hr : 0 < r) (j h ell : ℕ)
    (a : Fin m → ℕ) (A : Fin m →₀ ℕ) :
    PowerSeries.coeff ell
      ((rationalPeriodMonomial ((r : ℂ) ^ j) j (Real.log (r : ℝ) : ℂ) h a).coeff A) =
      AnalyticCollision.rowTest ell (fun t => PeriodAnalytic.columnFunction h a A
        ((j : ℂ) * (Real.log (r : ℝ) : ℂ) + Complex.log (1 + t))) := by
  exact rationalPeriodMonomial_coeff_eq_rowTest _ _ _ _ _ _ _
    (positive_rational_exp_log_center r hr j)

/-- B's analytic determinant inequality is an actual application of the
genuine OAI017 theorem. Differentiability and the whole exponential
monomial sphere bound are proved upstream and reused here.

Remaining hypotheses are the elementary column/weight, center-radius,
and row-order budgets supplied by B's chosen data. -/
theorem rational_log_monomial_determinant_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {m : ℕ} (group : ι → κ) (index : κ → Fin m →₀ ℕ)
    (j ell : ι → ℕ) (ω : ℂ)
    (h : ι → ℕ) (a : ι → Fin m → ℕ) (w : Fin m → ℝ)
    (R : NNReal) {H w0 wstar v0 : ℝ}
    (hR : 1 ≤ (R : ℝ)) (hH : 0 < H)
    (hw0 : 0 < w0) (hws : 0 < wstar) (hw : ∀ i, wstar ≤ w i)
    (hcol : ∀ c, w0 * h c + ∑ i, w i * a c i ≤ H)
    (hc : ∀ r, ‖(j r : ℂ) * ω‖ + 3 / 4 ≤ (R : ℝ) / 2)
    (hell : ((∑ r, ell r : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) * H / v0) :
    ‖Matrix.det (fun r c => AnalyticCollision.rowTest (ell r)
      (fun t => PeriodAnalytic.columnFunction (h c) (a c) (index (group r))
        ((j r : ℂ) * ω + Complex.log (1 + t))))‖ ≤
      Real.exp (-(Real.log 2 / 4) *
        (∑ A, (Collision.multiplicity Finset.univ group A : ℝ) ^ 2) +
        (Fintype.card ι : ℝ) * H *
          ((R : ℝ) / w0 + Real.log (2 * (R : ℝ)) / wstar +
            Real.log 2 / v0 + Collision.collisionRemainder (Fintype.card ι) H)) := by
  have hRpos : 0 < R := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hR
  apply AnalyticCollision.translated_row_determinant_exp_bound
    group (fun A c => PeriodAnalytic.columnFunction (h c) (a c) (index A))
    (fun r => (j r : ℂ) * ω) ell R hRpos hH
  · intro A c
    exact PeriodAnalytic.differentiable_columnFunction _ _ _
  · intro A c z hz
    apply PeriodAnalytic.norm_columnFunction_le (h c) (a c) (index A) w
      hR hH.le hw0 hws hw (hcol c)
    simpa only [Metric.mem_sphere, dist_zero_right] using hz.le
  · exact hc
  · exact hell

/-- The same bound directly for the translated coefficient determinant
at B's positive rational multiplicative centers. -/
theorem rational_log_coefficient_determinant_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {m : ℕ} (r : ℚ) (hr : 0 < r)
    (group : ι → κ) (index : κ → Fin m →₀ ℕ)
    (j ell : ι → ℕ) (h : ι → ℕ) (a : ι → Fin m → ℕ) (w : Fin m → ℝ)
    (R : NNReal) {H w0 wstar v0 : ℝ}
    (hR : 1 ≤ (R : ℝ)) (hH : 0 < H)
    (hw0 : 0 < w0) (hws : 0 < wstar) (hw : ∀ i, wstar ≤ w i)
    (hcol : ∀ c, w0 * h c + ∑ i, w i * a c i ≤ H)
    (hc : ∀ t, ‖(j t : ℂ) * (Real.log (r : ℝ) : ℂ)‖ + 3 / 4 ≤ (R : ℝ) / 2)
    (hell : ((∑ t, ell t : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) * H / v0) :
    ‖Matrix.det (fun t c => PowerSeries.coeff (ell t)
      ((rationalPeriodMonomial ((r : ℂ) ^ (j t)) (j t) (Real.log (r : ℝ) : ℂ)
        (h c) (a c)).coeff (index (group t))))‖ ≤
      Real.exp (-(Real.log 2 / 4) *
        (∑ A, (Collision.multiplicity Finset.univ group A : ℝ) ^ 2) +
        (Fintype.card ι : ℝ) * H *
          ((R : ℝ) / w0 + Real.log (2 * (R : ℝ)) / wstar +
            Real.log 2 / v0 + Collision.collisionRemainder (Fintype.card ι) H)) := by
  simp_rw [rational_log_periodMonomial_coeff_eq_rowTest r hr]
  exact rational_log_monomial_determinant_bound group index j ell
    (Real.log (r : ℝ) : ℂ) h a w R hR hH hw0 hws hw hcol hc hell

#print axioms rationalPeriodMonomial_shift
#print axioms rationalFormalMonomialImage_coeff
#print axioms rational_log_error_exp
#print axioms rational_log_rowScalar_bound
#print axioms rational_log_center_radius_budget
#print axioms rational_log_row_order_budget
#print axioms rational_matrix_entry_translation
#print axioms rational_matrix_entry_translation_choices
#print axioms rational_det_matrix_translation
#print axioms rational_periodFunction_eq_exponentialMonomial
#print axioms rationalPeriodMonomial_coeff_eq_rowTest
#print axioms positive_rational_exp_log_center
#print axioms rational_log_periodMonomial_coeff_eq_rowTest
#print axioms rational_log_monomial_determinant_bound
#print axioms rational_log_coefficient_determinant_bound
#print axioms OAI.PiExponent.RowTranslation.exact_row_identity
#print axioms OAI.PiExponent.AnalyticCollision.translated_row_determinant_exp_bound
#print axioms OAI.PiExponent.DeterminantAnalyticBound.two_alternative_exponent
#print axioms OAI.PiExponent.DeterminantAnalyticBound.log_norm_sum_le

end RationalLogOAI017
