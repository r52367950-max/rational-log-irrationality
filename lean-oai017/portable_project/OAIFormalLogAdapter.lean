import OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation
import OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic

/-!
# Actual OAI017 coefficient translation at arbitrary multiplicative centers

This adapter imports the original `MatrixTranslation` / `RowTranslation`
implementation. It keeps the multiplicative center in every matrix entry:
`Y ↦ y (1+t)`. The original OAI matrix uses `Y ↦ 1+t`.

For Theorem B the specializations are `y = R^j`, where `R` is a rational
base, and the additive approximate centers are `j * r_i`. All statements below
are exact coefficient identities. None assumes a determinant bound,
interpolation surjectivity, or the claimed irrationality exponent.
-/

namespace IrrationalityReview.OAIFormalLogAdapter

open scoped BigOperators
open OAI.PiExponent
open MvPolynomial
open RowTranslation

noncomputable section

/-- The literal truncated monomial substitution in equation (1) of Theorem B,
with an arbitrary multiplicative center `y`. -/
def centeredMonomialImage {m : ℕ} (y : ℂ) (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j h : ℕ) (a : Fin m → ℕ) :
    MvPolynomial (Fin m) (Polynomial ℂ) :=
  C ((Polynomial.C y * (1 + Polynomial.X)) ^ h) *
    ∏ i, (C (Polynomial.C ((j : ℂ) * r i) + G i) + X i) ^ a i

/-- This is a scale of the original OAI monomial, with the scale explicitly
depending on both the row center and the column exponent. -/
theorem centeredMonomialImage_eq_scaled {m : ℕ} (y : ℂ) (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j h : ℕ) (a : Fin m → ℕ) :
    centeredMonomialImage y r G j h a =
      C (Polynomial.C (y ^ h)) * InterpolationMatrix.monomialImage r G j h a := by
  simp [centeredMonomialImage, InterpolationMatrix.monomialImage,
    mul_pow, map_mul, map_pow, mul_assoc]

def centeredEntry {m : ℕ} (y : ℂ) (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j s : ℕ) (b : Fin m → ℕ)
    (h : ℕ) (a : Fin m → ℕ) : ℂ :=
  ((centeredMonomialImage y r G j h a).coeff
    (InterpolationMatrix.exponentVector b)).coeff s

theorem centeredEntry_eq_original_entry {m : ℕ} (y : ℂ) (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j s : ℕ) (b : Fin m → ℕ)
    (h : ℕ) (a : Fin m → ℕ) :
    centeredEntry y r G j s b h a =
      y ^ h * InterpolationMatrix.entry r G j s b h a := by
  rw [centeredEntry, centeredMonomialImage_eq_scaled, MvPolynomial.coeff_C_mul,
    Polynomial.coeff_C_mul]
  rfl

/-- The true-log monomial at the same multiplicative center. -/
def centeredPeriodMonomial {m : ℕ} (y : ℂ) (j : ℕ) (ω : ℂ) (h : ℕ)
    (a : Fin m → ℕ) : MvPolynomial (Fin m) (PowerSeries ℂ) :=
  C (PowerSeries.C (y ^ h)) * MatrixTranslation.periodMonomial j ω h a

def centeredFormalMonomialImage {m : ℕ} (y : ℂ) (r : Fin m → ℂ)
    (T : Fin m → ℕ) (j h : ℕ) (a : Fin m → ℕ) :
    MvPolynomial (Fin m) (PowerSeries ℂ) :=
  C (PowerSeries.C (y ^ h)) * MatrixTranslation.formalMonomialImage r T j h a

/-- Original exact shift identity, transported to `Y = y(1+t)`. -/
theorem centeredPeriodMonomial_shift {m : ℕ} (y : ℂ) (r : Fin m → ℂ)
    (T : Fin m → ℕ) (j : ℕ) (ω : ℂ) (h : ℕ) (a : Fin m → ℕ) :
    shift (fun i => PowerSeries.C ((j : ℂ) * (r i - ω)) +
      tail (T i) (PowerSeries.log ℂ)) (centeredPeriodMonomial y j ω h a) =
      centeredFormalMonomialImage y r T j h a := by
  rw [centeredPeriodMonomial, map_mul, shift_C,
    MatrixTranslation.periodMonomial_shift]
  rfl

theorem centeredFormalMonomialImage_coeff {m : ℕ} (y : ℂ) (r : Fin m → ℂ)
    (T : Fin m → ℕ) (j s : ℕ) (b : Fin m → ℕ)
    (h : ℕ) (a : Fin m → ℕ) :
    PowerSeries.coeff s ((centeredFormalMonomialImage y r T j h a).coeff
      (InterpolationMatrix.exponentVector b)) =
      centeredEntry y r (fun i => InterpolationMatrix.truncatedLog (T i)) j s b h a := by
  rw [centeredFormalMonomialImage, MvPolynomial.coeff_C_mul,
    PowerSeries.coeff_C_mul, MatrixTranslation.formalMonomialImage_coeff,
    centeredEntry_eq_original_entry]

/-- Theorem B's exact finite row expansion, with all `y^h` factors retained in
the column entries. The `rowScalar` coefficients are the original OAI ones. -/
theorem centered_entry_translation {m : ℕ} (y : ℂ) (r : Fin m → ℂ)
    (T : Fin m → ℕ) (j s : ℕ) (ω : ℂ) (b : Fin m → ℕ)
    (h : ℕ) (a : Fin m → ℕ) (S : Finset (Fin m →₀ ℕ))
    (hp : (centeredPeriodMonomial y j ω h a).support ⊆ S) :
    centeredEntry y r (fun i => InterpolationMatrix.truncatedLog (T i)) j s b h a =
      ∑ A ∈ S, ∑ d : (∀ i, Fin (A i - (InterpolationMatrix.exponentVector b) i + 1)),
        ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal s,
          rowScalar (fun i => (j : ℂ) * (r i - ω))
            (fun i => tail (T i) (PowerSeries.log ℂ))
            (InterpolationMatrix.exponentVector b) A d kl.1 *
              PowerSeries.coeff kl.2 ((centeredPeriodMonomial y j ω h a).coeff A) := by
  rw [← centeredFormalMonomialImage_coeff y r T j s b h a,
    ← centeredPeriodMonomial_shift y r T j ω h a]
  exact exact_row_identity _ _ _ _ S hp s

/-- Finite dependent choice form of the same exact row identity. -/
theorem centered_entry_translation_choices {m : ℕ} (y : ℂ) (r : Fin m → ℂ)
    (T : Fin m → ℕ) (j s : ℕ) (ω : ℂ) (b : Fin m → ℕ)
    (h : ℕ) (a : Fin m → ℕ) (S : Finset (Fin m →₀ ℕ))
    (hp : (centeredPeriodMonomial y j ω h a).support ⊆ S) :
    centeredEntry y r (fun i => InterpolationMatrix.truncatedLog (T i)) j s b h a =
      ∑ t : RowChoices S (InterpolationMatrix.exponentVector b) s,
        rowScalar (fun i => (j : ℂ) * (r i - ω))
          (fun i => tail (T i) (PowerSeries.log ℂ))
          (InterpolationMatrix.exponentVector b) t.1.1 t.2.1 t.2.2 *
          PowerSeries.coeff (s - t.2.2)
            ((centeredPeriodMonomial y j ω h a).coeff t.1.1) := by
  classical
  rw [centered_entry_translation y r T j s ω b h a S hp, Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type]
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range]

/-- Exact determinant multilinearity for the actual multiplicative centers.
Every factor `y(row)^h(column)` remains inside its translated test matrix. -/
theorem centered_det_translation {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (y : ι → ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (j s : ι → ℕ) (ω : ℂ) (b : ι → Fin m → ℕ)
    (h : ι → ℕ) (a : ι → Fin m → ℕ) (S : Finset (Fin m →₀ ℕ))
    (hp : ∀ i c, (centeredPeriodMonomial (y i) (j i) ω (h c) (a c)).support ⊆ S) :
    Matrix.det (fun i c => centeredEntry (y i) r
      (fun k => InterpolationMatrix.truncatedLog (T k)) (j i) (s i) (b i) (h c) (a c)) =
      ∑ f : (∀ i, RowChoices S (InterpolationMatrix.exponentVector (b i)) (s i)),
        (∏ i, rowScalar (fun k => (j i : ℂ) * (r k - ω))
          (fun k => tail (T k) (PowerSeries.log ℂ))
          (InterpolationMatrix.exponentVector (b i)) (f i).1.1 (f i).2.1 (f i).2.2) *
          Matrix.det (fun i c => PowerSeries.coeff (s i - (f i).2.2)
            ((centeredPeriodMonomial (y i) (j i) ω (h c) (a c)).coeff (f i).1.1)) := by
  have he : (fun i c => centeredEntry (y i) r
      (fun k => InterpolationMatrix.truncatedLog (T k)) (j i) (s i) (b i) (h c) (a c)) =
      (fun i c => ∑ t : RowChoices S (InterpolationMatrix.exponentVector (b i)) (s i),
        rowScalar (fun k => (j i : ℂ) * (r k - ω))
          (fun k => tail (T k) (PowerSeries.log ℂ))
          (InterpolationMatrix.exponentVector (b i)) t.1.1 t.2.1 t.2.2 *
          PowerSeries.coeff (s i - t.2.2)
            ((centeredPeriodMonomial (y i) (j i) ω (h c) (a c)).coeff t.1.1)) := by
    funext i c
    exact centered_entry_translation_choices _ _ _ _ _ _ _ _ _ S (hp i c)
  rw [he]
  exact MatrixTranslation.det_dependent_row_sum _ _

/-- The same source support simplex works uniformly for every multiplicative
center; scalar multiplication cannot create a new transverse monomial. -/
theorem centeredPeriodMonomial_support_subset {m : ℕ} (y : ℂ) (j : ℕ)
    (ω : ℂ) (h : ℕ) (a : Fin m → ℕ) (w : Fin m → ℝ) (H : ℝ)
    (hw : ∀ i, 0 < w i) (ha : ∑ i, w i * a i ≤ H) :
    (centeredPeriodMonomial y j ω h a).support ⊆
      MatrixTranslation.transverseIndices w H := by
  intro A hA
  apply MatrixTranslation.periodMonomial_support_subset j ω h a w H hw ha
  apply MvPolynomial.mem_support_iff.mpr
  intro hzero
  apply MvPolynomial.mem_support_iff.mp hA
  rw [centeredPeriodMonomial, MvPolynomial.coeff_C_mul, hzero, mul_zero]

/-- Direct specialization to rational-power multiplicative centers. -/
theorem rational_power_entry {m : ℕ} (R : ℚ) (r : Fin m → ℚ)
    (T : Fin m → ℕ) (j s : ℕ) (b : Fin m → ℕ)
    (h : ℕ) (a : Fin m → ℕ) :
    centeredEntry ((R : ℂ) ^ j) (fun i => (r i : ℂ))
      (fun i => InterpolationMatrix.truncatedLog (T i)) j s b h a =
      (R : ℂ) ^ (j * h) *
        InterpolationMatrix.entry (fun i => (r i : ℂ))
          (fun i => InterpolationMatrix.truncatedLog (T i)) j s b h a := by
  rw [centeredEntry_eq_original_entry, ← pow_mul]

/-- Equation (5) for the literal rational-power centers of Theorem B, on the
original weighted transverse simplex, rather than an assumed support set. -/
theorem rational_power_entry_translation {m : ℕ} (R : ℚ) (r : Fin m → ℚ)
    (T : Fin m → ℕ) (j s : ℕ) (ω : ℂ) (b : Fin m → ℕ)
    (h : ℕ) (a : Fin m → ℕ) (w : Fin m → ℝ) (H : ℝ)
    (hw : ∀ i, 0 < w i) (ha : ∑ i, w i * a i ≤ H) :
    centeredEntry ((R : ℂ) ^ j) (fun i => (r i : ℂ))
      (fun i => InterpolationMatrix.truncatedLog (T i)) j s b h a =
      ∑ A ∈ MatrixTranslation.transverseIndices w H,
        ∑ d : (∀ i, Fin (A i - (InterpolationMatrix.exponentVector b) i + 1)),
          ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal s,
            rowScalar (fun i => (j : ℂ) * ((r i : ℂ) - ω))
              (fun i => tail (T i) (PowerSeries.log ℂ))
              (InterpolationMatrix.exponentVector b) A d kl.1 *
                PowerSeries.coeff kl.2
                  ((centeredPeriodMonomial ((R : ℂ) ^ j) j ω h a).coeff A) := by
  exact centered_entry_translation _ _ _ _ _ _ _ _ _ _
    (centeredPeriodMonomial_support_subset _ _ _ _ _ _ _ hw ha)

/-- Every nonzero scalar in the exact row expansion satisfies the original
tail-degree budget; the multiplicative-center factor does not change it. -/
theorem nonzero_rowScalar_tail_budget {m : ℕ} (ε : Fin m → ℂ)
    (T : Fin m → ℕ) (β A : Fin m →₀ ℕ)
    (d : ∀ i, Fin (A i - β i + 1)) (k : ℕ)
    (hξ : rowScalar ε (fun i => tail (T i) (PowerSeries.log ℂ)) β A d k ≠ 0) :
    β ≤ A ∧ ∑ i, (d i : ℕ) * T i ≤ k := by
  have hk : PowerSeries.coeff k
      (∏ i, tail (T i) (PowerSeries.log ℂ) ^ (d i : ℕ)) ≠ 0 := by
    intro hz
    apply hξ
    simp [rowScalar, hz]
  exact ⟨rowScalar_ne_zero_le _ _ _ _ _ _ hξ,
    tail_budget_nat Finset.univ T (fun i => (d i : ℕ))
      (fun _ => PowerSeries.log ℂ) k hk⟩

/-- Exact rational-base height clearing. This proves the additional base
denominator factor of Theorem B's arithmetic section, for every `j ≤ N`. -/
theorem rational_base_denominator_identity (A B : ℂ) (h j N : ℕ)
    (hB : B ≠ 0) (hj : j ≤ N) :
    B ^ (N * h) * (A / B) ^ (j * h) =
      A ^ (j * h) * B ^ ((N - j) * h) := by
  have hexp : N * h = j * h + (N - j) * h := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hj]
  rw [hexp, pow_add, div_pow]
  calc
    _ = B ^ ((N - j) * h) *
        (B ^ (j * h) * (A ^ (j * h) / B ^ (j * h))) := by ring
    _ = B ^ ((N - j) * h) * A ^ (j * h) := by
      rw [mul_div_cancel₀ _ (pow_ne_zero _ hB)]
    _ = _ := mul_comm _ _

/-- The exact additional column scale for `R=A/B` in Theorem B. This is an
identity about the literal matrix entries, not a separately postulated factor. -/
theorem rational_base_column_scale {m : ℕ} (A B : ℤ) (K j s : ℕ)
    (hB : B ≠ 0) (hj : j < K) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (b : Fin m → ℕ) (h : ℕ) (a : Fin m → ℕ) :
    (B : ℂ) ^ ((K - 1) * h) *
      centeredEntry (((A : ℂ) / (B : ℂ)) ^ j) r G j s b h a =
      (A : ℂ) ^ (j * h) * (B : ℂ) ^ ((K - 1 - j) * h) *
        InterpolationMatrix.entry r G j s b h a := by
  rw [centeredEntry_eq_original_entry, ← pow_mul, ← mul_assoc]
  rw [rational_base_denominator_identity _ _ _ _ _ (Int.cast_ne_zero.mpr hB)
    (show j ≤ K - 1 by omega)]

/-- Original OAI denominator clearing adapted from imaginary rational centers
to the actual real rational centers `j*p_i/q_i` of Theorem B. -/
theorem real_rational_entry_cleared_gaussian {m : ℕ}
    (T q e : Fin m → ℕ) (p : Fin m → ℤ) (hq : ∀ i, q i ≠ 0)
    (j s h : ℕ) (β α : Fin m → ℕ) (hα : ∀ i, α i ≤ e i) :
    (∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) *
      (∏ i, (q i : ℂ) ^ α i) / (∏ i, (q i : ℂ) ^ β i) *
      InterpolationMatrix.entry (fun i => (p i : ℂ) / (q i : ℂ))
        (fun i => InterpolationMatrix.truncatedLog (T i)) j s β h α ∈
          GaussianInt.toComplex.range := by
  classical
  by_cases hβα : ∀ i, β i ≤ α i
  swap
  · rw [InterpolationMatrix.entry_eq_zero_of_not_le _ _ _ _ _ _ _ hβα, mul_zero]
    exact GaussianInt.toComplex.range.zero_mem
  have hqC : ∀ i, (q i : ℂ) ≠ 0 := by
    intro i
    exact_mod_cast hq i
  have hratio : (∏ i, (q i : ℂ) ^ α i) / (∏ i, (q i : ℂ) ^ β i) =
      ∏ i, (q i : ℂ) ^ (α i - β i) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    simpa only [div_eq_mul_inv] using (pow_sub₀ (q i : ℂ) (hqC i) (hβα i)).symm
  let z : Fin m → GaussianInt := fun i => (j : GaussianInt) * (p i : GaussianInt)
  have hz (i : Fin m) : Polynomial.C (q i : ℂ) *
      (Polynomial.C ((j : ℂ) * ((p i : ℂ) / (q i : ℂ))) +
        InterpolationMatrix.truncatedLog (T i)) =
      Polynomial.C (z i : ℂ) + Polynomial.C (q i : ℂ) *
        PowerSeries.trunc (T i) (PowerSeries.log ℂ) := by
    rw [mul_add, ← map_mul]
    congr 1
    apply congrArg Polynomial.C
    have hzc : (z i : ℂ) = (j : ℂ) * (p i : ℂ) := by simp [z]
    rw [hzc]
    field_simp [hqC i]
  have hclear := Arithmetic.shifted_truncation_product_coeff_gaussian Finset.univ
    T q e (fun i => α i - β i) z ((1 + Polynomial.X) ^ h)
    (fun i hi => (Nat.sub_le (α i) (β i)).trans (hα i)) s
  have hP : (((1 + Polynomial.X) ^ h : Polynomial GaussianInt).map GaussianInt.toComplex) =
      (1 + Polynomial.X) ^ h := by simp
  simp only [hP] at hclear
  have hchoose : (∏ i, ((α i).choose (β i) : ℂ)) ∈ GaussianInt.toComplex.range := by
    apply GaussianInt.toComplex.range.prod_mem
    intro i hi
    exact ⟨((α i).choose (β i) : GaussianInt), by simp⟩
  have hscalar := InterpolationMatrix.scalar_product_mul_coeff (fun i => (q i : ℂ))
    (fun i => α i - β i) ((1 + Polynomial.X) ^ h)
    (fun i => Polynomial.C ((j : ℂ) * ((p i : ℂ) / (q i : ℂ))) +
      InterpolationMatrix.truncatedLog (T i)) s
  simp_rw [hz] at hscalar
  rw [mul_div_assoc, hratio, InterpolationMatrix.entry_eq_binomial_product]
  have he := GaussianInt.toComplex.range.mul_mem hchoose hclear
  rw [← hscalar] at he
  convert he using 1
  ring

/-- Complete denominator clearing for the literal rational-log matrix entry,
including the rational-base height factor absent from the original pi matrix.
Gaussian integrality suffices for the nonzero determinant norm lower bound. -/
theorem centered_real_rational_entry_cleared_gaussian {m : ℕ}
    (A B : ℤ) (K j s h : ℕ) (hB : B ≠ 0) (hj : j < K)
    (T q e : Fin m → ℕ) (p : Fin m → ℤ) (hq : ∀ i, q i ≠ 0)
    (β α : Fin m → ℕ) (hα : ∀ i, α i ≤ e i) :
    (∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) * (B : ℂ) ^ ((K - 1) * h) *
      (∏ i, (q i : ℂ) ^ α i) / (∏ i, (q i : ℂ) ^ β i) *
      centeredEntry (((A : ℂ) / (B : ℂ)) ^ j)
        (fun i => (p i : ℂ) / (q i : ℂ))
        (fun i => InterpolationMatrix.truncatedLog (T i)) j s β h α ∈
          GaussianInt.toComplex.range := by
  have hbint : (A : ℂ) ^ (j * h) * (B : ℂ) ^ ((K - 1 - j) * h) ∈
      GaussianInt.toComplex.range := by
    refine ⟨(A : GaussianInt) ^ (j * h) * (B : GaussianInt) ^ ((K - 1 - j) * h), ?_⟩
    simp
  have hclear := real_rational_entry_cleared_gaussian T q e p hq j s h β α hα
  have hbase := rational_base_column_scale A B K j s hB hj
    (fun i => (p i : ℂ) / (q i : ℂ))
    (fun i => InterpolationMatrix.truncatedLog (T i)) β h α
  have he : (∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) * (B : ℂ) ^ ((K - 1) * h) *
      (∏ i, (q i : ℂ) ^ α i) / (∏ i, (q i : ℂ) ^ β i) *
      centeredEntry (((A : ℂ) / (B : ℂ)) ^ j)
        (fun i => (p i : ℂ) / (q i : ℂ))
        (fun i => InterpolationMatrix.truncatedLog (T i)) j s β h α =
      ((A : ℂ) ^ (j * h) * (B : ℂ) ^ ((K - 1 - j) * h)) *
        ((∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) *
          (∏ i, (q i : ℂ) ^ α i) / (∏ i, (q i : ℂ) ^ β i) *
          InterpolationMatrix.entry (fun i => (p i : ℂ) / (q i : ℂ))
            (fun i => InterpolationMatrix.truncatedLog (T i)) j s β h α) := by
    calc
      _ = ((∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) *
            (∏ i, (q i : ℂ) ^ α i) / (∏ i, (q i : ℂ) ^ β i)) *
          ((B : ℂ) ^ ((K - 1) * h) *
            centeredEntry (((A : ℂ) / (B : ℂ)) ^ j)
              (fun i => (p i : ℂ) / (q i : ℂ))
              (fun i => InterpolationMatrix.truncatedLog (T i)) j s β h α) := by ring
      _ = _ := by rw [hbase]; ring
  rw [he]
  exact GaussianInt.toComplex.range.mul_mem hbint hclear

/-- The actual rational-base matrix, for arbitrary selected rows and columns. -/
def centeredRationalMatrix {ι : Type*} {m : ℕ} (A B : ℤ)
    (p : Fin m → ℤ) (q T : Fin m → ℕ) (j s : ι → ℕ)
    (β : ι → Fin m → ℕ) (h : ι → ℕ) (α : ι → Fin m → ℕ) : Matrix ι ι ℂ :=
  fun i c => centeredEntry (((A : ℂ) / (B : ℂ)) ^ j i)
    (fun k => (p k : ℂ) / (q k : ℂ))
    (fun k => InterpolationMatrix.truncatedLog (T k)) (j i) (s i) (β i) (h c) (α c)

def commonDenominator {m : ℕ} (T e : Fin m → ℕ) : ℝ :=
  ∏ i, (Nat.lcmUpto (T i) : ℝ) ^ e i

def baseColumnScale {m : ℕ} (B : ℤ) (K h : ℕ)
    (q : Fin m → ℕ) (α : Fin m → ℕ) : ℝ :=
  (B : ℝ) ^ ((K - 1) * h) * MatrixArithmetic.columnScale q α

/-- An arithmetic logarithmic lower bound for the actual selected determinant.
The only nonvanishing premise is the determinant itself. No lower-bound
estimate is postulated: it follows from the proved entry clearing and the
original OAI Gaussian-integer determinant theorem. -/
theorem centeredRationalMatrix_arithmetic_lower_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (A B : ℤ) (K : ℕ) (hB : 0 < B) (p : Fin m → ℤ)
    (q T e : Fin m → ℕ) (hq : ∀ i, 0 < q i)
    (j s : ι → ℕ) (β : ι → Fin m → ℕ) (h : ι → ℕ) (α : ι → Fin m → ℕ)
    (hj : ∀ i, j i < K) (hα : ∀ c k, α c k ≤ e k)
    (hdet : (centeredRationalMatrix A B p q T j s β h α).det ≠ 0) :
    -(Fintype.card ι : ℝ) * Real.log (commonDenominator T e) -
      (∑ i, Real.log (MatrixArithmetic.rowScale q (β i))) -
      (∑ c, Real.log (baseColumnScale B K (h c) q (α c))) ≤
        Real.log ‖(centeredRationalMatrix A B p q T j s β h α).det‖ := by
  apply Arithmetic.cleared_det_log_bound_with_denominator
    (centeredRationalMatrix A B p q T j s β h α)
    (fun i => MatrixArithmetic.rowScale q (β i))
    (fun c => baseColumnScale B K (h c) q (α c)) (commonDenominator T e)
  · apply Finset.prod_pos
    intro k hk
    apply pow_pos
    exact_mod_cast Nat.lcmUpto_pos (T k)
  · intro i
    exact MatrixArithmetic.rowScale_pos hq (β i)
  · intro c
    apply mul_pos
    · apply pow_pos
      exact_mod_cast hB
    · exact MatrixArithmetic.columnScale_pos hq (α c)
  · exact hdet
  · intro i c
    have he := centered_real_rational_entry_cleared_gaussian A B K (j i) (s i) (h c)
      (ne_of_gt hB) (hj i) T q e p (fun k => ne_of_gt (hq k)) (β i) (α c) (hα c)
    simp only [commonDenominator, MatrixArithmetic.rowScale, baseColumnScale,
      MatrixArithmetic.columnScale, centeredRationalMatrix,
      Complex.ofReal_prod, Complex.ofReal_pow, Complex.ofReal_natCast,
      Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_intCast]
    convert he using 1
    ring

end
end IrrationalityReview.OAIFormalLogAdapter

#print axioms IrrationalityReview.OAIFormalLogAdapter.centeredMonomialImage_eq_scaled
#print axioms IrrationalityReview.OAIFormalLogAdapter.centeredEntry_eq_original_entry
#print axioms IrrationalityReview.OAIFormalLogAdapter.centeredPeriodMonomial_shift
#print axioms IrrationalityReview.OAIFormalLogAdapter.centeredFormalMonomialImage_coeff
#print axioms IrrationalityReview.OAIFormalLogAdapter.centered_entry_translation
#print axioms IrrationalityReview.OAIFormalLogAdapter.centered_entry_translation_choices
#print axioms IrrationalityReview.OAIFormalLogAdapter.centered_det_translation
#print axioms IrrationalityReview.OAIFormalLogAdapter.centeredPeriodMonomial_support_subset
#print axioms IrrationalityReview.OAIFormalLogAdapter.rational_power_entry
#print axioms IrrationalityReview.OAIFormalLogAdapter.rational_power_entry_translation
#print axioms IrrationalityReview.OAIFormalLogAdapter.nonzero_rowScalar_tail_budget
#print axioms IrrationalityReview.OAIFormalLogAdapter.rational_base_denominator_identity
#print axioms IrrationalityReview.OAIFormalLogAdapter.rational_base_column_scale
#print axioms IrrationalityReview.OAIFormalLogAdapter.real_rational_entry_cleared_gaussian
#print axioms IrrationalityReview.OAIFormalLogAdapter.centered_real_rational_entry_cleared_gaussian
#print axioms IrrationalityReview.OAIFormalLogAdapter.centeredRationalMatrix_arithmetic_lower_bound
