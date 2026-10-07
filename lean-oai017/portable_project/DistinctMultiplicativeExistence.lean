import DistinctMultiplicativeStatement
import DistinctMultiplicativeDegree
import OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters
import OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison

/-! Successive rational bounds are chosen before all center coordinates.
This proves the existence-version of A's weights with the upstream, larger
rectangular comparison constant; it does not assert the sharper printed C*.
-/
namespace OAI.PiExponent.DistinctMultiplicative
noncomputable section
open scoped BigOperators
open PiExponentApprox

private def extendWeights {m : ℕ} (x : Fin m → ℚ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => if h : n < m then (x ⟨n, h⟩ : ℝ) else 1

private theorem extendWeights_one_le {m : ℕ} (x : Fin m → ℚ)
    (hx : ∀ i, 1 ≤ x i) (n : ℕ) : 1 ≤ extendWeights x n := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [extendWeights]
    split
    · exact_mod_cast hx _
    · rfl

private theorem extendWeights_product {m : ℕ} (x : Fin m → ℚ) (i : Fin m) :
    (∏ j ∈ Finset.range (i.val + 1), extendWeights x j) =
      ∏ j : Fin i.val, (x ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ : ℝ) := by
  rw [Finset.prod_range_succ']
  simp only [extendWeights, mul_one]
  rw [← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro j _
  rw [dite_eq_left (Nat.lt_trans j.isLt i.isLt)]

private theorem geometric_casts {m : ℕ} (w0 v0 theta : ℚ) (x : Fin m → ℚ)
    (i : Fin (m + 1)) :
    ((Fin.cases w0 x i : ℚ) : ℝ) = geometricDegreeWeight w0 (extendWeights x) i.val ∧
    ((Fin.cases v0 (fun j => x j / theta) i : ℚ) : ℝ) =
      geometricJetWeight v0 theta (extendWeights x) i.val := by
  cases i using Fin.cases with
  | zero => simp [geometricDegreeWeight, geometricJetWeight]
  | succ i => simp [geometricDegreeWeight, geometricJetWeight, extendWeights, i.isLt]

/-- No center coordinates occur in these successive lower bounds. -/
def successiveCurveBounds (m : ℕ) (D : ℚ) : SuccessiveLowerBounds m :=
  fun i earlier => max 1 (D * ∏ j : Fin i.val, earlier j)

private theorem successive_implies_separation {m : ℕ} (sigma w0 v0 theta D : ℚ)
    (hsigma : 0 < (sigma : ℝ)) (hw0 : 0 < (w0 : ℝ))
    (hv0 : 0 < (v0 : ℝ)) (htheta : 0 < (theta : ℝ))
    (hD : weightSeparationFactor m (interpolationSeparationConstant m sigma)
      w0 v0 theta < (D : ℝ))
    (x : Fin m → ℚ) (hbound : ExceedsSuccessiveBounds (successiveCurveBounds m D) x) :
    ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      PersistentWeightComparison.comparisonConstant m sigma *
        (∏ j ∈ B, ((Fin.cases v0 (fun k => x k / theta) j : ℚ) : ℝ)) <
      ∏ j ∈ A, ((Fin.cases w0 x j : ℚ) : ℝ) := by
  classical
  have hx : ∀ i, 1 ≤ x i := fun i => le_of_lt ((le_max_left _ _).trans_lt (hbound i))
  have hxp : ∀ i, (0 : ℝ) < x i := fun i => by exact_mod_cast zero_lt_one.trans_le (hx i)
  have hgrowth : SeparatedWeightGrowth m
      (weightSeparationFactor m (interpolationSeparationConstant m sigma) w0 v0 theta)
      (extendWeights x) := by
    intro n hn hnm
    let i : Fin m := ⟨n - 1, by omega⟩
    have hnEq : n = i.val + 1 := by dsimp [i]; omega
    rw [hnEq, extendWeights_product]
    have hp : (0 : ℝ) < ∏ j : Fin i.val,
        (x ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ : ℝ) :=
      Finset.prod_pos (fun j _ => hxp _)
    have hb : D * (∏ j : Fin i.val, x ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) < x i :=
      (le_max_right _ _).trans_lt (hbound i)
    have hbR : (D : ℝ) * (∏ j : Fin i.val,
        (x ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ : ℝ)) < (x i : ℝ) := by exact_mod_cast hb
    simpa only [extendWeights, dite_eq_left i.isLt] using
      (mul_lt_mul_of_pos_right hD hp).trans hbR
  intro A B hcard i hi hiA hiB hhigh
  let e : Fin (m + 1) ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  have hsub (S : Finset (Fin (m + 1))) : S.map e ⊆ Finset.range (m + 1) := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hj
    exact Finset.mem_range.mpr k.isLt
  have hbelow : ∀ j ∈ B.map e \ A.map e, j < i.val := by
    intro j hj
    obtain ⟨hjB, hjA⟩ := Finset.mem_sdiff.mp hj
    obtain ⟨k, hkB, rfl⟩ := Finset.mem_map.mp hjB
    by_contra hnot
    have hik : i ≤ k := Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt hnot)
    have hne : i ≠ k := fun h => hiB (h.symm ▸ hkB)
    have hkA := (hhigh k (lt_of_le_of_ne hik hne)).mpr hkB
    exact hjA (Finset.mem_map.mpr ⟨k, hkA, rfl⟩)
  have h := geometric_weight_products_separated m
    (interpolationSeparationConstant m sigma) w0 v0 theta (extendWeights x)
    (interpolationSeparationConstant_pos m sigma hsigma) hw0 hv0 htheta rfl
    (extendWeights_one_le x hx) hgrowth (A.map e) (B.map e)
    (by simpa using hcard) (hsub A) (hsub B) i.val
    (Nat.pos_of_ne_zero (fun h => hi (Fin.ext h)))
    (Finset.mem_map.mpr ⟨i, hiA, rfl⟩)
    (by
      intro hj
      obtain ⟨a, haB, hai⟩ := Finset.mem_map.mp hj
      exact hiB ((Fin.ext hai : a = i) ▸ haB)) hbelow
  simp only [Finset.prod_map, e, Function.Embedding.coeFn_mk] at h
  simpa only [← (geometric_casts w0 v0 theta x _).1,
    ← (geometric_casts w0 v0 theta x _).2,
    PersistentWeightComparison.comparisonConstant, interpolationSeparationConstant] using h

/-- The auxiliary sigma and all lower bounds precede the weights and centers. -/
theorem exists_successive_curve_weights (m K : ℕ) (w0 v0 theta : ℚ)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta) (htheta1 : theta < 1)
    (hvol : (K : ℚ) * (w0 / v0) * theta ^ m < 1) :
    ∃ sigma : ℚ, 0 < sigma ∧ ∃ b : SuccessiveLowerBounds m,
      ∀ x : Fin m → ℚ, (∀ i, 0 < x i) → ExceedsSuccessiveBounds b x →
        (∀ i : Fin (m + 1), (0 : ℚ) < Fin.cases w0 x i) ∧
        (∀ i : Fin (m + 1), (0 : ℚ) < Fin.cases v0 (fun k => x k / theta) i) ∧
        (K : ℝ) * (1 + 3 * (sigma : ℝ)) ^ (m + 1) *
          (∏ i, ((Fin.cases w0 x i : ℚ) : ℝ)) /
          (∏ i, ((Fin.cases v0 (fun k => x k / theta) i : ℚ) : ℝ)) < 1 ∧
        (∀ A B : Finset (Fin (m + 1)), A.card = B.card →
          ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
          (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
          PersistentWeightComparison.comparisonConstant m sigma *
            (∏ j ∈ B, ((Fin.cases v0 (fun k => x k / theta) j : ℚ) : ℝ)) <
            ∏ j ∈ A, ((Fin.cases w0 x j : ℚ) : ℝ)) ∧
        (∀ i : Fin m, (1 + (sigma : ℝ)) * (x i : ℝ) < (x i / theta : ℚ)) := by
  have hw0R : (0 : ℝ) < w0 := by exact_mod_cast hw0
  have hv0R : (0 : ℝ) < v0 := by exact_mod_cast hv0
  have htR : (0 : ℝ) < theta := by exact_mod_cast htheta
  obtain ⟨sigma, hs, hvs, _, hts⟩ := exists_small_rational_sigma m
    ((K : ℝ) * ((w0 : ℝ) / v0) * (theta : ℝ) ^ m) 0 theta
    (by exact_mod_cast hvol) (by norm_num) (by exact_mod_cast htheta1)
  obtain ⟨D, hD⟩ := exists_rat_gt (weightSeparationFactor m
    (interpolationSeparationConstant m sigma) w0 v0 theta)
  refine ⟨sigma, by exact_mod_cast hs, successiveCurveBounds m D, ?_⟩
  intro x hx hb
  have hp : (∏ i : Fin m, (x i : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast ne_of_gt (hx i))
  have hratio : (∏ i : Fin (m + 1), ((Fin.cases w0 x i : ℚ) : ℝ)) /
      (∏ i : Fin (m + 1), ((Fin.cases v0 (fun k => x k / theta) i : ℚ) : ℝ)) =
      ((w0 : ℝ) / v0) * (theta : ℝ) ^ m := by
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ, Rat.cast_div, Finset.prod_div_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    field_simp [hp]
  refine ⟨(fun i => Fin.cases hw0 hx i),
    (fun i => Fin.cases hv0 (fun k => div_pos (hx k) htheta) i), ?_,
    successive_implies_separation sigma w0 v0 theta D hs hw0R hv0R htR hD x hb, ?_⟩
  · calc
      _ = (1 + 3 * (sigma : ℝ)) ^ (m + 1) *
          ((K : ℝ) * ((∏ i, ((Fin.cases w0 x i : ℚ) : ℝ)) /
            (∏ i, ((Fin.cases v0 (fun k => x k / theta) i : ℚ) : ℝ)))) := by ring
      _ = (1 + 3 * (sigma : ℝ)) ^ (m + 1) *
          ((K : ℝ) * ((w0 : ℝ) / v0) * (theta : ℝ) ^ m) := by rw [hratio]; ring
      _ < 1 := hvs
  · intro i
    rw [Rat.cast_div]
    apply (lt_div_iff₀ htR).mpr
    have hxi : (0 : ℝ) < x i := by exact_mod_cast hx i
    nlinarith [mul_lt_mul_of_pos_right hts hxi]

set_option maxHeartbeats 4000000 in
/-- Full A existence quantifiers, with no residual curve-degree hypothesis. -/
theorem separated_distinct_multiplicative_interpolation :
    SeparatedDistinctMultiplicativeInterpolationStatement := by
  intro m K _ _ w0 v0 theta hw0 hv0 ht ht1 hvolume
  obtain ⟨sigma, hs, b, hb⟩ := exists_successive_curve_weights m K w0 v0 theta
    hw0 hv0 ht ht1 hvolume
  refine ⟨b, ?_⟩
  intro x hx hbounds
  obtain ⟨hw, hv, hvol, hsep, hratio⟩ := hb x hx hbounds
  exact Degree.Weighted.eventual_interpolation_of_separated_weights
    (Fin.cases w0 x) (Fin.cases v0 (fun i => x i / theta))
    hw hv K sigma hs hvol hsep (by simpa only [Fin.cases_succ] using hratio)

#print axioms exists_successive_curve_weights
#print axioms separated_distinct_multiplicative_interpolation
end
end OAI.PiExponent.DistinctMultiplicative
