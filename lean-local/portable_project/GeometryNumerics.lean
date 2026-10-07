import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
Elementary numerical deductions used in A. This file does not construct a
blowup, prove a sheaf theorem, or prove interpolation. Those remain separate.
-/
namespace RationalLogReview
open Finset

/-- Pure-power products have at least the sum of their generator weights.
This is the exponent arithmetic behind I^n ⊆ M_V(nR), not an ideal theorem. -/
theorem pure_power_weight_bound {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (a e b : ι → ℕ) (R : ℝ) (n : ℕ)
    (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, w i * (a i : ℝ) = R)
    (hb : ∀ i, a i * e i ≤ b i) (he : ∑ i, e i = n) :
    (n : ℝ) * R ≤ ∑ i, w i * (b i : ℝ) := by
  have hterm (i : ι) : R * (e i : ℝ) ≤ w i * (b i : ℝ) := by
    calc
      R * (e i : ℝ) = w i * ((a i * e i : ℕ) : ℝ) := by
        rw [Nat.cast_mul, ← mul_assoc, ha]
      _ ≤ w i * (b i : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hb i) (hw i)
  calc
    (n : ℝ) * R = R * ∑ i, (e i : ℝ) := by
      rw [← Nat.cast_sum, he, mul_comm]
    _ = ∑ i, R * (e i : ℝ) := Finset.mul_sum ..
    _ ≤ ∑ i, w i * (b i : ℝ) := Finset.sum_le_sum (fun i _ => hterm i)

/-- The coefficients in A (7.3) are positive and have the stated exact sums. -/
theorem ample_combination_coefficients (a σ : ℝ) (ha : 1 < a) (hσ : 0 < σ) :
    let D := a * (1 + σ) - 1
    0 < (a - 1) / D ∧ 0 < σ / D ∧
      (a - 1) / D + (σ / D) * a = 1 ∧
      ((a - 1) / D) * (1 + σ) + σ / D = 1 := by
  dsimp
  have ha0 : 0 < a := by linarith
  have hprod : 0 < a * σ := mul_pos ha0 hσ
  have hD : 0 < a * (1 + σ) - 1 := by nlinarith
  refine ⟨div_pos (by linarith) hD, div_pos hσ hD, ?_, ?_⟩ <;>
    field_simp [ne_of_gt hD] <;> ring

#print axioms pure_power_weight_bound
#print axioms ample_combination_coefficients
end RationalLogReview
