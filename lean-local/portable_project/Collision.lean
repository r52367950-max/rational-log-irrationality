import Mathlib.Algebra.Order.Group.Int.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Finite combinatorics behind the determinant collision bound

These theorems prove the distinct Taylor-degree saving in Section 4 of B.
They do not assert Theorem A or the irrationality exponent conclusion.
-/

open scoped BigOperators

namespace LogarithmAudit

/-- A set of n distinct nonnegative degrees has sum at least n(n−1)/2.
The doubled form avoids natural-number division. -/
theorem distinct_nat_degrees_bound (s : Finset ℕ) :
    s.card * (s.card - 1) ≤ 2 * ∑ d ∈ s, d := by
  have hz :
      ∑ n ∈ Finset.range s.card, (n : ℤ) ≤ ∑ n ∈ s, (n : ℤ) := by
    have h := Finset.sum_range_le_sum
      (s := s.image (fun n : ℕ => (n : ℤ))) (c := 0) (by
        intro x hx
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
        exact Int.natCast_nonneg n)
    simpa only [zero_add,
      Finset.card_image_of_injective s Nat.cast_injective,
      Finset.sum_image Nat.cast_injective.injOn] using h
  have hn :
      ∑ n ∈ Finset.range s.card, n ≤ ∑ n ∈ s, n := by
    apply Int.ofNat_le.mp
    simpa only [Nat.cast_sum] using hz
  calc
    s.card * (s.card - 1) = (∑ n ∈ Finset.range s.card, n) * 2 :=
      (Finset.sum_range_id_mul_two s.card).symm
    _ ≤ (∑ n ∈ s, n) * 2 := Nat.mul_le_mul_right 2 hn
    _ = 2 * ∑ n ∈ s, n := Nat.mul_comm _ _

/-- The same bound for rows with degrees injective on a finite row set. -/
theorem injective_degrees_bound {ι : Type*} [DecidableEq ι]
    (rows : Finset ι) (degree : ι → ℕ)
    (hinj : Set.InjOn degree rows) :
    rows.card * (rows.card - 1) ≤ 2 * ∑ i ∈ rows, degree i := by
  have h := distinct_nat_degrees_bound (rows.image degree)
  simpa only [Finset.card_image_iff.mpr hinj,
    Finset.sum_image hinj] using h

/-- If (group, degree) is injective, each group contributes its triangular
collision saving. This is the finite inequality used after Taylor expansion. -/
theorem grouped_degrees_bound {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (rows : Finset ι) (group : ι → κ) (degree : ι → ℕ)
    (hinj : ∀ i ∈ rows, ∀ j ∈ rows,
      group i = group j → degree i = degree j → i = j) :
    (∑ a ∈ rows.image group,
      (rows.filter (fun i => group i = a)).card *
        ((rows.filter (fun i => group i = a)).card - 1)) ≤
      2 * ∑ i ∈ rows, degree i := by
  calc
    _ ≤ ∑ a ∈ rows.image group,
        2 * ∑ i ∈ rows.filter (fun i => group i = a), degree i := by
      apply Finset.sum_le_sum
      intro a ha
      apply injective_degrees_bound
      intro i hi j hj hdeg
      have hi' := Finset.mem_filter.mp hi
      have hj' := Finset.mem_filter.mp hj
      exact hinj i hi'.1 j hj'.1 (hi'.2.trans hj'.2.symm) hdeg
    _ = 2 * ∑ a ∈ rows.image group,
        ∑ i ∈ rows.filter (fun i => group i = a), degree i := by
      rw [Finset.mul_sum]
    _ = 2 * ∑ i ∈ rows, degree i := by
      rw [Finset.sum_fiberwise_of_maps_to
        (fun i hi => Finset.mem_image_of_mem group hi) degree]

private theorem nat_square_eq_collision_add (n : ℕ) :
    n * n = n * (n - 1) + n := by
  cases n with
  | zero => simp
  | succ n => simp only [Nat.add_sub_cancel]; ring

/-- Equivalent square form: Σ n_a² ≤ 2 Σ d_i + M.
This is exactly the combinatorial input for c = log(2)/4 in B. -/
theorem grouped_squares_bound {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (rows : Finset ι) (group : ι → κ) (degree : ι → ℕ)
    (hinj : ∀ i ∈ rows, ∀ j ∈ rows,
      group i = group j → degree i = degree j → i = j) :
    (∑ a ∈ rows.image group,
      (rows.filter (fun i => group i = a)).card ^ 2) ≤
      2 * ∑ i ∈ rows, degree i + rows.card := by
  have h := grouped_degrees_bound rows group degree hinj
  calc
    _ = (∑ a ∈ rows.image group,
        (rows.filter (fun i => group i = a)).card *
          ((rows.filter (fun i => group i = a)).card - 1)) +
        ∑ a ∈ rows.image group, (rows.filter (fun i => group i = a)).card := by
      simp_rw [pow_two, nat_square_eq_collision_add]
      rw [Finset.sum_add_distrib]
    _ = (∑ a ∈ rows.image group,
        (rows.filter (fun i => group i = a)).card *
          ((rows.filter (fun i => group i = a)).card - 1)) + rows.card := by
      rw [← Finset.card_eq_sum_card_image group rows]
    _ ≤ 2 * ∑ i ∈ rows, degree i + rows.card := Nat.add_le_add_right h _

/-- The real-valued version consumed by logarithmic determinant estimates. -/
theorem grouped_squares_bound_real {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (rows : Finset ι) (group : ι → κ) (degree : ι → ℕ)
    (hinj : ∀ i ∈ rows, ∀ j ∈ rows,
      group i = group j → degree i = degree j → i = j) :
    (∑ a ∈ rows.image group,
      ((rows.filter (fun i => group i = a)).card : ℝ) ^ 2) ≤
      2 * ∑ i ∈ rows, (degree i : ℝ) + (rows.card : ℝ) := by
  exact_mod_cast grouped_squares_bound rows group degree hinj

/-- A noncolliding Taylor determinant term has injective pairs (a,d).
This interface states the real collision bound in that exact form. -/
theorem collision_bound_of_pair_injective {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (rows : Finset ι) (group : ι → κ) (degree : ι → ℕ)
    (hinj : Set.InjOn (fun i => (group i, degree i)) rows) :
    (∑ a ∈ rows.image group,
      ((rows.filter (fun i => group i = a)).card : ℝ) ^ 2) ≤
      2 * ∑ i ∈ rows, (degree i : ℝ) + (rows.card : ℝ) := by
  apply grouped_squares_bound_real rows group degree
  intro i hi j hj hgroup hdegree
  exact hinj hi hj (Prod.ext hgroup hdegree)

/-- Finite Cauchy–Schwarz in the occupancy form used in B Section 5:
the squared number of rows is bounded by the number of indices times
the sum of squared occupancies. No positivity condition on n is needed. -/
theorem finite_occupancy_cauchy_schwarz {κ : Type*}
    (indices : Finset κ) (n : κ → ℝ) :
    (∑ a ∈ indices, n a) ^ 2 ≤
      (indices.card : ℝ) * ∑ a ∈ indices, n a ^ 2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq indices (fun _ => (1 : ℝ)) n

/-- If a nonnegative threshold (in B, ηM) is met by the total occupancy,
the threshold squared has the same Cauchy–Schwarz bound. -/
theorem occupancy_threshold_bound {κ : Type*}
    (indices : Finset κ) (n : κ → ℝ) (threshold : ℝ)
    (hthreshold : 0 ≤ threshold)
    (htotal : threshold ≤ ∑ a ∈ indices, n a) :
    threshold ^ 2 ≤ (indices.card : ℝ) * ∑ a ∈ indices, n a ^ 2 := by
  have hsquare : threshold ^ 2 ≤ (∑ a ∈ indices, n a) ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self hthreshold htotal
  exact hsquare.trans (finite_occupancy_cauchy_schwarz indices n)

/-- The low-index subset may be enlarged to all transverse indices in
the squared-occupancy sum while keeping the low-index cardinality factor. -/
theorem subset_occupancy_threshold_bound {κ : Type*}
    (lowIndices allIndices : Finset κ) (n : κ → ℝ) (threshold : ℝ)
    (hsubset : lowIndices ⊆ allIndices)
    (hthreshold : 0 ≤ threshold)
    (htotal : threshold ≤ ∑ a ∈ lowIndices, n a) :
    threshold ^ 2 ≤ (lowIndices.card : ℝ) * ∑ a ∈ allIndices, n a ^ 2 := by
  have hsquares :
      (∑ a ∈ lowIndices, n a ^ 2) ≤ ∑ a ∈ allIndices, n a ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun a _ _ => sq_nonneg (n a))
  exact (occupancy_threshold_bound lowIndices n threshold hthreshold htotal).trans
    (mul_le_mul_of_nonneg_left hsquares (Nat.cast_nonneg _))

#print axioms distinct_nat_degrees_bound
#print axioms injective_degrees_bound
#print axioms grouped_degrees_bound
#print axioms grouped_squares_bound
#print axioms grouped_squares_bound_real
#print axioms collision_bound_of_pair_injective
#print axioms finite_occupancy_cauchy_schwarz
#print axioms occupancy_threshold_bound
#print axioms subset_occupancy_threshold_bound

end LogarithmAudit
