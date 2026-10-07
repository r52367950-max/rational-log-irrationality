import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Kernel-checked algebraic part of manuscript B

These lemmas certify only the parameter and final numeric contradiction steps.
No interpolation, analytic determinant upper bound, or main irrationality theorem
is asserted or assumed as a global axiom.
-/
namespace RationalLogReview

/-- The exact margin identity used in B, section 5. -/
theorem margin_identity (nu A eta b theta : ℝ) :
    nu * (A * (1 - eta) - b) - (1 - b) =
    (nu * (A * (1 - eta) - theta) - (1 - theta)) +
      (nu - 1) * (theta - b) := by
  ring

/-- The smallest second-case margin is attained at `b = theta`. -/
theorem margin_lower_bound (nu A eta b theta : ℝ)
    (hnu : 1 ≤ nu) (hb : b ≤ theta) :
    nu * (A * (1 - eta) - theta) - (1 - theta) ≤
    nu * (A * (1 - eta) - b) - (1 - b) := by
  have hnonneg := mul_nonneg (sub_nonneg.mpr hnu) (sub_nonneg.mpr hb)
  nlinarith [margin_identity nu A eta b theta]

/-- Exact polynomial identity behind the small-delta volume inequality. -/
theorem volume_margin_identity (d delta : ℝ) :
    (1 - delta) - (1 - d * delta) ^ 2 =
      delta * ((2 * d - 1) - d ^ 2 * delta) := by
  ring

/-- The quantitative hypotheses that make B's initial small-delta choice valid. -/
theorem small_delta_parameters (nu d delta : ℝ)
    (hd0 : 0 < d) (hd1 : d < 1)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hgap : 1 < nu * (1 - d))
    (hquadratic : d ^ 2 * delta < 2 * d - 1) :
    0 < 1 - delta ∧
    1 - delta < 1 - d * delta ∧
    1 - d * delta < 1 ∧
    (1 - d * delta) ^ 2 < 1 - delta ∧
    1 - (1 - delta) < nu * ((1 - d * delta) - (1 - delta)) := by
  have hprod := mul_pos hd0 hdelta
  have hsmall := mul_lt_mul_of_pos_right hd1 hdelta
  have hvol : 0 < delta * ((2 * d - 1) - d ^ 2 * delta) :=
    mul_pos hdelta (sub_pos.mpr hquadratic)
  have hmargin := mul_lt_mul_of_pos_right hgap hdelta
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · rw [← volume_margin_identity] at hvol
    linarith
  · nlinarith

/-- Both determinant alternatives contradict the arithmetic lower bound.
`rho` explicitly represents the residual `o(1)` term. Thus this statement
also checks that the residual has to be budgeted, rather than silently dropped. -/
theorem determinant_bounds_inconsistent
    (nu A eta b theta Ear Etr Ehol rho c L x : ℝ)
    (hnu : 1 ≤ nu) (hb0 : 0 ≤ b) (hbtheta : b ≤ theta)
    (hgap : Ear + Etr + Ehol + rho <
      nu * (A * (1 - eta) - theta) - (1 - theta))
    (hcollision : 1 + (Ear + Etr + Ehol + rho) < c * L)
    (hlower : -(1 - b) - Ear ≤ x)
    (hupper : x ≤ Etr + Ehol + rho +
      max (-c * L) (-nu * (A * (1 - eta) - b))) : False := by
  have hsecond := margin_lower_bound nu A eta b theta hnu hbtheta
  rcases le_total (-c * L) (-nu * (A * (1 - eta) - b)) with hcase | hcase
  · rw [max_eq_right hcase] at hupper
    linarith
  · rw [max_eq_left hcase] at hupper
    linarith

/-- The `o(1)` in B's determinant upper bound is genuinely harmless:
strict fixed margins imply that, eventually, the lower and upper bounds
cannot both hold. This assertion does not furnish either bound. -/
theorem eventually_determinant_bounds_inconsistent
    (nu A eta theta Ear Etr Ehol c L : ℝ)
    (b rho x : ℕ → ℝ)
    (hnu : 1 ≤ nu) (hb0 : ∀ n, 0 ≤ b n) (hbtheta : ∀ n, b n ≤ theta)
    (hgap : Ear + Etr + Ehol <
      nu * (A * (1 - eta) - theta) - (1 - theta))
    (hcollision : 1 + (Ear + Etr + Ehol) < c * L)
    (hrho : Filter.Tendsto rho Filter.atTop (nhds 0)) :
    ∀ᶠ n in Filter.atTop,
      ¬ (-(1 - b n) - Ear ≤ x n ∧
        x n ≤ Etr + Ehol + rho n +
          max (-c * L) (-nu * (A * (1 - eta) - b n))) := by
  let gap := nu * (A * (1 - eta) - theta) - (1 - theta)
  let E := Ear + Etr + Ehol
  have hmargin : (0 : ℝ) < min (gap - E) (c * L - 1 - E) := by
    dsimp [gap, E]
    apply lt_min <;> linarith
  have hsmall := hrho.eventually_lt_const hmargin
  filter_upwards [hsmall] with n hn
  rintro ⟨hlower, hupper⟩
  apply determinant_bounds_inconsistent nu A eta (b n) theta Ear Etr Ehol (rho n) c L (x n)
    hnu (hb0 n) (hbtheta n) _ _ hlower hupper
  · have h := lt_of_lt_of_le hn (min_le_left (gap - E) (c * L - 1 - E))
    dsimp [gap, E] at h
    linarith
  · have h := lt_of_lt_of_le hn (min_le_right (gap - E) (c * L - 1 - E))
    dsimp [gap, E] at h
    linarith

/-- An exact rational sample for `nu = 3`, including all strict geometric
ratios used by the noncircular parameter selection. No asymptotic claim is
encoded in this sample. -/
theorem sample_parameter_certificate :
    (47 / 50 : ℝ) ^ 2 < 9 / 10 ∧
    (47 / 50 : ℝ) / (9 / 10) < 21 / 20 ∧
    (21 / 20 : ℝ) < 1 / (47 / 50) ∧
    (47 / 50 : ℝ) < 471 / 500 ∧
    (471 / 500 : ℝ) < 1 / (21 / 20) ∧
    (471 / 500 : ℝ) < (21 / 20) * (9 / 10) ∧
    (21 / 20 : ℝ) * (471 / 500) < 1 ∧
    1 < (21 / 20 : ℝ) * (9 / 10) / (471 / 500) ∧
    1 < (471 / 500 : ℝ) / (47 / 50) ∧
    (3 : ℝ) * ((47 / 50) * (1 - 1 / 1000) - 9 / 10) -
      (1 - 9 / 10) = 859 / 50000 := by
  norm_num

#print axioms margin_identity
#print axioms margin_lower_bound
#print axioms volume_margin_identity
#print axioms small_delta_parameters
#print axioms determinant_bounds_inconsistent
#print axioms sample_parameter_certificate
#print axioms eventually_determinant_bounds_inconsistent
end RationalLogReview
