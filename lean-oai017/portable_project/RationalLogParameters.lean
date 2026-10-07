import OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters
import OAI.NumberTheory.PiExponent.Approximation.Comparison
import OAIApproximationAdapter

/-! Parameters for every exponent greater than two, with the rational-base height
included before the approximation denominators are selected.  The original OAI017
parameter and dimension-existence proofs are used directly.  No determinant bound,
interpolation theorem, or eventual approximation lower bound is assumed here. -/

set_option autoImplicit false

namespace RationalLogReview.Parameters

open OAI.PiExponent Filter
open scoped Topology

/-- OAI's fixed coefficient 100 also absorbs any fixed nonnegative height coefficient.
The tolerance is shrunk before choosing m, so this is an existence theorem, not an
assumption that the desired dimension error is small. -/
theorem exists_dimension_margin_with_height
    (theta A B C eta a b D epsilon target : ℝ)
    (htheta : 0 < theta) (hB : 0 < B) (hC : 1 < C)
    (hsmall : C * B < 1) (hlarge : 1 < C * theta / B)
    (hratio : 1 < B / A) (heta : 0 < eta)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (_hD : 0 ≤ D) (hepsilon : 0 < epsilon) :
    ∃ m : ℕ, 1 ≤ m ∧
      (a * (m : ℝ) + b) / dimensionV theta B C m +
        D * (dimensionK C m : ℝ) / dimensionW B m < epsilon ∧
      target < eta ^ 2 * (B / A) ^ m / (2 * ((m : ℝ) + 1)) := by
  let scale : ℝ := max 1 D
  have hs1 : 1 ≤ scale := le_max_left _ _
  have hsD : D ≤ scale := le_max_right _ _
  have hs : 0 < scale := lt_of_lt_of_le zero_lt_one hs1
  obtain ⟨m, hm, herr, hcol⟩ := exists_dimension_margin theta A B C eta a b
    (epsilon / scale) target htheta hB hC hsmall hlarge hratio heta ha hb
    (div_pos hepsilon hs)
  have hV : 0 < dimensionV theta B C m :=
    dimensionV_pos theta B C htheta hB hC.le m
  have hW : 0 < dimensionW B m := dimensionW_pos B hB m
  have hlin : 0 ≤ (a * (m : ℝ) + b) / dimensionV theta B C m := by positivity
  have hratio0 : 0 ≤ (dimensionK C m : ℝ) / dimensionW B m := by positivity
  have hscaled := (lt_div_iff₀ hs).mp herr
  have hdom : (a * (m : ℝ) + b) / dimensionV theta B C m +
      D * ((dimensionK C m : ℝ) / dimensionW B m) ≤
      ((a * (m : ℝ) + b) / dimensionV theta B C m +
        100 * ((dimensionK C m : ℝ) / dimensionW B m)) * scale := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) hlin,
      mul_nonneg (show 0 ≤ 100 * scale - D by linarith) hratio0]
  refine ⟨m, hm, ?_, hcol⟩
  rw [mul_div_assoc] at herr hscaled ⊢
  exact hdom.trans_lt hscaled

noncomputable def weightErrorCoefficient (nu theta R0 : ℝ) (K : ℕ) : ℝ :=
  theta + Real.log 4 + Real.log (2 * (K : ℝ)) + nu + Real.log (2 * R0 * (K : ℝ))

theorem weightErrorCoefficient_nonneg (nu theta R0 : ℝ) (K : ℕ)
    (hnu : 0 < nu) (htheta : 0 < theta) (hR0 : 1 ≤ R0) (hK : 1 ≤ K) :
    0 ≤ weightErrorCoefficient nu theta R0 K := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h2K : 0 ≤ Real.log (2 * (K : ℝ)) := Real.log_nonneg (by linarith)
  have hRK : 1 ≤ 2 * R0 * (K : ℝ) := by nlinarith
  have h2RK : 0 ≤ Real.log (2 * R0 * (K : ℝ)) := Real.log_nonneg hRK
  unfold weightErrorCoefficient
  linarith

structure FixedParameters (nu Lambda c R0 logDen : ℝ) where
  base : OAI.PiExponent.Parameters nu
  epsilon : ℝ
  F0 : ℝ
  m : ℕ
  K : ℕ
  w0 : ℚ
  v0 : ℚ
  sigma : ℚ
  epsilon_pos : 0 < epsilon
  epsilon_lt_gap : epsilon <
    nu * ((base.A : ℝ) * (1 - base.eta) - base.theta) - (1 - base.theta)
  epsilon_le_half : epsilon ≤ 1 / 2
  F0_pos : 0 < F0
  F0_large : 2 / (base.theta : ℝ) < F0
  initial_margin : nu / F0 < epsilon / 3
  m_pos : 1 ≤ m
  K_eq : K = dimensionK (base.C : ℝ) m
  K_pos : 1 ≤ K
  w0_eq : (w0 : ℝ) = dimensionW (base.B : ℝ) m
  v0_eq : (v0 : ℝ) = dimensionV (base.theta : ℝ) base.B base.C m
  w0_pos : 0 < (w0 : ℝ)
  v0_pos : 0 < (v0 : ℝ)
  volume_eq : (K : ℝ) * ((w0 : ℝ) / v0) * (base.theta : ℝ) ^ m = 1 / 2
  volume_lt_one : (K : ℝ) * (base.theta : ℝ) ^ m < 1
  dimension_margin :
    (Lambda * F0 * (m : ℝ) + 2 * Real.log 2) / (v0 : ℝ) +
      (R0 * (K : ℝ) + ((K : ℝ) - 1) * logDen) / (w0 : ℝ) < epsilon / 3
  collision_margin : 2 < c *
    (base.eta ^ 2 * (K : ℝ) * (base.theta : ℝ) ^ m /
      (((m : ℝ) + 1) * (v0 : ℝ) * (base.A : ℝ) ^ m))
  sigma_pos : 0 < (sigma : ℝ)
  sigma_volume : (1 + 3 * (sigma : ℝ)) ^ (m + 1) *
    ((K : ℝ) * ((w0 : ℝ) / v0) * (base.theta : ℝ) ^ m) < 1
  sigma_centers : (1 + 3 * (sigma : ℝ)) ^ m *
    ((K : ℝ) * (base.theta : ℝ) ^ m) < 1
  sigma_theta : (1 + (sigma : ℝ)) * (base.theta : ℝ) < 1

/-- Simultaneous existence for arbitrary nu>2 and any fixed rational-base height.
The dependence on R0 and logDen is incorporated in the choice of m. -/
theorem exists_fixed_parameters (nu Lambda c R0 logDen : ℝ)
    (hnu : 2 < nu) (hLambda : 0 < Lambda) (hc : 0 < c)
    (hR0 : 1 ≤ R0) (hlogDen : 0 ≤ logDen) :
    Nonempty (FixedParameters nu Lambda c R0 logDen) := by
  obtain ⟨P⟩ := OAI.PiExponent.exists_parameters nu hnu
  let g : ℝ := nu * ((P.A : ℝ) * (1 - P.eta) - P.theta) - (1 - P.theta)
  have hg : 0 < g := P.gap_pos
  let epsilon : ℝ := min (g / 2) (1 / 2)
  have hepsilon : 0 < epsilon := lt_min (by positivity) (by norm_num)
  have hepsg : epsilon < g := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hepshalf : epsilon ≤ 1 / 2 := min_le_right _ _
  obtain ⟨F0, hF0, hFtheta, hFmargin⟩ :=
    exists_initial_scale nu P.theta epsilon P.theta_pos hepsilon
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨m, hm, hdim, hcollision⟩ := exists_dimension_margin_with_height
    P.theta P.A P.B P.C P.eta (Lambda * F0) (2 * Real.log 2)
    (R0 + logDen) (epsilon / 3) (2 / c) P.theta_pos P.B_pos P.one_lt_C
    P.CB_lt_one P.one_lt_C_theta_div_B P.one_lt_B_div_A P.eta_pos
    (mul_pos hLambda hF0).le (by positivity) (by linarith) (by positivity)
  let K : ℕ := dimensionK P.C m
  let w0 : ℚ := (P.B ^ m)⁻¹
  let v0 : ℚ := 2 * (K : ℚ) * P.theta ^ m * w0
  have hK : 1 ≤ K := dimensionK_one_le P.C P.one_lt_C.le m
  have hw0eq : (w0 : ℝ) = dimensionW P.B m := by simp [w0, dimensionW]
  have hv0eq : (v0 : ℝ) = dimensionV P.theta P.B P.C m := by
    simp [v0, dimensionV, K, hw0eq]
  have hw0 : 0 < (w0 : ℝ) := by
    rw [hw0eq]
    exact dimensionW_pos P.B P.B_pos m
  have hv0 : 0 < (v0 : ℝ) := by
    rw [hv0eq]
    exact dimensionV_pos P.theta P.B P.C P.theta_pos P.B_pos P.one_lt_C.le m
  have hvolume : (K : ℝ) * ((w0 : ℝ) / v0) * (P.theta : ℝ) ^ m = 1 / 2 := by
    rw [hw0eq, hv0eq]
    exact dimension_volume P.theta P.B P.C P.theta_pos P.B_pos P.one_lt_C.le m
  have hvolume1 : (K : ℝ) * (P.theta : ℝ) ^ m < 1 :=
    dimension_volume_lt_one P.theta P.C P.theta_pos P.C_pos.le P.C_theta_lt_one m hm
  have hcollision' : 2 < c *
      (P.eta ^ 2 * (K : ℝ) * (P.theta : ℝ) ^ m /
        (((m : ℝ) + 1) * (v0 : ℝ) * (P.A : ℝ) ^ m)) := by
    rw [hv0eq]
    change 2 < c * (P.eta ^ 2 * (dimensionK (P.C : ℝ) m : ℝ) *
      (P.theta : ℝ) ^ m / (((m : ℝ) + 1) *
        dimensionV (P.theta : ℝ) P.B P.C m * (P.A : ℝ) ^ m))
    rw [dimension_collision_identity P.theta P.A P.B P.C P.eta
      P.theta_pos P.A_pos P.B_pos P.one_lt_C.le]
    have hh := (div_lt_iff₀ hc).mp hcollision
    nlinarith
  obtain ⟨sigma, hsigma, hsigmaVol, hsigmaK, hsigmaTheta⟩ :=
    exists_small_rational_sigma m (1 / 2)
      ((K : ℝ) * (P.theta : ℝ) ^ m) P.theta (by norm_num) hvolume1 P.theta_lt_one
  refine ⟨{
    base := P, epsilon := epsilon, F0 := F0, m := m, K := K,
    w0 := w0, v0 := v0, sigma := sigma,
    epsilon_pos := hepsilon, epsilon_lt_gap := hepsg, epsilon_le_half := hepshalf,
    F0_pos := hF0, F0_large := hFtheta, initial_margin := hFmargin,
    m_pos := hm, K_eq := rfl, K_pos := hK,
    w0_eq := hw0eq, v0_eq := hv0eq, w0_pos := hw0, v0_pos := hv0,
    volume_eq := hvolume, volume_lt_one := hvolume1,
    dimension_margin := ?_, collision_margin := hcollision',
    sigma_pos := hsigma, sigma_volume := ?_,
    sigma_centers := hsigmaK, sigma_theta := hsigmaTheta
  }⟩
  · rw [hv0eq, hw0eq]
    have hbase : R0 * (K : ℝ) + ((K : ℝ) - 1) * logDen ≤
        (R0 + logDen) * (K : ℝ) := by nlinarith
    exact (add_le_add le_rfl (div_le_div_of_nonneg_right hbase
      (dimensionW_pos P.B P.B_pos m).le)).trans_lt hdim
  · rw [hvolume]
    exact hsigmaVol

/-- Unbounded denominators meet any prescribed logarithmic threshold, for a generic
real target. No density or ratio assumption on the denominator set is needed. -/
theorem exists_large_log_approximation (omega nu X : ℝ)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |omega - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    ∃ p : ℤ, ∃ q : ℕ, 2 ≤ q ∧ X < Real.log q ∧
      |omega - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp X)
  obtain ⟨p, q, hq, happrox⟩ := hbad (max 2 N)
  have hq2 : 2 ≤ q := le_trans (le_max_left _ _) hq
  have hNq : N ≤ q := le_trans (le_max_right _ _) hq
  have hexp : Real.exp X < (q : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hNq)
  have hlog : X < Real.log q := by
    simpa using Real.log_lt_log (Real.exp_pos X) hexp
  exact ⟨p, q, hq2, hlog, happrox⟩

/-- A generic-real version of OAI's successive selection construction. The proof
chooses each new denominator after the finite history is fixed. Numerators need not
be nonzero because new interpolation uses distinct multiplicative coordinates. -/
theorem exists_successive_approximations (omega nu : ℝ)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |omega - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu))
    (T : List ℝ → ℝ) :
    ∃ p : ℕ → ℤ, ∃ q : ℕ → ℕ, ∀ n,
      2 ≤ q n ∧ |omega - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-nu) ∧
      1 ≤ Nat.ceil (Real.log (q n)) ∧
      T (((List.range n).reverse).map
        (fun i => ((Nat.ceil (Real.log (q i))) : ℝ))) <
          ((Nat.ceil (Real.log (q n))) : ℝ) := by
  classical
  let wt : ℤ × ℕ → ℝ := fun a => (Nat.ceil (Real.log a.2) : ℝ)
  let Good : ℤ × ℕ → Prop := fun a =>
    2 ≤ a.2 ∧ |omega - (a.1 : ℝ) / a.2| ≤ (a.2 : ℝ) ^ (-nu) ∧
    1 ≤ Nat.ceil (Real.log a.2)
  have hex (L : List (ℤ × ℕ)) :
      ∃ a : ℤ × ℕ, Good a ∧ T (L.map wt) < wt a := by
    obtain ⟨p, q, hq, hlog, happ⟩ :=
      exists_large_log_approximation omega nu (max 1 (T (L.map wt))) hbad
    have hceil : Real.log q ≤ (Nat.ceil (Real.log q) : ℝ) := Nat.le_ceil _
    have hone : 1 < (Nat.ceil (Real.log q) : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hlog hceil)
    have hnat : 1 ≤ Nat.ceil (Real.log q) := by exact_mod_cast le_of_lt hone
    exact ⟨(p, q), ⟨hq, happ, hnat⟩,
      lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hlog hceil)⟩
  let next : List (ℤ × ℕ) → ℤ × ℕ := fun L => (hex L).choose
  have hnext (L : List (ℤ × ℕ)) : Good (next L) ∧ T (L.map wt) < wt (next L) :=
    (hex L).choose_spec
  let hist : ℕ → List (ℤ × ℕ) := Nat.rec [] (fun _ L => next L :: L)
  let a : ℕ → ℤ × ℕ := fun n => next (hist n)
  have hhist (n : ℕ) : hist n = (List.range n).reverse.map a := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change a n :: hist n = (List.range (n + 1)).reverse.map a
      rw [ih]
      simp [List.range_succ, List.reverse_append]
  refine ⟨fun n => (a n).1, fun n => (a n).2, fun n => ?_⟩
  have hgood : Good (a n) := (hnext (hist n)).1
  refine ⟨hgood.1, hgood.2.1, hgood.2.2, ?_⟩
  have hbound := (hnext (hist n)).2
  have hmap : (hist n).map wt = (List.range n).reverse.map (wt ∘ a) := by
    rw [hhist, List.map_map]
  rw [hmap] at hbound
  exact hbound

theorem exists_normalized_successive_approximations (omega nu X D : ℝ)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |omega - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    ∃ p : ℕ → ℤ, ∃ q : ℕ → ℕ, ∃ w : ℕ → ℝ,
      w 0 = 1 ∧
      (∀ n, w (n + 1) = (Nat.ceil (Real.log (q n)) : ℝ)) ∧
      (∀ n, 2 ≤ q n ∧ |omega - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-nu) ∧
        1 ≤ Nat.ceil (Real.log (q n)) ∧ X < w (n + 1)) ∧
      (∀ i, 1 ≤ w i) ∧
      (∀ i, 0 < i → D * (∏ j ∈ Finset.range i, w j) < w i) := by
  obtain ⟨p, q, h⟩ := exists_successive_approximations omega nu hbad
    (fun L => max X (D * L.prod))
  refine ⟨p, q, normalizedLogWeights q, rfl, fun _ => rfl, ?_, ?_, ?_⟩
  · intro n
    refine ⟨(h n).1, (h n).2.1, (h n).2.2.1, ?_⟩
    exact lt_of_le_of_lt (le_max_left _ _) (h n).2.2.2
  · intro i
    cases i with
    | zero => simp
    | succ n =>
      change (1 : ℝ) ≤ (Nat.ceil (Real.log (q n)) : ℝ)
      exact_mod_cast (h n).2.2.1
  · intro i hi
    cases i with
    | zero => omega
    | succ n =>
      have hprod := lt_of_le_of_lt (le_max_right _ _) (h n).2.2.2
      rw [reverse_logWeights_prod] at hprod
      exact hprod

structure SelectedParameters (omega nu Lambda c R0 logDen : ℝ)
    extends FixedParameters nu Lambda c R0 logDen where
  p : ℕ → ℤ
  q : ℕ → ℕ
  w : ℕ → ℝ
  wstar : ℝ
  w_zero : w 0 = 1
  w_log : ∀ n, w (n + 1) = (Nat.ceil (Real.log (q n)) : ℝ)
  approximations : ∀ n, 2 ≤ q n ∧
    |omega - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-nu)
  w_one_le : ∀ i, 1 ≤ w i
  weight_growth : OAI.PiExponentApprox.SeparatedWeightGrowth m
    (OAI.PiExponentApprox.weightSeparationFactor m (interpolationSeparationConstant m sigma)
      w0 v0 base.theta) w
  wstar_pos : 0 < wstar
  wstar_lower : ∀ i : Fin m, wstar ≤ w (i.val + 1)
  wstar_attained : ∃ i : Fin m, wstar = w (i.val + 1)
  weight_margin : Lambda * (∑ i : Fin m, 1 / w (i.val + 1)) +
    weightErrorCoefficient nu base.theta R0 K / wstar < epsilon / 3

/-- Actual denominators satisfy both a uniform error budget and successive separation;
all fixed geometry and height parameters are chosen before these denominators. -/
theorem exists_selected_parameters (omega nu Lambda c R0 logDen : ℝ)
    (hnu : 2 < nu) (hLambda : 0 < Lambda) (hc : 0 < c)
    (hR0 : 1 ≤ R0) (hlogDen : 0 ≤ logDen)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |omega - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    Nonempty (SelectedParameters omega nu Lambda c R0 logDen) := by
  classical
  obtain ⟨d⟩ := exists_fixed_parameters nu Lambda c R0 logDen hnu hLambda hc hR0 hlogDen
  have hS : 0 ≤ weightErrorCoefficient nu d.base.theta R0 d.K :=
    weightErrorCoefficient_nonneg nu d.base.theta R0 d.K (by linarith)
      d.base.theta_pos hR0 d.K_pos
  obtain ⟨X, hX, hXmargin⟩ := exists_uniform_weight_error_margin d.m Lambda
    (weightErrorCoefficient nu d.base.theta R0 d.K) (d.epsilon / 3)
    hLambda hS (div_pos d.epsilon_pos (by norm_num))
  obtain ⟨p, q, w, hw0, hwlog, happ, hw1, hgrowth⟩ :=
    exists_normalized_successive_approximations omega nu X
      (OAI.PiExponentApprox.weightSeparationFactor d.m
        (interpolationSeparationConstant d.m d.sigma) d.w0 d.v0 d.base.theta) hbad
  obtain ⟨wstar, hwstarX, hwstarLower, hwstarAttained⟩ :=
    exists_minimum_weight d.m d.m_pos (fun i : Fin d.m => w (i.val + 1)) X
      (fun i => (happ i.val).2.2.2)
  have hwstar : 0 < wstar := lt_of_lt_of_le zero_lt_one (le_trans hX hwstarX.le)
  exact ⟨{
    toFixedParameters := d, p := p, q := q, w := w, wstar := wstar,
    w_zero := hw0, w_log := hwlog,
    approximations := fun n => ⟨(happ n).1, (happ n).2.1⟩,
    w_one_le := hw1, weight_growth := fun i hi _ => hgrowth i hi,
    wstar_pos := hwstar, wstar_lower := hwstarLower, wstar_attained := hwstarAttained,
    weight_margin := hXmargin wstar (fun i : Fin d.m => w (i.val + 1))
      hwstarX hwstarLower
  }⟩

namespace SelectedParameters

variable {omega nu Lambda c R0 logDen : ℝ}
  (d : SelectedParameters omega nu Lambda c R0 logDen)

noncomputable def rationalWeight : ℕ → ℚ
  | 0 => 1
  | n + 1 => (Nat.ceil (Real.log (d.q n)) : ℚ)

theorem cast_rationalWeight (i : ℕ) : (d.rationalWeight i : ℝ) = d.w i := by
  cases i with
  | zero => simpa [rationalWeight] using d.w_zero.symm
  | succ n => simpa [rationalWeight] using (d.w_log n).symm

theorem rationalWeight_pos (i : ℕ) : 0 < d.rationalWeight i := by
  have h : (0 : ℝ) < (d.rationalWeight i : ℝ) := by
    rw [d.cast_rationalWeight]
    exact zero_lt_one.trans_le (d.w_one_le i)
  exact_mod_cast h

theorem rectangular_multiplicity_constant_bound (k : ℕ) (hk : k ≤ d.m) :
    (k : ℝ) ^ k * (((d.m : ℝ) + 2) / (d.sigma : ℝ)) ^ k ≤
      interpolationSeparationConstant d.m d.sigma := by
  exact OAI.PiExponentApprox.rectangular_multiplicity_constant_le_enlarged
    d.m k d.sigma d.sigma_pos hk

theorem separated_weight_products
    (A B : Finset ℕ) (hcard : A.card = B.card)
    (hA : A ⊆ Finset.range (d.m + 1)) (hB : B ⊆ Finset.range (d.m + 1))
    (i : ℕ) (hi : 0 < i) (hiA : i ∈ A) (hiB : i ∉ B)
    (hbelow : ∀ j ∈ B \ A, j < i) :
    interpolationSeparationConstant d.m d.sigma *
      (∏ j ∈ B, OAI.PiExponentApprox.geometricJetWeight d.v0 d.base.theta d.w j) <
      ∏ j ∈ A, OAI.PiExponentApprox.geometricDegreeWeight d.w0 d.w j := by
  exact OAI.PiExponentApprox.geometric_weight_products_separated d.m
    (interpolationSeparationConstant d.m d.sigma) d.w0 d.v0 d.base.theta d.w
    (interpolationSeparationConstant_pos d.m d.sigma d.sigma_pos)
    d.w0_pos d.v0_pos d.base.theta_pos d.w_zero d.w_one_le d.weight_growth
    A B hcard hA hB i hi hiA hiB hbelow

noncomputable def arithmeticError : ℝ :=
  Lambda * d.F0 * (d.m : ℝ) / (d.v0 : ℝ) +
    Lambda * (∑ i : Fin d.m, 1 / d.w (i.val + 1)) + (d.base.theta : ℝ) / d.wstar +
    ((d.K : ℝ) - 1) * logDen / (d.w0 : ℝ)

noncomputable def translationError : ℝ :=
  nu / d.F0 + Real.log 2 / (d.v0 : ℝ) +
    (Real.log 4 + Real.log (2 * (d.K : ℝ)) + nu) / d.wstar

noncomputable def holomorphicError : ℝ :=
  R0 * (d.K : ℝ) / (d.w0 : ℝ) + Real.log 2 / (d.v0 : ℝ) +
    Real.log (2 * R0 * (d.K : ℝ)) / d.wstar

noncomputable def analyticError : ℝ := d.translationError + d.holomorphicError

theorem error_sum_eq : d.arithmeticError + d.analyticError =
    nu / d.F0 +
      ((Lambda * d.F0 * (d.m : ℝ) + 2 * Real.log 2) / (d.v0 : ℝ) +
        (R0 * (d.K : ℝ) + ((d.K : ℝ) - 1) * logDen) / (d.w0 : ℝ)) +
      (Lambda * (∑ i : Fin d.m, 1 / d.w (i.val + 1)) +
        weightErrorCoefficient nu d.base.theta R0 d.K / d.wstar) := by
  unfold arithmeticError analyticError translationError holomorphicError weightErrorCoefficient
  ring

theorem error_sum_lt_gap : d.arithmeticError + d.analyticError <
    nu * ((d.base.A : ℝ) * (1 - d.base.eta) - d.base.theta) -
      (1 - d.base.theta) := by
  rw [d.error_sum_eq]
  have h1 := d.initial_margin
  have h2 := d.dimension_margin
  have h3 := d.weight_margin
  have h4 := d.epsilon_lt_gap
  linarith

theorem collision_exceeds_error_sum : 1 + d.arithmeticError + d.analyticError <
    c * (d.base.eta ^ 2 * (d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
      (((d.m : ℝ) + 1) * (d.v0 : ℝ) * (d.base.A : ℝ) ^ d.m)) := by
  rw [add_assoc, d.error_sum_eq]
  have h1 := d.initial_margin
  have h2 := d.dimension_margin
  have h3 := d.weight_margin
  have h4 := d.epsilon_le_half
  have h5 := d.collision_margin
  linarith

noncomputable def collisionLimit : ℝ :=
  c * (d.base.eta ^ 2 * (d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
    (((d.m : ℝ) + 1) * (d.v0 : ℝ) * (d.base.A : ℝ) ^ d.m))

/-- Once arithmetic and analytic estimates for actual minors are established on an
unbounded sequence of degrees, the original comparison proof gives a contradiction.
The two strict margins are proved from constructed parameters, not supplied here. -/
theorem contradiction_of_eventual_bounds
    (hnu : 2 < nu) (mean value error collision : ℕ → ℝ)
    (herror : Tendsto error atTop (𝓝 0))
    (hcollision : Tendsto collision atTop (𝓝 d.collisionLimit))
    (hmean0 : ∀ᶠ n in atTop, 0 ≤ mean n)
    (hmean : ∀ᶠ n in atTop, mean n ≤ (d.base.theta : ℝ))
    (hlower : ∀ᶠ n in atTop, -(1 - mean n) - d.arithmeticError ≤ value n)
    (hupper : ∀ᶠ n in atTop,
      value n ≤ d.analyticError + error n +
        max (-collision n) (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - mean n))) :
    False := by
  exact OAI.PiExponent.asymptotic_determinant_bounds_inconsistent
    nu d.base.theta ((d.base.A : ℝ) * (1 - d.base.eta))
    d.arithmeticError d.analyticError d.collisionLimit mean value error collision
    (by linarith) d.error_sum_lt_gap d.collision_exceeds_error_sum
    herror hcollision hmean0 hmean hlower hupper

/-- A real-degree version accommodating interpolation only on a cofinal divisibility
class. The selected column set and normalized determinant value may vary with H. -/
theorem contradiction_of_cofinal_bounds
    (hnu : 2 < nu) (error collision : ℝ → ℝ)
    (herror : Tendsto error atTop (𝓝 0))
    (hcollision : Tendsto collision atTop (𝓝 d.collisionLimit))
    (hdata : ∀ L : ℝ, ∃ H : ℝ, L ≤ H ∧ ∃ mean value : ℝ,
      0 ≤ mean ∧ mean ≤ (d.base.theta : ℝ) ∧
      -(1 - mean) - d.arithmeticError ≤ value ∧
      value ≤ d.analyticError + error H +
        max (-collision H) (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - mean))) :
    False := by
  have hsum : Tendsto (fun H : ℝ => d.arithmeticError + d.analyticError + error H)
      atTop (𝓝 (d.arithmeticError + d.analyticError + 0)) :=
    tendsto_const_nhds.add herror
  have hsmall : ∀ᶠ H : ℝ in atTop,
      d.arithmeticError + d.analyticError + error H <
        nu * ((d.base.A : ℝ) * (1 - d.base.eta) - d.base.theta) -
          (1 - d.base.theta) :=
    hsum.eventually (Iio_mem_nhds (by simpa using d.error_sum_lt_gap))
  have hdiff : Tendsto (fun H : ℝ =>
      collision H - (1 + d.arithmeticError + d.analyticError + error H))
      atTop (𝓝 (d.collisionLimit - (1 + d.arithmeticError + d.analyticError + 0))) :=
    hcollision.sub (tendsto_const_nhds.add herror)
  have hlarge : ∀ᶠ H : ℝ in atTop,
      0 < collision H - (1 + d.arithmeticError + d.analyticError + error H) := by
    apply hdiff.eventually (Ioi_mem_nhds ?_)
    have hh := d.collision_exceeds_error_sum
    change 1 + d.arithmeticError + d.analyticError < d.collisionLimit at hh
    linarith
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp (hsmall.and hlarge)
  obtain ⟨H, hLH, mean, value, hm0, hm, hl, hu⟩ := hdata L
  have hh := hL H hLH
  exact OAI.PiExponent.determinant_bounds_inconsistent
    nu d.base.theta ((d.base.A : ℝ) * (1 - d.base.eta)) mean
    d.arithmeticError d.analyticError (error H) (collision H) value
    (by linarith) hm0 hm hh.1 (by linarith [hh.2]) hl hu

end SelectedParameters

noncomputable def baseRadius (r : ℚ) : ℝ := 4 * (|Real.log (r : ℝ)| + 1) + 1

noncomputable def denominatorHeight (r : ℚ) : ℝ := Real.log (r.den : ℝ)

theorem baseRadius_bounds (r : ℚ) :
    1 ≤ baseRadius r ∧ 4 * (‖Real.log (r : ℝ)‖ + 1) < baseRadius r := by
  unfold baseRadius
  rw [Real.norm_eq_abs]
  constructor <;> linarith [abs_nonneg (Real.log (r : ℝ))]

theorem denominatorHeight_nonneg (r : ℚ) : 0 ≤ denominatorHeight r := by
  exact Real.log_nonneg (by exact_mod_cast r.pos)

/-- Every fixed rational base has parameters for every exponent nu>2. Neither the
base nor its denominator height depends on the hypothetical approximation denominators. -/
theorem exists_rational_log_fixed_parameters (r : ℚ) (nu Lambda c : ℝ)
    (hnu : 2 < nu) (hLambda : 0 < Lambda) (hc : 0 < c) :
    Nonempty (FixedParameters nu Lambda c (baseRadius r) (denominatorHeight r)) := by
  exact exists_fixed_parameters nu Lambda c (baseRadius r) (denominatorHeight r)
    hnu hLambda hc (baseRadius_bounds r).1 (denominatorHeight_nonneg r)

theorem exists_rational_log_selected_parameters (r : ℚ) (nu Lambda c : ℝ)
    (hnu : 2 < nu) (hLambda : 0 < Lambda) (hc : 0 < c)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |Real.log (r : ℝ) - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    Nonempty (SelectedParameters (Real.log (r : ℝ)) nu Lambda c
      (baseRadius r) (denominatorHeight r)) := by
  exact exists_selected_parameters (Real.log (r : ℝ)) nu Lambda c
    (baseRadius r) (denominatorHeight r) hnu hLambda hc
    (baseRadius_bounds r).1 (denominatorHeight_nonneg r) hbad

/-- This endpoint consumes an independently established contradiction for every actual
selected data set. It does not assert that interpolation or determinant estimates have
already produced that contradiction. -/
theorem eventualLowerBound_of_selected_contradictions (omega Lambda c R0 logDen : ℝ)
    (hLambda : 0 < Lambda) (hc : 0 < c) (hR0 : 1 ≤ R0) (hlogDen : 0 ≤ logDen)
    (hcontra : ∀ nu : ℝ, 2 < nu →
      SelectedParameters omega nu Lambda c R0 logDen → False) :
    OAI.PiExponent.EventualLowerBound omega := by
  apply OAI.PiExponent.eventualLowerBound_of_not_unbounded_approximations
  intro nu hnu hbad
  obtain ⟨d⟩ := exists_selected_parameters omega nu Lambda c R0 logDen
    hnu hLambda hc hR0 hlogDen hbad
  exact hcontra nu hnu d

/-- The stronger strict lower bound stated in manuscript B, including all integer
numerators and sufficiently large natural denominators. -/
theorem strictBound_of_selected_contradictions (omega Lambda c R0 logDen : ℝ)
    (hLambda : 0 < Lambda) (hc : 0 < c) (hR0 : 1 ≤ R0) (hlogDen : 0 ≤ logDen)
    (hcontra : ∀ nu : ℝ, 2 < nu →
      SelectedParameters omega nu Lambda c R0 logDen → False) :
    OAIAdapter.ManuscriptStrictBound omega := by
  intro nu hnu
  have hnot : ¬ ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |omega - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu) := by
    intro hbad
    obtain ⟨d⟩ := exists_selected_parameters omega nu Lambda c R0 logDen
      hnu hLambda hc hR0 hlogDen hbad
    exact hcontra nu hnu d
  push Not at hnot
  obtain ⟨Q, hQ⟩ := hnot
  exact ⟨Q, fun q hq _hqpos p => hQ p q hq⟩

theorem exponent_two_of_selected_contradictions (omega Lambda c R0 logDen : ℝ)
    (hLambda : 0 < Lambda) (hc : 0 < c) (hR0 : 1 ≤ R0) (hlogDen : 0 ≤ logDen)
    (hcontra : ∀ nu : ℝ, 2 < nu →
      SelectedParameters omega nu Lambda c R0 logDen → False) :
    OAI.PiExponent.irrationalityExponent omega = 2 := by
  exact OAIAdapter.exponent_two_of_original_eventualLowerBound
    (eventualLowerBound_of_selected_contradictions omega Lambda c R0 logDen
      hLambda hc hR0 hlogDen hcontra)

theorem rational_log_endpoint_of_selected_contradictions (r : ℚ) (Lambda c : ℝ)
    (hLambda : 0 < Lambda) (hc : 0 < c)
    (hcontra : ∀ nu : ℝ, 2 < nu →
      SelectedParameters (Real.log (r : ℝ)) nu Lambda c
        (baseRadius r) (denominatorHeight r) → False) :
    OAIAdapter.ManuscriptStrictBound (Real.log (r : ℝ)) ∧
      Irrational (Real.log (r : ℝ)) ∧
      OAI.PiExponent.irrationalityExponent (Real.log (r : ℝ)) = 2 := by
  have hstrict := strictBound_of_selected_contradictions (Real.log (r : ℝ)) Lambda c
    (baseRadius r) (denominatorHeight r) hLambda hc
    (baseRadius_bounds r).1 (denominatorHeight_nonneg r) hcontra
  exact ⟨hstrict, OAIAdapter.rational_logarithm_endpoint_from_manuscript_bound r hstrict⟩

end RationalLogReview.Parameters

#print axioms RationalLogReview.Parameters.exists_dimension_margin_with_height
#print axioms RationalLogReview.Parameters.weightErrorCoefficient_nonneg
#print axioms RationalLogReview.Parameters.exists_fixed_parameters
#print axioms RationalLogReview.Parameters.exists_large_log_approximation
#print axioms RationalLogReview.Parameters.exists_successive_approximations
#print axioms RationalLogReview.Parameters.exists_normalized_successive_approximations
#print axioms RationalLogReview.Parameters.exists_selected_parameters
#print axioms RationalLogReview.Parameters.SelectedParameters.cast_rationalWeight
#print axioms RationalLogReview.Parameters.SelectedParameters.rationalWeight_pos
#print axioms RationalLogReview.Parameters.SelectedParameters.rectangular_multiplicity_constant_bound
#print axioms RationalLogReview.Parameters.SelectedParameters.separated_weight_products
#print axioms RationalLogReview.Parameters.SelectedParameters.error_sum_eq
#print axioms RationalLogReview.Parameters.SelectedParameters.error_sum_lt_gap
#print axioms RationalLogReview.Parameters.SelectedParameters.collision_exceeds_error_sum
#print axioms RationalLogReview.Parameters.SelectedParameters.contradiction_of_eventual_bounds
#print axioms RationalLogReview.Parameters.SelectedParameters.contradiction_of_cofinal_bounds
#print axioms RationalLogReview.Parameters.baseRadius_bounds
#print axioms RationalLogReview.Parameters.denominatorHeight_nonneg
#print axioms RationalLogReview.Parameters.exists_rational_log_fixed_parameters
#print axioms RationalLogReview.Parameters.exists_rational_log_selected_parameters
#print axioms RationalLogReview.Parameters.eventualLowerBound_of_selected_contradictions
#print axioms RationalLogReview.Parameters.strictBound_of_selected_contradictions
#print axioms RationalLogReview.Parameters.exponent_two_of_selected_contradictions
#print axioms RationalLogReview.Parameters.rational_log_endpoint_of_selected_contradictions
