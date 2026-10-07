import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.EReal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# The logical endpoint of the rational-logarithm manuscript

This file DOES NOT prove the manuscript's determinant estimates or interpolation theorem.
It formalizes the final logical step, with the eventual approximation bound an explicit
hypothesis. No geometric or analytic claim is hidden in that hypothesis.

Denominators below are positive natural numbers and fractions need not be reduced.
Thus rational real numbers have exact representations with arbitrarily large denominators.
- All exponents are real (`Real.rpow`).
- The negation equivalence is independent of irrationality.
- The irrationality conclusion uses mathlib's existing `Irrational`.
- Dirichlet's exponent-two lower bound is imported from mathlib.
-/

namespace RationalLogReview

/-- The manuscript's hypothetical approximants, with arbitrarily large denominators. -/
def ArbitrarilyGoodApproximations (x ν : ℝ) : Prop :=
  ∀ N : ℕ, ∃ q : ℕ, N ≤ q ∧ 0 < q ∧
    ∃ p : ℤ, |x - (p : ℝ) / (q : ℝ)| ≤ (q : ℝ) ^ (-ν)

/-- The conventional strict-inequality version, used to define the exponent. -/
def StrictArbitrarilyGoodApproximations (x ν : ℝ) : Prop :=
  ∀ N : ℕ, ∃ q : ℕ, N ≤ q ∧ 0 < q ∧
    ∃ p : ℤ, |x - (p : ℝ) / (q : ℝ)| < (q : ℝ) ^ (-ν)

/-- Every strict approximant is also a weak approximant. -/
theorem StrictArbitrarilyGoodApproximations.to_weak {x ν : ℝ}
    (h : StrictArbitrarilyGoodApproximations x ν) : ArbitrarilyGoodApproximations x ν := by
  intro N
  obtain ⟨q, hqN, hqpos, p, herr⟩ := h N
  exact ⟨q, hqN, hqpos, p, herr.le⟩

/-- The eventual strict lower bound asserted as the conclusion of conditional Theorem B. -/
def EventualApproximationLowerBound (x ν : ℝ) : Prop :=
  ∃ N : ℕ, ∀ q : ℕ, N ≤ q → 0 < q →
    ∀ p : ℤ, (q : ℝ) ^ (-ν) < |x - (p : ℝ) / (q : ℝ)|

/-- Excluding unbounded good approximants really is the stated eventual bound. -/
theorem not_arbitrarilyGoodApproximations_iff (x ν : ℝ) :
    ¬ ArbitrarilyGoodApproximations x ν ↔ EventualApproximationLowerBound x ν := by
  classical
  simp only [ArbitrarilyGoodApproximations, EventualApproximationLowerBound,
    not_forall, not_exists, not_and, not_le]

/-- A rational real number has exact unreduced representations above every threshold. -/
theorem rational_has_arbitrarily_large_exact_representations (r : ℚ) (N : ℕ) :
    ∃ q : ℕ, N ≤ q ∧ 0 < q ∧ ∃ p : ℤ, (r : ℝ) = (p : ℝ) / (q : ℝ) := by
  let k : ℕ := N + 1
  have hk : 0 < k := Nat.zero_lt_succ N
  have hden : 1 ≤ r.den := r.pos
  have hq : k ≤ r.den * k := by
    calc
      k = 1 * k := (one_mul k).symm
      _ ≤ r.den * k := Nat.mul_le_mul_right k hden
  refine ⟨r.den * k, (Nat.le_succ N).trans hq, Nat.mul_pos r.den_pos hk,
    r.num * (k : ℤ), ?_⟩
  rw [Int.cast_mul, Int.cast_natCast, Nat.cast_mul,
    mul_div_mul_right _ _ (by exact_mod_cast hk.ne')]
  exact Rat.cast_def r

/-- Any eventually positive approximation-error lower bound excludes rational numbers.
No assumption on decay, monotonicity, or the exponent is needed. -/
theorem irrational_of_eventual_positive_lower_bound (x : ℝ) (f : ℕ → ℝ)
    (hf : ∀ q : ℕ, 0 < q → 0 < f q)
    (hbound : ∃ N : ℕ, ∀ q : ℕ, N ≤ q → 0 < q →
      ∀ p : ℤ, f q < |x - (p : ℝ) / (q : ℝ)|) : Irrational x := by
  rintro ⟨r, rfl⟩
  obtain ⟨N, hN⟩ := hbound
  obtain ⟨q, hqN, hqpos, p, heq⟩ :=
    rational_has_arbitrarily_large_exact_representations r N
  have hbad := hN q hqN hqpos p
  rw [← heq, sub_self, abs_zero] at hbad
  exact (not_lt_of_ge (hf q hqpos).le) hbad

/-- An eventual bound of the form in Theorem B implies irrationality, for any exponent. -/
theorem irrational_of_eventualApproximationLowerBound {x ν : ℝ}
    (h : EventualApproximationLowerBound x ν) : Irrational x := by
  apply irrational_of_eventual_positive_lower_bound x (fun q => (q : ℝ) ^ (-ν))
  · intro q hq
    exact Real.rpow_pos_of_pos (by exact_mod_cast hq) _
  · exact h

/-- A completely explicit upper-exponent-two property, without a new supremum convention. -/
def ApproximationExponentAtMostTwo (x : ℝ) : Prop :=
  ∀ ν : ℝ, 2 < ν → ¬ ArbitrarilyGoodApproximations x ν

theorem approximationExponentAtMostTwo_iff_eventual (x : ℝ) :
    ApproximationExponentAtMostTwo x ↔
      ∀ ν : ℝ, 2 < ν → EventualApproximationLowerBound x ν := by
  simp only [ApproximationExponentAtMostTwo, not_arbitrarilyGoodApproximations_iff]

/-- The all-exponent upper bound excludes rationality: ν = 3 suffices. -/
theorem irrational_of_approximationExponentAtMostTwo {x : ℝ}
    (h : ApproximationExponentAtMostTwo x) : Irrational x := by
  apply irrational_of_eventualApproximationLowerBound
  exact (not_arbitrarilyGoodApproximations_iff x 3).mp (h 3 (by norm_num))

/-- Dirichlet supplies infinitely many reduced fractions with error less than q⁻²,
conditional only on the explicit upper bound. The upper bound itself is NOT proved here. -/
theorem infinite_dirichlet_approximants_of_upper_bound {x : ℝ}
    (h : ApproximationExponentAtMostTwo x) :
    {r : ℚ | |x - (r : ℝ)| < 1 / (r.den : ℝ) ^ 2}.Infinite := by
  exact Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational
    (irrational_of_approximationExponentAtMostTwo h)

/-- Rational numbers in a bounded real interval with bounded denominator form a
finite set. This turns mathlib's infinite Dirichlet set into unbounded denominators. -/
theorem finite_bounded_denominator_near (x : ℝ) (N : ℕ) :
    {r : ℚ | r.den ≤ N ∧ |x - (r : ℝ)| ≤ 1}.Finite := by
  let B : ℤ := ⌈(|x| + 1) * (N : ℝ)⌉
  let f : ℚ → ℤ × ℕ := fun r => (r.num, r.den)
  have hinj : Function.Injective f := by
    intro a b hab
    simp only [f, Prod.mk.injEq] at hab
    rw [← Rat.num_div_den a, ← Rat.num_div_den b, hab.1, hab.2]
  have hsub : f '' {r : ℚ | r.den ≤ N ∧ |x - (r : ℝ)| ≤ 1} ⊆
      Set.Icc (-B) B ×ˢ Set.Icc 0 N := by
    rintro z ⟨r, ⟨hden, hclose⟩, rfl⟩
    have hdenpos : 0 < (r.den : ℝ) := by exact_mod_cast r.den_pos
    have habs : |(r : ℝ)| ≤ |x| + 1 := by
      calc
        |(r : ℝ)| = |x - (x - (r : ℝ))| := by congr 1; ring
        _ ≤ |x| + |x - (r : ℝ)| := abs_sub _ _
        _ ≤ |x| + 1 := add_le_add_left hclose _
    have hrepr : (r.num : ℝ) = (r : ℝ) * (r.den : ℝ) := by
      rw [Rat.cast_def, div_mul_cancel₀ _ hdenpos.ne']
    have hB : |(r.num : ℝ)| ≤ (B : ℝ) := by
      calc
        |(r.num : ℝ)| = |(r : ℝ)| * (r.den : ℝ) := by
          rw [hrepr, abs_mul, abs_of_pos hdenpos]
        _ ≤ (|x| + 1) * (r.den : ℝ) := mul_le_mul_of_nonneg_right habs hdenpos.le
        _ ≤ (|x| + 1) * (N : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hden) (by positivity)
        _ ≤ (B : ℝ) := Int.le_ceil _
    have hnumb : -B ≤ r.num ∧ r.num ≤ B := by
      have hh := abs_le.mp hB
      constructor
      · exact_mod_cast hh.1
      · exact_mod_cast hh.2
    exact ⟨hnumb, Nat.zero_le _, hden⟩
  exact (((Set.finite_Icc (-B) B).prod (Set.finite_Icc 0 N)).subset hsub).of_finite_image
    hinj.injOn

/-- Dirichlet's infinitely many reduced approximants have arbitrarily large denominators. -/
theorem strictArbitrarilyGoodApproximations_two_of_irrational {x : ℝ}
    (hx : Irrational x) : StrictArbitrarilyGoodApproximations x 2 := by
  intro N
  obtain ⟨r, hgood, hnot⟩ :=
    (Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hx).exists_notMem_finite
      (finite_bounded_denominator_near x N)
  have hdenpos : 0 < (r.den : ℝ) := by exact_mod_cast r.den_pos
  have hdenone : 1 ≤ (r.den : ℝ) := by exact_mod_cast r.pos
  have hsmall : |x - (r : ℝ)| ≤ 1 := by
    apply hgood.le.trans
    exact (div_le_one (by positivity)).mpr (by nlinarith)
  have hdenN : N < r.den := by
    by_contra hn
    exact hnot ⟨by omega, hsmall⟩
  refine ⟨r.den, hdenN.le, r.den_pos, r.num, ?_⟩
  rw [← Rat.cast_def]
  simpa only [Real.rpow_neg hdenpos.le, Real.rpow_two, one_div] using hgood

/-- The manuscript's weak form also follows from strict Dirichlet approximants. -/
theorem arbitrarilyGoodApproximations_two_of_irrational {x : ℝ} (hx : Irrational x) :
    ArbitrarilyGoodApproximations x 2 :=
  (strictArbitrarilyGoodApproximations_two_of_irrational hx).to_weak

/-- Both sides of the exponent-two claim, expressed by explicit denominator quantifiers. -/
def ApproximationExponentExactlyTwo (x : ℝ) : Prop :=
  ArbitrarilyGoodApproximations x 2 ∧ ApproximationExponentAtMostTwo x

/-- Dirichlet establishes the lower side once the upper side is known. -/
theorem approximationExponentExactlyTwo_of_upper {x : ℝ}
    (h : ApproximationExponentAtMostTwo x) : ApproximationExponentExactlyTwo x := by
  exact ⟨arbitrarilyGoodApproximations_two_of_irrational
    (irrational_of_approximationExponentAtMostTwo h), h⟩

/-- Weakening an exponent preserves arbitrarily good approximations. -/
theorem ArbitrarilyGoodApproximations.of_exponent_le {x ν₁ ν₂ : ℝ}
    (h : ArbitrarilyGoodApproximations x ν₂) (hν : ν₁ ≤ ν₂) :
    ArbitrarilyGoodApproximations x ν₁ := by
  intro N
  obtain ⟨q, hqN, hqpos, p, herr⟩ := h N
  refine ⟨q, hqN, hqpos, p, herr.trans ?_⟩
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast (hqpos : 1 ≤ q)
  · exact neg_le_neg hν

/-- Under the upper bound, the admissible real exponents are exactly ν ≤ 2. -/
theorem arbitrarilyGoodApproximations_iff_exponent_le_two {x ν : ℝ}
    (h : ApproximationExponentAtMostTwo x) :
    ArbitrarilyGoodApproximations x ν ↔ ν ≤ 2 := by
  constructor
  · intro hν
    by_contra hn
    exact h ν (lt_of_not_ge hn) hν
  · intro hν
    exact (arbitrarilyGoodApproximations_two_of_irrational
      (irrational_of_approximationExponentAtMostTwo h)).of_exponent_le hν

/-- The approximation exponent as an extended-real supremum. For irrational real
numbers this is the usual irrationality exponent. The use of `EReal` permits value `⊤`
when exponents are unbounded. With the manuscript's unreduced-denominator convention,
rational numbers also have value `⊤`; no identification with conventions for rational
numbers is intended. -/
noncomputable def irrationalityExponent (x : ℝ) : EReal :=
  sSup ((fun ν : ℝ => (ν : EReal)) '' {ν : ℝ | StrictArbitrarilyGoodApproximations x ν})

/-- Actual supremum equality: the two explicit approximation properties imply μ(x)=2. -/
theorem irrationalityExponent_eq_two_of_exact {x : ℝ}
    (h : ApproximationExponentExactlyTwo x) : irrationalityExponent x = 2 := by
  apply le_antisymm
  · apply sSup_le
    rintro y ⟨ν, hν, rfl⟩
    have hle : ν ≤ 2 := by
      by_contra hn
      exact h.2 ν (lt_of_not_ge hn) (StrictArbitrarilyGoodApproximations.to_weak hν)
    calc
      (ν : EReal) ≤ ((2 : ℝ) : EReal) := EReal.coe_le_coe hle
      _ = (2 : EReal) := EReal.coe_natCast (n := 2)
  · exact le_sSup ⟨(2 : ℝ),
      strictArbitrarilyGoodApproximations_two_of_irrational
        (irrational_of_approximationExponentAtMostTwo h.2), EReal.coe_natCast (n := 2)⟩

/-- The quantitative upper bounds plus mathlib Dirichlet give the actual exponent. -/
theorem irrationalityExponent_eq_two_of_eventual_bounds {x : ℝ}
    (h : ∀ ν : ℝ, 2 < ν → EventualApproximationLowerBound x ν) :
    irrationalityExponent x = 2 := by
  exact irrationalityExponent_eq_two_of_exact (approximationExponentExactlyTwo_of_upper
    ((approximationExponentAtMostTwo_iff_eventual x).mpr h))

/-- The manuscript's final conditional bridge, with all missing analytic work exposed
in the `hbound` argument. This is not an unconditional theorem about real logarithms. -/
theorem conditional_logarithm_endpoint (r : ℝ)
    (hbound : ∀ ν : ℝ, 2 < ν →
      EventualApproximationLowerBound (Real.log r) ν) :
    Irrational (Real.log r) ∧
      irrationalityExponent (Real.log r) = 2 ∧
      ApproximationExponentAtMostTwo (Real.log r) ∧
      {s : ℚ | |Real.log r - (s : ℝ)| < 1 / (s.den : ℝ) ^ 2}.Infinite := by
  have hupper := (approximationExponentAtMostTwo_iff_eventual (Real.log r)).mpr hbound
  exact ⟨irrational_of_approximationExponentAtMostTwo hupper,
    irrationalityExponent_eq_two_of_eventual_bounds hbound, hupper,
    infinite_dirichlet_approximants_of_upper_bound hupper⟩

end RationalLogReview

/- Kernel dependency audit: none of these may depend on `sorryAx`. -/
#print axioms RationalLogReview.not_arbitrarilyGoodApproximations_iff
#print axioms RationalLogReview.rational_has_arbitrarily_large_exact_representations
#print axioms RationalLogReview.irrational_of_eventual_positive_lower_bound
#print axioms RationalLogReview.irrational_of_eventualApproximationLowerBound
#print axioms RationalLogReview.approximationExponentAtMostTwo_iff_eventual
#print axioms RationalLogReview.irrational_of_approximationExponentAtMostTwo
#print axioms RationalLogReview.infinite_dirichlet_approximants_of_upper_bound
#print axioms RationalLogReview.finite_bounded_denominator_near
#print axioms RationalLogReview.arbitrarilyGoodApproximations_two_of_irrational
#print axioms RationalLogReview.approximationExponentExactlyTwo_of_upper
#print axioms RationalLogReview.ArbitrarilyGoodApproximations.of_exponent_le
#print axioms RationalLogReview.arbitrarilyGoodApproximations_iff_exponent_le_two
#print axioms RationalLogReview.irrationalityExponent_eq_two_of_exact
#print axioms RationalLogReview.irrationalityExponent_eq_two_of_eventual_bounds
#print axioms RationalLogReview.conditional_logarithm_endpoint

#print axioms RationalLogReview.StrictArbitrarilyGoodApproximations.to_weak
#print axioms RationalLogReview.strictArbitrarilyGoodApproximations_two_of_irrational
