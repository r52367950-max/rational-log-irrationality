import RationalLogAsymptotic
import RationalLogGeometryParameters
import DistinctMultiplicativeDegree
import Round2MainReference

/-! Unconditional assembly of actual distinct-center interpolation and the
height-aware rational-logarithm determinant contradiction. -/

set_option autoImplicit false

namespace RationalLogReview.Main

open Filter OAI.PiExponent
open scoped Topology

theorem rational_power_centers_injective (r : ℚ) (hr : 0 < r) (hne : r ≠ 1) :
    Function.Injective (fun j : ℕ => r ^ j) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (pow_right_strictAnti₀ hr hlt).injective
  · exact (pow_right_strictMono₀ hgt).injective

theorem complex_rational_power_centers (r : ℚ) (hr : 0 < r) (hne : r ≠ 1) (K : ℕ) :
    (∀ j : Fin K, (r : ℂ) ^ j.val ≠ 0) ∧
      Function.Injective (fun j : Fin K => (r : ℂ) ^ j.val) := by
  refine ⟨fun j => pow_ne_zero j.val (by exact_mod_cast ne_of_gt hr), ?_⟩
  intro i j hij
  apply Fin.ext
  apply rational_power_centers_injective r hr hne
  change (r : ℂ) ^ i.val = (r : ℂ) ^ j.val at hij
  change r ^ i.val = r ^ j.val
  exact_mod_cast hij

theorem cofinal_packet_interpolation (r : ℚ) (hr : 0 < r) (hne : r ≠ 1) :
    Analytic.CofinalPacketInterpolation r hr := by
  intro nu _hnu d L
  have hA := DistinctMultiplicative.Degree.Weighted.eventual_interpolation_of_separated_weights
    (GeometryParameters.sourceWeights d) (GeometryParameters.targetWeights d)
    (GeometryParameters.sourceWeights_pos d) (GeometryParameters.targetWeights_pos d)
    d.K d.sigma (by exact_mod_cast d.sigma_pos)
    (GeometryParameters.curve_volume d)
    (GeometryParameters.curve_separated_weight_products d)
    (GeometryParameters.curve_coordinate_ratio d)
  obtain ⟨R, hR, _hW, _hV, hpacket⟩ := hA
  have hy := complex_rational_power_centers r hr hne d.K
  have hsurj := hpacket (fun j : Fin d.K => (r : ℂ) ^ j.val)
    (fun j : Fin d.K => fun i => (j.val : ℂ) * ((d.p i.val : ℂ) / (d.q i.val : ℂ)))
    hy.1 hy.2
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) * (R : ℝ)) atTop atTop :=
    Tendsto.atTop_mul_const (by exact_mod_cast hR) tendsto_natCast_atTop_atTop
  obtain ⟨n, hn, hlarge⟩ := (hsurj.and (hlim.eventually (eventually_ge_atTop L))).exists
  refine ⟨(n : ℚ) * (R : ℚ), by simpa using hlarge, ?_⟩
  exact hn

/-- Full usual main theorem: there is no geometric, interpolation, determinant,
counting, asymptotic or parameter-selection hypothesis. -/
theorem rational_log_main (r : ℚ) (hr : 0 < r) (hne : r ≠ 1) :
    OAIAdapter.ManuscriptStrictBound (Real.log (r : ℝ)) ∧
      Irrational (Real.log (r : ℝ)) ∧
      OAI.PiExponent.irrationalityExponent (Real.log (r : ℝ)) = 2 :=
  Analytic.rational_log_endpoint_of_cofinal_packets r hr
    (cofinal_packet_interpolation r hr hne)

/-- Exact independently defined strict-bound target, quantified over every
positive rational base other than one. -/
theorem strict_rational_log_main : MainReference.StrictRationalLogMain := by
  intro r hr hne
  exact (rational_log_main r hr hne).1

end RationalLogReview.Main

#print axioms RationalLogReview.Main.rational_power_centers_injective
#print axioms RationalLogReview.Main.complex_rational_power_centers
#print axioms RationalLogReview.Main.cofinal_packet_interpolation
#print axioms RationalLogReview.Main.rational_log_main
#print axioms RationalLogReview.Main.strict_rational_log_main
