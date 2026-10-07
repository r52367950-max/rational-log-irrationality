# Theorem B: actual normalized determinant and asymptotic assembly

This round uses the genuine OAI017 proof bodies at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, Lean 4.34.1, and mathlib pin `d13f23b723b8a846827a245b89c10fc7d3f11612`. Working copies narrow umbrella imports only; pristine upstream source is preserved.

## Newly closed part

`oai017/RationalLogAsymptotic.lean` derives the normalized analytic aggregate for the literal rational-base matrix, derives its cardinality and remainder limits, joins the actual normalized arithmetic lower bound, and obtains the usual logarithm endpoint conditional only on the actual cofinal packet interpolation. `oai017/RationalLogMain.lean` now supplies that interpolation using the proved geometry and derives the unconditional main theorem. Neither module accepts determinant upper/lower bounds, row counts, collision limits, vanishing remainders, or existence of suitable parameters as hypotheses.

The initial completed matrix endpoint is `RationalLogReview.Analytic.rational_log_endpoint_of_cofinal_interpolation`. Its only extra input is `CofinalActualInterpolation r hr`, namely cofinal surjectivity of the actual weighted finite matrix at the proved selected data. The process exited 0, emitted `.olean`, and printed 15 axiom lists containing only `propext`, `Classical.choice`, and `Quot.sound`. This checkpoint is retained in `round2/B_cofinal_matrix_checkpoint.txt`.

The final refinement `rational_log_endpoint_of_cofinal_packets` uses the genuine new `DistinctMultiplicative.packetMapAt` instead of postulating a minor or a finite matrix estimate. This full packet-based B assembly has passed strict checking with exit 0 and 20 printed axiom lists, all containing only the three standard axioms. The final log is `oai017/RationalLogAsymptotic-verification.txt`.

## Concrete matrix and normalized bounds

The matrix entry retains the factor `(r^j)^h` and uses the additive approximant `j*p_i/q_i` and the actual truncated logarithm of order

`T_i = ceil(F0*w_i/v0)`, `w_i = ceil(log q_i)`.

The source weights are `W=(w0,w_1,…,w_m)`; the strict target weights are `V=(v0,w_1/theta,…,w_m/theta)`. The finite row set is exactly the original strict weighted simplex times `Fin K`, and the column set is exactly the original inclusive weighted simplex. The mean transverse row weight is its actual sum divided by `M H`, with proved bounds `0 ≤ mean ≤ theta`.

For every nonzero selected minor, actual Gaussian-integral clearing gives

`log(norm(det))/(M H) >= -(1-mean)-E_ar`,

where

`E_ar = Lambda*F0*m/v0 + Lambda*sum_i(1/w_i) + theta/wstar + (K-1)*log(r.den)/w0`.

Here `Lambda` is the proved upstream `Arithmetic.lcmConstant=log(4)+4`. This constant is larger than the manuscript's chosen LCM constant, and the constructed parameters explicitly absorb it. The base-height loss is derived from the literal entries, including canonical numerator/denominator conversion; it is not postulated as a factor.

The analytic upper estimate is

`log(norm(det))/(M H) <= E_an + remainder(H) + max(-collisionRate(H), -nu*(A*(1-eta)-mean))`,

with

`E_an = nu/F0 + R0*K/w0 + 2*log(2)/v0 + (log(4)+log(2*K)+nu+log(2*R0*K))/wstar`.

It is proved from the actual finite row/determinant expansion, actual scalar bound, genuine Taylor-collision theorem, finite low-index capacity, and genuine determinant-sum inequality. The factor `r^(j*h)` remains inside each tested matrix. Both alternatives of the collision argument are derived rather than supplied.

## Counts and H-limits

The original generic rational-weight theorems `MatrixCounting.tendsto_rowCount_normalized`, `tendsto_lowIndexCount_normalized`, and `tendsto_collisionRatio` are used with the actual finite denominator vector. They give

`M/H^(m+1) -> K*theta^m/((m+1)!*v0*prod_i(w_i))`,

`N_low/H^m -> A^m/(m!*prod_i(w_i))`,

`collisionRate(H) -> c*eta^2*K*theta^m/((m+1)*v0*A^m)`, `c=log(2)/4`.

The finite translation family has cardinality at most `Q_H^M`, where

`Q_H=(floor(H)+1)^(2m)*(floor(H/v0)+1)`.

The explicit remainder is

`Collision.collisionRemainder(M,H) + log(Q_H)/H`.

Its limit is proved to be zero from the actual row-count asymptotic and the actual polynomial term-count asymptotic. No asymptotic assertion is an input field of `Data` or of `SelectedParameters`.

## Joining the proved parameters

`ofSelected` constructs the finite analytic data from `RationalLogParameters.SelectedParameters` and its actual approximation sequence. The center radius is `R0=4*(abs(log r)+1)+1`; the base height is `log(r.den)`. The exact identities between the selected-data analytic/arithmetic errors and the matrix-derived errors are proved.

The parameter module independently proves existence, the two strict contradiction margins, separation, and the usual exponent endpoint. The B assembly constructs actual determinant values from cofinal nonzero minors, proves their lower and upper bounds and limits, and feeds those concrete values to the proved cofinal comparison. At this intermediate boundary, the strict bound, irrationality, and exponent-two conclusion have only actual cofinal packet interpolation as an input; the main module supplies it from the fully proved fixed-weight geometry.

## Unconditional main assembly and exact target

`RationalLogMain.cofinal_packet_interpolation` calls the actual geometric theorem `DistinctMultiplicative.Degree.Weighted.eventual_interpolation_of_separated_weights` at the source and target weights of `SelectedParameters`. Weight positivity, volume, all separated product inequalities, and the transverse coordinate ratio come from the independently proved `RationalLogGeometryParameters` module. Distinctness and nonvanishing of the actual centers `(r : ℂ)^j` follow from positivity of `r` and `r ≠ 1`. The geometry produces a positive natural scale `R` and packet surjectivity eventually for budgets `nR`; the proved limit `nR → ∞` supplies every real cofinal threshold used by B.

The final theorem is

```
RationalLogReview.Main.rational_log_main
  (r : ℚ) (hr : 0 < r) (hne : r ≠ 1) :
  OAIAdapter.ManuscriptStrictBound (Real.log (r : ℝ)) ∧
  Irrational (Real.log (r : ℝ)) ∧
  OAI.PiExponent.irrationalityExponent (Real.log (r : ℝ)) = 2
```

There is no interpolation, curve, determinant, counting, limit or approximation hypothesis in its type. Its proof uses the actual new-center A geometry, the rational-base arithmetic clearing (including denominator height), and the complete B assembly above.

The strict projection has exactly the independently defined expected type:

```
RationalLogReview.Main.strict_rational_log_main :
  RationalLogReview.MainReference.StrictRationalLogMain
```

That reference file imports no solution module. Unfolding its proposition states, for every positive rational `r ≠ 1` and every real `ν > 2`, an eventual strict lower bound `q^(-ν) < |Real.log r - p/q|` for all integer numerators and positive natural denominators. No custom redefinition of `Real.log`, real numbers or rational approximation is involved.

Strict checking of `oai017/RationalLogMain.lean` exited 0, emitted `.olean`/`.ilean`, produced no warnings, and printed all five theorem axiom dependencies as exactly `propext`, `Classical.choice`, and `Quot.sound`. See `oai017/RationalLogMain-verification.txt`. The setup agent independently checks the whole final theorem against the reference and replays the declaration graph into a fresh kernel; that separate certificate is reported by the parent agent.
