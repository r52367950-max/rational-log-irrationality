# Direct reuse of OAI017 for the rational-logarithm determinant argument

Source: `openai/math`, fixed commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Original toolchain: Lean 4.34.1. Original mathlib pin: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Relevant original proved code

The actual code is under `lean/OAI/NumberTheory/PiExponent/`. The comparator file `lean/ComparatorChallenges/PiExponent.lean` contains a challenge signature with `by sorry`; it is not a proof and is not used by this adapter. The recursive repository-root tree API response is truncated, so that response alone cannot establish which original modules exist. The PiExponent subtree and its Analysis and Approximation subtrees have been fetched independently.

The real `Main.lean` proves its main theorem by composing `AdmissibleMatrixInterpolation.globalInterpolation` with the interpolation consequence. The generic analytic modules below have full source proofs; the reuse described here does not assume the main theorem about π.

| B component | Original module and theorem | Reuse status |
|---|---|---|
| Exact finite polynomial/jet translation | `Approximation/RowTranslation.lean`, `exact_row_identity` | Ring-generic; directly reused with the full rational-base polynomial. |
| Nonzero tail degree/weight budget | `Approximation/RowTranslation.lean`, `tail_budget_nat`, `tail_weight_budget` | Generic formal power-series results; no π or rational-base hypothesis. |
| Binomial coefficient/scalar factor bound | `Approximation/RowTranslation.lean`, `norm_rowScalar_le` | Generic complex coefficients; reusable for rational approximant errors. |
| Entire column function | `Analysis/PeriodAnalytic.lean`, `columnFunction`, `differentiable_columnFunction` | Exactly the function used by B; π-independent. |
| Full exponential/monomial growth estimate | `Analysis/PeriodAnalytic.lean`, `norm_columnFunction_le` | Exactly B's bound `exp(H(R/w0+log(2R)/wstar))`; proved and reused directly. |
| Finite determinant multilinearity and repeated Taylor-pair cancellation | `Analysis/FiniteDeterminantCollision.lean`, `det_finite_row_sum`, `finite_collision_bound` | Generic row/group/degree data. |
| Infinite Taylor determinant bound | `Analysis/AnalyticDeterminantCollision.lean`, `translated_row_determinant_exp_bound` | Exactly the `log 2 / 4` collision saving in B (8), with arbitrary entire functions and centers. |
| Two alternatives | `Analysis/DeterminantAnalyticBound.lean`, `two_alternative_exponent`, `translated_summand_bound` | Generic finite groups and weights; no π-specific assumption. |
| Summing the translated determinant terms | `Analysis/DeterminantAnalyticBound.lean`, `log_norm_sum_le` | Generic finite term set and nonzero determinant. |
| Rational theta/A/B/C and eta choices | `Approximation/Parameters.lean`, `exists_rational_parameters`, `exists_eta_preserving_exponent_gap`, `exists_parameters` | Entirely π-independent; can be imported directly. |

The analytic determinant theorem has genuine proved premises: differentiability, the sphere modulus bound, the center-radius inequality, and the sum-of-row-orders inequality. It does not take the desired determinant estimate as an assumption. Its exact collision remainder is

`(log M + log 2 / 4 − log(1−exp(−log 2/2)))/H`.

## The rational-base change

The upstream `MatrixTranslation.periodMonomial` has Y factor `(1+t)^h`. That is correct for the original periodic centers because `exp(center)=1`. For B, the center has Y coordinate `y=exp(center)`, and the Y factor is `y^h(1+t)^h`. Reusing the original periodic coefficient bridge without this factor would be wrong.

The new `RationalLogAnalytic.lean` therefore defines

`rationalPeriodMonomial y … = C(C(y^h)) * periodMonomial …`.

It proves that the same exact polynomial shift, finite row expansion, and full finite determinant expansion hold with that factor retained. It generalizes the periodic coefficient/function bridge from `exp(center)=1` to `exp(center)=y`. For positive `r : ℚ`, the adapter also proves `exp(j log r)=r^j` and specializes the coefficient bridge to B's actual center `y=r^j`. This is the actual local change needed to connect the rational-base jet to the generic entire column functions.

It then instantiates the original `translated_row_determinant_exp_bound`, reusing the original differentiability and entire column function bound. The last theorem states this collision bound directly for the determinant of the translated polynomial coefficients at the actual rational centers. The adapter's remaining budget hypotheses are the elementary weight/column, center-radius, and row-order inequalities, rather than an assumed determinant bound.

## Parts that cannot be imported unchanged

* Original arithmetic entries use the original Y-center behavior. B's extra denominator-height term `(K−1) log b/w0` for `r=a/b` is not supplied by importing the original π theorem.
* Original `AdmissibleParameters` and `FixedData` explicitly store approximations to `Real.pi` and a hardcoded `100K/w0` analytic budget. Reuse their generic base-parameter and growth lemmas, rather than presenting these whole records as rational-log data.
* The original `AnalyticAggregate` is built around those π-specific records. Its generic determinant summation theorem can be reused; the whole aggregate is not already a theorem about rational logarithms.
* The general logarithmic jet interpolation theorem A requires a geometric extension to distinct multiplicative coordinates; the original π interpolation result by itself does not establish that extension.

## Verification status

The build uses the pinned original Lean/mathlib versions. To fit the available memory, the working copies replace upstream's umbrella `import Mathlib` with selected stock mathlib module imports; the original proof bodies are unchanged, and the pristine downloaded source is retained separately. This import-only change must be distinguished from checking a pristine upstream checkout verbatim.

`RationalLogAnalytic.lean` was checked successfully with the pinned Lean 4.34.1/mathlib environment using `oai017/check.sh --adapter RationalLogAnalytic.lean`. The observed process exit code was 0, and both `.olean` and `.ilean` artifacts were emitted. The check sets `autoImplicit=false`.

The successful log `RationalLogAnalytic-verification.txt` prints axiom dependencies for all 15 new theorems and for four actual upstream theorems: `exact_row_identity`, `translated_row_determinant_exp_bound`, `two_alternative_exponent`, and `log_norm_sum_le`. Every printed list contains only `propext`, `Classical.choice`, and `Quot.sound`. There is no `sorryAx` or project-specific axiom. The compiler emitted an informational `ring_nf` suggestion; it emitted no error and accepted every theorem.

This certifies the full finite rational-base row/determinant translation, the approximation-error and scalar-saving adapters, the positive-rational exponential-center bridge, and the analytic collision bound directly on the translated coefficient determinant. It also certifies the genuine generic OAI two-alternative and determinant-sum inequalities. These are actual applications of proved upstream code, rather than accepting the desired analytic bound as an input hypothesis.

It does not certify the complete rational-logarithm interpolation theorem A, the full B asymptotic parameter/counting assembly, or the final unconditional exponent-two theorem. The explicit weight/column, center-radius, row-order, and support budgets remain premises of the adapter; B's proof must provide these. A successful original-main proof would not establish the new interpolation theorem automatically.
