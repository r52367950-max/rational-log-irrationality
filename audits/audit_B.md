# Independent audit of the arithmetic–analytic implication B

Audited file: `source/Theorem-B-rational-logarithm-proof.md`, dated 7 October 2026.

Scope: I assumed only the statement of Theorem A in `source/Theorem-A-revised-proof.md`; I did not assume A's geometric proof is correct. I checked the rational arithmetic, the row expansion, the analytic determinant estimate, the counting alternatives, and the order in which parameters and approximants are chosen.

## Finding

I did not identify a substantive error in the written implication **A ⇒ μ(log r) = 2 for positive rational r ≠ 1**. In particular, the height contribution from the denominator of r is present, the approximate logarithm translation is an exact finite identity, the determinant collision estimate has the claimed constant, and the final parameter inequalities are compatible.

This is an independent mathematical audit of B, not a full formal certificate. It does not validate A, and it does not justify calling the combined main theorem established before A's independent audit and formal work are assessed.

## 1. Arithmetic denominator clearing

For a selected column `Y^h X^α`, and a row `(j,s,β)`, the scalar factors in the manuscript give

`a^(jh) b^((K−1−j)h) ∏ binom(α_i,β_i)`

times the coefficient of

`(1+t)^h ∏ [q_i(j r_i + G_i(t))]^(α_i−β_i)`.

Here `0 ≤ j < K`, so the exponent of b is nonnegative; `q_i j r_i = j p_i` is an integer. The coefficients of `G_i` have denominator dividing `L_i = lcm(1,…,T_i−1)`. The denominator of the whole coefficient therefore divides `∏ L_i^(α_i−β_i)`, which divides the common `D_H` because `α_i ≤ floor(H/w_i)`. If some `α_i < β_i`, the coefficient is zero and causes no problem.

Multiplying every entry of the already scaled minor by `D_H` gives an integral nonsingular matrix. Undoing the row and column scalings gives exactly the sign pattern in the displayed lower bound: column scaling subtracts its logarithm, and row scaling `∏ q_i^(−β_i)` adds `∑ β_i log q_i`.

The simplification is valid:

* `∑ α_i log q_i ≤ ∑ α_i w_i ≤ H`;
* `h ≤ H/w₀`;
* `log q_i ≥ w_i−1`;
* `∑ β_i ≤ (∑ w_i β_i)/w_* < θ H/w_*`.

Thus the loss `θ/w_*` is sufficient. The term `(K−1) log b / w₀` correctly accounts for the rational base denominator. The lcm constant `Λ = 4 log 2` is generous; no sharp prime-number-theorem estimate is needed. The estimate `T_i ≤ F₀ w_i/v₀ + 1` yields the quoted `Λ F₀ m/v₀ + Λ∑1/w_i` upper bound.

## 2. Exact translation identity

Write `z = jω + log(1+t)` and `δ_i = ε_i + τ_i(t)`. Then the original entry is the u coefficient of

`P(e^z, z+δ₁+u₁, …, z+δ_m+u_m)`.

Expanding the polynomial in its additive variables around `(z,…,z)` gives

`∑_{a≥β} binom(a,β) δ^(a−β) f_{a,P}(z)`.

Expanding each `δ_i^(a_i−β_i)` by the binomial theorem and then taking the t coefficient gives equation (5). The potentially important feature is that each coefficient is independent of the selected column P. The index restriction `w a ≤ H` is valid: `f_{a,P}` vanishes unless `a ≤ α`, and every column obeys `w α ≤ H`.

The formula is finite for each row. A summand should be regarded as indexed by `(a,d,k)` rather than by a alone; this is merely a wording clarification and is already reflected in `Q_H`.

Since `τ_i` starts in t degree `T_i`, a nonzero coefficient with tail index d satisfies `∑ d_i T_i ≤ k ≤ s`. Using `T_i ≥ F₀ w_i/v₀` and `v₀s < H` gives `w d ≤ H/F₀` (indeed a strict inequality except at discarded boundary cases). On `|t|=1/2`,

`|τ_i(t)| ≤ ∑_{k≥T_i} 2^(−k)/k ≤ log 2 < 1`.

The tail coefficient is therefore bounded by `2^k ≤ 2^s`. Moreover `|ε_i| ≤ K e^ν exp(−ν w_i)`, and the product of the two binomial factors is bounded by `4^|a|`. The exponential bound (6), including the compensating loss `ν/F₀` for the tail index d, follows.

## 3. Entire-function and collision estimates

For every selected column,

`f_{a,P}(z) = binom(α,a) e^(hz) z^(|α|−|a|)`

when `a ≤ α`, and it is zero otherwise. Because `R ≥ 4`, its modulus on `|z| ≤ R` is bounded by

`exp(H R/w₀) (2R)^(H/w_*)`.

This gives equation (7). It includes the complete numerator growth from `r^(jh)`; that growth was not omitted in the arithmetic argument.

On the t circle `|t|=1/2`, the chosen `R₀ > 4(ω+1)` actually gives a bound stronger than `|z| < R/2`. Applying Cauchy's coefficient bound to `(z(t)/R)^d` yields `2^ℓ 2^(−d)`, as claimed. The row Taylor coefficient vectors depend only on `(a,d)`, so repeating a pair makes the determinant zero.

For `n_a` rows with a fixed transverse a, distinct nonnegative d indices have sum at least `n_a(n_a−1)/2`. Splitting `2^(−∑d)` into two equal factors forces

`−(log 2)/4 ∑ n_a² + (log 2)/4 M`.

The remaining factor sums to at most `(1−2^(−1/2))^(−M)`. Together with `M! (D'_H)^M` and `2^(∑ℓ)`, this proves (8) with `c = log 2 / 4`. The `+cM` and geometric-series constants become `O(1/H)` after division by `MH`; `log(M!)/(MH)` tends to zero because fixed-data simplex counting gives `M ≍ H^(m+1)`. These error terms are uniform over selected columns and expanded test rows.

Absolute convergence is sufficient to rearrange the Taylor-expanded determinant, and it follows directly from the same geometric factors before removing collision terms.

## 4. Counting alternatives

The total number of rows is asymptotic to

`K θ^m H^(m+1) / [(m+1)! v₀ ∏w_i]`.

The number of a with `wa ≤ AH` is asymptotic to `A^m H^m/[m!∏w_i]`. If at least `ηM` rows lie among these a, Cauchy–Schwarz gives

`∑n_a² / (MH) ≥ η² K θ^m / [(m+1)v₀ A^m] + o(1) = L + o(1)`.

The scalar exponent is nonpositive since every expanded a satisfies `a ≥ β`. If fewer than `ηM` rows have `wa ≤ AH`, then the remaining rows yield `∑wa > MH A(1−η)`, hence the displayed approximation-error exponent. The number of expansion terms grows only polynomially in H per row, so `log Q_H/H → 0` with fixed m. Taking a maximum of the two alternatives is legitimate.

The high-index comparison to the arithmetic lower bound reduces to

`ν A(1−η) − 1 − (ν−1)bbar ≥ ν(A(1−η)−θ) − (1−θ) = g`,

because `bbar ≤ θ` and `ν−1 > 0`. The low-index alternative is excluded by `cL > 1+E`. No missing sign change was found.

## 5. Parameter selection and quantifiers

For `ν > 2`, the rational interval `(1/2, 1−1/ν)` is nonempty. Choosing d there and sufficiently small rational δ gives

`ν(A−θ) > 1−θ`, `A² < θ`, and `θ < A < 1`.

The inequality `A² < θ` makes `(A/θ,1/A)` nonempty, so C can be chosen as in the text. The interval for B is nonempty because `Cθ > A` and `1/C > A`. These choices give all three strict exponential conditions:

`CB < 1`, `Cθ/B > 1`, and `B/A > 1`.

With `w₀=B^(−m)`, `v₀=2Kθ^m w₀`, and `K=floor(C^m)`, the volume ratio is exactly one half. The formula

`L = η²(B/A)^m/[2(m+1)]`

is exact: K cancels, so the floor introduces no error there. The limits for `K/w₀`, `v₀`, `m/v₀`, and L are valid. `R₀` and the rational-base height are fixed before m, so their terms can be made small at this stage.

After fixing m, the approximant denominators are chosen. An unbounded set of hypothetical denominators suffices to meet each of finitely many successive thresholds: density and bounded growth ratios are unnecessary. The weights `ceil(log q_i)` are positive integers once q is sufficiently large, satisfying A's rational-weight requirement. A's denominator R and its center-dependent lower threshold are then fixed; H can subsequently tend to infinity along `nR`.

The three disjoint error budgets add to `E < ε₀ ≤ min(g/2,1/2)`. Together with `cL > 2`, they imply all contradiction inequalities (10).

## 6. Consequence and remaining work

Conditional on A, the contradiction proves the eventual strict lower bound for each `ν > 2`. If ω were rational, taking integer multiples of one exact denominator would violate this lower bound, so irrationality follows. The usual Dirichlet theorem then gives exponent at least two, while the proved upper bounds give at most two.

At the first audit, the main work for full Lean certification of B included the row expansion, lattice asymptotics, determinant collision estimate, denominator-clearing argument, and a proved formal instance of A. The subsequent direct OAI017 adapter now certifies the finite rational-base row/determinant expansion and the actual analytic collision estimate (see Section 8). The full lattice asymptotic and parameter assembly and the new theorem A remain to be formalized. A Lean theorem that accepts such remaining ingredients as hypotheses certifies the resulting implication only and must be labeled accordingly.

Suggested small manuscript improvement: explicitly index each expansion term by `(a,d,k)` and state the elementary lcm bound as its own lemma. Neither improvement changes the audited mathematics.

## 7. Completed Lean component

`lean/Collision.lean` was checked by Lean 4.24.0 with mathlib v4.24.0 using `lean/check.sh`; the process exited successfully. It contains nine proved theorems with no `sorry` and no added axioms:

* finite distinct natural degrees satisfy `n(n−1) ≤ 2∑d`;
* the corresponding bound for a finite injectively indexed row set;
* the grouped triangular inequality;
* the grouped square inequality `∑n_a² ≤ 2∑d_i + M`;
* its real-valued version;
* the real-valued version with the exact hypothesis that the Taylor pair `(a,d)` is injective on the selected rows.
* the finite occupancy inequality `(∑n_a)² ≤ N∑n_a²`, for arbitrary real occupancies and `N` equal to the index-set cardinality;
* its nonnegative-threshold implication `L² ≤ N∑n_a²` when `0 ≤ L ≤ ∑n_a` (take `L = ηM` in B);
* the corresponding inequality with the occupancy square sum enlarged from the low-index subset to all indices.

The printed axiom dependencies of all nine theorems are only the usual Lean foundational axioms `propext`, `Classical.choice`, and `Quot.sound`. `sorryAx` and project-specific axioms are absent. The observed compile record is in `lean/Collision-verification.txt`.

This gives actual kernel verification of the combinatorial collision saving and the finite Cauchy–Schwarz ingredient in Section 5. This standalone combinatorial file by itself does not certify the analytic inequality (8), the weighted-simplex asymptotic cardinalities, or the complete B theorem; the subsequent analytic certificate is described below.

## 8. Actual reuse of OAI017

`oai017/RationalLogAnalytic.lean` subsequently passed a strict Lean 4.34.1 check against the original pinned mathlib dependency and the actual proved OAI017 modules at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The build retains original proof bodies and narrows the original umbrella mathlib import headers in working copies to fit memory. It uses none of the comparator file's `by sorry` challenge signature.

Its 15 new theorems prove the finite polynomial shift, the finite row expansion, the full determinant expansion with the essential `y_i^h` factor, the approximation-error and scalar-saving estimates, center/order budgets, and the coefficient/analytic bridge. For positive rational r it proves `exp(j log r)=r^j` and states the actual OAI collision inequality directly for the translated rational-base coefficient determinant.

The process exited 0 and emitted `.olean`/`.ilean` files. All 15 new theorem axiom lists and the four reused generic upstream theorem axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axiom is present. The successful record is `oai017/RationalLogAnalytic-verification.txt`; the detailed exact reuse scope is `oai017/reuse_B_audit.md`.

This certifies B's analytic collision ingredient and finite translation by actual proved upstream code, with explicit elementary budget premises. Full certification of A and the final B asymptotic assembly remain open tasks for this review.
