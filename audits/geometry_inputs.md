# Independent geometric audit of Theorem A, Sections 5–9

Audit date: 2026-10-07. Scope: the pure-power blowup, compactification,
curve-degree calculations, ampleness on the possibly singular blowup, and
passage from global sections to formal logarithmic jets. This audit does not
verify the arithmetic argument or independently prove Proposition 4.1.

## Verdict

**No mathematical error was found in Sections 5–8.** Conditional on the curve
inequality of Proposition 4.1, the written geometric deductions give the
claimed eventual jet surjectivity. In particular, the ordinary, unnormalized
blowup and its non-normality cause no defect in these deductions. The
all-`n` recovery in Lemma 5.1 is justified for the actual pure-power ideals.

This is an independent ordinary-mathematical audit, not a Lean certificate of
the scheme-theoretic argument.

## 1. Lemma 5.1: local monomials and all powers

Write `f_i = z_i^{a_i}`. Because every monomial in the variables `z_i` is a
non-zero-divisor in `A[z]`, the relevant localization embeds in the Laurent
polynomial ring even if `A` itself has zero divisors. There is no hidden
domain assumption on `A`.

On the intersection indexed by a nonempty `S`, a Laurent exponent `b` occurs
in degree `n` precisely when there are integers `e_i` with

* `sum e_i = n`;
* `e_i >= 0` for `i` outside `S`;
* `a_i e_i <= b_i` for every `i`.

This is equivalent to the manuscript's formula (5.2). Necessity follows
immediately. For sufficiency, start with `e_i = floor(b_i/a_i)` and lower an
`e_i` indexed by `S` until the sum is `n`. Exponents outside `S` remain
nonnegative. Arbitrarily negative exponents inside `S` are allowed by the
localized degree-one generators. Every resulting expression can be cleared
back into the Rees ring, so no nonexistent localized section was admitted.

The exponentwise Čech complex is therefore correctly described. For a
nonempty proper negative-index set `T_b`, insertion of a fixed index outside
`T_b` is a contracting homotopy, including at its lowest degree. If `T_b`
is the full index set, every floor is at most `-1`, so this exponent cannot
occur for `n >= 0`. For empty `T_b`, the usual simplex complex has precisely
one copy of `A` in degree-zero cohomology. Thus the surviving sections have
`b >= 0` and `sum floor(b_i/a_i) >= n`, exactly the monomials of `I^n`.

The manuscript's signed contraction was also checked by exact integer
arithmetic on **9,322 basis cochains in dimensions 2–8**, over every nonempty
proper mandatory-index subset. Every check gave `dh + hd = id`.
The reproducible check is `cech_contraction_check.py`. This finite check
corroborates the signs; the general proof remains the displayed contraction.

Localization at an arbitrary element of `R`, not just an element of `A`,
commutes with the finite Čech complex. This proves the vanishing over every
principal open of the base and hence the higher-direct-image assertion.
The direct-sum decomposition by Laurent exponent need not survive that
localization; exactness already established before localization does.

An independent conceptual explanation is available. Put
`S=A[x_1,...,x_d]` and map `x_i` to `z_i^{a_i}`. Then `R` is finite free
over `S`, with basis `z^r` for `0 <= r_i < a_i`. The pure-power blowup is
the flat base change of the ordinary blowup of `(x_1,...,x_d)`.
This also explains why this special case has ordinary-power recovery in
every nonnegative degree, in contrast to arbitrary ideals.

Primary source checked for the Čech computation:
[Stacks 01XD](https://stacks.math.columbia.edu/tag/01XD), Lemma 30.2.6.
Its hypothesis is an open cover all of whose finite intersections are
affine; its conclusion identifies Čech and sheaf cohomology for a
quasi-coherent sheaf. The standard Proj opens satisfy that hypothesis.

## 2. Compactification and branch invariants

Choosing `R/w_i` and `R/v_i` positive integers is possible for positive
rational weights. The affine chart of the projective closure is indeed the
original affine space, because the embedding contains the constant and
every original coordinate. There is no assumption of projective normality.

The line-bundle degree formula (6.1) is correct after pulling back to the
complete nonsingular model of the curve. At each point the greatest pole
order among the embedding monomials is `R` times the weighted maximum:
the pure coordinate powers attain that maximum. Clearing those poles
produces a linear series with no base points. The constant section deals
with the case in which every pole order is zero. Thus no additional
base-point subtraction is missing from (6.1).

The difference between the algebraic coordinate `u_i'` and the formal
coordinate `u_i` has weight strictly above `v_i`. Both substitutions are
well-defined automorphisms of the completed local ring and preserve every
weighted monomial ideal. Along a branch, the correction has order strictly
greater than `v_i h_P`. Since some coordinate attains the finite minimum,
that minimum is unchanged. If `t` is identically zero, the correction is
zero and the same argument holds using infinite order.

The local ideals glue without an extension problem at the boundary: on
the overlap between the affine chart and the complement of the finite
center set their restriction is the unit ideal. Distinct centers make the
other factors in the affine product units locally. Hence Lemma 5.1 applies
near every center, and the blowup is the identity elsewhere. Formula (6.3)
follows locally on the base for every `n >= 0`.

## 3. Degrees on the blowup and ampleness

Every noncontracted irreducible curve maps birationally to its image,
because the blowup is the identity off a finite set. Its normalization is
the complete nonsingular model of that image. Pullback of the center ideal
to a discrete valuation ring has order
`min_i a_i ord(z_i) = R h_P`. Consequently the exceptional degree is exactly
`R sum h_P`; no normalization multiplicity or field-degree factor is lost.

Curves contained in the projective boundary avoid the center set and have
exceptional degree zero. Contracted curves have degree zero for `A` and
strictly positive degree for `-E`, by relative ampleness. These are all
cases, so Proposition 4.1 implies nefness of `A-(1+sigma)E`.

The Rees immersion following global generation of `I tensor L^b` is valid:
the surjection from the trivial symmetric algebra to
`direct sum I^n tensor L^{bn}` induces a closed immersion into
`X times P^r`. The second hyperplane bundle pulls back to `bA-E`.
The external tensor product of the two very ample bundles restricts to
`(b+1)A-E`, proving the auxiliary ampleness claim.

Identity (7.3) has the correct coefficients. They are positive for
`a>1`, `sigma>0`; their contributions to the `A` coefficient sum to one
and their contributions to the `E` coefficient sum to minus one.

The specific cited theorem really does allow singular and non-normal
projective schemes. Lazarsfeld, *Positivity I*, Corollary 1.4.10, printed
page 53, states the ample-plus-positive-nef conclusion for a projective
variety **or scheme**. Thus an objection based solely on lack of smoothness
or normality would be incorrect.

Primary source independently opened:
[Lazarsfeld chapter 1 PDF](https://www.math.stonybrook.edu/~roblaz/Reprints/Laz.PAG.Chapt1.pdf),
PDF page index 48, Corollary 1.4.10.

Also checked:
[Stacks 02OS](https://stacks.math.columbia.edu/tag/02OS), effective Cartier
exceptional divisor and `O(-1)=O(E)`;
[Stacks 02NS](https://stacks.math.columbia.edu/tag/02NS), projectivity and
relative ampleness for a finite-type ideal.

## 4. Section 8: actual surjectivity

Serre vanishing on `X'` for the ample invertible sheaf `O(A-E)` gives the
required first cohomology vanishing. Formula (6.3), projection formula,
and the degenerate Leray spectral sequence identify it with
`H^1(X,I^n tensor L^n)`. The quotient exact sequence then gives (8.1).
This use of ordinary powers is justified; replacing them silently by
integral closures is unnecessary.

Every pure-power generator has weight precisely `R`, so
`I_j^n subset M_V(nR)`. The induced quotient arrow consequently has the
correct direction, `O/I_j^n -> O/M_V(nR)`, and is surjective. The strict
retained-weight convention in the target is relevant: the ideal contains
monomials of weight equal to `nR`.

All target quotients have finite length, so passage from polynomial local
rings to their completions does not change them. The coordinate change
then recovers the original logarithmic evaluation packet.

Finally, eventual surjectivity from degree-`n` homogeneous forms to
`H^0(X,L^n)` follows from Serre vanishing for the projective ideal sheaf.
This is eventual and does not assert projective normality in small
degrees. Restriction of these homogeneous forms has weighted degree at
most `nR`. Their jet images are therefore contained in the image of the
stated source `P_W(nR)`, proving the asserted surjectivity.

## 5. Exposition improvements and formalization boundary

The following additions would make the proof easier to independently
check, without changing the mathematical argument:

1. Spell out that finite Čech-complex localization works at all `g in R`.
2. Spell out the twisted Rees algebra
   `direct sum I^n tensor L^{bn}` in the Rees-immersion paragraph.
3. State once that curve intersection degrees are computed on the
   normalization and that the noncontracted map has degree one.

For Lean, the floor-sum monomial membership criterion, the exclusion of
the full negative-index set for `n >= 0`, signed-complex contraction, and
identity (7.3) are separable elementary targets. A faithful Lean proof of
the entire passage in Sections 6–8 additionally requires a substantial
algebraic-geometry library for blowups, sheaf cohomology, Serre vanishing,
intersection degrees, and nef-plus-ample. Declaring those substantive
geometric conclusions as axioms would produce a conditional
formalization, not a machine verification of Theorem A.
