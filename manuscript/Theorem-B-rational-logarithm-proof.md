# Arithmetic and analytic transfer for rational logarithms

7 October 2026. This manuscript gives the full written implication from Theorem A to the rational-logarithm conclusion. The paired geometric manuscript supplies A's revised proof. The combined important conclusion has not been externally confirmed or formally verified; numerical checks are not premises of either proof.

## Exact dependency

Use Theorem A in the paired manuscript `Theorem-A-revised-proof.md`: separated-weight logarithmic jet interpolation at centers with distinct nonzero Y-coordinates. The argument below reproduces the arithmetic, analytic, and parameter steps needed for a rational logarithm. It is independent of the statement mu(pi)=2.

The model for the argument is Sections 3 and 4 of OpenAI, *The irrationality exponent of pi is 2*, fixed commit adc7f1241b42e322a6451854ab7e4b4c146bf78a:

https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf

## Conditional theorem B

Assuming Theorem A, for every positive rational r != 1 and every real nu>2 there is Q(r,nu) such that

    |log r - p/q| > q^(-nu) for every integer p and every integer q >= Q(r,nu).

Consequently, assuming A, log r is irrational and mu(log r)=2.

The condition r>0 and r!=1 is essential to the stated real-number conclusion. Replacing r by 1/r replaces log r by its negative, preserving its rational approximation exponent; it suffices to take r=a/b>1, with positive coprime integers a,b. Put omega=log r>0.

### 1. Hypothetical approximants and matrix

Fix nu>2. Suppose arbitrarily large q admit p with |omega-p/q|<=q^(-nu). We will choose m such pairs (p_i,q_i) successively, with

    w_i=ceil(log q_i),    r_i=p_i/q_i,    w_*=min_i w_i.

Only unboundedness of the hypothetical denominator set is required, not positive density or a growth-ratio bound. At each stage all previous choices are fixed and the next one must exceed a finite threshold.

Choose the parameters m,K,w0,v0,theta below and satisfy Theorem A's separated thresholds. Centers are

    y_j=r^j,      c_ji=j r_i,       0<=j<K.

They have distinct nonzero y_j irrespective of the approximants. Choose F0>2/theta and let

    T_i=ceil(F0 w_i/v0),
    G_i(t)=sum_{1<=k<T_i} (-1)^(k+1)t^k/k.

The omitted terms have V-weight at least v0 T_i>=F0 w_i>w_i/theta, so the substitution replacing log(1+t) by G_i(t) induces an invertible map on every weighted jet quotient.

Use columns P=Y^h X^alpha with w0 h+w alpha<=H, and rows (j,s,beta) with v0 s+w beta/theta<H. The entry is

    [t^s u^beta] P(r^j(1+t), j r_1+G_1(t)+u_1,...,j r_m+G_m(t)+u_m).       (1)

By A, for every sufficiently large suitable H there is a nonzero square minor Delta_H using every row. Let its size be M and write

    bbar=(sum_rows w beta)/(M H),      0<=bbar<=theta.

Simplex counting with all parameters fixed gives

    M ~ K theta^m H^(m+1) / ((m+1)! v0 product_i w_i).                    (2)

The selected columns may vary with H; the bounds below are uniform over every possible selection.

### 2. Arithmetic lower bound, including rational-base height

Let L_i=lcm(1,...,T_i-1), with empty value 1, and D_H=product_i L_i^floor(H/w_i). Scale column Y^h X^alpha by

    b^((K-1)h) product_i q_i^alpha_i,

and row (j,s,beta) by product_i q_i^(-beta_i). A scaled entry is zero unless alpha>=beta; otherwise it is

    a^(jh) b^((K-1-j)h) product_i binom(alpha_i,beta_i)
        * [t^s] (1+t)^h product_i [q_i(jr_i+G_i(t))]^(alpha_i-beta_i).

All prefactors are integers. Its denominator divides product_i L_i^(alpha_i-beta_i), which divides D_H. Thus multiplying every entry by D_H yields an integer matrix with nonzero determinant, whose absolute value is at least one. Therefore

    log|Delta_H| >= -M log D_H
                    -sum_columns ((K-1)h log b + sum_i alpha_i log q_i)
                    +sum_rows sum_i beta_i log q_i.

Since sum alpha_i log q_i<=H, h<=H/w0, and log q_i>=w_i-1, we get

    log|Delta_H|/(MH) >= -(1-bbar)-E_ar,                              (3)

where, with Lambda=4 log 2,

    E_ar = Lambda F0 m/v0 + Lambda sum_i 1/w_i + theta/w_*
            + (K-1)log b/w0.                                        (4)

Here log lcm(1,...,n)<=Lambda n follows by bounding each dyadic prime-power increment by the logarithm of a central binomial coefficient.

For r=2, b=1 and the last term is zero. This does not discard the growth of 2^(jh): its numerator growth appears in the analytic estimate through e^(hz). For a/b the denominator height has been included explicitly. No product-formula estimate for a number field is being silently invoked; the matrix is over Q and the cleared determinant is in Z.

### 3. Exact row translation and approximation-error saving

For each a in N^m define the row-vector-valued entire function

    f_{a,P}(z)=[u^a]P(e^z,z+u_1,...,z+u_m).

For P=Y^h X^alpha this is binom(alpha,a)e^(hz)z^(|alpha|-|a|) if a<=alpha and zero otherwise. Put

    epsilon_i=j(r_i-omega),    tau_i(t)=G_i(t)-log(1+t),
    z=j omega+log(1+t).

Then e^z=r^j(1+t), so (1) has the exact finite row-vector expansion

    sum_{a>=beta, wa<=H} binom(a,beta)
      sum_{0<=d<=a-beta} binom(a-beta,d) epsilon^(a-beta-d)
      sum_{k=0}^s ([t^k] product_i tau_i(t)^d_i)
           * ([t^(s-k)] f_{a,P}(j omega+log(1+t)))_P.                  (5)

The scalar coefficients are independent of the column, allowing determinant multilinearity. A nonzero tail coefficient requires sum_i d_i T_i<=s and hence w d<=H/F0. On |t|=1/2 each |tau_i(t)|<=1, so Cauchy gives the coefficient bound 2^k<=2^s. Also

    |epsilon_i|<=K q_i^(-nu)<=2K exp(nu) exp(-nu w_i),

and the binomial product is at most 4^|a|. Thus each scalar xi indexed by a has

    |xi|<=exp(-nu w(a-beta)+H E_tr),
    E_tr=nu/F0 + log2/v0 + (log4+log(2K)+nu)/w_*.                    (6)

The number of terms per original row is at most

    Q_H=(floor H+1)^(2m)(floor(H/v0)+1),

once all w_i>=1, which is imposed during their choice.

### 4. Collision saving and all base-coordinate growth

Choose a fixed real R0>4(omega+1), with R0>=4, and set R=R0 K. On |z|<=R,

    |f_{a,P}(z)|<=exp(H (R/w0+log(2R)/w_*) )=:D_H'.                 (7)

The R/w0 term includes all growth from the rational base powers r^(jh). Expand f_{a,P}(z)=sum_{d>=0} c_{a,d,P}(z/R)^d. Cauchy gives |c_{a,d,P}|<=D_H'. At the test centers and on |t|=1/2,

    |j omega+log(1+t)|<=K(omega+1)<R/2.

Thus a test of order ell applied to (z/R)^d has modulus at most 2^ell 2^(-d).

Select one test row from each expansion (5), discard its scalar, and call the resulting matrix T. Let n_a be the number of rows with transverse index a. In the Taylor-expanded determinant, any term with two rows having the same pair (a,d) vanishes, because their coefficient vectors are identical. Therefore every nonzero term has sum d>=sum_a binom(n_a,2). Split the geometric decay in half: use one half to force that lower bound and sum the other half freely. The coefficient determinants are bounded by M! (D_H')^M. Consequently, with c=log2/4,

    |det T|<=exp(-c sum_a n_a^2 + MH(E_hol+rho_H)),
    E_hol=R0 K/w0+log2/v0+log(2R0 K)/w_*,                          (8)

where rho_H->0 uniformly over the row choices and selected columns. For example the terms log(M!)/(MH), O(M)/(MH), and log(1-2^(-1/2))^(-1)/H all tend to zero by (2). Absolute convergence follows directly from the geometric bounds before using any cancellation.

### 5. Two alternatives and contradiction inequalities

Fix 0<A<1 and 0<eta<1. Define

    g=nu(A(1-eta)-theta)-(1-theta),
    L=eta^2 K theta^m / ((m+1)v0 A^m),
    E=E_ar+E_tr+E_hol.

If at least eta M rows in a term have wa<=AH, there are asymptotically (AH)^m/(m! product wi) possible such indices. Cauchy-Schwarz gives sum n_a^2>=MH(L+o(1)), while the scalar main exponent -nu sum w(a-beta) is nonpositive.

If fewer than eta M rows have wa<=AH, then sum_rows wa>MH A(1-eta), so the scalar main exponent is at most -nu MH(A(1-eta)-bbar); discard the nonpositive collision term.

Summing at most Q_H^M terms gives

    log|Delta_H|/(MH)
      <= E_tr+E_hol+o(1)+max(-cL,-nu(A(1-eta)-bbar)).               (9)

In the second alternative,

    nu(A(1-eta)-bbar)-(1-bbar)
        =nu A(1-eta)-1-(nu-1)bbar >=g.

Thus (3) and (9) contradict each other if

    g>0,       E<g,       cL>1+E.                                 (10)

### 6. Noncircular parameter selection

Given nu>2, choose rational d with 1/2<d<1-1/nu. For sufficiently small rational delta>0 set theta=1-delta, A=1-d delta. Then

    nu(A-theta)>1-theta,      A^2<theta,      theta<A<1.

Choose rational C with A/theta<C<1/A, and rational B with

    A<B<min(1/C,C theta).

Choose eta>0 small enough that g>0. Put epsilon0=min(g/2,1/2), and choose F0>2/theta with nu/F0<epsilon0/3.

For each prospective m define

    K=floor(C^m),    w0=B^(-m),    v0=2K theta^m w0.

Theorem A's volume condition equals 1/2. Moreover,

    K/w0<= (CB)^m ->0,
    v0~2(C theta/B)^m ->infinity,        m/v0->0,
    L=eta^2(B/A)^m/(2(m+1))->infinity.

Fix a sufficiently large finite m that cL>2 and

    (Lambda F0 m+2log2)/v0 + (R0 K+(K-1)log b)/w0 <epsilon0/3.

All these choices depend only on r,nu and fixed auxiliary parameters, not on the approximation denominators.

Next choose approximants successively so large that their w_i meet A's successive geometric thresholds, w_i>=1, and

    Lambda sum_i 1/w_i
     +(theta+log4+log(2K)+nu+log(2R0 K))/w_* <epsilon0/3.

This is possible by the assumed unbounded denominator set: first enforce a common lower threshold using sum_i 1/w_i<=m/w_*, then enforce successive separation. No previously chosen denominator is changed, and A's thresholds are independent of the centers. The center coordinates r^j are fixed already.

Combining the three error budgets yields E<epsilon0, hence (10). Only now does H tend to infinity over the divisibility class supplied by A. Contradiction excludes unbounded q with error <=q^(-nu), proving the stated eventual bound conditional on A.

Exact rational representations with arbitrarily large unreduced denominators would violate that bound, so omega is irrational under the same assumption. Dirichlet's pigeonhole theorem supplies the usual lower exponent 2. Thus mu(omega)=2, conditional on A. QED.

## Falsification checks and limitations

- This cannot prove mu(xi)=2 for an arbitrary real xi: for generic xi, exp(j xi) is not rational, and the integer determinant lower bound in Section 2 disappears completely.
- The case r=1 is excluded: all y_j coincide and the input interpolation theorem fails to apply; log1=0 also has exact rational approximations.
- The argument gives no effective threshold Q(r,nu), because no effective numerical bound for the geometric interpolation threshold in terms of the fixed data is supplied.
- No claim of bounded partial quotients, a uniform c/q^2 lower bound, or an effective numerical bound is made.
- Algebraic nonrational r is not covered. Additional embeddings and arithmetic height losses must be analyzed separately; the rational proof must not be silently extended by replacing Z with algebraic integers.
- The novelty search identified Marcovecchio's 2009 bound for log2 and a 2026 primary-source statement that its exact exponent remains unknown. This is evidence of significance if the proof is validated, not proof of novelty or correctness.

## Current primary sources for context

1. R. Marcovecchio, *The Rhin-Viola method for log 2*, Acta Arithmetica 139 (2009), 147–184, DOI 10.4064/aa139-2-5. Author/institution record: https://ricerca.unich.it/handle/11564/648605?mode=complete
2. Y. Bugeaud and D. H. Kim, *On the b-ary expansion of a real number whose irrationality exponent is close to 2*, arXiv:2510.02059v2 (20 April 2026), introduction says the exponent of log2 remains unknown: https://arxiv.org/abs/2510.02059
3. W. Zudilin, *An essay on irrationality measures of pi and other logarithms*: https://wain.mi-ras.ru/PS/pi.pdf

The article dates above were checked in the primary text or publication record, rather than using search-engine crawl dates.
