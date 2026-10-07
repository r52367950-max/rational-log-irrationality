"""Exact finite falsification checks; these are NOT proofs of Theorems A/B."""
import itertools
import json
import math
from pathlib import Path
import sympy as sp

t, omega = sp.symbols('t omega')
max_order = 4
log = sum(sp.Rational((-1) ** (k + 1), k) * t**k for k in range(1, max_order + 1))
base = sp.Rational(3, 2)
ri = (sp.Rational(2, 5), sp.Rational(3, 7))
T = (2, 3)
G = [sum(sp.Rational((-1) ** (k + 1), k) * t**k for k in range(1, q)) for q in T]

def truncated(p):
    return sp.Poly(sp.expand(p), t)

translations = 0
cleared_entries = 0
for j, h, alpha in itertools.product(range(3), range(3), itertools.product(range(3), repeat=2)):
    for beta in itertools.product(*(range(a + 1) for a in alpha)):
        direct = base**(j*h) * (1+t)**h
        for i in range(2):
            direct *= sp.binomial(alpha[i], beta[i]) * (j*ri[i]+G[i])**(alpha[i]-beta[i])
        expanded = sp.S.Zero
        for a in itertools.product(*(range(beta[i], alpha[i]+1) for i in range(2))):
            f = base**(j*h) * (1+t)**h * (j*omega+log)**(sum(alpha)-sum(a))
            f *= math.prod(sp.binomial(alpha[i], a[i]) for i in range(2))
            for d in itertools.product(*(range(a[i]-beta[i]+1) for i in range(2))):
                scalar = sp.S.One
                for i in range(2):
                    scalar *= sp.binomial(a[i], beta[i]) * sp.binomial(a[i]-beta[i], d[i])
                    scalar *= (j*(ri[i]-omega))**(a[i]-beta[i]-d[i]) * (G[i]-log)**d[i]
                expanded += scalar * f
        # Logarithms were truncated beyond the tested coefficients, legitimately.
        diff = truncated(direct-expanded)
        for s in range(max_order+1):
            assert sp.expand(diff.nth(s)) == 0
            translations += 1
        # K=3, b=2. The column and row q scaling is as in B §2.
        scale = 2**(2*h) * math.prod(int(ri[i].q)**(alpha[i]-beta[i]) for i in range(2))
        lcms = [sp.ilcm(*range(1, q)) if q>2 else 1 for q in T]
        denom_bound = math.prod(int(lcms[i])**(alpha[i]-beta[i]) for i in range(2))
        p = truncated(direct * scale)
        for s in range(max_order+1):
            x = p.nth(s)
            assert denom_bound % int(x.q) == 0
            cleared_entries += 1

# Exact check of lower-degree collision bound, independently of the analytic estimates.
collision_groups = 0
for n in range(7):
    for ds in itertools.combinations(range(10), n):
        assert sum(ds) >= n*(n-1)//2
        collision_groups += 1

# Exact B margin / A ample-plus-nef identities, all variables symbolic.
nu,A,eta,theta,bbar = sp.symbols('nu A eta theta bbar')
g = nu*(A*(1-eta)-theta) - (1-theta)
assert sp.expand(nu*(A*(1-eta)-bbar)-(1-bbar)-g-(nu-1)*(theta-bbar)) == 0
a,sigma = sp.symbols('a sigma')
den = a*(1+sigma)-1
assert sp.cancel((a-1)/den + sigma*a/den) == 1
assert sp.cancel((a-1)*(1+sigma)/den + sigma/den) == 1

result = {'status':'all exact finite checks passed', 'translation_coefficients':translations,
          'denominator_entries':cleared_entries,'distinct_degree_groups':collision_groups,
          'identities':3, 'scope':'finite falsification checks, not a proof of A or B'}
Path(__file__).with_name('exact_checks.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(result,ensure_ascii=False))
