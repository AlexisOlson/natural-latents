# The affinity bound

This page proves that two distinct positive contacts of a common feasible kernel are separated in both marginals: each
marginal Bhattacharyya affinity is at most the quadratic $`b(s)`$, so that $`-\ln BC_X-\ln BC_Y\ge\Psi(s)`$, with the
separation $`s`$ defined below and $`b`$, $`BC_X`$, $`BC_Y`$ and $`\Psi`$ defined in (A2.1). The mismatch payment (step 6
of the [route](overview.md#the-route)) uses this for every pair of distinct components of the setup
latent: it combines this bound with the midpoint relative-entropy inequality and replica symmetry to bound the weighted
off-diagonal sum of separation prices $`\sum_{i\ne j}\mu_{ij}\Psi(s_{ij})`$ (with the pair masses $`\mu_{ij}`$ of
Lemma P5.1 and the separations $`s_{ij}`$ of Lemma P5.3 on the [payment page](payment.md)) by the replica budget $`K`$; the pair charge
then compares this sum with the mismatch $`d`$. In the assembly `NaturalLatents.General.T_le_of_connected`
(`NaturalLatents/General/Pricing.lean`), the affinity hypothesis of `mismatch_payment` is discharged by
`affinity_bound` applied to the conclusion of `contact_moments`.

## 2. The affinity bound

Units and conventions are those of section 0 of the [contact page](contact.md): logarithms are natural. Fix finite
nonempty alphabets $`X,Y`$, a nonempty common support $`S\subseteq X\times Y`$ with all rows and columns used, a feasible
kernel $`w>0`$ on $`S`$ as in (C1.1), and two positive contacts $`P,R`$ of $`w`$ as in (C1.2). The fields of (C1.3) are the
cube-root marginal ratios $`f=(R_X\text/P_X)^{1\text/3}`$ and $`g=(R_Y\text/P_Y)^{1\text/3}`$, their shifts $`U=f-1`$
and $`V=g-1`$, the mean losses $`A_0=1-E_Pf`$ and $`B_0=1-E_Pg`$, the separation $`s=A_0+B_0`$, and the quartic moment
$`J=E_P[U^2V^2]`$; all expectations are under $`P`$. For contacts as in section 1 define

```math
\begin{aligned}
BC_X(P,R)&=\sum_x\sqrt{P_X(x)R_X(x)},&
BC_Y(P,R)&=\sum_y\sqrt{P_Y(y)R_Y(y)},\\
b(t)&=1-\frac{9t}{16}+\frac{3t^2}{64},&
\Psi(t)&=-2\ln b(t).
\end{aligned}
\qquad \text{(A2.1)}
```

The formula for $`\Psi(t)`$ is used only where $`b(t)>0`$. This section uses the identities and the quartic estimate of
section 1 (Lemmas C1.1, C1.2 and C1.5 of the [contact page](contact.md)); it establishes no further contact or Hessian
argument. The letters $`P,R`$, $`f,g,U,V,A_0,B_0,s,J`$ are those of the contact page; $`h_X,h_Y`$ below are Hellinger
distances, not the seed entropy $`h`$, and $`y=\sqrt f`$ is a local variable.

Lean: `affinityPoly` ($`b`$), `separationPrice` ($`\Psi`$) and `AffinityBound` (`NaturalLatents/General/Definitions.lean`),
all `NaturalLatents.General.*`; $`BC_X`$ and $`BC_Y`$ are `stoch_to_det.BC` (`NaturalLatents/Upstream/Toolkit.lean`)
applied to the $`X`$ and $`Y`$ marginals. `separationPrice` is defined for every real $`t`$ through Lean's totalized
logarithm, and agrees with (A2.1) where $`b(t)>0`$.

**Lemma A2.1 (each marginal affinity is at most the quadratic $`b`$ at $`s`$).** For every finite nonempty $`X,Y`$, every nonempty
common support $`S`$ with all rows and columns used, every feasible $`w>0`$ on $`S`$, and every pair of distinct positive
contacts $`P,R`$, assume the conclusions (C1.4), (C1.9), $`0<s<2`$, and (C1.23) of section 1. Then the affinities defined in
(A2.1) satisfy

```math
0<BC_X(P,R)\leq b(s),\qquad 0<BC_Y(P,R)\leq b(s).
\qquad \text{(A2.2)}
```

*Proof.* Define the squared marginal Hellinger distances

```math
\begin{aligned}
h_X^2
&=\sum_x\left(\sqrt{P_X(x)}-\sqrt{R_X(x)}\right)^2
=E_P(f^{3\text/2}-1)^2,\\
h_Y^2
&=\sum_y\left(\sqrt{P_Y(y)}-\sqrt{R_Y(y)}\right)^2
=E_P(g^{3\text/2}-1)^2.
\end{aligned}
\qquad \text{(A2.3)}
```

The moments of section 1 give

```math
\begin{aligned}
E_P[(f-1)^2(f+1)]
&=E_P[f^3-f^2-f+1]=1-E_Pg-E_Pf+1=s,\\
E_P[(g-1)^2(g+1)]
&=E_P[g^3-g^2-g+1]=1-E_Pf-E_Pg+1=s.
\end{aligned}
\qquad \text{(A2.4)}
```

For every $`f>0`$, put $`y=\sqrt f>0`$. The factorization and its bound are

```math
\begin{aligned}
\frac98(f-1)^2(f+1)-(f^{3\text/2}-1)^2
&=\frac98(y^6-y^4-y^2+1)-(y^6-2y^3+1)\\
&=\frac{y^6-9y^4+16y^3-9y^2+1}{8}
=\frac{(y-1)^4(y^2+4y+1)}8,\\
\frac32(y+1)^2-(y^2+4y+1)
&=\frac12(y-1)^2\geq0,\\
\frac{(y-1)^4(y^2+4y+1)}8
&\leq\frac3{16}(y-1)^4(y+1)^2
=\frac3{16}(f-1)^2(\sqrt f-1)^2.
\end{aligned}
\qquad \text{(A2.5)}
```

For every used row $`x`$, conditional Cauchy-Schwarz for the probability weights $`P(x,y)\text/P_X(x)`$ gives

```math
\begin{aligned}
(E_P[g\mid X=x])^2
&\leq E_P[g^2\mid X=x]=f(x),\\
E_P[V^2\mid X=x]
&=E_P[g^2\mid X=x]-2E_P[g\mid X=x]+1\\
&=f(x)-2E_P[g\mid X=x]+1
\geq f(x)-2\sqrt{f(x)}+1=(\sqrt{f(x)}-1)^2.
\end{aligned}
\qquad \text{(A2.6)}
```

Multiply the last inequality by $`U(x)^2\geq0`$ and average:

```math
E_P[U^2(\sqrt f-1)^2]
\leq E_P[U^2E_P[V^2\mid X]]
=E_P[U^2V^2]=J.
\qquad \text{(A2.7)}
```

Average (A2.5), use (A2.4), and then use the quartic bound (C1.23):

```math
\begin{aligned}
h_X^2
&\geq\frac98E_P[(f-1)^2(f+1)]
 -\frac3{16}E_P[U^2(\sqrt f-1)^2]\\
&\geq\frac{9s}{8}-\frac{3J}{16}
\geq\frac{9s}{8}-\frac{3s^2}{32}.
\end{aligned}
\qquad \text{(A2.8)}
```

For the other coordinate, conditional Cauchy-Schwarz and the other conditional moment of section 1 give

```math
\begin{aligned}
E_P[f\mid Y]&\leq\sqrt{E_P[f^2\mid Y]}=\sqrt g,\\
E_P[U^2\mid Y]
&=g-2E_P[f\mid Y]+1\geq(\sqrt g-1)^2,\\
E_P[V^2(\sqrt g-1)^2]
&\leq E_P[V^2E_P[U^2\mid Y]]=J,\\
h_Y^2
&\geq\frac98E_P[(g-1)^2(g+1)]
 -\frac3{16}E_P[V^2(\sqrt g-1)^2]\\
&\geq\frac{9s}{8}-\frac{3J}{16}
\geq\frac{9s}{8}-\frac{3s^2}{32}.
\end{aligned}
\qquad \text{(A2.9)}
```

Finally expand the Hellinger sums using normalization of both marginal laws:

```math
\begin{aligned}
h_X^2
&=\sum_xP_X(x)+\sum_xR_X(x)-2\sum_x\sqrt{P_X(x)R_X(x)}
=2-2BC_X(P,R),\\
h_Y^2
&=\sum_yP_Y(y)+\sum_yR_Y(y)-2\sum_y\sqrt{P_Y(y)R_Y(y)}
=2-2BC_Y(P,R),\\
BC_X(P,R),\,BC_Y(P,R)
&\leq1-\frac12\left(\frac{9s}{8}-\frac{3s^2}{32}\right)
=1-\frac{9s}{16}+\frac{3s^2}{64}=b(s).
\end{aligned}
\qquad \text{(A2.10)}
```

Every term in each affinity sum is positive on a used symbol, so both affinities are strictly positive. The analytic
input is conditional Cauchy-Schwarz; the rest is the moment list of section 1 and polynomial algebra. $`\square`$

Lean: `NaturalLatents.General.affinity_bhattacharyyaX_le` and `NaturalLatents.General.affinity_bhattacharyyaY_le` (the upper bounds) and
`NaturalLatents.General.affinity_affinities_pos` (positivity), in `NaturalLatents/General/Affinity.lean`. They take
`CommonSupportPair S w P R` and, for the upper bounds, `ContactMoments S P R`, the conclusions of section 1 as stated in
Lean. In place of a named Cauchy-Schwarz theorem, `affinity_conditional_square` (same file) derives the conditional
comparison of (A2.6) and (A2.9) by expanding a nonnegative weighted square.

**Lemma A2.2 (the natural-log affinity payment and the equal-pair endpoint).** For every finite nonempty $`X,Y`$, every
nonempty common support $`S`$ with all rows and columns used, every feasible $`w>0`$ on $`S`$, and every pair of distinct
positive contacts $`P,R`$, assume the conclusions of section 1 and of Lemma A2.1. Then $`\Psi(s)`$ is well defined and
nonnegative, and

```math
-\ln BC_X(P,R)-\ln BC_Y(P,R)\geq\Psi(s).
\qquad \text{(A2.11)}
```

Distinct pairs and equal pairs are treated separately. For every equal pair $`P=R`$ on the same contact domain, (C1.3)
gives $`s=0`$, so marginal normalization gives $`BC_X=BC_Y=b(0)=1`$ and $`\Psi(0)=0`$, with equality in (A2.11).

*Proof.* For every $`t\in[0,2]`$,

```math
b'(t)=-\frac9{16}+\frac{3t}{32}<0,\qquad
b(0)=1,\qquad b(2)=1-\frac{18}{16}+\frac{12}{64}=\frac1{16}.
\qquad \text{(A2.12)}
```

Thus $`1\text/16\leq b(t)\leq1`$ on this whole scalar interval. In particular $`0<b(s)\leq1`$, so $`-2\ln b(s)`$ is well
defined and nonnegative. Lemma A2.1 supplies positive affinities; monotonicity of the natural logarithm therefore gives

```math
\begin{aligned}
\ln BC_X(P,R)&\leq\ln b(s),\\
\ln BC_Y(P,R)&\leq\ln b(s),\\
\ln BC_X(P,R)+\ln BC_Y(P,R)&\leq2\ln b(s),\\
-\ln BC_X(P,R)-\ln BC_Y(P,R)&\geq-2\ln b(s)=\Psi(s).
\end{aligned}
\qquad \text{(A2.13)}
```

For equal contacts, $`f=g=1`$, so (A2.1) and marginal normalization give $`BC_X=BC_Y=1`$, $`s=0`$, $`b(0)=1`$ and
$`\Psi(0)=0`$. The scalar endpoint $`t=2`$ is used only to bound $`b`$; it cannot occur for two positive contacts because
section 1 gives $`s<2`$. The analytic facts are the derivative criterion for monotonicity and monotonicity of $`\ln`$ on
$`(0,\infty)`$. This proves the affinity bound. $`\square`$

Lean: `NaturalLatents.General.affinity_bound` (`NaturalLatents/General/Affinity.lean`) proves `AffinityBound P R`, which
is (A2.11), for every `CommonSupportPair S w P R` given `ContactMoments S P R`. It obtains $`b(s)>0`$ from
`NaturalLatents.General.affinityPoly_pos` (`NaturalLatents/General/Definitions.lean`, positivity of $`b(t)`$ for $`t\le2`$), and does
not state the range $`1\text/16\le b\le1`$, the nonnegativity of $`\Psi(s)`$, or the case of equal contacts.
