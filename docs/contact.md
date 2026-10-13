# Contact moments and the feasible Hessian

This page fixes the units and notation shared by the proof pages, and proves the moment relations of two positive
contacts of one feasible kernel: the ratio and conditional-moment identities, the quadratic and quartic moment
identities, the separation range $`0<s<2`$ for distinct contacts and $`s=J=0`$ for equal contacts, a feasibility
inequality for nonnegative marginal fields, the Hessian test for centered marginal fields, and the quartic bound
$`J\le6A_0B_0-s^2\le s^2\text/2`$, with $`s`$, $`J`$, $`A_0`$ and $`B_0`$ defined in (C1.3). These relations are the
input of the [affinity bound](affinity.md), which the mismatch payment applies to every pair of distinct components of
the setup latent (step 6 of the [route](overview.md#the-route)); Lemma C1.3 and the Hessian test are
also used by the pair charge. In the assembly `NaturalLatents.General.T_le_of_connected`
(`NaturalLatents/General/Pricing.lean`), `contact_moments` is applied to each pair of distinct components of the setup
latent, and its conclusion is passed to `affinity_bound`.

Each lemma below states its quantified hypotheses, so that it can be read alone. Lemma, theorem, remark and equation
numbers carry the prefix of the page that states them: S for the [setup](setup.md), C for this page, L for the
[ledger](ledger.md), R for the [race](race.md), K for the [cap](cap.md), A for the [affinity bound](affinity.md), Q for
the [replica budget](replica.md), P for the [payment](payment.md), PC for the [pair charge](pair-charge.md), M for the
[assembly](assembly.md), E for the [extension](extension.md) and T for the [table form](table-form.md); the tags (D1) to
(D3) of section 0 serve every page. Unless explicitly
qualified otherwise, the Lean declarations named below are in the namespace `NaturalLatents.General`; declarations
prefixed `stoch_to_det` are upstream, in `NaturalLatents/Upstream/`, adapted from
[DLorell/stoch_to_det](https://github.com/DLorell/stoch_to_det).

## 0. Units, notation and standing inputs

**Units.** All entropies, mutual informations and relative entropies in the proof pages are in nats. The deterministic
optimum $`T`$ and the stochastic optimum $`\tau`$ scale by the same factor under a change of units, so the final
inequality $`T(p)\le(13999\text/2000)\,\tau(p)`$ is unit-free. A quantity stated in bits is converted once:

```math
H_{\mathrm{nat}}=(\ln2)H_{\mathrm{bits}},\quad I_{\mathrm{nat}}=(\ln2)I_{\mathrm{bits}},
\qquad (M,B,T,\tau,h)_{\mathrm{nat}}=(\ln2)(M,B,T,\tau,h)_{\mathrm{bits}}.
\qquad \text{(D1)}
```

Hereafter $`H,I,M,B,T,\tau,h`$ are in nats. The relative entropy and the pair charge are natural-log quantities and are
unchanged. Probabilities and $`d,s,J,BC,\beta`$ are dimensionless, whereas $`\Psi`$ and $`\gamma`$ have nat units. There
is no final division by $`\ln 2`$ in the mismatch conclusion. Here $`M`$, $`B`$, $`T`$, $`\tau`$ and $`d`$ are defined
in (D3) and $`s`$, $`J`$ in (C1.3); $`BC`$ denotes either marginal affinity, $`BC_X`$ or $`BC_Y`$, and these and
$`\Psi`$ are defined in (A2.1) on the [affinity page](affinity.md); $`h`$ is the seed average of the two fixed-map
conditional entropies $`H(f(Z)\mid X)+H(f(Z)\mid Y)`$, defined in (L1) and (L7) on the [ledger page](ledger.md); and
$`\beta`$, $`\gamma`$ are the parameters of the pair charge below.

Lean: `NaturalLatents.General.TNat` and `NaturalLatents.General.tauNat` (`NaturalLatents/General/Definitions.lean`) are the
bit-valued `stoch_to_det.T` and `stoch_to_det.tau` (`NaturalLatents/Upstream/Functionals.lean`) converted by
`NaturalLatents.General.nats`, multiplication by `Real.log 2` (`NaturalLatents/General/Nats.lean`, the only General file
where that factor appears); `mediation`, `redundancy`, `replicaBudget` and `seedEntropy` in `Definitions.lean`, the Lean
forms of $`M`$, $`B`$, $`K`$ and $`h`$, are converted the same way. `NaturalLatents.General.bits_of_nats` (`Nats.lean`)
converts the nat-valued bound on connected supports back to the bit-valued `stoch_to_det.T` and `stoch_to_det.tau`, and
`NaturalLatents.T_le_c_mul_tau` (`NaturalLatents/Main.lean`) then extends it to every law in bits.

**Conventions.** For a finite law, all conditional sums range over positive-probability conditioning events. Entropy
uses $`0\ln0=0`$, and a relative entropy sums over the positive mass of its first argument. With the reference
positive on that support,

```math
H(q)=-\sum_{i:q_i>0}q_i\ln q_i,\qquad
D(q\Vert v)=\sum_{i:q_i>0}q_i\ln(q_i\text/v_i),\qquad
I(q)=D(q\Vert q_X\otimes q_Y).
\qquad \text{(D2)}
```

Lean: the mutual information $`I(q)`$ of a law on $`X\times Y`$ is the natural-log `stoch_to_det.Knat`
(`NaturalLatents/Upstream/DomFloorCore.lean`), used directly, with no conversion. `Knat` is an equivalent all-cell scalar-integrand formula rather than
the positive-support sum (D2); on probability laws, `stoch_to_det.Knat_eq_log_two_mul_Ixy` (same file) identifies it
with natural-log mutual information.

**Latents and scores.** A finite latent is a joint law of $`Z=(X,Y)`$ and a finite label $`L`$, or equivalently a
mixture $`p=\sum_i\pi_iq_i`$, with $`r_z(i)=\Pr(L=i\mid Z=z)`$ on $`\mathrm{supp}\,p`$. Set

```math
\begin{aligned}
M&=I(X;Y\mid L),&B&=I(L;X\mid Y)+I(L;Y\mid X),\\
\tau(p)&=\inf_L(M+B),&
T(p)&=\min_{A=f(Z)}[I(X;Y\mid A)+H(A\mid X)+H(A\mid Y)],\\
d&=\sum_{z:p(z)>0}p(z)\left[1-\sum_i r_z(i)^2\right].
\end{aligned}
\qquad \text{(D3)}
```

The deterministic minimum exists because a finite alphabet has finitely many partitions. For a deterministic map $`f`$
on $`\mathrm{supp}\,p`$, write $`D_p(f) = I(X;Y\mid f(Z)) + H(f(Z)\mid X) + H(f(Z)\mid Y)`$ for the score of the code
$`f(Z)`$, so that $`T(p)=\min_f D_p(f)`$.

Lean: a finite latent is `stoch_to_det.Latent` (`NaturalLatents/Upstream/Functionals.lean`), and `posterior` (the
posterior $`r_z(i)`$), `mediation` ($`M`$), `redundancy` ($`B`$) and `mismatch` ($`d`$) are in
`NaturalLatents/General/Definitions.lean`. `stoch_to_det.detScore` (`NaturalLatents/Upstream/Functionals.lean`) is the
score in bits of a map on all of $`X\times Y`$: the score $`D_p(f)`$ is `detScoreNat` (`NaturalLatents/General/Nats.lean`),
that is `nats` of `detScore`, after extending the map off the support. In Lean, $`T`$ is an infimum over deterministic latents
and $`d`$ sums over all cells, the cells with $`p(z)=0`$ contributing zero.

**The supplied setup.** The mismatch payment is applied to a latent $`p=\sum_i\pi_iq_i`$ with positive priors, distinct
components that are positive contacts of one feasible kernel on the common support $`\mathrm{supp}\,p`$ (contacts and
feasibility are defined in section 1), and $`M+B=\tau(p)`$. Such a latent exists when the support of $`p`$ is connected
as a bipartite graph between the values of $`X`$ and the values of $`Y`$ (defined on the
[setup page](setup.md#1-the-setup-on-a-connected-support)), and the bound for a general finite law is
reduced to that case by splitting the support into its connected components: with component weights $`\rho_k`$ and
normalized component laws $`\bar p_k`$, $`\sum_k\rho_k\tau(\bar p_k)\le\tau(p)`$ and $`T(p)\le\sum_k\rho_kT(\bar p_k)`$
((E3.F) on the [extension page](extension.md)). Neither step is proved on this page; they are proved by
`NaturalLatents.General.exists_setup_of_connected` (`NaturalLatents/General/Setup.lean`) and
`NaturalLatents.General.extension_of_connected` (`NaturalLatents/General/Extension.lean`).

Lean: the setup is the structure `NaturalLatents.General.CommonSetup` (`NaturalLatents/General/Definitions.lean`),
which also records that every posterior $`r_z(i)`$ is positive on the support; it is constructed for connected support
by `NaturalLatents.General.exists_setup_of_connected` (`NaturalLatents/General/Setup.lean`), and the extension to every
law is `NaturalLatents.General.extension_of_connected` (`NaturalLatents/General/Extension.lean`), which applies
`stoch_to_det.reduce_to_connected` (`NaturalLatents/Upstream/Connected.lean`).

**The pair charge.** The pair charge $`PC(\beta,\gamma)`$, for $`\beta\ge0`$ and $`\gamma>0`$, is the averaged
natural-logarithm inequality

```math
\frac{I(P)+I(R)}2+\beta\Psi(s(P,R))\ge\gamma
```

for every two distinct positive contacts $`P,R`$ of a common feasible kernel, on a support $`S`$ that need not be a rectangle (cells of $`X\times Y`$
outside $`S`$, the holes, are allowed); $`s`$ is defined in
(C1.3) and $`\Psi`$ in (A2.1). It is a hypothesis of the mismatch payment, generic in $`\beta\ge0`$ and $`\gamma>0`$, and
is not used on this page.

Lean: `NaturalLatents.General.HasPairCharge` (`NaturalLatents/General/Definitions.lean`), stated over a domain of pairs;
`NaturalLatents.General.pairCharge_C` (`NaturalLatents/General/PairCharge.lean`) proves it on
distinct positive contacts of a common feasible kernel at $`(\beta,\gamma)=(23\text/250,7\text/60)`$. The formal `HasPairCharge` definition accepts
arbitrary real $`\beta`$ and $`\gamma`$; the formal payment inequality `mismatch_payment`
(`NaturalLatents/General/Payment.lean`) requires $`\beta\ge0`$ and $`\gamma\ge0`$. This page keeps $`\gamma>0`$ so that
later bounds may divide by $`\gamma`$.

## 1. Contact moments and the feasible Hessian

Fix finite nonempty alphabets $`X,Y`$, a nonempty support $`S\subseteq X\times Y`$, and a kernel $`w:S\to(0,\infty)`$,
extended by zero outside $`S`$. Remove unused rows and columns, so every symbol of $`X`$ and $`Y`$ occurs in $`S`$.
Feasibility means that, for every pair of probability vectors $`u`$ on $`X`$ and $`v`$ on $`Y`$,

```math
\sum_{(x,y)\in S}w(x,y)u_x^{2\text/3}v_y^{2\text/3}\leq1.
\qquad \text{(C1.1)}
```

A positive contact is a probability law $`P`$ positive at every cell of $`S`$, zero outside $`S`$, and satisfying

```math
P(x,y)=w(x,y)P_X(x)^{2\text/3}P_Y(y)^{2\text/3}
\quad((x,y)\in S).
\qquad \text{(C1.2)}
```

Thus all used marginal probabilities are positive. Neither full rectangular support nor connectedness is assumed. For
two such contacts $`P,R`$, define

```math
\begin{aligned}
f(x)&=\left(\frac{R_X(x)}{P_X(x)}\right)^{1\text/3},
&g(y)&=\left(\frac{R_Y(y)}{P_Y(y)}\right)^{1\text/3},\\
U&=f-1,&V&=g-1,\\
A_0&=1-E_Pf,&B_0&=1-E_Pg,\\
s&=A_0+B_0=2-E_Pf-E_Pg,
&J&=E_P[U^2V^2].
\end{aligned}
\qquad \text{(C1.3)}
```

All expectations in this section are under $`P`$, including expectations of a field depending on only one coordinate.
Some letters in this section are local: $`f,g`$ are the fields (C1.3), not maps or codes; $`u,v`$ in (C1.1) are
probability vectors, not the price bound $`u`$ of the [cap page](cap.md); the fields $`A,B`$ and the normalizers $`a,b`$
of Lemma C1.3 are not the budget $`B`$, the race exponent $`a`$ or the quadratic $`b`$ of (A2.1); and $`L(t)`$, $`R(t)`$
in the proof of Lemma C1.4 are not a latent or a contact.

Lean: a pair of distinct positive contacts of one feasible kernel is `CommonSupportPair S w P R`. Feasibility (C1.1) is
`stoch_to_det.Feasible` and the contact equation (C1.2), with $`P`$ a probability law zero
outside $`S`$, is `stoch_to_det.IsContact` (`NaturalLatents/Upstream/Duality.lean`), both used directly, and positivity on $`S`$ is
`PositiveOn` (`NaturalLatents/General/Definitions.lean`). `Feasible` also
records $`w>0`$ on $`S`$. Lean does not remove unused rows and columns: `Feasible` quantifies over probability vectors
on the full alphabets, and the conditional statements are restricted to the used symbols `xSupport S` and
`ySupport S`. Lean leaves $`w`$ outside $`S`$ unrestricted, because those values never enter the conditions. On unused
marginal symbols, its totalized division gives $`f=g=0`$ and hence $`U=V=-1`$; these symbols contribute zero to every
expectation, and conditional identities are asserted only on used symbols. The fields
(C1.3) are `rootRatioX`, `rootRatioY`, `defectX`, `defectY`, `separation` and `quarticMoment`, with $`E_P`$ written
`expect P`, all in `NaturalLatents/General/Definitions.lean`, and $`U,V`$ are the upstream secants
`stoch_to_det.contactSecantX` and `stoch_to_det.contactSecantY` (`NaturalLatents/Upstream/Floor.lean`), with
`rootRatioX` defined as `contactSecantX + 1`.

**Lemma C1.1 (contact ratios and conditional moments).** For every finite nonempty $`X,Y`$, every nonempty
$`S\subseteq X\times Y`$ with all rows and columns used, every feasible kernel $`w>0`$ on $`S`$, and every pair of
positive contacts $`P,R`$ of $`w`$, the fields in (C1.3) satisfy, at every cell of $`S`$ and every used conditioning
symbol respectively,

```math
\frac RP=f^2g^2,\qquad
E_P[g^2\mid X]=f,\qquad E_P[f^2\mid Y]=g,\qquad
E_Pf^3=E_Pg^3=1,\qquad E_Pf^2=E_Pg,\quad E_Pg^2=E_Pf.
\qquad \text{(C1.4)}
```

*Proof.* Divide the two contact equations:

```math
\frac{R(x,y)}{P(x,y)}
=\left(\frac{R_X(x)}{P_X(x)}\right)^{2\text/3}
 \left(\frac{R_Y(y)}{P_Y(y)}\right)^{2\text/3}
=f(x)^2g(y)^2.
\qquad \text{(C1.5)}
```

Summing this ratio identity along a row and a column gives

```math
\begin{aligned}
E_P[g^2\mid X=x]
&=\frac{\sum_{y:(x,y)\in S}P(x,y)g(y)^2}{P_X(x)}
=\frac{R_X(x)}{P_X(x)f(x)^2}=f(x),\\
E_P[f^2\mid Y=y]
&=\frac{\sum_{x:(x,y)\in S}P(x,y)f(x)^2}{P_Y(y)}
=\frac{R_Y(y)}{P_Y(y)g(y)^2}=g(y).
\end{aligned}
\qquad \text{(C1.6)}
```

The normalizations of the marginal laws yield

```math
E_Pf^3=\sum_xP_X(x)\frac{R_X(x)}{P_X(x)}
=\sum_xR_X(x)=1,\qquad
E_Pg^3=\sum_yP_Y(y)\frac{R_Y(y)}{P_Y(y)}
=\sum_yR_Y(y)=1.
\qquad \text{(C1.7)}
```

The tower rule for conditional expectation gives both second-moment identities explicitly:

```math
\begin{aligned}
E_Pf^2
&=\sum_yP_Y(y)\sum_{x:(x,y)\in S}
       \frac{P(x,y)}{P_Y(y)}f(x)^2
=\sum_yP_Y(y)g(y)=E_Pg,\\
E_Pg^2
&=\sum_xP_X(x)\sum_{y:(x,y)\in S}
       \frac{P(x,y)}{P_X(x)}g(y)^2
=\sum_xP_X(x)f(x)=E_Pf.
\end{aligned}
\qquad \text{(C1.8)}
```

This proves all the claims. The analytic input is finite conditional expectation and its tower rule; feasibility beyond
the contact equations is not used here. $`\square`$

Lean: `contact_ratio_mul` (the ratio identity, stated as $`R=Pf^2g^2`$ at every cell), `contact_cond_rootRatioY_square`,
`contact_cond_rootRatioX_square`, `contact_rootRatioX_cube`, `contact_rootRatioY_cube`, `contact_rootRatioX_square` and `contact_rootRatioY_square`, all `NaturalLatents.General.*` in
`NaturalLatents/General/Contact.lean`. Their hypothesis is `CommonSupportPair S w P R`, which includes feasibility and
$`P\ne R`$. The proof above uses neither feasibility nor distinctness; the stated lemma retains feasibility to match the
common contact domain.

**Lemma C1.2 (separation and the quartic moment list).** For every finite nonempty $`X,Y`$, every nonempty common
support $`S`$ with all rows and columns used, every feasible $`w>0`$ on $`S`$, and every pair of positive contacts
$`P,R`$, the quantities in (C1.3) satisfy

```math
A_0,B_0\geq0,\qquad
E_PU^2=2A_0-B_0,\qquad E_PV^2=2B_0-A_0,\qquad
J=4E_P[UV]-s,\qquad s(P,R)=s(R,P).
\qquad \text{(C1.9)}
```

If $`P\ne R`$, then $`0<s<2`$. If $`P=R`$, then $`f=g=1`$ and $`s=J=0`$.

*Proof.* Jensen's inequality for the strictly convex function $`t\mapsto t^3`$ on $`(0,\infty)`$, together with (C1.7),
gives

```math
(E_Pf)^3\leq E_Pf^3=1,\qquad
(E_Pg)^3\leq E_Pg^3=1.
\qquad \text{(C1.10)}
```

Hence $`A_0,B_0\geq0`$. If $`E_Pf=1`$, equality in strict Jensen forces $`f=1`$ on all used rows: it makes $`f\equiv c`$ on the used rows, and then
$`c^3=E_Pf^3=1`$, so $`c=1`$. Then
$`g=E_P[f^2\mid Y]=1`$, and (C1.5) forces $`R=P`$. If $`E_Pg=1`$, the same argument with the coordinates exchanged gives
$`R=P`$. Thus distinct contacts have $`A_0,B_0>0`$, so $`s>0`$; positivity of $`f,g`$ gives $`E_Pf+E_Pg>0`$, so
$`s<2`$. For equal contacts every ratio is one, giving the stated zero case.

Expand the two squares and use (C1.8):

```math
\begin{aligned}
E_PU^2
&=E_Pf^2-2E_Pf+1
=(1-B_0)-2(1-A_0)+1=2A_0-B_0,\\
E_PV^2
&=E_Pg^2-2E_Pg+1
=(1-A_0)-2(1-B_0)+1=2B_0-A_0.
\end{aligned}
\qquad \text{(C1.11)}
```

The conditional identities and the ratio normalization give

```math
\begin{aligned}
E_P[f^2g]
&=\sum_yP_Y(y)g(y)E_P[f^2\mid Y=y]
=E_Pg^2=E_Pf,\\
E_P[fg^2]
&=\sum_xP_X(x)f(x)E_P[g^2\mid X=x]
=E_Pf^2=E_Pg,\\
E_P[f^2g^2]&=\sum_{(x,y)\in S}R(x,y)=1.
\end{aligned}
\qquad \text{(C1.12)}
```

The complete product expansion is

```math
\begin{aligned}
J
&=E_P[(f^2-2f+1)(g^2-2g+1)]\\
&=E_P[f^2g^2]-2E_P[f^2g]-2E_P[fg^2]
 +E_Pf^2+E_Pg^2+4E_P[fg]-2E_Pf-2E_Pg+1\\
&=1-2E_Pf-2E_Pg+E_Pg+E_Pf+4E_P[fg]-2E_Pf-2E_Pg+1\\
&=2-3(E_Pf+E_Pg)+4E_P[fg]\\
&=4(E_P[fg]-E_Pf-E_Pg+1)-(2-E_Pf-E_Pg)
=4E_P[UV]-s.
\end{aligned}
\qquad \text{(C1.13)}
```

Under reversal the two marginal fields become $`1\text/f`$ and $`1\text/g`$. Therefore

```math
\begin{aligned}
E_R[1\text/f]&=\sum_S P f^2g^2(1\text/f)=E_P[fg^2]=E_Pg,\\
E_R[1\text/g]&=\sum_S P f^2g^2(1\text/g)=E_P[f^2g]=E_Pf,\\
s(R,P)&=2-E_R[1\text/f]-E_R[1\text/g]=2-E_Pg-E_Pf=s(P,R).
\end{aligned}
\qquad \text{(C1.14)}
```

The analytic fact used for separation is strict Jensen; the remaining steps are finite sums and polynomial expansions.
$`\square`$

Lean: `contact_energy_identities` (the two identities for $`E_PU^2`$ and $`E_PV^2`$, and their sum $`s`$),
`contact_quartic_identity`, `contact_separation` ($`0<s`$) and `contact_upper_separation` ($`s<2`$) in
`NaturalLatents/General/Contact.lean`, and `pairCharge_separation_reverse` (the symmetry) in
`NaturalLatents/General/PairCharge/MomentBounds.lean`, all `NaturalLatents.General.*`.

These assume distinctness: the positive-separation lemma `contact_separation`, the symmetry `pairCharge_separation_reverse` and
`contact_moments`. `contact_separation` derives $`0<s`$ from $`s=E_PU^2+E_PV^2`$ rather than from strict Jensen.

These do not assume distinctness: the energy and quartic identities and the upper bound $`s<2`$. `contact_energy_identities` assumes two contacts whose support is
exactly $`S`$; `contact_quartic_identity` takes probability laws $`P,R`$ together with the ratio identity and the conditional and
second-moment identities of Lemma C1.1 as inputs; and `contact_upper_separation` takes a probability law $`P`$ and
nonnegativity of $`f,g`$ with positivity wherever $`P`$ is positive. Neither the energy nor the quartic lemma assumes
feasibility. The equal-pair conclusions are not collected into a separate Lean statement, and $`A_0,B_0\ge0`$ is not
stated separately, though it follows from the two energy identities.

**Lemma C1.3 (feasibility for nonnegative marginal fields).** For every finite nonempty $`X,Y`$, every nonempty
$`S\subseteq X\times Y`$ with all rows and columns used, every feasible $`w>0`$ on $`S`$, every positive contact $`P`$ of
$`w`$, and every pair of fields $`A:X\to[0,\infty)`$, $`B:Y\to[0,\infty)`$,

```math
E_P[A(X)^2B(Y)^2]\leq(E_PA^3)^{2\text/3}(E_PB^3)^{2\text/3}.
\qquad \text{(C1.15)}
```

*Proof.* Write $`a=E_PA^3`$, $`b=E_PB^3`$. Two cases are treated: a zero normalizer, and two positive normalizers. If
either normalizer is zero, the corresponding nonnegative field is zero on every used symbol because all its marginal
weights are positive. Both sides of (C1.15) are then zero.

If $`a,b>0`$, the vectors

```math
u_x=\frac{P_X(x)A(x)^3}{a},\qquad
v_y=\frac{P_Y(y)B(y)^3}{b},\qquad
\sum_xu_x=\sum_yv_y=1
\qquad \text{(C1.16)}
```

are probability vectors. Substitute them into feasibility and use the contact equation:

```math
\begin{aligned}
1
&\geq\sum_S w(x,y)
 \left(\frac{P_X(x)A(x)^3}{a}\right)^{2\text/3}
 \left(\frac{P_Y(y)B(y)^3}{b}\right)^{2\text/3}\\
&=\frac{\sum_S w(x,y)P_X(x)^{2\text/3}P_Y(y)^{2\text/3}A(x)^2B(y)^2}
        {a^{2\text/3}b^{2\text/3}}
=\frac{E_P[A^2B^2]}{a^{2\text/3}b^{2\text/3}}.
\end{aligned}
\qquad \text{(C1.17)}
```

Multiplication by the positive denominator proves (C1.15). This directly uses feasibility, with the zero-normalizer case
handled separately. $`\square`$

Lean: (C1.15) is not stated separately; it is the case of `stoch_to_det.contact_hypercontractive`
(`NaturalLatents/Upstream/Duality.lean`) with the fields $`A^2`$ and $`B^2`$, which assumes a feasible kernel and a
contact, without positivity on $`S`$. `contact_hessian_cube_test` (`NaturalLatents/General/Contact.lean`) applies it to
the fields $`(1+tF)^2`$ and $`(1+tG)^2`$ in the proof of Lemma C1.4.

**Lemma C1.4 (the feasible Hessian test).** For every finite nonempty $`X,Y`$, every nonempty support $`S`$ with all rows
and columns used, every feasible $`w>0`$ on $`S`$, every positive contact $`P`$ of $`w`$, and every real marginal fields
$`F:X\to\mathbb R`$, $`G:Y\to\mathbb R`$ satisfying $`E_PF=E_PG=0`$,

```math
4E_P[FG]\leq E_PF^2+E_PG^2.
\qquad \text{(C1.18)}
```

*Proof.* Finiteness of the alphabets makes $`1+tF`$ and $`1+tG`$ positive for all sufficiently small $`\lvert t\rvert`$.
Insert these fields into Lemma C1.3. The left side expands exactly as

```math
\begin{aligned}
L(t)
&=E_P[(1+tF)^2(1+tG)^2]\\
&=1+2t(E_PF+E_PG)
 +t^2(E_PF^2+E_PG^2+4E_P[FG])\\
&\qquad+2t^3(E_P[F^2G]+E_P[FG^2])+t^4E_P[F^2G^2]\\
&=1+t^2(E_PF^2+E_PG^2+4E_P[FG])
 +2t^3(E_P[F^2G]+E_P[FG^2])+t^4E_P[F^2G^2].
\end{aligned}
\qquad \text{(C1.19)}
```

The cubic normalizers expand as

```math
\begin{aligned}
E_P(1+tF)^3
&=1+3tE_PF+3t^2E_PF^2+t^3E_PF^3
=1+3t^2E_PF^2+t^3E_PF^3,\\
E_P(1+tG)^3
&=1+3tE_PG+3t^2E_PG^2+t^3E_PG^3
=1+3t^2E_PG^2+t^3E_PG^3.
\end{aligned}
\qquad \text{(C1.20)}
```

Taylor's formula at $`1`$ for $`z^{2\text/3}`$ gives

```math
\begin{aligned}
(E_P(1+tF)^3)^{2\text/3}
&=1+\frac23(3t^2E_PF^2+t^3E_PF^3)+o(t^2)
=1+2t^2E_PF^2+o(t^2),\\
(E_P(1+tG)^3)^{2\text/3}
&=1+\frac23(3t^2E_PG^2+t^3E_PG^3)+o(t^2)
=1+2t^2E_PG^2+o(t^2),\\
R(t)
&=(E_P(1+tF)^3)^{2\text/3}(E_P(1+tG)^3)^{2\text/3}\\
&=1+2t^2(E_PF^2+E_PG^2)+o(t^2).
\end{aligned}
\qquad \text{(C1.21)}
```

At $`t=0`$, $`L(0)=R(0)=1`$, so both sides equal one. For sufficiently small nonzero $`t`$, division by $`t^2`$ is
legitimate. Consequently feasibility implies

```math
0\leq\frac{R(t)-L(t)}{t^2}
=E_PF^2+E_PG^2-4E_P[FG]+o(1).
\qquad \text{(C1.22)}
```

Taking $`t\to0`$ proves (C1.18). The analytic inputs are Taylor's formula for a smooth positive power and preservation
of a nonnegative inequality under a finite real limit. $`\square`$

Lean: `NaturalLatents.General.contact_hessian` (`NaturalLatents/General/Contact.lean`). It assumes a feasible kernel and
a contact, without positivity on $`S`$. Its proof uses `contact_hessian_cube_test`, the cube of (C1.15) for the fields
$`1+tF`$ and $`1+tG`$, and extracts the coefficient of $`t^2`$ by a one-sided limit (`contact_hessian_coefficient`)
instead of Taylor's formula for $`z^{2\text/3}`$.

**Lemma C1.5 (the contact quartic bound).** For every finite nonempty $`X,Y`$, every nonempty common support $`S`$ with
all rows and columns used, every feasible $`w>0`$ on $`S`$, and every pair of positive contacts $`P,R`$, the quantities
defined in (C1.3) satisfy

```math
J\leq6A_0B_0-s^2\leq\frac{s^2}{2}.
\qquad \text{(C1.23)}
```

*Proof.* Set $`F=U+A_0`$, $`G=V+B_0`$; these fields are centered because $`E_PU=-A_0`$ and $`E_PV=-B_0`$. Expand all the
moments used by Lemma C1.4:

```math
\begin{aligned}
E_P[FG]
&=E_P[UV]+B_0E_PU+A_0E_PV+A_0B_0
=E_P[UV]-A_0B_0,\\
E_PF^2
&=E_PU^2+2A_0E_PU+A_0^2=2A_0-B_0-A_0^2,\\
E_PG^2
&=E_PV^2+2B_0E_PV+B_0^2=2B_0-A_0-B_0^2.
\end{aligned}
\qquad \text{(C1.24)}
```

Using (C1.13) and $`s=A_0+B_0`$, the Hessian inequality becomes

```math
J+s-4A_0B_0=4E_P[FG]
\leq E_PF^2+E_PG^2=s-A_0^2-B_0^2.
\qquad \text{(C1.25)}
```

Thus

```math
\begin{aligned}
J&\leq4A_0B_0-A_0^2-B_0^2
=6A_0B_0-(A_0+B_0)^2=6A_0B_0-s^2,\\
0&\leq(A_0-B_0)^2=s^2-4A_0B_0,\qquad
6A_0B_0-s^2\leq6\frac{s^2}{4}-s^2=\frac{s^2}{2}.
\end{aligned}
\qquad \text{(C1.26)}
```

This proves the bound using the Hessian test and elementary square nonnegativity. Lemmas C1.1, C1.2, C1.4 and C1.5
together give the contact-moment lemma: the ratio and conditional identities, the moment list, the Hessian test for
centered marginal fields, and the consequence $`J\le6A_0B_0-s^2\le s^2\text/2`$. $`\square`$

Lean: `contact_quarticMoment_bound` (the first inequality) and `contact_scalar_bound` (the second), both
`NaturalLatents.General.*` in `NaturalLatents/General/Contact.lean`. `contact_quarticMoment_bound` assumes only that $`P`$ is a
probability law, together with the energy and quartic identities of Lemma C1.2 and the Hessian test as hypotheses; $`R`$
is an arbitrary real array and no contact hypothesis appears. `contact_scalar_bound` holds for arbitrary real arrays
$`P,R`$, since it uses only $`s=A_0+B_0`$. The contact-moment lemma is
`NaturalLatents.General.contact_moments` (`NaturalLatents/General/Contact.lean`): for every `CommonSupportPair S w P R`
it proves the structure `ContactMoments S P R` (`NaturalLatents/General/Definitions.lean`), whose fields are the
conditional identities, $`E_Pf^3=E_Pg^3=1`$, the second-moment identities, $`0<s<2`$, the two energy identities, the
quartic identity, the Hessian test and both inequalities of (C1.23). It does not include the ratio identity,
$`A_0,B_0\ge0`$ or the symmetry of $`s`$.
