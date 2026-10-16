# The ledger

This page proves the ledger inequality, in the notation of section 0 of the [contact page](contact.md) (the posterior
$`r_z`$ and the optimum $`T`$ are defined in (D3)). Let $`L`$ be a finite latent of $`p`$ and let $`F`$ be a random
deterministic map from the cells to the labels of $`L`$, independent of $`Z=(X,Y)`$, such that at each cell $`z`$ of the
support the label $`F(z)`$ is distributed as the posterior $`r_z`$ of $`L`$. With $`M`$ and $`B`$ the budgets of
(D3) and $`h`$ the average over $`F`$ of $`H(f(Z)\mid X)+H(f(Z)\mid Y)`$ computed with the map $`f`$ fixed,
$`T(p)\le M-B\text/2+3h\text/2`$; the page also proves the exact average-score identity behind it. The inequality is the
coordinate-entropy ledger of [pull request #6](https://github.com/DLorell/stoch_to_det/pull/6) by Jeremy Gillen to
DLorell/stoch_to_det (`T_le_coordinate_entropy_ledger` in its `CoordinateLedger.lean`, stated there for the
shared-race winner of a seed setup); this page proves it for any calibrated random map. This is the first
inequality of the assembly (step 2 of the [route](overview.md#the-route)). For the supplied setup
latent, whose posteriors are positive, and every $`a>1`$, the exponential race supplies such an $`F`$ with
$`h\le aB+2\,j(a)\,d`$, where $`j(a)=a\ln\Gamma(1-1\text/a)-\gamma_E`$ with $`\gamma_E`$ Euler's
constant, and $`d`$ is the mismatch of (D3); the mismatch payment then bounds $`d`$. The ledger lemma itself needs no
positivity. In the assembly
`NaturalLatents.General.T_le_of_connected` (`NaturalLatents/General/Pricing.lean`), `T_le_ledger` is applied to the
setup latent and the family given by `exists_race`.

## 4. The ledger

Units and conventions are those of section 0 of the [contact page](contact.md): entropies and informations are in nats,
conditional sums range over positive-probability conditioning events, and $`D_p(f)=I(X;Y\mid f(Z))+H(f(Z)\mid X)+H(f(Z)\mid Y)`$
is the deterministic score of a map $`f`$, so that $`T(p)=\min_fD_p(f)`$ as in (D3). The random map $`F`$ is the one of
step 2 of the [route](overview.md#the-route), not the cap $`F`$ of the [cap page](cap.md); $`Q=F(Z)`$, $`U`$, $`A`$ and $`\Delta`$
below are local, and $`Q`$ is not the reference of the [race page](race.md).

**Lemma L4.1 (calibrated finite-map averaging and the ledger).** Let $`X,Y,L`$ be finite random variables, $`Z=(X,Y)`$,
and let $`p`$ be the law of $`Z`$. Let $`F`$ be a finite-valued random deterministic map from $`\mathrm{supp}\,p`$ to the
label set of $`L`$, independent of $`Z`$. Suppose $`\Pr(F(z)=i)=r_z(i)=\Pr(L=i\mid Z=z)`$ for every positive source atom
$`z`$. Put $`Q=F(Z)`$, $`M=I(X;Y\mid L)`$, $`B=I(L;X\mid Y)+I(L;Y\mid X)`$, and

```math
h=H(Q\mid X,F)+H(Q\mid Y,F),\qquad
\Delta=I(F;X\mid Q)+I(F;Y\mid Q).
\qquad \text{(L1)}
```

Then $`\Delta\ge0`$, and

```math
\mathbb E_F D_p(F)
=M-\frac B2+\frac{3h}{2}-\frac{\Delta}{2},
\qquad
T(p)\le M-\frac B2+\frac{3h}{2}.
\qquad \text{(L2)}
```

Here $`D_p(f)`$ is the deterministic score of $`f(Z)`$, as in section 0. No positivity, contact, optimality or
distinct-component hypothesis is needed. Fix a label $`i_0`$ and extend every map by $`i_0`$ outside
$`\mathrm{supp}\,p`$. This does not change $`Q`$, calibration, $`h`$, $`\Delta`$ or any fixed-map score, and turns $`F`$
into a random complete map, as used below.

*Proof.* For every finite random variable $`U`$ jointly distributed with $`Z`$, expand the finite entropy identities and
the mutual-information chain rule:

```math
\begin{aligned}
I(X;Y\mid U)
&=H(X\mid U)+H(Y\mid U)-H(Z\mid U)\\
&=I(X;Y)+I(U;Z)-I(U;X)-I(U;Y),\\
I(U;X\mid Y)&=I(U;Z)-I(U;Y),\\
I(U;Y\mid X)&=I(U;Z)-I(U;X),\\
I(X;Y\mid U)-\frac{I(U;X\mid Y)+I(U;Y\mid X)}2
&=I(X;Y)-\frac{I(U;X)+I(U;Y)}2 .
\end{aligned}
\qquad \text{(L3)}
```

For a deterministic $`A=f(Z)`$, $`H(A\mid Z)=0`$. Thus

```math
\begin{aligned}
I(A;X\mid Y)&=H(A\mid Y),&
I(A;Y\mid X)&=H(A\mid X),\\
D_p(f)
&=I(X;Y\mid A)+H(A\mid X)+H(A\mid Y)\\
&=I(X;Y)+\frac32[H(A\mid X)+H(A\mid Y)]
-\frac12[I(A;X)+I(A;Y)].
\end{aligned}
\qquad \text{(L4)}
```

Calibration and independence give the entire joint-law equality, not just a marginal equality:

```math
\begin{aligned}
\Pr(Q=i,Z=z)
&=p(z)\sum_f\Pr(F=f)\mathbf1_{\{f(z)=i\}}\\
&=p(z)r_z(i)=\Pr(L=i,Z=z).
\end{aligned}
\qquad \text{(L5)}
```

Consequently $`I(Q;X)=I(L;X)`$ and $`I(Q;Y)=I(L;Y)`$. Independence gives $`I(F;X)=I(F;Y)=0`$. For every positive-weight
map $`f`$, independence gives $`\Pr(Z=z\mid F=f)=p(z)`$; hence, conditional on $`F=f`$, $`Q=f(Z)`$ has exactly the
fixed-map law computed from $`p`$. Expand the chain rule in both orders, separately on both coordinates:

```math
\begin{aligned}
I(Q,F;X)
&=I(F;X)+I(Q;X\mid F)
=I(Q;X)+I(F;X\mid Q),\\
\sum_f\Pr(F=f)I(f(Z);X)
&=I(Q;X\mid F)=I(L;X)+I(F;X\mid Q),\\
I(Q,F;Y)
&=I(F;Y)+I(Q;Y\mid F)
=I(Q;Y)+I(F;Y\mid Q),\\
\sum_f\Pr(F=f)I(f(Z);Y)
&=I(Q;Y\mid F)=I(L;Y)+I(F;Y\mid Q).
\end{aligned}
\qquad \text{(L6)}
```

The seed-averaged entropy is equally

```math
h=\sum_f\Pr(F=f)
[H(f(Z)\mid X)+H(f(Z)\mid Y)].
\qquad \text{(L7)}
```

Averaging (L4) and using (L6), (L7) and the balance identity (L3) gives:

```math
\begin{aligned}
\sum_f\Pr(F=f)D_p(f)
&=I(X;Y)+\frac{3h}{2}
-\frac12\sum_f\Pr(F=f)[I(f(Z);X)+I(f(Z);Y)]\\
&=I(X;Y)+\frac{3h}{2}
-\frac12[I(L;X)+I(L;Y)+\Delta]\\
&=M-\frac B2+\frac{3h}{2}-\frac{\Delta}{2}\\
&\le M-\frac B2+\frac{3h}{2}.
\end{aligned}
\qquad \text{(L8)}
```

Nonnegativity of conditional mutual information is Gibbs' inequality on each conditional probability law, averaged over
the conditioning variable. A finite probability-weighted average is at least one of its positive-weight summands. Such a
deterministic map is admissible for $`T(p)`$, which proves (L2). Zero-probability seed values are omitted throughout
finite conditional sums and contribute no term. If the maps are generated by a continuous auxiliary seed independent of
$`Z`$, use its finite map-valued pushforward $`F`$; conditional entropy is always computed with that map seed held fixed. $`\square`$

Lean: `NaturalLatents.General.T_le_ledger` (`NaturalLatents/General/Ledger.lean`) states only the inequality
$`T(p)\le M-B\text/2+3h\text/2`$; Lean does not define $`\Delta`$ or state the identity for $`\mathbb E_FD_p(F)`$. The
random map is a `CalibratedSeededFamily L` (`NaturalLatents/General/Definitions.lean`): a probability law on complete
maps from all of $`X\times Y`$ to the labels, calibrated at every cell of the support, whose independence from $`Z`$ is
the product law `seedSourceJoint`; $`h`$ is `seedEntropy` in the same file, the form (L7). The steps are in
`NaturalLatents/General/Ledger.lean`. (L5) is `ledger_calibrated_graph`. The final identity of (L4), in bits, is
`ledger_detScore_coordinate_identity`; conversion by `nats`, through `detScoreNat`, gives its page form. The final identity of (L3) with
$`U=L`$ is `ledger_information_balance`, stated in nats through `nats`. `ledger_average_MI_lower` is
bit-valued and states $`I(L;g(Z))\le\sum_f\Pr(F=f)I(f(Z);g(Z))`$ for every finite function $`g`$ of the cell; applying it
to each coordinate and converting by `nats` gives the lower bounds used from (L6), in place of the identities with
$`\Delta`$. The proof averages
$`T(p)\le D_p(f)`$, from `stoch_to_det.T_le_score` (`NaturalLatents/Upstream/Functionals.lean`), over the seed.
