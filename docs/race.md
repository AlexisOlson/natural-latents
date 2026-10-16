# The exponential race

This page proves the race inequality. Notation follows section 0 of the [contact page](contact.md). Let $`p`$ be a
probability law on a product $`X\times Y`$ of finite alphabets, let $`L`$ be a finite latent of $`p`$ whose posterior rows
$`r_z(i)=\Pr(L=i\mid Z=z)`$ are positive at every cell $`z`$ of the support, and let $`a>1`$. Running an exponential race
among the labels, with one set of clocks shared by all cells, gives a calibrated random deterministic map $`F`$ from the
cells to the labels with $`h\le aB+2\,j(a)\,d`$. Here $`B=I(L;X\mid Y)+I(L;Y\mid X)`$ is the leakage budget of $`L`$,
$`d`$ is the probability that two labels drawn independently from the posterior at a cell drawn from $`p`$ disagree,
$`h`$ is the seed average of the conditional entropies of the fixed maps given $`X`$ and given $`Y`$, and
$`j(a)=a\ln\Gamma(1-1\text/a)-\gamma_E`$, with $`\Gamma`$ the Gamma function and $`\gamma_E`$ Euler's constant; section 1
gives the exact definitions. This is step 3 of the
[route](overview.md#the-route): the [ledger](ledger.md) turns such an $`F`$ into
$`T(p)\le M-B\text/2+3h\text/2`$, where $`T(p)`$ is the deterministic optimum and $`M=I(X;Y\mid L)`$ as in (D3), a
separate cap page bounds $`j(a)`$, and the mismatch payment bounds $`d`$. In the
assembly `NaturalLatents.General.T_le_of_connected` (`NaturalLatents/General/Pricing.lean`), `exists_race` is applied at
$`a=211\text/45`$ to the setup latent, whose posterior rows are positive by the field `rows_pos` of the setup.

The race with clocks shared by all cells is upstream's Gumbel race, formalized abstractly in
[pull request #5](https://github.com/DLorell/stoch_to_det/pull/5) by Satya Benson; bounding its entropy against a
powered reference is the method of [pull request #6](https://github.com/DLorell/stoch_to_det/pull/6) by Jeremy Gillen,
which works at fixed integer exponents. The price $`j(a)`$ for general $`a>1`$
(Lemmas R7 and R8) is worked out on this page.

Each lemma below states its hypotheses, so that it can be read alone. The lemmas are numbered R1 to R11 and the equations
(R1) to (R31); the [cap page](cap.md) continues both numberings. Unless prefixed `stoch_to_det`, the Lean declarations named below are in the namespace
`NaturalLatents.General`; the `stoch_to_det` declarations are in `NaturalLatents/Upstream/`, adapted from
[DLorell/stoch_to_det](https://github.com/DLorell/stoch_to_det).

## 1. Setting

**Units.** Units and conventions are those of section 0 of the [contact page](contact.md): all entropies and mutual
informations on this page are in nats, and every logarithm is natural. The race calculation concerns $`B,d,h,j(a)`$;
the optima used in the introductory assembly discussion are defined in section 0 of the contact page. Neither $`d`$ nor
$`j(a)`$ is divided by $`\ln2`$ in its definition.

**Notation.** Let $`X,Y`$ be finite alphabets and $`p`$ a probability law on $`X\times Y`$. Let
$`\mathcal I = \{1, \ldots, n\}`$ with $`n \ge 1`$. A finite latent is a joint law of $`Z = (X,Y)`$ and
$`L \in \mathcal I`$. On the support of $`Z`$, write $`p(z) = \Pr(Z = z) > 0`$, $`r_z(i) = \Pr(L = i \mid Z = z) > 0`$ and
$`\pi_i = \sum_z p(z)\, r_z(i) > 0`$. Each row and the prior sum to one. A seeded map is a deterministic map
$`A_e : \mathrm{supp}\,p \to \mathcal I`$ for each seed $`e`$, with the seed independent of $`Z`$. Calibration means
$`\Pr_E(A_E(z) = i) = r_z(i)`$. The entropy $`H`$, the relative entropy
$`D(r\Vert\pi)=\sum_ir_i\ln(r_i\text/\pi_i)`$, the budget $`B=I(L;X\mid Y)+I(L;Y\mid X)`$ and the posterior mismatch
$`d=\sum_zp(z)\left(1-\sum_ir_z(i)^2\right)`$ are those of (D2) and (D3). Define

```math
h=\mathbb E_E\left[H(A_E(Z)\mid X)+H(A_E(Z)\mid Y)\right],\qquad
j(a)=a\ln\Gamma(1-1\text/a)-\gamma_E .
\qquad \text{(R1)}
```

In the definition of $`h`$, entropy is taken over $`Z`$ with $`E = e`$ held fixed, then averaged over $`E`$. Equivalently
the two terms are $`H(A_E(Z) \mid X, E)`$ and $`H(A_E(Z) \mid Y, E)`$ on the joint probability space. Here $`\gamma_E`$ is
Euler's constant. Some letters are reused locally and are unrelated to the notation $`T(p)`$ and $`D_p(f)`$ of section 0:
in Lemma R4 the letter $`T`$ is the minimal scaled clock time; in Lemma R1 the letters $`D_k`$ and $`B_\ell`$ are
exponential variables and sets; from Lemma R5 on, $`J_i`$, $`S_i`$, $`S`$ and $`Q`$ are the reference masses and the reference
of (R8), unrelated to the quartic moment $`J`$ and the support $`S`$ of the contact page; $`N`$ is the Poisson process
in Lemma R1 and the limit index in Lemma R3; $`M`$ in the proof of Lemma R2 is an interval endpoint, not the budget
$`M`$; $`b`$ in Lemma R3 and $`\alpha=1\text/a`$ in Lemmas R7 and R8 are scalars, not the quadratic $`b`$ of (A2.1) or
the coefficient $`\alpha`$ of the [pair-charge page](pair-charge.md); $`s`$, $`v`$, $`w`$ and $`y`$ are integration or
transform variables, $`s`$ not the separation; $`G=\Gamma(1-\alpha)`$ in Lemma R8 and the Gumbel coordinates $`G_i`$ are not the
profile $`G(s)`$ of the pair-charge page; and $`\Phi_a`$ in (R12) is not the component functional of the
[setup page](setup.md). The random map $`F`$, the posterior $`r_z`$, $`B`$, $`d`$, $`h`$ and $`j(a)`$ are the shared
objects of section 0 of the contact page and of (R1).

Lean: `gammaPrice` ($`j`$), `seedEntropy` ($`h`$), `mismatch` ($`d`$) and `CalibratedSeededFamily`
(`NaturalLatents/General/Definitions.lean`). A calibrated family is a probability law on complete maps from
$`X\times Y`$ to the labels, calibrated at every cell of the support, and `seedEntropy` is the seed average of the
fixed-map conditional entropies, the form (L7) of the [ledger](ledger.md), each the bit-valued conditional entropy
converted by `condHNat` (`NaturalLatents/General/Nats.lean`). The function `gammaPrice` uses
Mathlib's `Real.Gamma` and `Real.eulerMascheroniConstant`.

## 2. Analytic facts

**Lemma R1 (interval theorem, Campbell formula and Laplace functional).** Let $`D_1, D_2, \ldots`$ be independent
rate-one exponential variables, and let $`N = \{D_1 + \cdots + D_k : k \ge 1\}`$. Then $`N`$ is a rate-one Poisson
process: counts in disjoint Borel sets of finite Lebesgue measure are independent Poisson variables with those measures
as means. For every nonnegative measurable $`g : (0,\infty) \to [0,\infty]`$,

```math
\mathbb E\sum_{t\in N}g(t)=\int_0^\infty g(t)\,dt,\qquad
\mathbb E\exp\!\left(-\sum_{t\in N}g(t)\right)
=\exp\!\left(-\int_0^\infty(1-e^{-g(t)})\,dt\right).
\qquad \text{(R2)}
```

Extended nonnegative integrals are allowed and $`e^{-\infty} = 0`$.

*Proof and analytic input.* The interval theorem is
[Last and Penrose, Theorem 7.2](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf), printed page 59. Campbell's
formula is Proposition 2.7, page 13; the Laplace functional is Theorem 3.9, page 23. Here are short proofs of the two
formulas once the interval theorem is applied. For a simple function $`g = \sum_{\ell=1}^m c_\ell \mathbf 1_{B_\ell}`$
with disjoint finite-measure sets and $`c_\ell \ge 0`$, write $`\lambda_\ell = \lvert B_\ell \rvert`$. The Poisson
probability series gives

```math
\begin{aligned}
\mathbb E N(B_\ell)&=\lambda_\ell,\\
\mathbb E e^{-c_\ell N(B_\ell)}
&=\sum_{k=0}^\infty e^{-c_\ell k}e^{-\lambda_\ell}\frac{\lambda_\ell^k}{k!}
=\exp\left[-\lambda_\ell(1-e^{-c_\ell})\right],\\
\mathbb E\sum_{t\in N}g(t)&=\sum_\ell c_\ell\lambda_\ell,\\
\mathbb E e^{-\sum_{t\in N}g(t)}
&=\prod_\ell\exp\left[-\lambda_\ell(1-e^{-c_\ell})\right]
=\exp\left[-\int(1-e^{-g(t)})\,dt\right].
\end{aligned}
\qquad \text{(R3)}
```

Approximate general $`g`$ increasingly by such simple functions on bounded windows. Monotone convergence gives Campbell
and the integral in the exponent; bounded convergence gives the exponential expectation. These are measure-theoretic
inputs, not moment formulas for the race mass. $`\square`$

Lean: Lemma R1 is not stated in general. The arrival times are the partial sums `arrivalTime` of independent rate-one
exponential increments under `arrivalLaw` (`NaturalLatents/General/Definitions.lean`), and the Laplace functional is
stated only for the shifted power sums the race uses: `race_shifted_arrival_laplace`, with $`g(s)=v(t+s)^{-a}`$, and
`race_arrival_laplace`, which evaluates the case $`t=0`$ in the Gamma form of (R20) and (R21)
(`NaturalLatents/General/RaceLaplace.lean`). Lean has no Poisson
process, interval theorem or Campbell formula; it obtains the transform from a renewal equation
(`race_arrival_laplace_renewal` and `race_renewal_unique`).

**Lemma R2 (Frullani logarithm identities).** For every $`x \ge 0`$ and every $`r > 0`$,

```math
\ln(1+x)=\int_0^\infty e^{-v}\frac{1-e^{-vx}}v\,dv,\qquad
\ln r=\int_0^\infty\frac{e^{-v}-e^{-vr}}v\,dv.
\qquad \text{(R4)}
```

If $`R > 0`$ almost surely and $`\mathbb E\lvert\ln R\rvert < \infty`$, then

```math
\mathbb E\ln R=\int_0^\infty\frac{e^{-v}-\mathbb E e^{-vR}}v\,dv.
\qquad \text{(R5)}
```

*Proof and analytic input.* Differentiating the first integral in $`x`$ on compact intervals gives
$`\int_0^\infty e^{-(1+x)v}\,dv = 1\text/(1+x)`$, and its value at zero is zero. The second is the first with
$`r = 1+x`$, extended to $`0 < r < 1`$ by the same derivative $`\int_0^\infty e^{-rv}\,dv = 1\text/r`$ and the value at
$`r = 1`$. On a compact interval $`[\varepsilon,M]\subset(0,\infty)`$ for $`r`$, the differentiated integrand is
$`e^{-rv}\le e^{-\varepsilon v}`$. The original integrand is bounded near zero and has an integrable exponential tail, so
dominated differentiation applies. For $`x\ge0`$, the derivative is bounded by $`e^{-v}`$. For fixed $`r`$, the integrand
has constant sign; its absolute integral is $`\lvert\ln r\rvert`$. Thus Tonelli
for the absolute value followed by Fubini proves (R5). The two sign regions $`r \ge 1`$ and $`0 < r < 1`$ are treated
separately. $`\square`$

Lean: `race_frullani_log_one_add` (the first identity of (R4), as an extended nonnegative integral) and
`race_expected_log_one_add_laplace` (the corresponding identity for $`\mathbb E\ln(1+V)`$, for measurable $`V\ge0`$
almost surely with $`\mathbb E\ln(1+V)<\infty`$, also in extended nonnegative integral form),
both in `NaturalLatents/General/ExponentialRace.lean`. The identity for $`\ln r`$ and (R5) for a general positive $`R`$ are not
stated.

**Lemma R3 (Gamma integral and Euler's logarithmic integral).** Let $`b > 0`$, and let
$`\gamma_E = \lim_{N\to\infty}\left(\sum_{k=1}^N 1\text/k-\ln N\right)`$ be Euler's constant. The classical identities
needed in the race calculation are

```math
\Gamma(b)=\int_0^\infty e^{-y}y^{b-1}\,dy,\qquad
\int_0^\infty e^{-y}\,dy=1,\qquad
\int_0^\infty e^{-y}\ln y\,dy=-\gamma_E.
\qquad \text{(R6)}
```

*Analytic input.* These are Euler's Gamma integral, [DLMF 5.2.1](https://dlmf.nist.gov/5.2.E1), and Euler's logarithmic
integral, [DLMF 5.9.18](https://dlmf.nist.gov/5.9.E18). The last integral is absolutely convergent: on $`0 < y < 1`$,
$`e^{-y}\lvert\ln y\rvert \le -\ln y`$; on $`y \ge 1`$, $`e^{-y}\lvert\ln y\rvert \le y e^{-y}`$. These regions are treated
separately. $`\square`$

Lean: `race_scalar_exp_log_integrable_mean` (`NaturalLatents/General/RaceLaplace.lean`) states the integrability and
the mean of $`\ln T`$ under $`T\sim\mathrm{Exp}(1)`$, equivalently the density-weighted integral in (R6). The Gamma integral
is Mathlib's `Real.Gamma_eq_integral` for positive arguments, with integrability `Real.GammaIntegral_convergent`; the
race uses them through `race_exp_rpow_moment` (`NaturalLatents/General/RaceLaplace.lean`). No single declaration combines
the three integrals.

## 3. The race

**Lemma R4 (calibrated exponential winner).** Let $`r = (r_i)_{i=1}^n`$ be a strictly positive probability vector and let
$`E_1, \ldots, E_n`$ be independent rate-one exponential variables. With any fixed ordering to resolve ties, put
$`W = \arg\min_i E_i\text/r_i`$ and $`T = \min_i E_i\text/r_i`$. Then

```math
\Pr(W=i,\ T\in dt)
=r_i e^{-r_i t}\prod_{k\ne i}e^{-r_k t}\,dt
=r_i e^{-t}\,dt.
\qquad \text{(R7)}
```

Consequently $`W`$ has law $`r`$, $`T`$ has law $`\mathrm{Exp}(1)`$, $`W`$ and $`T`$ are independent, and $`E_i = r_i T`$ on
$`W = i`$. For every finite source with positive rows $`r_z`$, the maps $`A_E(z) = \arg\min_i E_i\text/r_z(i)`$, with $`E`$
independent of the source, are calibrated.

*Proof and analytic input.* The scaled clocks have independent exponential densities with rates $`r_i`$; (R7) is their
winner density and survival product. Each pair of scaled clocks has zero tie probability. A finite union covers every
row and pair, so almost every seed is tie-free simultaneously on the whole source. The fixed tie convention also defines
the map on the exceptional seeds, which form a null event. Only exponential densities and finite independence are used.
$`\square`$

Lean: `race_clock_probability` (the winner has law $`r`$), `race_seed_probability` (the same in Gumbel coordinates) and
`race_map_calibrated` (the calibrated family), all in `NaturalLatents/General/RaceTransport.lean`. Lean runs the race in
Gumbel coordinates $`G_i=-\ln E_i`$ under `stoch_to_det.seedLaw` (`NaturalLatents/Upstream/Seed.lean`), with winner
`stoch_to_det.SharedRace.weightedLexWinner`, the lexicographic maximizer of $`\ln r_i+G_i`$
(`NaturalLatents/Upstream/SharedRace/Definitions.lean`), which is $`\arg\min_iE_i\text/r_i`$ with a fixed tie rule. The
density (R7) and the independence of $`W`$ and $`T`$ are not stated; their consequence for averages of a statistic of the
winning clock is `race_selected_coordinate_average` (`NaturalLatents/General/ExponentialRace.lean`).

**Lemma R5 (appended reference masses are finite).** Let $`a > 1`$, let $`\pi = (\pi_i)_{i=1}^n`$ be a strictly positive
probability vector, and let $`E_i`$ be independent rate-one exponential variables. Append to each $`E_i`$ independent
rate-one exponential spacings, independent across labels and of all $`E_i`$. Let $`T_{i1} = E_i, T_{i2}, \ldots`$ be the
resulting arrival times, and set

```math
J_i=\pi_i^aE_i^{-a},\quad
S_i=\pi_i^a\sum_{k\ge1}T_{ik}^{-a},\quad
S=\sum_iS_i,\quad Q_i=S_i\text/S.
\qquad \text{(R8)}
```

Then every $`S_i`$ and $`S`$ is finite and strictly positive almost surely, so $`Q`$ is a strictly positive probability
vector. For a separate rate-one Poisson process $`N`$, define

```math
V_t=\sum_{v\in N}\left(\frac{t}{t+v}\right)^a\ (t>0),
\quad V_0=0,\qquad m_a(t)=\mathbb E\ln(1+V_t).
\qquad \text{(R9)}
```

Conditionally on $`E_i = t > 0`$, $`S_i = J_i(1 + V_t^{(i)})`$, where $`V_t^{(i)}`$ uses the appended process for label
$`i`$, and

```math
\mathbb EV_t
=\int_0^\infty\left(\frac{t}{t+v}\right)^a\,dv
=t\int_0^\infty(1+s)^{-a}\,ds
=\frac{t}{a-1}.
\qquad \text{(R10)}
```

*Proof and analytic input.* Apply Lemma R1 to the appended spacings after fixing $`E_i = t`$. Formula (R10) is Campbell
plus $`v = ts`$ and the antiderivative $`(1+s)^{1-a}\text/(1-a)`$. Finite conditional expectation implies finite
appended mass, hence finite $`S_i`$ after integrating over $`E_i > 0`$; the first arrival ensures positivity. This does
not claim $`\mathbb E S_i < \infty`$. The appendages change only the reference $`Q`$; the original winner map $`A_E`$
still depends only on $`E`$. $`\square`$

Lean: `tailSum`, `logGain` and `arrivalLaw` (`NaturalLatents/General/Definitions.lean`) are $`V_t`$, $`m_a`$ and the law of the
appended spacings. `race_arrival_mass_ae_summable` (`NaturalLatents/General/RaceLaplace.lean`) gives almost-sure
finiteness of the appended sums, and `race_reference_isPMF` (`NaturalLatents/General/RaceTransport.lean`) states that
$`Q`$ is a strictly positive probability vector. Lean totalizes the reference: it uses $`1+\max(0,V_t)`$, and a divergent
series has value zero, so $`Q`$ is a positive probability vector at every seed. The mean (R10) is not stated.

**Lemma R6 (concave gain and absolute log integrability).** Let $`a > 1`$ and define $`V_t, m_a`$ by (R9). Then
$`m_a(0) = 0`$, $`0 \le m_a(t) \le t\text/(a-1)`$ for $`t \ge 0`$, $`m_a`$ is concave on $`[0,\infty)`$, and

```math
m_a(rt)\ge r\,m_a(t)\qquad(t\ge0,\ 0\le r\le1).
\qquad \text{(R11)}
```

For every strictly positive probability vector $`\pi`$ and reference masses $`S_i, S`$ constructed as in (R8),
$`\mathbb E\lvert\ln S_i\rvert < \infty`$, $`\mathbb E\lvert\ln J_i\rvert < \infty`$, and
$`\mathbb E\lvert\ln S\rvert < \infty`$.

*Proof and analytic input.* First $`\ln(1+x) \le x`$ and (R10) give the gain bound. For $`v \ge 0`$ define

```math
\Phi_a(v)=\int_0^\infty\left[1-e^{-v(1+s)^{-a}}\right]ds,\qquad
0\le\Phi_a(v)\le\frac{v}{a-1}.
\qquad \text{(R12)}
```

For $`t > 0`$, the Laplace functional and the change of variable from the appended arrival coordinate to $`ts`$ yield

```math
\mathbb E e^{-vV_t}
=\exp\left[-\int_0^\infty\left(1-e^{-v\left(\frac{t}{t+w}\right)^a}\right)dw\right]
=e^{-t\Phi_a(v)}.
\qquad \text{(R13)}
```

At $`t = 0`$ both sides are one, which completes the two cases $`t = 0`$ and $`t > 0`$. Lemma R2 and Tonelli, with
nonnegative integrand, give

```math
m_a(t)=\int_0^\infty e^{-v}\frac{1-\mathbb E e^{-vV_t}}v\,dv
=\int_0^\infty e^{-v}\frac{1-e^{-t\Phi_a(v)}}v\,dv.
\qquad \text{(R14)}
```

For every $`c \ge 0`$, $`t \mapsto 1 - e^{-ct}`$ is concave. Integration preserves the concavity inequality, and
$`m_a(0) = 0`$ gives (R11).

For an exponential variable $`E_i`$, the absolute-log estimate splits at one:

```math
\begin{aligned}
\mathbb E\lvert\ln E_i\rvert
&=\int_0^1e^{-t}(-\ln t)\,dt+\int_1^\infty e^{-t}\ln t\,dt\\
&\le\int_0^1(-\ln t)\,dt+\int_1^\infty te^{-t}\,dt
=1+2\text/e<\infty,\\
\ln S_i&=a\ln\pi_i-a\ln E_i+\ln(1+V_{E_i}^{(i)}),\\
\mathbb E\ln(1+V_{E_i}^{(i)})
&\le\frac{\mathbb EE_i}{a-1}=\frac{1}{a-1}.
\end{aligned}
\qquad \text{(R15)}
```

Thus $`\ln S_i`$ and $`\ln J_i = a\ln\pi_i - a\ln E_i`$ are absolutely integrable. Define $`\log^+x = \max(\ln x, 0)`$ and
$`\log^-x = \max(-\ln x, 0)`$. Since $`S \le n\prod_i\max(1, S_i)`$ and $`S \ge S_1`$,

```math
\log^+S\le\ln n+\sum_i\log^+S_i,\qquad
\log^-S\le\log^-S_1.
\qquad \text{(R16)}
```

This proves the remaining integrability, without fractional moments. $`\square`$

Lean: `race_logGain_zero`, `race_logGain_nonneg` and `race_gain_scaling_of_shifted_transform` (the scaling inequality (R11)), in
`NaturalLatents/General/ExponentialRace.lean`. The proof of (R11) uses `race_tailSum_laplace_of_shifted_transform`, which is (R13),
`race_expected_log_gain_scaling_of_laplace`, which is (R14) followed by the concavity step, and
`race_laplace_gain_scalar_concavity`. Lean states neither the upper bound $`m_a(t)\le t\text/(a-1)`$ nor concavity of
$`m_a`$ itself, only (R11). It obtains log-integrability from the stable Laplace transform rather than from (R15) and (R16):
`race_unit_log_integrable` (`NaturalLatents/General/RaceLaplace.lean`) applies
`race_scalar_log_integrable_of_stable_laplace` to the unit appended mass.

**Lemma R7 (log mean from a Laplace transform).** Let $`0 < \alpha < 1`$, $`c > 0`$, and let $`R > 0`$ almost surely satisfy
$`\mathbb E\lvert\ln R\rvert < \infty`$ and $`\mathbb Ee^{-vR} = e^{-cv^\alpha}`$ for every $`v > 0`$. Then

```math
\mathbb E\ln R=\frac{\ln c}{\alpha}
+\left(\frac1\alpha-1\right)\gamma_E.
\qquad \text{(R17)}
```

*Proof and analytic input.* Lemma R2 gives the first line below. Integrate by parts on a finite interval and pass to the
two endpoints, then put $`y = cv^\alpha`$:

```math
\begin{aligned}
\mathbb E\ln R
&=\int_0^\infty\frac{e^{-v}-e^{-cv^\alpha}}v\,dv\\
&=\int_0^\infty\ln v\,\left[e^{-v}-c\alpha v^{\alpha-1}e^{-cv^\alpha}\right]dv\\
&=\int_0^\infty e^{-v}\ln v\,dv
-\frac1\alpha\int_0^\infty e^{-y}(\ln y-\ln c)\,dy\\
&=-\gamma_E-\frac1\alpha(-\gamma_E-\ln c)
=\frac{\ln c}{\alpha}+\left(\frac1\alpha-1\right)\gamma_E .
\end{aligned}
\qquad \text{(R18)}
```

The boundary term is $`\ln v\,(e^{-v} - e^{-cv^\alpha})`$. Near zero its magnitude is at most
$`\lvert\ln v\rvert\,(v + cv^\alpha)`$, which tends to zero; at infinity each exponential times $`\ln v`$ tends to zero.
These are the two endpoint regimes. Each separated integral on the second line is absolutely convergent: use
$`v^{\alpha-1}\lvert\ln v\rvert`$ near zero, and $`y = cv^\alpha`$ at infinity. Lemma R3 supplies both logarithmic integrals
and $`\int e^{-y} = 1`$. No Mellin transform is used. $`\square`$

Lean: `race_scalar_log_mean_of_stable_laplace` (`NaturalLatents/General/RaceLaplace.lean`), which drops the
restriction $`\alpha<1`$ and keeps measurability, positivity and log-integrability of $`R`$, and $`c>0`$. Its proof differs from the page: `race_scalar_log_ratio_law_of_stable_laplace` shows that, for an
independent rate-one exponential variable $`E`$, the law of $`\ln E-\ln R`$ is the law of $`(\ln E-\ln c)\text/\alpha`$,
and the mean follows from the logarithmic integral of (R6); neither (R5) nor integration by parts is used.

**Lemma R8 (identification of the race price).** Let $`a > 1`$, $`\alpha = 1\text/a`$, $`G = \Gamma(1-\alpha)`$, and let
$`S_i, S, J_i`$ be constructed from a strictly positive probability vector $`\pi`$ and independent original and appended
exponential clocks as in (R8). With $`m_a`$ from (R9),

```math
\mathbb E\ln S=a\ln G+(a-1)\gamma_E,\qquad
\mathbb E\ln S_i-\mathbb E\ln J_i=j(a),\qquad
\mathbb E_{T\sim\mathrm{Exp}(1)}m_a(T)=j(a)\ge0.
\qquad \text{(R19)}
```

*Proof and analytic input.* For $`v > 0`$, substitute $`y = v\pi_i^at^{-a}`$, so $`t = \pi_i v^\alpha y^{-\alpha}`$, in the
Laplace exponent of the entire arrival process:

```math
\begin{aligned}
\int_0^\infty(1-e^{-v\pi_i^at^{-a}})\,dt
&=\pi_i\alpha v^\alpha
  \int_0^\infty(1-e^{-y})y^{-\alpha-1}\,dy,\\
\int_0^\infty(1-e^{-y})y^{-\alpha-1}\,dy
&=\left[-\frac{(1-e^{-y})y^{-\alpha}}{\alpha}\right]_0^\infty
+\frac1\alpha\int_0^\infty e^{-y}y^{-\alpha}\,dy\\
&=\frac{\Gamma(1-\alpha)}{\alpha}.
\end{aligned}
\qquad \text{(R20)}
```

For the boundary in (R20), $`1 - e^{-y} \le y`$ near zero gives $`y^{1-\alpha} \to 0`$; at infinity use
$`y^{-\alpha} \to 0`$. Lemmas R1 and R3, followed by independence across labels and $`\sum_i\pi_i = 1`$, give

```math
\mathbb Ee^{-vS_i}=e^{-\pi_iGv^\alpha},\qquad
\mathbb Ee^{-vS}=\prod_i e^{-\pi_iGv^\alpha}=e^{-Gv^\alpha}.
\qquad \text{(R21)}
```

All required absolute-log hypotheses hold by Lemma R6. Lemma R7 and Lemma R3 now display the subtraction completely:

```math
\begin{aligned}
\mathbb E\ln S_i&=a\ln(\pi_iG)+(a-1)\gamma_E
=a\ln\pi_i+a\ln G+(a-1)\gamma_E,\\
\mathbb E\ln J_i&=a\ln\pi_i-a\mathbb E\ln E_i
=a\ln\pi_i+a\gamma_E,\\
\mathbb E\ln S_i-\mathbb E\ln J_i&=a\ln G-\gamma_E=j(a),\\
\mathbb E\ln S&=a\ln G+(a-1)\gamma_E.
\end{aligned}
\qquad \text{(R22)}
```

The conditional appended representation also gives $`\mathbb E(\ln S_i - \ln J_i) = \mathbb E_{T\sim\mathrm{Exp}(1)}m_a(T)`$,
which proves the last assertion in (R19). $`\square`$

Lean: `race_gamma_price` (`NaturalLatents/General/RaceLaplace.lean`) states `gammaPriceET a = gammaPrice a`, the third identity of
(R19), where `gammaPriceET` (`NaturalLatents/General/Definitions.lean`) is $`\mathbb E_{T\sim\mathrm{Exp}(1)}m_a(T)`$. It is proved through
`race_unit_log_mean_eq_gammaPriceET` (the log mean of one appended mass with $`\pi_i=1`$ is $`a\gamma_E`$ plus `gammaPriceET a`),
`race_unit_arrival_laplace` (the Laplace transform (R21) of that mass) and `race_gamma_price_of_unit_laplace`. The
superposition step of (R21) is `race_superposition_pi_laplace` and `race_superposition_clock_append_laplace`
(`NaturalLatents/General/ExponentialRace.lean`). The other identities of (R19) appear only inside proofs.

**Lemma R9 (rowwise reference loss, not a rowwise entropy bound).** Let $`a > 1`$, let $`r, \pi`$ be strictly positive
probability vectors on the same finite label set, and construct the winner $`W = \arg\min_i E_i\text/r_i`$ and the
reference $`Q`$ from (R8) using the same original clocks and independent appendages. Write $`\Omega`$ for all appended
spacings. Then

```math
\mathbb E_{E,\Omega}\left[-\ln Q_W\right]
\le aD(r\Vert\pi)+j(a)\left(1-\sum_i r_i^2\right).
\qquad \text{(R23)}
```

*Proof and analytic input.* Lemma R4 gives $`E_i = r_iT`$ conditionally on $`W = i`$, with $`T \sim \mathrm{Exp}(1)`$. The
appended spacings $`\Omega`$ are independent of the winning event and original clocks. Using Lemma R3 for
$`\mathbb E\ln T = -\gamma_E`$,

```math
\begin{aligned}
\mathbb E\ln S_W
&=\sum_i r_i\left[a\ln\pi_i-a\ln r_i
-a\mathbb E\ln T+\mathbb E m_a(r_iT)\right]\\
&=-aD(r\Vert\pi)+a\gamma_E+\sum_i r_i\mathbb E m_a(r_iT),\\
\mathbb E\left[-\ln Q_W\right]
&=\mathbb E\ln S-\mathbb E\ln S_W\\
&=aD(r\Vert\pi)+j(a)-\sum_i r_i\mathbb E m_a(r_iT)\\
&\le aD(r\Vert\pi)+j(a)-\sum_i r_i^2\mathbb E m_a(T)\\
&=aD(r\Vert\pi)+j(a)\left(1-\sum_i r_i^2\right).
\end{aligned}
\qquad \text{(R24)}
```

The inequality is exactly Lemma R6 with scaling $`r_i \in (0,1]`$, followed by Lemma R8. Expectations are finite:
$`\lvert\ln S_W\rvert \le \sum_i\lvert\ln S_i\rvert`$, even though the selected index depends on $`E`$. This lemma bounds
cross entropy averaged over the clocks; it makes no assertion about the unconditional entropy $`H(r)`$. $`\square`$

Lean: `race_reference_loss_bound` (`NaturalLatents/General/ExponentialRace.lean`) states the integrability and (R23), with the
clocks in Gumbel coordinates. The exact identity of (R24), with the price written `gammaPriceET a`, is
`race_appended_logloss_of_unit_laplace`, and the scaling step is `race_gain_average`, which states
$`r\,j(a)\le\mathbb E\,m_a(rT)`$ for $`0\le r\le1`$, both in the same file.

**Lemma R10 (fixed-seed mixture entropy).** Let $`\mathcal Z, \mathcal I`$ be finite nonempty sets, $`\nu`$ a probability
law positive on $`\mathcal Z`$ (here $`\nu`$ is the source law; in Lemma R11 it is the conditional law on an $`X=x`$ or $`Y=y`$ fiber, restricted to its positive support), and $`r_z`$ strictly positive probability rows on $`\mathcal I`$. Put
$`\pi_i = \sum_z\nu(z)r_z(i)`$, let $`Z \sim \nu`$, and let $`L \mid Z = z \sim r_z`$. For $`a > 1`$, take original
independent exponential clocks $`E`$, independent of $`Z`$, and define $`A_E(z) = \arg\min_iE_i\text/r_z(i)`$. Then

```math
H(A_E(Z)\mid E)=\mathbb E_E H(\mu_E)
\le aI(Z;L)+j(a)\sum_z\nu(z)\left(1-\sum_i r_z(i)^2\right),
\quad
\mu_e(i)=\sum_z\nu(z)\mathbf 1_{\{A_e(z)=i\}}.
\qquad \text{(R25)}
```

*Proof and analytic input.* Append independent arrivals and form $`Q(e,\omega)`$ using $`\pi`$. At each fixed original
seed $`e`$ and fixed appendage realization $`\omega`$ where $`Q`$ is defined, Gibbs applies to the actual source-image
probability measure $`\mu_e`$:

```math
0\le D(\mu_e\Vert Q(e,\omega))
=\sum_i\mu_e(i)\ln\mu_e(i)-\sum_i\mu_e(i)\ln Q_i(e,\omega),
\quad
H(\mu_e)\le-\sum_i\mu_e(i)\ln Q_i(e,\omega).
\qquad \text{(R26)}
```

Terms of zero $`\mu_e`$-mass are zero; only labels of positive source-image mass contribute. Gibbs follows from
$`\ln x \le x - 1`$, applied on the positive $`\mu_e`$-support to $`x = Q_i\text/\mu_e(i)`$, then summing; the omitted
$`Q`$-mass can only improve the inequality. On the null event where the reference construction fails, which is the
complement of the almost-sure event on which $`Q`$ is defined, $`Q`$ is assigned any positive probability vector.

Average (R26) over $`E, \Omega`$ and the finite source, then apply Lemma R9 to each row:

```math
\begin{aligned}
\mathbb E_EH(\mu_E)
&\le\sum_z\nu(z)\mathbb E_{E,\Omega}\left[-\ln Q_{A_E(z)}\right]\\
&\le a\sum_z\nu(z)D(r_z\Vert\pi)
+j(a)\sum_z\nu(z)\left(1-\sum_i r_z(i)^2\right),\\
\sum_z\nu(z)D(r_z\Vert\pi)
&=\sum_{z,i}\nu(z)r_z(i)
 \ln\frac{\nu(z)r_z(i)}{\nu(z)\pi_i}=I(Z;L).
\end{aligned}
\qquad \text{(R27)}
```

This is the fixed-seed entropy $`H(A_E(Z) \mid E)`$; $`\Omega`$ is used only in the reference and does not change
$`\mu_E`$ or the map. $`\square`$

Lean: `race_single_law` (`NaturalLatents/General/ExponentialRace.lean`) states (R25) for a probability law $`\nu`$ with strictly
positive rows wherever $`\nu(z)>0`$, so $`\nu`$ may vanish at some atoms; like `exists_race` it is stated in nats, through
`sharedRaceEntropyNat` and `MINat` (`NaturalLatents/General/Nats.lean`). The Gibbs step (R26) is `race_gibbs_nats` and the averaging (R27) is
`race_entropy_from_reference`, both in `NaturalLatents/General/RaceTransport.lean`, with the integrability of the
fixed-seed entropy from `stoch_to_det.SharedRace.integrable_sharedWinner_code`
(`NaturalLatents/Upstream/CoordinateRace.lean`).

**Lemma R11 (the race bound, with the original clocks on both fibers).** Let $`X, Y, L`$ be finite random variables, let
$`Z = (X,Y)`$, write $`p(z)=\Pr(Z=z)`$, and suppose $`r_z(i) = \Pr(L = i \mid Z = z) > 0`$ for every $`z`$ with
$`p(z) > 0`$; then $`\pi_i = \Pr(L = i) = \sum_zp(z)r_z(i) > 0`$, since the support of $`p`$ is nonempty. Let
$`a > 1`$, let $`E_i`$ be independent rate-one exponential clocks independent of $`(X,Y,L)`$, and put $`A_E(z) = \arg\min_iE_i\text/r_z(i)`$. With $`B, d, h, j(a)`$ exactly as in section 1, this
calibrated family satisfies

```math
h\le aB+2j(a)d.
\qquad \text{(R28)}
```

It also induces a finite-valued random deterministic map $`F = (A_E(z))_{z\in\mathrm{supp}\,p}`$, independent of $`Z`$,
with the same calibration and the same $`h`$.

*Proof and analytic input.* Fix an $`x`$ with $`p_X(x) > 0`$. Its conditional source law and prior are

```math
\nu_x(y)=\frac{p(x,y)}{p_X(x)},\qquad
\pi_i^x=\sum_{y:p(x,y)>0}\nu_x(y)r_{(x,y)}(i)>0.
\qquad \text{(R29)}
```

Apply Lemma R10 to the source law $`\nu_x`$ and the rows $`r_{(x,\cdot)}`$ on $`Y_x=\{y:p(x,y)>0\}`$, using the same
$`E_i`$; its prior is $`\pi^x`$. Every sum involving the posterior or race map on this fiber ranges over $`Y_x`$. The
pointwise mixture is $`\mu_{e,x}(i) = \sum_{y\in Y_x}\nu_x(y)\mathbf 1_{\{A_e(x,y)=i\}}`$. Since
$`\pi_i^x=\Pr(L=i\mid X=x)`$, the relative-entropy average is
$`\sum_{y}\nu_x(y)D(r_{(x,y)}\Vert\pi^x)=I(L;Y\mid X=x)`$. Averaging in $`x`$ gives

```math
\begin{aligned}
H(A_E(Z)\mid X,E)
&\le a\sum_{x,y,i}p(x,y)r_{(x,y)}(i)\ln\frac{r_{(x,y)}(i)}{\pi_i^x}
+j(a)\sum_{x,y}p(x,y)\left(1-\sum_i r_{(x,y)}(i)^2\right)\\
&=aI(L;Y\mid X)+j(a)d.
\end{aligned}
\qquad \text{(R30)}
```

The sum uses only positive source atoms; fibers of zero probability carry no weight, and only fibers of positive
probability contribute. For the other coordinate use $`X_y=\{x:p(x,y)>0\}`$, for $`y`$ with $`p_Y(y)>0`$. The
conditional prior on a $`Y = y`$ fiber is $`\pi_i^y = \sum_{x\in X_y}p(x,y)r_{(x,y)}(i)\text/p_Y(y) > 0`$. The same
clocks and Lemma R10 similarly give

```math
H(A_E(Z)\mid Y,E)\le aI(L;X\mid Y)+j(a)d,\qquad
h\le a\left[I(L;Y\mid X)+I(L;X\mid Y)\right]+2j(a)d.
\qquad \text{(R31)}
```

Both deficit sums equal $`d`$, since
$`\sum_xp_X(x)\sum_y\nu_x(y)\left(1-\sum_ir_{(x,y)}(i)^2\right)=\sum_{x,y}p(x,y)\left(1-\sum_ir_{(x,y)}(i)^2\right)`$.

There are at most $`n^{\lvert\mathrm{supp}\,p\rvert}`$ maps. Their seed preimages are measurable finite intersections of
clock inequalities, so $`F`$ is a finite-valued function of $`E`$, independent of $`Z`$. At a fixed map $`F = f`$,
source-image entropy depends only on $`f`$, not on which seed realizes it; averaging over map probabilities therefore
agrees with averaging over $`E`$. This supplies the finite-map formulation without adding the appendages to the coding
seed. $`\square`$

Lean: `exists_race` (`NaturalLatents/General/ExponentialRace.lean`): for every finite latent `L` of a law `p` whose posterior rows
`posterior L i z` are positive on the support, and every $`a>1`$, there is a `CalibratedSeededFamily L` with
$`h\le aB+2j(a)d`$. It states existence only: that the
family is the race map with the original clocks on both fibers is in the proof, not in the statement. The proof is
`race_of_single_law` (`NaturalLatents/General/RaceTransport.lean`), which takes the family from `race_map_calibrated`,
conditions Lemma R10 on $`X`$ and on $`Y`$ through `stoch_to_det.SharedRace.conditional_entropy_le_of_uniform_entropy_bound`
(`NaturalLatents/Upstream/CoordinateRace.lean`), and identifies the two conditional mutual informations with $`B`$ by
`race_condMI_transport` and `race_condMI_coordinate_sum`.

The race inequality (R28) retains the exact price $`j(a)`$; a separate [cap page](cap.md) supplies the explicit
bound on $`j(a)`$ for every $`a>1`$ (`racePrice_lt_capC3b`, `NaturalLatents/General/Cap.lean`) that the assembly uses at
$`a=211\text/45`$.
