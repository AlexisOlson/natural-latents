import Verso
import VersoManual
import VersoBlueprint
import NaturalLatents.Main

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "The exponential race" =>

:::group "race"
The exponential race.
:::

This page proves the race inequality. Notation follows section 0 of the [contact page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md). Let $`p` be a
probability law on a product $`X\times Y` of finite alphabets, let $`L` be a finite latent of $`p` whose posterior rows
$`r_z(i)=\Pr(L=i\mid Z=z)` are positive at every cell $`z` of the support, and let $`a>1`. Running an exponential race
among the labels, with one set of clocks shared by all cells, gives a calibrated random deterministic map $`F` from the
cells to the labels with $`h\le aB+2\,j(a)\,d`. Here $`B=I(L;X\mid Y)+I(L;Y\mid X)` is the leakage budget of $`L`,
$`d` is the probability that two labels drawn independently from the posterior at a cell drawn from $`p` disagree,
$`h` is the seed average of the conditional entropies of the fixed maps given $`X` and given $`Y`, and
$`j(a)=a\ln\Gamma(1-1/a)-\gamma_E`, with $`\Gamma` the Gamma function and $`\gamma_E` Euler's constant; section 1
gives the exact definitions. This is step 3 of the
[route](https://github.com/AlexisOlson/natural-latents/blob/main/docs/overview.md#the-route): the [ledger](https://github.com/AlexisOlson/natural-latents/blob/main/docs/ledger.md) turns such an $`F` into
$`T(p)\le M-B/2+3h/2`, where $`T(p)` is the deterministic optimum and $`M=I(X;Y\mid L)` as in (D3), a
separate cap page bounds $`j(a)`, and the mismatch payment bounds $`d`. In the
assembly `NaturalLatents.General.T_le_of_connected` (`NaturalLatents/General/Pricing.lean`), `exists_race` is applied at
$`a=211/45` to the setup latent, whose posterior rows are positive by the field `rows_pos` of the setup.

Each lemma below states its hypotheses, so that it can be read alone. The lemmas are numbered R1 to R11 and the equations
(R1) to (R31); the [cap page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/cap.md) continues both numberings. Unless prefixed `stoch_to_det`, the Lean declarations named below are in the namespace
`NaturalLatents.General`; the `stoch_to_det` declarations are in `NaturalLatents/Upstream/`, adapted from
[DLorell/stoch_to_det](https://github.com/DLorell/stoch_to_det).

# 1. Setting

*Units.* Units and conventions are those of section 0 of the [contact page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md): all entropies and mutual
informations on this page are in nats, and every logarithm is natural. The race calculation concerns $`B,d,h,j(a)`;
the optima used in the introductory assembly discussion are defined in section 0 of the contact page. Neither $`d` nor
$`j(a)` is divided by $`\ln2` in its definition.

*Notation.* Let $`X,Y` be finite alphabets and $`p` a probability law on $`X\times Y`. Let
$`\mathcal I = \{1, \ldots, n\}` with $`n \ge 1`. A finite latent is a joint law of $`Z = (X,Y)` and
$`L \in \mathcal I`. On the support of $`Z`, write $`p(z) = \Pr(Z = z) > 0`, $`r_z(i) = \Pr(L = i \mid Z = z) > 0` and
$`\pi_i = \sum_z p(z)\, r_z(i) > 0`. Each row and the prior sum to one. A seeded map is a deterministic map
$`A_e : \mathrm{supp}\,p \to \mathcal I` for each seed $`e`, with the seed independent of $`Z`. Calibration means
$`\Pr_E(A_E(z) = i) = r_z(i)`. The entropy $`H`, the relative entropy
$`D(r\Vert\pi)=\sum_ir_i\ln(r_i/\pi_i)`, the budget $`B=I(L;X\mid Y)+I(L;Y\mid X)` and the posterior mismatch
$`d=\sum_zp(z)\left(1-\sum_ir_z(i)^2\right)` are those of (D2) and (D3). Define

$$`
h=\mathbb E_E\left[H(A_E(Z)\mid X)+H(A_E(Z)\mid Y)\right],\qquad
j(a)=a\ln\Gamma(1-1/a)-\gamma_E .
\qquad \text{(R1)}
`

In the definition of $`h`, entropy is taken over $`Z` with $`E = e` held fixed, then averaged over $`E`. Equivalently
the two terms are $`H(A_E(Z) \mid X, E)` and $`H(A_E(Z) \mid Y, E)` on the joint probability space. Here $`\gamma_E` is
Euler's constant. Some letters are reused locally and are unrelated to the notation $`T(p)` and $`D_p(f)` of section 0:
in Lemma R4 the letter $`T` is the minimal scaled clock time; in Lemma R1 the letters $`D_k` and $`B_\ell` are
exponential variables and sets; from Lemma R5 on, $`J_i`, $`S_i`, $`S` and $`Q` are the reference masses and the reference
of (R8), unrelated to the quartic moment $`J` and the support $`S` of the contact page; $`N` is the Poisson process
in Lemma R1 and the limit index in Lemma R3; $`M` in the proof of Lemma R2 is an interval endpoint, not the budget
$`M`; $`b` in Lemma R3 and $`\alpha=1/a` in Lemmas R7 and R8 are scalars, not the quadratic $`b` of (A2.1) or
the coefficient $`\alpha` of the [pair-charge page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/pair-charge.md); $`s`, $`v`, $`w` and $`y` are integration or
transform variables, $`s` not the separation; $`G=\Gamma(1-\alpha)` in Lemma R8 and the Gumbel coordinates $`G_i` are not the
profile $`G(s)` of the pair-charge page; and $`\Phi_a` in (R12) is not the component functional of the
[setup page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/setup.md). The random map $`F`, the posterior $`r_z`, $`B`, $`d`, $`h` and $`j(a)` are the shared
objects of section 0 of the contact page and of (R1).

Lean: `gammaPrice` ($`j`), `seedEntropy` ($`h`), `mismatch` ($`d`) and `CalibratedSeededFamily`
(`NaturalLatents/General/Definitions.lean`). A calibrated family is a probability law on complete maps from
$`X\times Y` to the labels, calibrated at every cell of the support, and `seedEntropy` is the seed average of the
fixed-map conditional entropies, the form (L7) of the [ledger](https://github.com/AlexisOlson/natural-latents/blob/main/docs/ledger.md), each the bit-valued conditional entropy
converted by `condHNat` (`NaturalLatents/General/Nats.lean`). The function `gammaPrice` uses
Mathlib's `Real.Gamma` and `Real.eulerMascheroniConstant`.

# 2. Analytic facts

:::theorem "R1" (parent := "race") (uses := "") (tags := "paper proof")
*Lemma R1 (interval theorem, Campbell formula and Laplace functional).* Let $`D_1, D_2, \ldots` be independent
rate-one exponential variables, and let $`N = \{D_1 + \cdots + D_k : k \ge 1\}`. Then $`N` is a rate-one Poisson
process: counts in disjoint Borel sets of finite Lebesgue measure are independent Poisson variables with those measures
as means. For every nonnegative measurable $`g : (0,\infty) \to [0,\infty]`,

$$`
\mathbb E\sum_{t\in N}g(t)=\int_0^\infty g(t)\,dt,\qquad
\mathbb E\exp\!\left(-\sum_{t\in N}g(t)\right)
=\exp\!\left(-\int_0^\infty(1-e^{-g(t)})\,dt\right).
\qquad \text{(R2)}
`

Extended nonnegative integrals are allowed and $`e^{-\infty} = 0`.
:::

:::proof "R1"
Apply the interval theorem, calculate the formulas for simple functions using independent Poisson counts, and pass to general nonnegative functions by convergence. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/race.md#2-analytic-facts).
:::

Lean: Lemma R1 is not stated in general. The arrival times are the partial sums `arrivalTime` of independent rate-one
exponential increments under `arrivalLaw` (`NaturalLatents/General/Definitions.lean`), and the Laplace functional is
stated only for the shifted power sums the race uses: `race_shifted_arrival_laplace`, with $`g(s)=v(t+s)^{-a}`, and
`race_arrival_laplace`, which evaluates the case $`t=0` in the Gamma form of (R20) and (R21)
(`NaturalLatents/General/RaceLaplace.lean`). Lean has no Poisson
process, interval theorem or Campbell formula; it obtains the transform from a renewal equation
(`race_arrival_laplace_renewal` and `race_renewal_unique`).

:::theorem "R2" (parent := "race") (lean := "NaturalLatents.General.race_frullani_log_one_add, NaturalLatents.General.race_expected_log_one_add_laplace") (uses := "") (tags := "kernel-verified")
*Lemma R2 (Frullani logarithm identities).* For every $`x \ge 0` and every $`r > 0`,

$$`
\ln(1+x)=\int_0^\infty e^{-v}\frac{1-e^{-vx}}v\,dv,\qquad
\ln r=\int_0^\infty\frac{e^{-v}-e^{-vr}}v\,dv.
\qquad \text{(R4)}
`

If $`R > 0` almost surely and $`\mathbb E\lvert\ln R\rvert < \infty`, then

$$`
\mathbb E\ln R=\int_0^\infty\frac{e^{-v}-\mathbb E e^{-vR}}v\,dv.
\qquad \text{(R5)}
`
:::

:::proof "R2"
Differentiate the scalar integrals under domination, then apply Tonelli and Fubini using absolute log integrability. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/race.md#2-analytic-facts).
:::

Lean: `race_frullani_log_one_add` (the first identity of (R4), as an extended nonnegative integral) and
`race_expected_log_one_add_laplace` (the corresponding identity for $`\mathbb E\ln(1+V)`, for measurable $`V\ge0`
almost surely with $`\mathbb E\ln(1+V)<\infty`, also in extended nonnegative integral form),
both in `NaturalLatents/General/ExponentialRace.lean`. The identity for $`\ln r` and (R5) for a general positive $`R` are not
stated.

:::theorem "R3" (parent := "race") (lean := "NaturalLatents.General.race_scalar_exp_log_integrable_mean, Real.Gamma_eq_integral, Real.GammaIntegral_convergent, NaturalLatents.General.race_exp_rpow_moment") (uses := "") (tags := "kernel-verified")
*Lemma R3 (Gamma integral and Euler's logarithmic integral).* Let $`b > 0`, and let
$`\gamma_E = \lim_{N\to\infty}\left(\sum_{k=1}^N 1/k-\ln N\right)` be Euler's constant. The classical identities
needed in the race calculation are

$$`
\Gamma(b)=\int_0^\infty e^{-y}y^{b-1}\,dy,\qquad
\int_0^\infty e^{-y}\,dy=1,\qquad
\int_0^\infty e^{-y}\ln y\,dy=-\gamma_E.
\qquad \text{(R6)}
`
:::

:::proof "R3"
Use Euler’s Gamma and logarithmic integrals, checking absolute convergence separately at zero and infinity. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/race.md#2-analytic-facts).
:::

Lean: `race_scalar_exp_log_integrable_mean` (`NaturalLatents/General/RaceLaplace.lean`) states the integrability and
the mean of $`\ln T` under $`T\sim\mathrm{Exp}(1)`, equivalently the density-weighted integral in (R6). The Gamma integral
is Mathlib's `Real.Gamma_eq_integral` for positive arguments, with integrability `Real.GammaIntegral_convergent`; the
race uses them through `race_exp_rpow_moment` (`NaturalLatents/General/RaceLaplace.lean`). No single declaration combines
the three integrals.

# 3. The race

:::theorem "R4" (parent := "race") (lean := "NaturalLatents.General.race_clock_probability, NaturalLatents.General.race_seed_probability, NaturalLatents.General.race_map_calibrated, NaturalLatents.General.race_selected_coordinate_average") (uses := "") (tags := "kernel-verified")
*Lemma R4 (calibrated exponential winner).* Let $`r = (r_i)_{i=1}^n` be a strictly positive probability vector and let
$`E_1, \ldots, E_n` be independent rate-one exponential variables. With any fixed ordering to resolve ties, put
$`W = \arg\min_i E_i/r_i` and $`T = \min_i E_i/r_i`. Then

$$`
\Pr(W=i,\ T\in dt)
=r_i e^{-r_i t}\prod_{k\ne i}e^{-r_k t}\,dt
=r_i e^{-t}\,dt.
\qquad \text{(R7)}
`

Consequently $`W` has law $`r`, $`T` has law $`\mathrm{Exp}(1)`, $`W` and $`T` are independent, and $`E_i = r_i T` on
$`W = i`. For every finite source with positive rows $`r_z`, the maps $`A_E(z) = \arg\min_i E_i/r_z(i)`, with $`E`
independent of the source, are calibrated.
:::

:::proof "R4"
Multiply the winner density by the other clocks’ survival probabilities and exclude the finite union of tie events. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/race.md#3-the-race).
:::

Lean: `race_clock_probability` (the winner has law $`r`), `race_seed_probability` (the same in Gumbel coordinates) and
`race_map_calibrated` (the calibrated family), all in `NaturalLatents/General/RaceTransport.lean`. Lean runs the race in
Gumbel coordinates $`G_i=-\ln E_i` under `stoch_to_det.seedLaw` (`NaturalLatents/Upstream/Seed.lean`), with winner
`stoch_to_det.SharedRace.weightedLexWinner`, the lexicographic maximizer of $`\ln r_i+G_i`
(`NaturalLatents/Upstream/SharedRace/Definitions.lean`), which is $`\arg\min_iE_i/r_i` with a fixed tie rule. The
density (R7) and the independence of $`W` and $`T` are not stated; their consequence for averages of a statistic of the
winning clock is `race_selected_coordinate_average` (`NaturalLatents/General/ExponentialRace.lean`).

:::theorem "R5" (parent := "race") (lean := "NaturalLatents.General.race_arrival_mass_ae_summable, NaturalLatents.General.race_reference_isPMF") (uses := "R1") (tags := "kernel-verified")
*Lemma R5 (appended reference masses are finite).* Let $`a > 1`, let $`\pi = (\pi_i)_{i=1}^n` be a strictly positive
probability vector, and let $`E_i` be independent rate-one exponential variables. Append to each $`E_i` independent
rate-one exponential spacings, independent across labels and of all $`E_i`. Let $`T_{i1} = E_i, T_{i2}, \ldots` be the
resulting arrival times, and set

$$`
J_i=\pi_i^aE_i^{-a},\quad
S_i=\pi_i^a\sum_{k\ge1}T_{ik}^{-a},\quad
S=\sum_iS_i,\quad Q_i=S_i/S.
\qquad \text{(R8)}
`

Then every $`S_i` and $`S` is finite and strictly positive almost surely, so $`Q` is a strictly positive probability
vector. For a separate rate-one Poisson process $`N`, define

$$`
V_t=\sum_{v\in N}\left(\frac{t}{t+v}\right)^a\ (t>0),
\quad V_0=0,\qquad m_a(t)=\mathbb E\ln(1+V_t).
\qquad \text{(R9)}
`

Conditionally on $`E_i = t > 0`, $`S_i = J_i(1 + V_t^{(i)})`, where $`V_t^{(i)}` uses the appended process for label
$`i`, and

$$`
\mathbb EV_t
=\int_0^\infty\left(\frac{t}{t+v}\right)^a\,dv
=t\int_0^\infty(1+s)^{-a}\,ds
=\frac{t}{a-1}.
\qquad \text{(R10)}
`
:::

:::proof "R5"
Use Campbell’s formula for the appended process; finite conditional expectation gives almost sure finiteness and the first arrival gives positivity. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/race.md#3-the-race).
:::

Lean: `tailSum`, `logGain` and `arrivalLaw` (`NaturalLatents/General/Definitions.lean`) are $`V_t`, $`m_a` and the law of the
appended spacings. `race_arrival_mass_ae_summable` (`NaturalLatents/General/RaceLaplace.lean`) gives almost-sure
finiteness of the appended sums, and `race_reference_isPMF` (`NaturalLatents/General/RaceTransport.lean`) states that
$`Q` is a strictly positive probability vector. Lean totalizes the reference: it uses $`1+\max(0,V_t)`, and a divergent
series has value zero, so $`Q` is a positive probability vector at every seed. The mean (R10) is not stated.

:::theorem "R6" (parent := "race") (lean := "NaturalLatents.General.race_logGain_zero, NaturalLatents.General.race_logGain_nonneg, NaturalLatents.General.race_gain_scaling_of_shifted_transform, NaturalLatents.General.race_tailSum_laplace_of_shifted_transform, NaturalLatents.General.race_expected_log_gain_scaling_of_laplace, NaturalLatents.General.race_laplace_gain_scalar_concavity, NaturalLatents.General.race_unit_log_integrable, NaturalLatents.General.race_scalar_log_integrable_of_stable_laplace") (uses := "R1, R2, R5") (tags := "kernel-verified")
*Lemma R6 (concave gain and absolute log integrability).* Let $`a > 1` and define $`V_t, m_a` by (R9). Then
$`m_a(0) = 0`, $`0 \le m_a(t) \le t/(a-1)` for $`t \ge 0`, $`m_a` is concave on $`[0,\infty)`, and

$$`
m_a(rt)\ge r\,m_a(t)\qquad(t\ge0,\ 0\le r\le1).
\qquad \text{(R11)}
`

For every strictly positive probability vector $`\pi` and reference masses $`S_i, S` constructed as in (R8),
$`\mathbb E\lvert\ln S_i\rvert < \infty`, $`\mathbb E\lvert\ln J_i\rvert < \infty`, and
$`\mathbb E\lvert\ln S\rvert < \infty`.
:::

:::proof "R6"
Use the Laplace functional and Frullani identity to obtain concavity; bound the positive and negative logarithmic parts separately. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/race.md#3-the-race).
:::

Lean: `race_logGain_zero`, `race_logGain_nonneg` and `race_gain_scaling_of_shifted_transform` (the scaling inequality (R11)), in
`NaturalLatents/General/ExponentialRace.lean`. The proof of (R11) uses `race_tailSum_laplace_of_shifted_transform`, which is (R13),
`race_expected_log_gain_scaling_of_laplace`, which is (R14) followed by the concavity step, and
`race_laplace_gain_scalar_concavity`. Lean states neither the upper bound $`m_a(t)\le t/(a-1)` nor concavity of
$`m_a` itself, only (R11). It obtains log-integrability from the stable Laplace transform rather than from (R15) and (R16):
`race_unit_log_integrable` (`NaturalLatents/General/RaceLaplace.lean`) applies
`race_scalar_log_integrable_of_stable_laplace` to the unit appended mass.

:::theorem "R7" (parent := "race") (lean := "NaturalLatents.General.race_scalar_log_mean_of_stable_laplace, NaturalLatents.General.race_scalar_log_ratio_law_of_stable_laplace") (uses := "R2, R3") (tags := "kernel-verified")
*Lemma R7 (log mean from a Laplace transform).* Let $`0 < \alpha < 1`, $`c > 0`, and let $`R > 0` almost surely satisfy
$`\mathbb E\lvert\ln R\rvert < \infty` and $`\mathbb Ee^{-vR} = e^{-cv^\alpha}` for every $`v > 0`. Then

$$`
\mathbb E\ln R=\frac{\ln c}{\alpha}
+\left(\frac1\alpha-1\right)\gamma_E.
\qquad \text{(R17)}
`
:::

:::proof "R7"
Apply Frullani, integrate by parts, change variables, and use Euler’s logarithmic integral with both boundary terms controlled. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/race.md#3-the-race).
:::

Lean: `race_scalar_log_mean_of_stable_laplace` (`NaturalLatents/General/RaceLaplace.lean`), which drops the
restriction $`\alpha<1` and keeps measurability, positivity and log-integrability of $`R`, and $`c>0`. Its proof differs from the page: `race_scalar_log_ratio_law_of_stable_laplace` shows that, for an
independent rate-one exponential variable $`E`, the law of $`\ln E-\ln R` is the law of $`(\ln E-\ln c)/\alpha`,
and the mean follows from the logarithmic integral of (R6); neither (R5) nor integration by parts is used.

:::theorem "R8" (parent := "race") (lean := "NaturalLatents.General.race_gamma_price, NaturalLatents.General.race_unit_log_mean_eq_gammaPriceET, NaturalLatents.General.race_unit_arrival_laplace, NaturalLatents.General.race_gamma_price_of_unit_laplace, NaturalLatents.General.race_superposition_pi_laplace, NaturalLatents.General.race_superposition_clock_append_laplace") (uses := "R1, R3, R6, R7") (tags := "kernel-verified")
*Lemma R8 (identification of the race price).* Let $`a > 1`, $`\alpha = 1/a`, $`G = \Gamma(1-\alpha)`, and let
$`S_i, S, J_i` be constructed from a strictly positive probability vector $`\pi` and independent original and appended
exponential clocks as in (R8). With $`m_a` from (R9),

$$`
\mathbb E\ln S=a\ln G+(a-1)\gamma_E,\qquad
\mathbb E\ln S_i-\mathbb E\ln J_i=j(a),\qquad
\mathbb E_{T\sim\mathrm{Exp}(1)}m_a(T)=j(a)\ge0.
\qquad \text{(R19)}
`
:::

:::proof "R8"
Evaluate the power-sum Laplace exponent, multiply the independent transforms, and subtract their log means. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/race.md#3-the-race).
:::

Lean: `race_gamma_price` (`NaturalLatents/General/RaceLaplace.lean`) states `gammaPriceET a = gammaPrice a`, the third identity of
(R19), where `gammaPriceET` (`NaturalLatents/General/Definitions.lean`) is $`\mathbb E_{T\sim\mathrm{Exp}(1)}m_a(T)`. It is proved through
`race_unit_log_mean_eq_gammaPriceET` (the log mean of one appended mass with $`\pi_i=1` is $`a\gamma_E` plus `gammaPriceET a`),
`race_unit_arrival_laplace` (the Laplace transform (R21) of that mass) and `race_gamma_price_of_unit_laplace`. The
superposition step of (R21) is `race_superposition_pi_laplace` and `race_superposition_clock_append_laplace`
(`NaturalLatents/General/ExponentialRace.lean`). The other identities of (R19) appear only inside proofs.

:::theorem "R9" (parent := "race") (lean := "NaturalLatents.General.race_reference_loss_bound, NaturalLatents.General.race_appended_logloss_of_unit_laplace, NaturalLatents.General.race_gain_average") (uses := "R3, R4, R6, R8") (tags := "kernel-verified")
*Lemma R9 (rowwise reference loss, not a rowwise entropy bound).* Let $`a > 1`, let $`r, \pi` be strictly positive
probability vectors on the same finite label set, and construct the winner $`W = \arg\min_i E_i/r_i` and the
reference $`Q` from (R8) using the same original clocks and independent appendages. Write $`\Omega` for all appended
spacings. Then

$$`
\mathbb E_{E,\Omega}\left[-\ln Q_W\right]
\le aD(r\Vert\pi)+j(a)\left(1-\sum_i r_i^2\right).
\qquad \text{(R23)}
`
:::

:::proof "R9"
Condition on the winning clock, subtract the selected log mass from the total log mass, and apply concave gain scaling. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/race.md#3-the-race).
:::

Lean: `race_reference_loss_bound` (`NaturalLatents/General/ExponentialRace.lean`) states the integrability and (R23), with the
clocks in Gumbel coordinates. The exact identity of (R24), with the price written `gammaPriceET a`, is
`race_appended_logloss_of_unit_laplace`, and the scaling step is `race_gain_average`, which states
$`r\,j(a)\le\mathbb E\,m_a(rT)` for $`0\le r\le1`, both in the same file.

:::theorem "R10" (parent := "race") (lean := "NaturalLatents.General.race_single_law, NaturalLatents.General.race_gibbs_nats, NaturalLatents.General.race_entropy_from_reference, stoch_to_det.SharedRace.integrable_sharedWinner_code") (uses := "R9") (tags := "kernel-verified")
*Lemma R10 (fixed-seed mixture entropy).* Let $`\mathcal Z, \mathcal I` be finite nonempty sets, $`\nu` a probability
law positive on $`\mathcal Z` (here $`\nu` is the source law; in Lemma R11 it is $`p`), and $`r_z` strictly positive probability rows on $`\mathcal I`. Put
$`\pi_i = \sum_z\nu(z)r_z(i)`, let $`Z \sim \nu`, and let $`L \mid Z = z \sim r_z`. For $`a > 1`, take original
independent exponential clocks $`E`, independent of $`Z`, and define $`A_E(z) = \arg\min_iE_i/r_z(i)`. Then

$$`
H(A_E(Z)\mid E)=\mathbb E_E H(\mu_E)
\le aI(Z;L)+j(a)\sum_z\nu(z)\left(1-\sum_i r_z(i)^2\right),
\quad
\mu_e(i)=\sum_z\nu(z)\mathbf 1_{\{A_e(z)=i\}}.
\qquad \text{(R25)}
`
:::

:::proof "R10"
Apply Gibbs inequality to the actual fixed-seed source image and average the rowwise reference losses. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/race.md#3-the-race).
:::

Lean: `race_single_law` (`NaturalLatents/General/ExponentialRace.lean`) states (R25) for a probability law $`\nu` with strictly
positive rows wherever $`\nu(z)>0`, so $`\nu` may vanish at some atoms; like `exists_race` it is stated in nats, through
`sharedRaceEntropyNat` and `MINat` (`NaturalLatents/General/Nats.lean`). The Gibbs step (R26) is `race_gibbs_nats` and the averaging (R27) is
`race_entropy_from_reference`, both in `NaturalLatents/General/RaceTransport.lean`, with the integrability of the
fixed-seed entropy from `stoch_to_det.SharedRace.integrable_sharedWinner_code`
(`NaturalLatents/Upstream/CoordinateRace.lean`).

:::theorem "R11" (parent := "race") (lean := "NaturalLatents.General.exists_race, NaturalLatents.General.race_of_single_law, NaturalLatents.General.race_map_calibrated, stoch_to_det.SharedRace.conditional_entropy_le_of_uniform_entropy_bound, NaturalLatents.General.race_condMI_transport, NaturalLatents.General.race_condMI_coordinate_sum") (uses := "R10") (tags := "kernel-verified")
*Lemma R11 (the race bound, with the original clocks on both fibers).* Let $`X, Y, L` be finite random variables, let
$`Z = (X,Y)`, write $`p(z)=\Pr(Z=z)`, and suppose $`r_z(i) = \Pr(L = i \mid Z = z) > 0` for every $`z` with
$`p(z) > 0`; then $`\pi_i = \Pr(L = i) = \sum_zp(z)r_z(i) > 0`, since the support of $`p` is nonempty. Let
$`a > 1`, let $`E_i` be independent rate-one exponential clocks independent of $`(X,Y,L)`, and put $`A_E(z) = \arg\min_iE_i/r_z(i)`. With $`B, d, h, j(a)` exactly as in section 1, this
calibrated family satisfies

$$`
h\le aB+2j(a)d.
\qquad \text{(R28)}
`

It also induces a finite-valued random deterministic map $`F = (A_E(z))_{z\in\mathrm{supp}\,p}`, independent of $`Z`,
with the same calibration and the same $`h`.
:::

:::proof "R11"
Apply the single-source entropy estimate on both coordinate fibers with the same clocks, then pass to the finite map-valued seed. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/race.md#3-the-race).
:::

Lean: `exists_race` (`NaturalLatents/General/ExponentialRace.lean`): for every finite latent `L` of a law `p` whose posterior rows
`posterior L i z` are positive on the support, and every $`a>1`, there is a `CalibratedSeededFamily L` with
$`h\le aB+2j(a)d`. It states existence only: that the
family is the race map with the original clocks on both fibers is in the proof, not in the statement. The proof is
`race_of_single_law` (`NaturalLatents/General/RaceTransport.lean`), which takes the family from `race_map_calibrated`,
conditions Lemma R10 on $`X` and on $`Y` through `stoch_to_det.SharedRace.conditional_entropy_le_of_uniform_entropy_bound`
(`NaturalLatents/Upstream/CoordinateRace.lean`), and identifies the two conditional mutual informations with $`B` by
`race_condMI_transport` and `race_condMI_coordinate_sum`.

The race inequality (R28) retains the exact price $`j(a)`; a separate [cap page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/cap.md) supplies the explicit
bound on $`j(a)` for every $`a>1` (`racePrice_lt_capC3b`, `NaturalLatents/General/Cap.lean`) that the assembly uses at
$`a=211/45`.
