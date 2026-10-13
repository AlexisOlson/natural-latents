import Verso
import VersoManual
import VersoBlueprint
import NaturalLatents.Main

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "The cap on the race price" =>

:::group "cap"
The cap on the race price.
:::

This page proves an explicit upper bound on the race price $`j(a)=a\ln\Gamma(1-1/a)-\gamma_E` of the
[race page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/race.md), equation (R1): for every real $`a>1`,

$$`
j(a)<F(a)=\frac{533}{648a}+\frac{241}{600a^2}+\frac{6503}{24000a^2(a-1)},
`

and at $`a=211/45` it evaluates the right side exactly, $`F(211/45)=838748045/4256919936`, which is below
the rational price $`u=3941/20000` used by the assembly. This is step 4 of the [route](https://github.com/AlexisOlson/natural-latents/blob/main/docs/overview.md#the-route). The race inequality
$`h\le aB+2\,j(a)\,d` keeps the exact price $`j(a)`; since $`d\ge0`, the cap turns it into $`h\le aB+2ud`, which the
assembly `NaturalLatents.General.T_le_of_connected` (`NaturalLatents/General/Pricing.lean`) combines with the ledger and
the mismatch payment at $`a=211/45` and $`u=3941/20000`. Notation
follows section 0 of the [contact page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md); every logarithm is natural.

*What the cap is.* The price $`j(a)` is a value of the Gamma function. The proof expands it in a power series in
$`1/a` whose coefficients are the values $`\zeta(k)=\sum_{n\ge1}n^{-k}` of the Riemann zeta function $`\zeta`, keeps the terms $`k=2` and $`k=3`, dominates the
rest by a geometric series, and bounds $`\zeta(2)`, $`\zeta(3)` and $`\zeta(4)` by rational numbers obtained from
elementary sums and from $`\pi<3.1416`. The series and a sharp bound on $`\zeta(2)` are needed because the margin is
small: at $`a=211/45` the cap lies below $`u` by only $`48767743/2660574960000\approx1.8\cdot10^{-5}`, while
the cap itself exceeds the price, whose numerical value is $`j(211/45)\approx0.196778`, by about
$`2.5\cdot10^{-4}`. With the bound $`\zeta(2)<79/48` of (K33) at $`(k,N)=(2,4)` in place of $`533/324`, the same cap would be
$`93233145/472991104\approx0.197114`, above $`u`. The numerical values in this paragraph are for orientation
only; the pricing uses only the exact comparison of section 5.

Each lemma below states its hypotheses, so that it can be read alone. The lemmas are numbered K12 and K13 and the
equations (K32) to (K40a), continuing the numbering of the [race page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/race.md). Here $`F` is the cap, not the random
map of the [ledger page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/ledger.md); $`f` in the proof of Lemma K12 is the function $`x^{-k}`, and $`y`, $`k`, $`n`,
$`N` are local. Unless prefixed otherwise, the Lean declarations named
below are in the namespace `NaturalLatents.General`, in `NaturalLatents/General/Cap.lean`.

# 4. The universal cap

:::theorem "K12" (parent := "cap") (lean := "NaturalLatents.General.gamma_hasSum_product_remainder, NaturalLatents.General.gammaPriceCap_log_remainder_hasSum, NaturalLatents.General.cap_midpoint_three, NaturalLatents.General.cap_tail_three, NaturalLatents.General.cap_telescope_bound, NaturalLatents.General.cap_telescope_strict") (uses := "") (tags := "partly kernel-verified")
*Lemma K12 (log-Gamma series and strict midpoint bounds).* For $`0 < y < 1` and every $`a > 1`,
respectively,

$$`
\ln\Gamma(1-y)=\gamma_Ey+\sum_{k=2}^\infty\frac{\zeta(k)y^k}{k},
\qquad
j(a)=\sum_{k=2}^\infty\frac{\zeta(k)}{k\,a^{k-1}}.
\qquad \text{(K32)}
`

For every real $`k > 1` and integer $`N \ge 1`, with $`\zeta(k) = \sum_{n=1}^\infty n^{-k}`,

$$`
\zeta(k)<\sum_{n=1}^N n^{-k}
+\frac{1}{(k-1)(N+1/2)^{k-1}}.
\qquad \text{(K33)}
`
:::

:::proof "K12"
Lean proves: $`\ln\Gamma(1-y)-\gamma_Ey=\sum_{n\ge1}[-\ln(1-y/n)-y/n]` for $`y<1`, $`-\ln(1-x)-x=\sum_{k\ge2}x^k/k` for $`0\le x<1`, $`x^{-3}<\frac12(x-1/2)^{-2}-\frac12(x+1/2)^{-2}` for $`x\ge1`, and $`\sum_{n\ge3}n^{-3}<2/25`.

Expand log Gamma and the logarithm series; strict convexity on midpoint intervals bounds the zeta tail. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/cap.md#4-the-universal-cap).
:::

Lean: Lean states neither (K32) nor (K33) in this form. In place of (K32), `gamma_hasSum_product_remainder` states
$`\ln\Gamma(1-y)-\gamma_Ey=\sum_{n\ge1}\left[-\ln(1-y/n)-y/n\right]` for $`y<1`, obtained from Mathlib's
Bohr-Mollerup limit `Real.BohrMollerup.tendsto_log_gamma`, and `gammaPriceCap_log_remainder_hasSum` states the logarithm series
$`-\ln(1-x)-x=\sum_{k\ge2}x^k/k` for $`0\le x<1`; expanding each term of the first by the second and summing over
$`n` gives (K32), but Lean never forms the coefficients $`\zeta(k)` for $`k\ge5`. The midpoint estimate (K33) is stated
only for $`k=3`: `cap_midpoint_three` is the strict one-interval inequality, and `cap_tail_three` the tail bound
$`\sum_{n\ge3}n^{-3}<2/25`, through the telescoping lemmas `cap_telescope_bound` and `cap_telescope_strict`.

:::theorem "K13" (parent := "cap") (lean := "NaturalLatents.General.racePrice_lt_capC3b, NaturalLatents.General.gammaPriceCap_assemble_remainders, NaturalLatents.General.gammaPriceCap_reciprocal_conversion, NaturalLatents.General.cap_zeta_two, NaturalLatents.General.cap_zeta_three, NaturalLatents.General.cap_zeta_four, NaturalLatents.General.gammaPriceCap_log_remainder_le") (uses := "K12") (tags := "kernel-verified")
*Lemma K13 (the cap).* For every real $`a > 1`, define the explicit rational function

$$`
F(a)=\frac{533}{648a}+\frac{241}{600a^2}
+\frac{6503}{24000a^2(a-1)}.
\qquad \text{(K36)}
`

Then $`j(a) < F(a)`.
:::

:::proof "K13"
Bound the first zeta coefficients rationally and dominate the remaining coefficients by a geometric series. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/cap.md#4-the-universal-cap).
:::

Lean: `racePrice_lt_capC3b` states $`j(a)<F(a)` for every $`a>1`, with $`F` the function `gammaPriceCap`
(`NaturalLatents/General/Definitions.lean`). It runs through `gammaPriceCap_assemble_remainders` (the bound in the variable
$`y=1/a`) and `gammaPriceCap_reciprocal_conversion` (multiplication by $`a`), with the zeta bounds `cap_zeta_two`
($`\zeta(2)<533/324`), `cap_zeta_three` ($`\zeta(3)<241/200`, from `cap_tail_three`) and `cap_zeta_four`
($`\zeta(4)<6503/6000`). `cap_zeta_two` proves its bound as this page does, from Mathlib's `hasSum_zeta_two`
($`\zeta(2)=\pi^2/6`) and `Real.pi_lt_d4` ($`\pi<3.1416`). Lean bounds $`\zeta(4)` from Mathlib's `hasSum_zeta_four`
($`\zeta(4)=\pi^4/90`) and $`\pi^2<9.87`, not by the midpoint sum of (K37). Lean bounds the tail term by term
rather than through $`\zeta(k)\le\zeta(4)`: with $`x=y/n`, `gammaPriceCap_log_remainder_le` gives
$`-\ln(1-x)-x\le x^2/2+x^3/3+x^4/(4(1-x))`, then $`1-x\ge1-y`, and summing over $`n` gives the same
three terms with $`\zeta(2)`, $`\zeta(3)` and $`\zeta(4)` as coefficients.

# 5. Remark: the cap at a = 211/45

This remark is outside the proof of Lemma K13. For $`a = 211/45` and $`u = 3941/20000`, the
preceding universal lemma gives $`j(211/45) < F(211/45)`. Termwise substitution, with
$`a - 1 = 166/45`, is

$$`
\begin{aligned}
\frac{533}{648a}&=\frac{533\cdot45}{648\cdot211}=\frac{23985}{136728}=\frac{2665}{15192},\\
\frac{241}{600a^2}&=\frac{241\cdot45^2}{600\cdot211^2}=\frac{488025}{26712600}=\frac{6507}{356168},\\
\frac{6503}{24000a^2(a-1)}
&=\frac{6503\cdot45^3}{24000\cdot211^2\cdot166}
=\frac{592585875}{177371664000}=\frac{1580229}{472991104}.
\end{aligned}
\qquad \text{(K39a)}
`

The three reduced denominators are $`15192=2^3\cdot3^2\cdot211`, $`356168=2^3\cdot211^2` and
$`472991104=2^7\cdot83\cdot211^2`, so their least common multiple is $`2^7\cdot3^2\cdot83\cdot211^2=4256919936`, with
multipliers $`280208`, $`11952` and $`9`. Common-denominator arithmetic gives

$$`
\begin{aligned}
F(211/45)
&=\frac{2665}{15192}+\frac{6507}{356168}+\frac{1580229}{472991104}\\
&=\frac{2665\cdot280208+6507\cdot11952+1580229\cdot9}{4256919936}\\
&=\frac{746754320+77771664+14222061}{4256919936}
=\frac{838748045}{4256919936}.
\end{aligned}
\qquad \text{(K39)}
`

The strict comparison and reduced margin are

$$`
\begin{aligned}
&20000\cdot838748045=16774960900000<16776521467776=3941\cdot4256919936,\\
&3941\cdot4256919936-20000\cdot838748045=1560567776>0,\qquad
\frac{3941}{20000}-F(211/45)=\frac{48767743}{2660574960000}>0.
\end{aligned}
\qquad \text{(K40)}
`

The exact margin reduction is

$$`
1560567776=32\cdot48767743,\qquad
20000\cdot4256919936=85138398720000=32\cdot2660574960000.
\qquad \text{(K40a)}
`

Thus the full cap lies strictly between $`j(211/45)` and $`3941/20000`. This remark supplies pricing
arithmetic only; it does not change the universal statement of Lemma K13.

Lean: inside `T_le_of_connected` (`NaturalLatents/General/Pricing.lean`), `racePrice_lt_capC3b` at `211/45` followed
by `norm_num [gammaPriceCap]` proves `gammaPrice (211/45) < 3941/20000`; the intermediate fractions of (K39a) to (K40a) are not stated.
