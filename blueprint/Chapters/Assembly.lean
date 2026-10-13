import Verso
import VersoManual
import VersoBlueprint
import NaturalLatents.Main

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "The pricing" =>

:::group "assembly"
The pricing.
:::

This page proves the pricing: for a law with connected support, the setup, the ledger, the race, the cap and the mismatch
payment combine linearly into $`T(p)\le C\tau(p)` with $`C=\max\{C_M,C_B\}` (Lemma M5.1), and at the parameters
$`(a,u,\beta,\gamma)=(211/45,3941/20000,23/250,7/60)` the stated constant $`13999/2000`
dominates both coefficients (Lemma M5.4). Both conclusions are for laws with connected support only. This is the assembly
itself: Lemma M5.4 is the Lean theorem `NaturalLatents.General.T_le_of_connected` (`NaturalLatents/General/Pricing.lean`),
step 8 of the [route](https://github.com/AlexisOlson/natural-latents/blob/main/docs/overview.md#the-route). Notation follows section 0 of the [contact page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md).

# 5. The pricing

> *Pricing.* At the parameters of Lemma M5.4, given the setup, the ledger, the race and its cap, and the mismatch
> payment with $`PC(23/250,7/60)`, the inequality $`T(p)\le(13999/2000)\,\tau(p)` holds for every law
> $`p` whose support is connected.

The components named in the statement are proved on other pages; this page supplies no new proof of the pair charge,
the ledger, the race, the cap or the setup. The calibrated family, $`h`, $`d` and $`j(a)` are those of section 1 of
the [race page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/race.md), equation (R1), and of (D3); $`d\ge0`, and the conditional entropies in $`h` are evaluated at
each fixed seed and then averaged, so no unconditional label entropy is used. Combining a ledger with a race in this way
is the method of pull request #6 by Jeremy Gillen to DLorell/stoch_to_det: powered-reference race coding with a
coordinate ledger (see the [upstream page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/upstream.md)).

:::theorem "M5.1" (parent := "assembly") (uses := "S1.3, S1.4, L4.1, R11, P5.5") (tags := "paper proof")
*Lemma M5.1 (generic assembly).* For every finite nonempty $`X,Y`, every law $`p` whose support is connected, and every
real $`a,u,\beta,\gamma` with $`a>1`, $`u\ge0`, $`\beta\ge0`, $`\gamma>0`, suppose the setup (Lemma S1.4 of the
[setup page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/setup.md)) supplies an attained latent with $`M+B=\tau(p)`, positive priors, posterior rows positive on
the support, and distinct components that are positive contacts of one feasible kernel on the support; the race uses
the positive posterior rows, and the payment uses the priors and the contacts. Suppose the ledger (Lemma L4.1 of the
[ledger page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/ledger.md)), the race (Lemma R11 of the [race page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/race.md)) and the mismatch payment (Lemma P5.5 of the
[payment page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/payment.md)) supply a calibrated family satisfying

$$`
T(p)\le M-\frac B2+\frac{3h}{2},\qquad
h\le aB+2j(a)d,\qquad
\gamma d\le(1+2\beta)M+\beta B,\qquad
M\ge0,\quad B\ge0,\quad d\ge0.
\qquad \text{(M5.C)}
`

Assume a cap gives $`u>j(a)`, and that the pair charge used by the payment is $`PC(\beta,\gamma)`. Then

$$`
T(p)\le C\,\tau(p),\qquad
C=\max\left\{1+\frac{3u(1+2\beta)}{\gamma},
                 \frac{3a-1}{2}+\frac{3u\beta}{\gamma}\right\}.
\qquad \text{(M5.D)}
`
:::

:::proof "M5.1"
Substitute the race and cap into the ledger, multiply the mismatch payment by the nonnegative price factor, and dominate both budgets by the maximum coefficient. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/assembly.md#5-the-pricing).
:::

Lean: no generic theorem; the calculation (M5.E) is carried out inside `NaturalLatents.General.T_le_of_connected` at its
fixed parameters, by `linarith` from `T_le_ledger`, the race bound of `exists_race`, the cap, `mismatch_payment` and the
sign facts. The affinity hypothesis of `mismatch_payment` is discharged by `affinity_bound` applied to `contact_moments`
for each pair of distinct components of the setup latent, and its replica hypothesis by `replica_budget`.

*Remark M5.2 (the cap evaluation at a = 211/45).* The cap premise is, for every $`a>1`, $`j(a)<F(a)`, with all three
terms of the cap $`F` of Lemma K13 on the [cap page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/cap.md) shown:

$$`
\begin{aligned}
F(a)&=\frac{533}{648a}+\frac{241}{600a^2}
             +\frac{6503}{24000a^2(a-1)},\\
F(211/45)&=\frac{2665}{15192}+\frac{6507}{356168}
                +\frac{1580229}{472991104}
          =\frac{838748045}{4256919936},\\
\frac{3941}{20000}-F(211/45)&=\frac{48767743}{2660574960000}>0 .
\end{aligned}
\qquad \text{(M5.F)}
`

Thus $`j(211/45)<3941/20000`. This is point arithmetic for the universal cap, not a new cap proof; the
termwise substitution is displayed in section 5 of the [cap page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/cap.md).

Lean: `racePrice_lt_capC3b` at `211/45` followed by `norm_num [gammaPriceCap]` inside `T_le_of_connected`, the step
`hj`.

:::theorem "M5.4" (parent := "assembly") (lean := "NaturalLatents.General.T_le_of_connected") (uses := "S1.4, L4.1, R11, K13, A2.2, Q3.1, P5.5, PC5.3, M5.1") (tags := "kernel-verified")
*Lemma M5.4 (the specialization).* For every finite law with connected support, satisfying the setup, ledger, race,
payment and cap inputs, the pair charge $`PC(23/250,7/60)` gives

$$`
\begin{aligned}
a&=\frac{211}{45}>1,\quad u=\frac{3941}{20000}>0,\quad
\beta=\frac{23}{250}\ge0,\quad\gamma=\frac7{60}>0,\quad
\frac{3u}{\gamma}=\frac{5067}{1000},\\
C_M&=1+\frac{5067}{1000}\cdot\frac{148}{125}
     =\frac{218729}{31250},\qquad
C_B=\frac{98}{15}+\frac{5067}{1000}\cdot\frac{23}{250}
     =\frac{5249623}{750000},\\
C_B-C_M&=\frac{127}{750000}>0,\qquad
\frac{13999}{2000}-C_B=\frac1{375000}>0,\qquad
7-\frac{13999}{2000}=\frac1{2000}>0,\\
T(p)&\le\frac{13999}{2000}\,\tau(p).
\end{aligned}
\qquad \text{(M5.H)}
`
:::

:::proof "M5.4"
Evaluate the cap at the selected exponent and compute both pricing coefficients exactly, then use their positive margins below the stated constant. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/assembly.md#5-the-pricing).
:::

Lean: `NaturalLatents.General.T_le_of_connected` (`NaturalLatents/General/Pricing.lean`) is Lemma M5.4, in nats and for a
law with connected support only; it states `TNat p ≤ (13999/2000 : ℝ) * tauNat p`. Its proof consists of:

- `exists_race` at `211/45`, and `hj : gammaPrice (211/45) < 3941/20000` from `racePrice_lt_capC3b` and
  `norm_num [gammaPriceCap]`;
- the race bound `hh` with `211/45` and `3941/20000`;
- `mismatch_payment` at `(23/250) (7/60)` with `pairCharge_C`;
- `hM : 0 ≤ mediation D.L` and `hB : 0 ≤ redundancy D.L`, from `stoch_to_det.condMI_nonneg` through `nats_nonneg_iff`,
  both passed to the final `linarith`, since
  $`13999/2000` exceeds both $`C_M` and $`C_B` (the proof of Lemma M5.4).

The constant `NaturalLatents.c := 13999 / 2000` and `NaturalLatents.T_le_mul_tau` are in `NaturalLatents/Main.lean`, and
`Verify.lean` pins `T_le_mul_tau` with an example at `13999 / 2000`.

The extension to every finite law is not in `Pricing.lean`: `NaturalLatents.T_le_c_mul_tau` (`NaturalLatents/Main.lean`)
converts the bound of `T_le_of_connected` to bits by `bits_of_nats` (`NaturalLatents/General/Nats.lean`) and applies
`extension_of_connected`, stated in bits, with `c_nonneg`.
