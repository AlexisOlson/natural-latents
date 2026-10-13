# The pricing

This page proves the pricing: for a law with connected support, the setup, the ledger, the race, the cap and the mismatch
payment combine linearly into $`T(p)\le C\tau(p)`$ with $`C=\max\{C_M,C_B\}`$ (Lemma M5.1), and at the parameters
$`(a,u,\beta,\gamma)=(211\text/45,3941\text/20000,23\text/250,7\text/60)`$ the stated constant $`13999\text/2000`$
dominates both coefficients (Lemma M5.4). Both conclusions are for laws with connected support only. This is the assembly
itself: Lemma M5.4 is the Lean theorem `NaturalLatents.General.T_le_of_connected` (`NaturalLatents/General/Pricing.lean`),
step 8 of the [route](overview.md#the-route). Notation follows section 0 of the [contact page](contact.md).

## 5. The pricing

> **Pricing.** At the parameters of Lemma M5.4, given the setup, the ledger, the race and its cap, and the mismatch
> payment with $`PC(23\text/250,7\text/60)`$, the inequality $`T(p)\le(13999\text/2000)\,\tau(p)`$ holds for every law
> $`p`$ whose support is connected.

The components named in the statement are proved on other pages; this page supplies no new proof of the pair charge,
the ledger, the race, the cap or the setup. The calibrated family, $`h`$, $`d`$ and $`j(a)`$ are those of section 1 of
the [race page](race.md), equation (R1), and of (D3); $`d\ge0`$, and the conditional entropies in $`h`$ are evaluated at
each fixed seed and then averaged, so no unconditional label entropy is used. Combining a ledger with a race in this way
is the method of pull request #6 by Jeremy Gillen to DLorell/stoch_to_det: powered-reference race coding with a
coordinate ledger (see the [upstream page](upstream.md)).

**Lemma M5.1 (generic assembly).** For every finite nonempty $`X,Y`$, every law $`p`$ whose support is connected, and every
real $`a,u,\beta,\gamma`$ with $`a>1`$, $`u\ge0`$, $`\beta\ge0`$, $`\gamma>0`$, suppose the setup (Lemma S1.4 of the
[setup page](setup.md)) supplies an attained latent with $`M+B=\tau(p)`$, positive priors, posterior rows positive on
the support, and distinct components that are positive contacts of one feasible kernel on the support; the race uses
the positive posterior rows, and the payment uses the priors and the contacts. Suppose the ledger (Lemma L4.1 of the
[ledger page](ledger.md)), the race (Lemma R11 of the [race page](race.md)) and the mismatch payment (Lemma P5.5 of the
[payment page](payment.md)) supply a calibrated family satisfying

```math
T(p)\le M-\frac B2+\frac{3h}{2},\qquad
h\le aB+2j(a)d,\qquad
\gamma d\le(1+2\beta)M+\beta B,\qquad
M\ge0,\quad B\ge0,\quad d\ge0.
\qquad \text{(M5.C)}
```

Assume a cap gives $`u>j(a)`$, and that the pair charge used by the payment is $`PC(\beta,\gamma)`$. Then

```math
T(p)\le C\,\tau(p),\qquad
C=\max\left\{1+\frac{3u(1+2\beta)}{\gamma},
                 \frac{3a-1}{2}+\frac{3u\beta}{\gamma}\right\}.
\qquad \text{(M5.D)}
```

*Proof.* Conditional mutual information is an average of divergences from conditional product laws, hence nonnegative by
Gibbs' inequality, (S1.P) on the [setup page](setup.md); this supplies $`M,B\ge0`$. Posterior rows are probability
vectors, so $`\sum_ir_z(i)^2\le\sum_ir_z(i)=1`$, supplying $`d\ge0`$. Substitute the race bound into the ledger, use
$`j(a)d\le ud`$, and multiply the payment inequality by the nonnegative number $`3u\text/\gamma`$. The complete chain is

```math
\begin{aligned}
T(p)&\le M-\frac B2+\frac32(aB+2j(a)d)\\
    &=M+\frac{3a-1}{2}B+3j(a)d\\
    &\le M+\frac{3a-1}{2}B+3ud\\
    &\le \left[1+\frac{3u(1+2\beta)}{\gamma}\right]M
        +\left[\frac{3a-1}{2}+\frac{3u\beta}{\gamma}\right]B\\
    &\le C(M+B)=C\tau(p).
\end{aligned}
\qquad \text{(M5.E)}
```

The maximum dominates both coefficients because $`M,B\ge0`$. Only the known positive parameter $`\gamma`$ is divided by.
The argument remains valid when $`u=0`$, $`d=0`$, either budget is zero, or $`\tau(p)=0`$. $`\square`$

Here $`PC(\beta,\gamma)`$ is the pair charge of section 0 of the [contact page](contact.md), on every two distinct positive
contacts of one feasible kernel on a common support, holes allowed; at $`(\beta,\gamma)=(23\text/250,7\text/60)`$ it is
Theorem PC5.3 of the [pair-charge page](pair-charge.md).

Lean: no generic theorem; the calculation (M5.E) is carried out inside `NaturalLatents.General.T_le_of_connected` at its
fixed parameters, by `linarith` from `T_le_ledger`, the race bound of `exists_race`, the cap, `mismatch_payment` and the
sign facts. The affinity hypothesis of `mismatch_payment` is discharged by `affinity_bound` applied to `contact_moments`
for each pair of distinct components of the setup latent, and its replica hypothesis by `replica_budget`.

**Remark M5.2 (the cap evaluation at a = 211/45).** The cap premise is, for every $`a>1`$, $`j(a)<F(a)`$, with all three
terms of the cap $`F`$ of Lemma K13 on the [cap page](cap.md) shown:

```math
\begin{aligned}
F(a)&=\frac{533}{648a}+\frac{241}{600a^2}
             +\frac{6503}{24000a^2(a-1)},\\
F(211\text/45)&=\frac{2665}{15192}+\frac{6507}{356168}
                +\frac{1580229}{472991104}
          =\frac{838748045}{4256919936},\\
\frac{3941}{20000}-F(211\text/45)&=\frac{48767743}{2660574960000}>0 .
\end{aligned}
\qquad \text{(M5.F)}
```

Thus $`j(211\text/45)<3941\text/20000`$. This is point arithmetic for the universal cap, not a new cap proof; the
termwise substitution is displayed in section 5 of the [cap page](cap.md).

Lean: `racePrice_lt_capC3b` at `211/45` followed by `norm_num [gammaPriceCap]` inside `T_le_of_connected`, the step
`hj`.

**Lemma M5.4 (the specialization).** For every finite law with connected support, satisfying the setup, ledger, race,
payment and cap inputs, the pair charge $`PC(23\text/250,7\text/60)`$ gives

```math
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
```

*Proof.* Remark M5.2 verifies the strict cap premise at the selected tuple. Lemma M5.1 and the exact arithmetic in (M5.H)
give $`C=C_B=5249623\text/750000`$. The stated constant $`c=13999\text/2000`$ is larger than both coefficients, so the
last line of (M5.E), taken at $`c`$ instead of $`C`$, reads

```math
T(p)\le C_M\,M+C_B\,B
=c\,(M+B)-(c-C_M)\,M-(c-C_B)\,B
\le c\,\tau(p),
\qquad c-C_M=\frac{43}{250000},\quad c-C_B=\frac1{375000}.
```

Both subtracted coefficients are positive, so this step uses $`M\ge0`$ and $`B\ge0`$. Had the constant been stated at
exactly $`C_B`$, the $`B`$ term would vanish and $`M\ge0`$ alone would suffice. The bound needs no case split: when
$`\tau(p)=0`$ it reads $`T(p)\le0`$. $`\square`$

**Remark (every finite law).** Lemma M5.4 concerns laws with connected support. Lemma E3.4 of the
[extension page](extension.md), with $`c\ge0`$, extends its conclusion to every finite law.

All $`H,I,D,M,B,T,\tau,h`$ and $`j`$ here are in nats; $`d`$ is a probability. The race price $`u`$ has the same entropy
unit as $`j`$, $`\gamma`$ the unit of the pair charge's information terms, and $`a,\beta,C`$ are dimensionless. Dividing
every information quantity, $`u`$ and $`\gamma`$ by $`\ln2`$ preserves the displayed inequalities and the coefficients
in (M5.D). Thus the final $`T\le C\tau`$ is invariant under passage to bits.

Lean: `NaturalLatents.General.T_le_of_connected` (`NaturalLatents/General/Pricing.lean`) is Lemma M5.4, in nats and for a
law with connected support only; it states `TNat p ≤ (13999/2000 : ℝ) * tauNat p`. Its proof consists of:

- `exists_race` at `211/45`, and `hj : gammaPrice (211/45) < 3941/20000` from `racePrice_lt_capC3b` and
  `norm_num [gammaPriceCap]`;
- the race bound `hh` with `211/45` and `3941/20000`;
- `mismatch_payment` at `(23/250) (7/60)` with `pairCharge_C`;
- `hM : 0 ≤ mediation D.L` and `hB : 0 ≤ redundancy D.L`, from `stoch_to_det.condMI_nonneg` through `nats_nonneg_iff`,
  both passed to the final `linarith`, since
  $`13999\text/2000`$ exceeds both $`C_M`$ and $`C_B`$ (the proof of Lemma M5.4).

The constant `NaturalLatents.c := 13999 / 2000` and `NaturalLatents.T_le_mul_tau` are in `NaturalLatents/Main.lean`, and
`Verify.lean` pins `T_le_mul_tau` with an example at `13999 / 2000`.

The extension to every finite law is not in `Pricing.lean`: `NaturalLatents.T_le_c_mul_tau` (`NaturalLatents/Main.lean`)
converts the bound of `T_le_of_connected` to bits by `bits_of_nats` (`NaturalLatents/General/Nats.lean`) and applies
`extension_of_connected`, stated in bits, with `c_nonneg`.
