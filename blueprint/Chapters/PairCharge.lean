import Verso
import VersoManual
import VersoBlueprint
import NaturalLatents.Main

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "The pair charge" =>

:::group "pair-charge"
The pair charge.
:::

This page proves the pair charge $`PC(23/250,7/60)` of section 0 of the [contact page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md), in
strict form: for every two distinct positive contacts $`P,R` of one feasible kernel on a common support $`S`, holes
allowed,

$$`
\frac{I(P)+I(R)}2+\frac{23}{250}\Psi(s)>\frac7{60},\qquad \Psi(s)=-2\ln b(s),\quad b(s)=1-\frac{9s}{16}+\frac{3s^2}{64},
`

with $`s` the separation of (C1.3) and $`b`, $`\Psi` as in (A2.1) of the [affinity page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/affinity.md). For
$`0<s\le1` an entropy payment for one explicit statistic bounds the averaged information below (section 4), and a
scalar certificate closes the charge (section 5); for $`1\le s<2` the separation price alone pays. The charge is the
hypothesis $`PC` of the mismatch payment, which turns it into $`\gamma d\le(1+2\beta)M+\beta B` for the setup latent (step 6 of the
[route](https://github.com/AlexisOlson/natural-latents/blob/main/docs/overview.md#the-route)), and its two parameters $`(\beta,\gamma)=(23/250,7/60)`
enter the pricing of the constant. In the assembly `NaturalLatents.General.T_le_of_connected`
(`NaturalLatents/General/Pricing.lean`), the `HasPairCharge` hypothesis of `mismatch_payment` (`NaturalLatents/General/Payment.lean`)
is discharged by the pair-charge theorem `pairCharge_C`.

Lemma PC4.0 and Theorem PC5.3 state the standing hypotheses in full; Lemmas PC4.1 to PC4.5 refer to Lemma PC4.0,
and the scalar Lemmas PC5.1 and PC5.2 state their ranges. Unless prefixed `stoch_to_det`, the Lean
declarations named below are in the namespace `NaturalLatents.General`; the `stoch_to_det` declarations are in
`NaturalLatents/Upstream/`, adapted from [DLorell/stoch_to_det](https://github.com/DLorell/stoch_to_det). The Lean proof
of this charge is complete; its declarations are in `NaturalLatents/General/PairCharge.lean` and the modules
`PairCharge/Gram.lean`, `Features.lean`, `MomentBounds.lean`, `Information.lean`, `Correction.lean` and
`Certificate.lean`.

# 4. Pair information from a positive quadratic form

*Setting.* Units and conventions are those of section 0 of the [contact page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md): logarithms are natural and
$`I(P)=D(P\Vert P_X\otimes P_Y)` as in (D2). Fix finite nonempty alphabets $`X,Y`, a nonempty support
$`S\subseteq X\times Y` with all rows and columns used, a feasible kernel $`w>0` on $`S` as in (C1.1), and two distinct
positive contacts $`P,R` of $`w` as in (C1.2). Extend both laws by zero to the rectangle $`X\times Y`; its cells outside
$`S` are the holes. The fields $`f,g,U,V,A_0,B_0,s,J` are those of (C1.3), and an unmarked expectation is under $`P`.
Every marginal probability of a used symbol is positive, so $`f` and $`g` are positive and finite on every row and
column, every field below is finite on every cell of the rectangle, holes included, and both contacts have positive
marginals on every used symbol. Put

$$`
\begin{aligned}
z&=\frac{A_0-B_0}s,&v&=\frac{A_0B_0}{s^2}=\frac{1-z^2}4,&j&=\frac J{s^2},\\
\eta&=\frac{1+sj}4,&y&=1-s+sj,&t_0&=\frac12-j-\frac32z^2,
\end{aligned}
\qquad
D_X=E[V^2\mid X],\quad D_Y=E[U^2\mid Y].
\qquad \text{(PC4.1)}
`

Some letters are local to this page: $`z` is an asymmetry and $`y` a scalar, not a cell or a column symbol;
$`w_X,w_Y` below are fields, not the kernel $`w`; $`h` below is a cross moment, not the seed entropy $`h`; unadorned
$`D` denotes the integrated variance, while $`D(\cdot\Vert\cdot)` denotes relative entropy; $`u` is a mixing parameter
and $`v` a scalar, not the probability vectors of (C1.1) or the price bound $`u` of the [cap page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/cap.md);
$`j=J/s^2` is not the race price $`j(a)`; $`d_X,d_Y` are fields, not the mismatch $`d`; $`Q` is a product law
and $`W` a statistic, not the reference $`Q` or the winner $`W` of the [race page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/race.md); $`K(u)` in the proof of Lemma PC4.5 is a
relative entropy, not the replica budget $`K`, and $`\tau` in its Lean note is a real parameter; $`F`, $`F_l`,
$`F_m`, $`F_h` in section 5 are scalar functions, not the cap $`F`; $`M_l,M_m,M_h` are polynomials, not the budget
$`M`; and $`\beta,\gamma` are the charge pair of section 0 of the contact page, while $`\alpha,\kappa,\lambda,k,c_0`
are local coefficients.

:::theorem "PC4.0" (parent := "pair-charge") (lean := "NaturalLatents.General.contact_moments, NaturalLatents.General.contact_hessian, NaturalLatents.General.pairCharge_contact_defect_X, NaturalLatents.General.pairCharge_contact_defect_Y, NaturalLatents.General.pairCharge_contact_defects_centered, NaturalLatents.General.pairCharge_contact_gram_energy, NaturalLatents.General.pairCharge_quarticRatio_bounds, NaturalLatents.General.defect_bounds, NaturalLatents.General.pairCharge_secant_mixed_moments") (uses := "C1.1, C1.2, C1.4, C1.5") (tags := "partly kernel-verified")
*Lemma PC4.0 (the moment inputs).* For every finite nonempty $`X,Y`, every nonempty $`S` with all rows and columns used,
every feasible $`w>0` on $`S`, and every pair of distinct positive contacts $`P,R` of $`w`, the quantities (C1.3) and
(PC4.1) satisfy $`0<A_0,B_0<1`, $`0<s<2`, $`v\le1/4`,

$$`
EU=-A_0,\quad EV=-B_0,\quad EU^2=2A_0-B_0,\quad EV^2=2B_0-A_0,\quad E[UV]=s\eta,\quad E[UV(U+V)]=-J,
\qquad \text{(PC4.M)}
`

and the centered conditionals $`2E[V\mid X]+D_X=U` and $`2E[U\mid Y]+D_Y=V` on used rows and columns. For every pair of
real marginal fields $`e_X` on $`X` and $`e_Y` on $`Y` with $`Ee_X=Ee_Y=0`,

$$`
\mathcal Q(e):=Ee_X^2+Ee_Y^2-4E[e_Xe_Y]\ge0.
\qquad \text{(PC-H)}
`

The fields $`w_X=U+A_0`, $`w_Y=V+B_0`, $`d_X=D_X-(2B_0-A_0)` and $`d_Y=D_Y-(2A_0-B_0)` are centered and satisfy

$$`
d_X=w_X-2E[w_Y\mid X],\qquad d_Y=w_Y-2E[w_X\mid Y],
\qquad \text{(PC-C)}
`

and $`\mathcal Q(w)=s^2t_0`, so that $`t_0\ge0`, $`j\le1/2` and $`1/16\le\eta^2\le j`.
:::

:::proof "PC4.0"
Lean proves: the `ContactMoments` identities and bounds, the Hessian inequality (PC-H), the centered defect identities (PC-C), $`\mathcal Q(w)=6A_0B_0-s^2-J`, $`1/16\le j\le1/2`, $`2/9\le v\le1/4`, and the two mixed moments whose sum is $`E[UV(U+V)]=-J`.

Combine the contact moments and Hessian test with centering, conditional expansions, and Cauchy-Schwarz. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/pair-charge.md#4-pair-information-from-a-positive-quadratic-form).
:::

Lean: `contact_moments` (`NaturalLatents/General/Contact.lean`) supplies the conditional and moment identities of
(C1.4), the energy and quartic identities, $`0<s<2` and $`J\le6A_0B_0-s^2`; the Hessian test (PC-H) is `contact_hessian`
(same file); the identities (PC-C) are
`pairCharge_contact_defect_X` and `pairCharge_contact_defect_Y`, the centering of $`d_X,d_Y` is
`pairCharge_contact_defects_centered`, and $`\mathcal Q(w)=6A_0B_0-s^2-J` is `pairCharge_contact_gram_energy`, all in
`NaturalLatents/General/PairCharge/Gram.lean`; the bounds on $`j` and $`v` are `pairCharge_quarticRatio_bounds` and
`defect_bounds` (`NaturalLatents/General/PairCharge/MomentBounds.lean`). The identity $`E[UV(U+V)]=-J` is the sum of the
two parts of `pairCharge_secant_mixed_moments` (`MomentBounds.lean`), which states $`E[UV^2]` and $`E[U^2V]` separately; (PC-C) is stated at used rows and columns, with conditional expectations written as quotients of sums;
and `defect_bounds` also proves $`v\ge2/9`, which this page does not use.

## 4.1 Reversal and a corrected statistic

The reversed orientation takes $`R` as reference and $`P` as the second contact; its quantities carry a prime. In each
orientation, $`Q` is the product of the reference marginals, positive on every cell of the rectangle, and
$`P_u=(1-u)Q+uP` (with $`R` in place of $`P` for the reversed orientation). An overbar averages a quantity over the
two orientations with weight one half; in the reversed orientation $`E_P` becomes $`E_R` and $`E_Q` becomes the
expectation under $`R_X\otimes R_Y`. Define

$$`
\begin{aligned}
W&=\frac{(U+s/5)(V+s/5)}s,&\Theta&=\frac{D_X+D_Y}s-1,\\
\lambda&=\frac{27-55s}{40},\quad k=13\lambda+2s,\quad c_0=\frac32-\frac s2,&W_u&=W-\lambda u\Theta,\\
\mathrm{Res}&=\overline{\int_0^1(1-u)\mathrm{Var}_{P_u}W_u\,du}.
\end{aligned}
\qquad \text{(PC4.2)}
`

The correction leaves the expectation gap between the contact and the product law unchanged: $`\Theta` has zero mean
under both $`P` and $`Q` (PC4.B), so $`E_PW_u-E_QW_u=E_PW-E_QW` for every $`u`. On $`0<s\le1` the Hessian test
(PC-H) then bounds the integrated variance $`\mathrm{Res}` by $`\mathrm{Den}(s,j)/192` (Lemma PC4.4), and
Cauchy–Schwarz turns the gap into the information floor (PC-FLOOR) of Lemma PC4.5.

:::theorem "PC4.1" (parent := "pair-charge") (lean := "NaturalLatents.General.pairCharge_mean_losses_reverse, NaturalLatents.General.pairCharge_separation_reverse, NaturalLatents.General.pairCharge_quarticMoment_reverse, NaturalLatents.General.pairCharge_quarticRatio_reverse, NaturalLatents.General.pairCharge_defectProductRatio_reverse, NaturalLatents.General.pairCharge_pair_reverse, NaturalLatents.General.pairCharge_cond_defect_X_reverse, NaturalLatents.General.pairCharge_cond_defect_Y_reverse, NaturalLatents.General.pairCharge_fixed_coefficient_data, NaturalLatents.General.pairCharge_fixed_endpoint_table") (uses := "PC4.0, C1.1, C1.2") (tags := "partly kernel-verified")
*Lemma PC4.1 (reversal and raw moments).* Under the hypotheses of Lemma PC4.0,

$$`
U'=-\frac Uf,\quad V'=-\frac Vg,\quad D_X'=\frac{D_X}f,\quad D_Y'=\frac{D_Y}g,\quad J'=J,\quad A_0'=B_0,\quad B_0'=A_0,
`

so $`s,j,z^2,v,t_0,\eta,y` are common to both orientations. With $`\mu_Q=E_QW` and $`\mu_P=E_PW`,

$$`
\begin{aligned}
\mu_Q&=s\left(v-\frac4{25}\right),\qquad \mu_P=\eta-\frac{4s}{25},\\
E_QW^2&=\frac{[(2A_0-B_0)-2sA_0/5+s^2/25][(2B_0-A_0)-2sB_0/5+s^2/25]}{s^2},\\
E_PW^2&=\frac{J+(2s/5)(-J)+(s^2/25)(s+4s\eta)-2s^4/125+s^4/625}{s^2},
\end{aligned}
\qquad \text{(PC-W)}
`

and in terms of $`s,j,z` these read

$$`
\mu_Q=\frac{s(1-z^2)}4-\frac{4s}{25},\quad \mu_P=\frac{1+sj}4-\frac{4s}{25},\quad
E_QW^2=\left(\frac12-\frac{4s}{25}\right)^2-z^2\left(\frac32-\frac s5\right)^2,\quad
E_PW^2=j\left(1-\frac s5\right)^2+\frac{2s}{25}-\frac{9s^2}{625}.
`

All four are invariant under reversal.
:::

:::proof "PC4.1"
Lean proves: reversal of $`A_0,B_0,s,J,j,v` and the conditional defects, the endpoint moments of $`UV` and $`U+V+s`, and the mean gap and collected algebraic variance of the statistic $`W+4s/25`.

Change measure under contact reversal and expand the first and second moments under the contact and product laws. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/pair-charge.md#41-reversal-and-a-corrected-statistic).
:::

Lean: `pairCharge_mean_losses_reverse`, `pairCharge_separation_reverse`, `pairCharge_quarticMoment_reverse`, `pairCharge_quarticRatio_reverse`,
`pairCharge_defectProductRatio_reverse` and `pairCharge_pair_reverse` (`NaturalLatents/General/PairCharge/MomentBounds.lean`) and
`pairCharge_cond_defect_X_reverse`, `pairCharge_cond_defect_Y_reverse`
(`NaturalLatents/General/PairCharge/Features.lean`); `pairCharge_fixed_coefficient_data` (`MomentBounds.lean`) at
coefficient $`1/5` gives the mean gap and the integrated variance $`D` of Lemma PC4.3, from the component moments of
$`UV` and $`U+V+s` under $`P` and $`Q` in `pairCharge_fixed_endpoint_table` (`MomentBounds.lean`). Lean does not state
the four raw moments (PC-W) themselves, but states $`D` directly in a collected form in $`s,j,v`, and its statistic is
$`UV/s+(U+V+s)/5=W+4s/25`, a constant shift that changes no gap, variance or product with $`\Theta`.

## 4.2 Correction products

In one orientation put

$$`
\rho=Ed_X^2+Ed_Y^2,\qquad h=E[d_Xd_Y],\qquad H_0=\frac{UV}s.
`

Since $`d_X+d_Y=D_X+D_Y-s`, the correction field is $`\Theta=(d_X+d_Y)/s`.

:::theorem "PC4.2" (parent := "pair-charge") (lean := "NaturalLatents.General.pairCharge_correction_eq, NaturalLatents.General.pairCharge_correction_means, NaturalLatents.General.pairCharge_defect_products, NaturalLatents.General.pairCharge_correction_second_moments, NaturalLatents.General.pairCharge_linear_correction, NaturalLatents.General.pairCharge_statistic_correction_average, NaturalLatents.General.pairCharge_secantStatistic_correction_product, NaturalLatents.General.pairCharge_secantStatistic_correction_joint") (uses := "PC4.0, PC4.1, C1.1") (tags := "kernel-verified")
*Lemma PC4.2 (correction products).* Under the hypotheses of Lemma PC4.0, in each orientation,

$$`
\begin{aligned}
E[w_Xd_X+w_Yd_Y]&=s^2t_0,\qquad E[w_Xd_Y+w_Yd_X]=\frac{s^2t_0-\rho}2,
&&\text{(PC4.D)}\\
E_P\Theta&=E_Q\Theta=0,\qquad E_Q\Theta^2=\frac\rho{s^2},\qquad E_P\Theta^2=\frac{\rho+2h}{s^2},
&&\text{(PC4.B)}\\
E_Q[(w_X+w_Y)\Theta]+E_P[(w_X+w_Y)\Theta]&=\frac{5s^2t_0-\rho}{2s},
&&\text{(PC4.L)}
\end{aligned}
`

and, averaged over the two orientations,

$$`
\overline{E_Q(W\Theta)+E_P(W\Theta)}=j\left(1-\frac s4\right)-\frac14+c_0z^2-\frac{\bar\rho}{10s}.
\qquad \text{(PC-X)}
`
:::

:::proof "PC4.2"
Use centered conditional defects for the linear products and a paired change of measure for the nonlinear correction product. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/pair-charge.md#42-correction-products).
:::

Lean: `pairCharge_correction_eq` and `pairCharge_correction_means` (the form and means of $`\Theta`),
`pairCharge_defect_products` (PC4.D), `pairCharge_correction_second_moments` (PC4.B) and `pairCharge_linear_correction`
(PC4.L), all in `NaturalLatents/General/PairCharge/Correction.lean`, which write $`s^2t_0` as $`6A_0B_0-s^2-J`; and
`pairCharge_statistic_correction_average` (PC-X) (`NaturalLatents/General/PairCharge.lean`), with the statistic
$`W+4s/25` and $`\bar\rho/(10s)` written as $`(\rho+\rho')/(20s)`. Its proof uses
`pairCharge_secantStatistic_correction_product` (`NaturalLatents/General/PairCharge/Features.lean`), which states $`E_Q[H_0\Theta]` in the
equivalent form $`3z^2/2+J/(2s)-A_0B_0/s`, and `pairCharge_secantStatistic_correction_joint` (same file), which states the
one-orientation product $`E_P[H_0\Theta]` in a form that keeps the terms $`E[UD_X^2]` and $`E[VD_Y^2]`.

## 4.3 Integrated residual

Let

$$`
D=\frac{2E_QW^2+E_PW^2}6-\frac{3\mu_Q^2+2\mu_Q\mu_P+\mu_P^2}{12}.
`

:::theorem "PC4.3" (parent := "pair-charge") (lean := "NaturalLatents.General.pairCharge_residual_information, NaturalLatents.General.pairCharge_correction_hessian, NaturalLatents.General.pairCharge_residual_identity, NaturalLatents.General.pairCharge_fixed_coefficient_data") (uses := "PC4.0, PC4.1, PC4.2") (tags := "partly kernel-verified")
*Lemma PC4.3 (the integrated residual).* Under the hypotheses of Lemma PC4.0, with the definitions (PC4.2),

$$`
\mathrm{Res}=D-\frac\lambda6\overline{E_Q(W\Theta)+E_P(W\Theta)}+\frac{\lambda^2}{60s^2}\overline{5\rho+6h}.
\qquad \text{(PC-R1)}
`

The fields $`e_X=6\lambda d_X-kw_X` and $`e_Y=6\lambda d_Y-kw_Y` are centered, and

$$`
\mathcal Q(e)=36\lambda^2(\rho-4h)-12\lambda k\rho+k^2s^2t_0.
\qquad \text{(PC-R2)}
`

Consequently

$$`
192\,\mathrm{Res}=192D-32\lambda\left[j\left(1-\frac s4\right)-\frac14+c_0z^2\right]+\frac2{15}k^2t_0
-\frac2{15s^2}\overline{\mathcal Q(e)}.
\qquad \text{(PC-R3)}
`

(PC-R1) to (PC-R3) are exact identities; their proof divides only by $`s`, never by $`\lambda`, $`\rho` or $`h`.
:::

:::proof "PC4.3"
Lean proves: positivity and the information bound for the algebraic one-orientation residual, $`0\le36\lambda^2(\rho-4h)-12\lambda k\rho+k^2s^2t_0`, and the scalar collected residual identity `pairCharge_residual_identity`.

Integrate the corrected variance polynomial and complete the Hessian quadratic form using the defect products. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/pair-charge.md#43-integrated-residual).
:::

Lean: the one-orientation shape of (PC-R1) is the residual in the conclusion of `pairCharge_residual_information`
(`NaturalLatents/General/PairCharge.lean`), with the statistic $`W+4s/25` and correction $`\Theta`; the nonnegativity
consequence of (PC-R2) and (PC-H), $`0\le36\lambda^2(\rho-4h)-12\lambda k\rho+k^2s^2t_0` for all real $`\lambda,k`, is
`pairCharge_correction_hessian` (`NaturalLatents/General/PairCharge/Correction.lean`), which does not state the
equality (PC-R2) itself. (PC-R1) with (PC-X)
substituted, (PC-R3) and (PC-R4) below are one statement, `pairCharge_residual_identity`
(`NaturalLatents/General/PairCharge/Certificate.lean`), in the scalars $`s,j,v,\rho,h` with $`z^2=1-4v`, taking $`D`
in the collected form of `pairCharge_fixed_coefficient_data` at coefficient $`1/5`, which equals (PC-D-RAW)
divided by $`192`.

## 4.4 A direct residual bound

Define

$$`
\begin{aligned}
\mathrm{Den}(s,j)&=15+32j-\left(\frac{178}{25}+\frac{74j}5\right)s+\left(\frac{21}{25}+\frac{46j}{25}-j^2\right)s^2
-32\lambda\left[j\left(1-\frac s4\right)-\frac14\right]+\frac2{15}k^2\left(\frac12-j\right),\\
\Xi&=3-\frac{101}{120}s+\left(\frac7{200}-\frac j{24}\right)s^2+\frac{s^2z^2}{16}.
\end{aligned}
\qquad \text{(PC-DEN)}
`

:::theorem "PC4.4" (parent := "pair-charge") (lean := "NaturalLatents.General.pairCharge_residual_identity, NaturalLatents.General.pairCharge_asymmetry_bracket, NaturalLatents.General.pairCharge_residual_le_denominator, NaturalLatents.General.pairCharge_residual_bound") (uses := "PC4.0, PC4.1, PC4.3") (tags := "partly kernel-verified")
*Lemma PC4.4 (the residual bound).* Under the hypotheses of Lemma PC4.0,

$$`
192D=15+32j-\left(\frac{178}{25}+\frac{74j}5\right)s+\left(\frac{21}{25}+\frac{46j}{25}-j^2\right)s^2-48z^2\Xi,
\qquad \text{(PC-D-RAW)}
`

$$`
192\,\mathrm{Res}=\mathrm{Den}(s,j)-z^2\left[48\Xi+32\lambda c_0+\frac{k^2}5\right]-\frac2{15s^2}\overline{\mathcal Q(e)},
\qquad \text{(PC-R4)}
`

and if $`0<s\le1`, then $`192\,\mathrm{Res}\le \mathrm{Den}(s,j)`.
:::

:::proof "PC4.4"
Lean proves: the scalar collected residual identity `pairCharge_residual_identity`, the asymmetry-bracket lower bound $`70`, and $`192\,\overline{\mathrm{pairCharge\_residual}}\le\mathrm{Den}(s,j)` for $`0<s\le1`, with the residual defined algebraically.

Expand the scalar residual identity and discard the nonnegative asymmetry and Hessian terms after bounding their coefficients. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/pair-charge.md#44-a-direct-residual-bound).
:::

Lean: `pairCharge_residual_identity` ((PC-R1) with (PC-X) substituted, (PC-R3) and (PC-R4) as one identity, with $`D` in the
collected form of `pairCharge_fixed_coefficient_data`, equal to (PC-D-RAW) divided by $`192`),
`pairCharge_asymmetry_bracket` (the bound $`70`) and `pairCharge_residual_le_denominator` (the scalar form of the bound),
all in `NaturalLatents/General/PairCharge/Certificate.lean`; the bound for a contact pair is
`pairCharge_residual_bound` (`NaturalLatents/General/PairCharge.lean`), for $`s\le1`.

## 4.5 Information, support holes and positivity

:::theorem "PC4.5" (parent := "pair-charge") (lean := "NaturalLatents.General.pairCharge_residual_information, NaturalLatents.General.pairCharge_entropy_linear_field_affine, NaturalLatents.General.pairCharge_entropy_path_payment, stoch_to_det.joint_absCont_product, NaturalLatents.General.pairCharge_fixed_floor_gap, NaturalLatents.General.pairCharge_average_KL_separate, NaturalLatents.General.pairCharge_projection_information, NaturalLatents.General.pairCharge_information_floor") (uses := "PC4.0, PC4.3, PC4.4") (tags := "partly kernel-verified")
*Lemma PC4.5 (the information floor).* Under the hypotheses of Lemma PC4.0, if $`0<s\le1`, then $`\mathrm{Res}>0`,
$`\mathrm{Den}(s,j)>0`, and the averaged information $`\bar I=(I(P)+I(R))/2` satisfies

$$`
\bar I\ge\frac{3y^2}{\mathrm{Den}(s,j)}.
\qquad \text{(PC-FLOOR)}
`
:::

:::proof "PC4.5"
Lean proves: positivity and $`\Delta^2/(4\,\mathrm{Res}_P)\le I(P)` for the algebraic one-orientation residual with nonzero gap, and $`\mathrm{Den}(s,j)>0` with the information floor (PC-FLOOR) for $`0<s\le1`.

Compare the expectation gap with the integrated variance by Cauchy-Schwarz and obtain the entropy path integral by a monotone limit, including support holes. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/pair-charge.md#45-information-support-holes-and-positivity).
:::

Lean: `pairCharge_residual_information` (`NaturalLatents/General/PairCharge.lean`) proves, in one orientation and for
any statistic and any correction with zero means under $`P` and $`Q` and a nonzero gap, that the residual
$`\mathrm{Res}_P` of that orientation alone (the integral in (PC4.2) without the average) is positive and
$`\Delta^2/(4\,\mathrm{Res}_P)\le I(P)`, holes allowed; it rests on `pairCharge_entropy_linear_field_affine` and
`pairCharge_entropy_path_payment` (`NaturalLatents/General/PairCharge/Information.lean`), with
`stoch_to_det.joint_absCont_product` (`NaturalLatents/Upstream/ContactInformation.lean`) supplying that $`P` vanishes
where $`Q` does. The bound $`\Delta\ge y/4` is `pairCharge_fixed_floor_gap` (`MomentBounds.lean`), the averaging step is
`pairCharge_average_KL_separate` (`PairCharge.lean`), and the division by $`\mathrm{Den}(s,j)` is
`pairCharge_projection_information` (`MomentBounds.lean`); the assembled floor is `pairCharge_information_floor`
(`PairCharge.lean`), which states $`\mathrm{Den}(s,j)>0` and (PC-FLOOR) for $`s\le1`. Lean has no integral formula for $`I(P)`: it proves $`\tau\Delta\le I(P)+\tau^2\,\mathrm{Res}_P` in one
orientation, with $`\mathrm{Res}_P` defined algebraically rather than by the integral in (PC4.2), for every real $`\tau`, by a second-derivative comparison on $`[0,1)` and continuity at $`u=1`, and it
combines the two orientations by a reciprocal-mean step on their separate residuals rather than by one Cauchy-Schwarz
over the pooled measure.

# 5. A direct positive scalar certificate

## 5.1 The priced profile

Put

$$`
\beta=\frac{23}{250},\quad\gamma=\frac7{60},\quad\alpha=\frac{103}{1000},\quad\kappa=\frac{23}{1000},\qquad
G(s)=\gamma-\alpha s-\kappa s^2.
`

:::theorem "PC5.1" (parent := "pair-charge") (lean := "NaturalLatents.General.pairCharge_price") (uses := "A2.2") (tags := "partly kernel-verified")
*Lemma PC5.1 (the price).* For $`0\le s\le2`, $`b(s)>0` and

$$`
b(s)[\beta\Psi'(s)-\alpha-2\kappa s]=\frac{1071}{64000}\left(s-\frac{170}{1071}\right)^2+\frac{1343}{17136000}
+\frac{69}{32000}s^2(2-s)>0,
\qquad \text{(PC-PRICE)}
`

$$`
\beta\Psi(s)\ge\alpha s+\kappa s^2.
\qquad \text{(PC-PRICE-INTEGRAL)}
`
:::

:::proof "PC5.1"
Lean proves: $`(23/250)\Psi(s)\ge(103/1000)s+(23/1000)s^2` for $`0\le s\le2`, the inequality (PC-PRICE-INTEGRAL).

Complete squares in the price derivative and integrate the positive derivative from the zero endpoint. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/pair-charge.md#51-the-priced-profile).
:::

Lean: `pairCharge_price` (`NaturalLatents/General/PairCharge/Certificate.lean`) states (PC-PRICE-INTEGRAL) only, for
$`0\le t\le2`; the identity (PC-PRICE) and $`b>0` enter its proof but not its statement.

## 5.2 Three positive quartics

The proof uses explicitly given constants: the shift $`s/5` in $`W`, the slope $`\lambda`, the weight $`k`,
the profile coefficients $`\alpha,\kappa`, the polynomials $`M_l,M_m,M_h` and the fifteen numerator coefficients below.
Nothing depends on how they were found: every identity below is checked by exact rational arithmetic.

For $`0\le s\le1` and $`1/16\le j\le1/2` put $`q=(16j-1)/7`, so $`0\le q\le1`, and define

$$`
\begin{aligned}
F(s,j)&=3(1-s+sj)^2-G(s)\mathrm{Den}(s,j),\qquad F_l(s)=F(s,1/16),\qquad F_h(s)=F(s,1/2),\\
F_m(s)&=\frac{F_l(s)+F_h(s)}2-\frac{49}{512}[3+G(s)]s^2.
\end{aligned}
`

:::theorem "PC5.2" (parent := "pair-charge") (lean := "NaturalLatents.General.pairCharge_quartic_low, NaturalLatents.General.pairCharge_quartic_mid, NaturalLatents.General.pairCharge_quartic_high, NaturalLatents.General.pairCharge_scalar_certificate") (uses := "") (tags := "partly kernel-verified")
*Lemma PC5.2 (the scalar certificate).* For $`0\le s\le1` and $`1/16\le j\le1/2`,

$$`
F(s,j)=(1-q)^2F_l(s)+2q(1-q)F_m(s)+q^2F_h(s),
\qquad \text{(PC-INTERPOLATION)}
`

$$`
3(1-s+sj)^2-G(s)\mathrm{Den}(s,j)>0.
\qquad \text{(PC-SCALAR)}
`
:::

:::proof "PC5.2"
Lean proves: $`F_l>0`, $`F_m>0` and $`F_h>0` on their stated scalar domains, and $`3(1-s+sj)^2-G(s)\mathrm{Den}(s,j)>0` for $`0\le s\le1` and $`1/16\le j\le1/2`.

Interpolate quadratically in the normalized quartic ratio and certify each edge quartic by exact rational positive decompositions. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/pair-charge.md#52-three-positive-quartics).
:::

Lean: `pairCharge_quartic_low`, `pairCharge_quartic_mid` and `pairCharge_quartic_high`
(`NaturalLatents/General/PairCharge/Certificate.lean`) state the positivity consequences of (PC-CERTIFICATE),
$`F_l>0`, $`F_m>0` and $`F_h>0`, the first two for $`s\ge0` and the third for $`0\le s\le1`; the certificate
identities appear only in their proofs. `pairCharge_scalar_certificate` (same file) states (PC-SCALAR), with
(PC-INTERPOLATION) used only in its proof. The scalar functions $`G`, $`\lambda`, $`k`, $`\mathrm{Den}(s,j)` and $`F`
are `pairChargeProfile`, `pairChargeSlope`, `pairChargeWeight`, `pairChargeDenominator` and `pairChargeScalar` (same
file).

:::theorem "PC5.3" (parent := "pair-charge") (lean := "NaturalLatents.General.pairCharge_C, NaturalLatents.General.contact_moments, NaturalLatents.General.pairCharge_price, NaturalLatents.General.pairCharge_information_floor, NaturalLatents.General.pairCharge_quarticRatio_bounds, NaturalLatents.General.pairCharge_scalar_certificate, stoch_to_det.Knat_nonneg") (uses := "PC4.0, PC4.5, PC5.1, PC5.2") (tags := "partly kernel-verified")
*Theorem PC5.3 (the pair charge C).* For every finite nonempty $`X,Y`, every nonempty $`S` with all rows and columns
used, every feasible $`w>0` on $`S`, and every pair of distinct positive contacts $`P,R` of $`w`,

$$`
\frac{I(P)+I(R)}2+\frac{23}{250}\Psi(s)>\frac7{60}.
`
:::

:::proof "PC5.3"
Lean proves: $`(I(P)+I(R))/2+(23/250)\Psi(s)\ge7/60` for distinct positive contacts of a common feasible kernel, the non-strict charge `HasPairCharge CommonSupportPair (23/250) (7/60)`.

For separation at most one, combine the information floor, positive scalar certificate, and price; above one, the price and nonnegative information suffice. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/pair-charge.md#52-three-positive-quartics).
:::

Lean: `pairCharge_C` (`NaturalLatents/General/PairCharge.lean`), stating `HasPairCharge CommonSupportPair (23/250) (7/60)`. It
uses `contact_moments` for $`0<s<2` and `pairCharge_price`; for $`s\le1`, `pairCharge_information_floor`,
`pairCharge_quarticRatio_bounds` and `pairCharge_scalar_certificate`; and for $`s>1`, `stoch_to_det.Knat_nonneg`
(`NaturalLatents/Upstream/ContactInformation.lean`) for nonnegative information. Lean splits the cases at $`s\le1` and
$`s>1`. Lean's `HasPairCharge` is the non-strict inequality, which the strict one implies.
