import Verso
import VersoManual
import VersoBlueprint
import NaturalLatents.Main

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "Contact moments and the feasible Hessian" =>

:::group "contact"
Contact moments and the feasible Hessian.
:::

The reproduced contact conventions apply to the analytic chapters; the table-form chapter uses bits.

This page fixes the units and notation shared by the proof pages, and proves the moment relations of two positive
contacts of one feasible kernel: the ratio and conditional-moment identities, the quadratic and quartic moment
identities, the separation range $`0<s<2` for distinct contacts and $`s=J=0` for equal contacts, a feasibility
inequality for nonnegative marginal fields, the Hessian test for centered marginal fields, and the quartic bound
$`J\le6A_0B_0-s^2\le s^2/2`, with $`s`, $`J`, $`A_0` and $`B_0` defined in (C1.3). These relations are the
input of the [affinity bound](https://github.com/AlexisOlson/natural-latents/blob/main/docs/affinity.md), which the mismatch payment applies to every pair of distinct components of
the setup latent (step 6 of the [route](https://github.com/AlexisOlson/natural-latents/blob/main/docs/overview.md#the-route)); Lemma C1.3 and the Hessian test are
also used by the pair charge. In the assembly `NaturalLatents.General.T_le_of_connected`
(`NaturalLatents/General/Pricing.lean`), `contact_moments` is applied to each pair of distinct components of the setup
latent, and its conclusion is passed to `affinity_bound`.

Each lemma below states its quantified hypotheses, so that it can be read alone. Lemma, theorem, remark and equation
numbers carry the prefix of the page that states them: S for the [setup](https://github.com/AlexisOlson/natural-latents/blob/main/docs/setup.md), C for this page, L for the
[ledger](https://github.com/AlexisOlson/natural-latents/blob/main/docs/ledger.md), R for the [race](https://github.com/AlexisOlson/natural-latents/blob/main/docs/race.md), K for the [cap](https://github.com/AlexisOlson/natural-latents/blob/main/docs/cap.md), A for the [affinity bound](https://github.com/AlexisOlson/natural-latents/blob/main/docs/affinity.md), Q for
the [replica budget](https://github.com/AlexisOlson/natural-latents/blob/main/docs/replica.md), P for the [payment](https://github.com/AlexisOlson/natural-latents/blob/main/docs/payment.md), PC for the [pair charge](https://github.com/AlexisOlson/natural-latents/blob/main/docs/pair-charge.md), M for the
[assembly](https://github.com/AlexisOlson/natural-latents/blob/main/docs/assembly.md), E for the [extension](https://github.com/AlexisOlson/natural-latents/blob/main/docs/extension.md) and T for the [table form](https://github.com/AlexisOlson/natural-latents/blob/main/docs/table-form.md); the tags (D1) to
(D3) of section 0 serve every page. Unless explicitly
qualified otherwise, the Lean declarations named below are in the namespace `NaturalLatents.General`; declarations
prefixed `stoch_to_det` are upstream, in `NaturalLatents/Upstream/`, adapted from
[DLorell/stoch_to_det](https://github.com/DLorell/stoch_to_det).

# 0. Units, notation and standing inputs

*Units.* All entropies, mutual informations and relative entropies in the proof pages are in nats. The deterministic
optimum $`T` and the stochastic optimum $`\tau` scale by the same factor under a change of units, so the final
inequality $`T(p)\le(13999/2000)\,\tau(p)` is unit-free. A quantity stated in bits is converted once:

$$`
H_{\mathrm{nat}}=(\ln2)H_{\mathrm{bits}},\quad I_{\mathrm{nat}}=(\ln2)I_{\mathrm{bits}},
\qquad (M,B,T,\tau,h)_{\mathrm{nat}}=(\ln2)(M,B,T,\tau,h)_{\mathrm{bits}}.
\qquad \text{(D1)}
`

Hereafter $`H,I,M,B,T,\tau,h` are in nats. The relative entropy and the pair charge are natural-log quantities and are
unchanged. Probabilities and $`d,s,J,BC,\beta` are dimensionless, whereas $`\Psi` and $`\gamma` have nat units. There
is no final division by $`\ln 2` in the mismatch conclusion. Here $`M`, $`B`, $`T`, $`\tau` and $`d` are defined
in (D3) and $`s`, $`J` in (C1.3); $`BC` denotes either marginal affinity, $`BC_X` or $`BC_Y`, and these and
$`\Psi` are defined in (A2.1) on the [affinity page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/affinity.md); $`h` is the seed average of the two fixed-map
conditional entropies $`H(f(Z)\mid X)+H(f(Z)\mid Y)`, defined in (L1) and (L7) on the [ledger page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/ledger.md); and
$`\beta`, $`\gamma` are the parameters of the pair charge below.

Lean: `NaturalLatents.General.TNat` and `NaturalLatents.General.tauNat` (`NaturalLatents/General/Definitions.lean`) are the
bit-valued `stoch_to_det.T` and `stoch_to_det.tau` (`NaturalLatents/Upstream/Functionals.lean`) converted by
`NaturalLatents.General.nats`, multiplication by `Real.log 2` (`NaturalLatents/General/Nats.lean`, the only General file
where that factor appears); `mediation`, `redundancy`, `replicaBudget` and `seedEntropy` in `Definitions.lean`, the Lean
forms of $`M`, $`B`, $`K` and $`h`, are converted the same way. `NaturalLatents.General.bits_of_nats` (`Nats.lean`)
converts the nat-valued bound on connected supports back to the bit-valued `stoch_to_det.T` and `stoch_to_det.tau`, and
`NaturalLatents.T_le_c_mul_tau` (`NaturalLatents/Main.lean`) then extends it to every law in bits.

*Conventions.* For a finite law, all conditional sums range over positive-probability conditioning events. Entropy
uses $`0\ln0=0`, and a relative entropy sums over the positive mass of its first argument. With the reference
positive on that support,

$$`
H(q)=-\sum_{i:q_i>0}q_i\ln q_i,\qquad
D(q\Vert v)=\sum_{i:q_i>0}q_i\ln(q_i/v_i),\qquad
I(q)=D(q\Vert q_X\otimes q_Y).
\qquad \text{(D2)}
`

Lean: the mutual information $`I(q)` of a law on $`X\times Y` is the natural-log `stoch_to_det.Knat`
(`NaturalLatents/Upstream/DomFloorCore.lean`), used directly, with no conversion. `Knat` is an equivalent all-cell scalar-integrand formula rather than
the positive-support sum (D2); on probability laws, `stoch_to_det.Knat_eq_log_two_mul_Ixy` (same file) identifies it
with natural-log mutual information.

*Latents and scores.* A finite latent is a joint law of $`Z=(X,Y)` and a finite label $`L`, or equivalently a
mixture $`p=\sum_i\pi_iq_i`, with $`r_z(i)=\Pr(L=i\mid Z=z)` on $`\mathrm{supp}\,p`. Set

$$`
\begin{aligned}
M&=I(X;Y\mid L),&B&=I(L;X\mid Y)+I(L;Y\mid X),\\
\tau(p)&=\inf_L(M+B),&
T(p)&=\min_{A=f(Z)}[I(X;Y\mid A)+H(A\mid X)+H(A\mid Y)],\\
d&=\sum_{z:p(z)>0}p(z)\left[1-\sum_i r_z(i)^2\right].
\end{aligned}
\qquad \text{(D3)}
`

The deterministic minimum exists because a finite alphabet has finitely many partitions. For a deterministic map $`f`
on $`\mathrm{supp}\,p`, write $`D_p(f) = I(X;Y\mid f(Z)) + H(f(Z)\mid X) + H(f(Z)\mid Y)` for the score of the code
$`f(Z)`, so that $`T(p)=\min_f D_p(f)`.

Lean: a finite latent is `stoch_to_det.Latent` (`NaturalLatents/Upstream/Functionals.lean`), and `posterior` (the
posterior $`r_z(i)`), `mediation` ($`M`), `redundancy` ($`B`) and `mismatch` ($`d`) are in
`NaturalLatents/General/Definitions.lean`. `stoch_to_det.detScore` (`NaturalLatents/Upstream/Functionals.lean`) is the
score in bits of a map on all of $`X\times Y`: the score $`D_p(f)` is `detScoreNat` (`NaturalLatents/General/Nats.lean`),
that is `nats` of `detScore`, after extending the map off the support. In Lean, $`T` is an infimum over deterministic latents
and $`d` sums over all cells, the cells with $`p(z)=0` contributing zero.

*The supplied setup.* The mismatch payment is applied to a latent $`p=\sum_i\pi_iq_i` with positive priors, distinct
components that are positive contacts of one feasible kernel on the common support $`\mathrm{supp}\,p` (contacts and
feasibility are defined in section 1), and $`M+B=\tau(p)`. Such a latent exists when the support of $`p` is connected
as a bipartite graph between the values of $`X` and the values of $`Y` (defined on the
[setup page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/setup.md#1-the-setup-on-a-connected-support)), and the bound for a general finite law is
reduced to that case by splitting the support into its connected components: with component weights $`\rho_k` and
normalized component laws $`\bar p_k`, $`\sum_k\rho_k\tau(\bar p_k)\le\tau(p)` and $`T(p)\le\sum_k\rho_kT(\bar p_k)`
((E3.F) on the [extension page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/extension.md)). Neither step is proved on this page; they are proved by
`NaturalLatents.General.exists_setup_of_connected` (`NaturalLatents/General/Setup.lean`) and
`NaturalLatents.General.extension_of_connected` (`NaturalLatents/General/Extension.lean`).

Lean: the setup is the structure `NaturalLatents.General.CommonSetup` (`NaturalLatents/General/Definitions.lean`),
which also records that every posterior $`r_z(i)` is positive on the support; it is constructed for connected support
by `NaturalLatents.General.exists_setup_of_connected` (`NaturalLatents/General/Setup.lean`), and the extension to every
law is `NaturalLatents.General.extension_of_connected` (`NaturalLatents/General/Extension.lean`), which applies
`stoch_to_det.reduce_to_connected` (`NaturalLatents/Upstream/Connected.lean`).

*The pair charge.* The pair charge $`PC(\beta,\gamma)`, for $`\beta\ge0` and $`\gamma>0`, is the averaged
natural-logarithm inequality

$$`
\frac{I(P)+I(R)}2+\beta\Psi(s(P,R))\ge\gamma
`

for every two distinct positive contacts $`P,R` of a common feasible kernel, on a support $`S` that need not be a rectangle (cells of $`X\times Y`
outside $`S`, the holes, are allowed); $`s` is defined in
(C1.3) and $`\Psi` in (A2.1). It is a hypothesis of the mismatch payment, generic in $`\beta\ge0` and $`\gamma>0`, and
is not used on this page.

Lean: `NaturalLatents.General.HasPairCharge` (`NaturalLatents/General/Definitions.lean`), stated over a domain of pairs;
`NaturalLatents.General.pairCharge_C` (`NaturalLatents/General/PairCharge.lean`) proves it on
distinct positive contacts of a common feasible kernel at $`(\beta,\gamma)=(23/250,7/60)`. The formal `HasPairCharge` definition accepts
arbitrary real $`\beta` and $`\gamma`; the formal payment inequality `mismatch_payment`
(`NaturalLatents/General/Payment.lean`) requires $`\beta\ge0` and $`\gamma\ge0`. This page keeps $`\gamma>0` so that
later bounds may divide by $`\gamma`.

# 1. Contact moments and the feasible Hessian

Fix finite nonempty alphabets $`X,Y`, a nonempty support $`S\subseteq X\times Y`, and a kernel $`w:S\to(0,\infty)`,
extended by zero outside $`S`. Remove unused rows and columns, so every symbol of $`X` and $`Y` occurs in $`S`.
Feasibility means that, for every pair of probability vectors $`u` on $`X` and $`v` on $`Y`,

$$`
\sum_{(x,y)\in S}w(x,y)u_x^{2/3}v_y^{2/3}\leq1.
\qquad \text{(C1.1)}
`

A positive contact is a probability law $`P` positive at every cell of $`S`, zero outside $`S`, and satisfying

$$`
P(x,y)=w(x,y)P_X(x)^{2/3}P_Y(y)^{2/3}
\quad((x,y)\in S).
\qquad \text{(C1.2)}
`

Thus all used marginal probabilities are positive. Neither full rectangular support nor connectedness is assumed. For
two such contacts $`P,R`, define

$$`
\begin{aligned}
f(x)&=\left(\frac{R_X(x)}{P_X(x)}\right)^{1/3},
&g(y)&=\left(\frac{R_Y(y)}{P_Y(y)}\right)^{1/3},\\
U&=f-1,&V&=g-1,\\
A_0&=1-E_Pf,&B_0&=1-E_Pg,\\
s&=A_0+B_0=2-E_Pf-E_Pg,
&J&=E_P[U^2V^2].
\end{aligned}
\qquad \text{(C1.3)}
`

All expectations in this section are under $`P`, including expectations of a field depending on only one coordinate.
Some letters in this section are local: $`f,g` are the fields (C1.3), not maps or codes; $`u,v` in (C1.1) are
probability vectors, not the price bound $`u` of the [cap page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/cap.md); the fields $`A,B` and the normalizers $`a,b`
of Lemma C1.3 are not the budget $`B`, the race exponent $`a` or the quadratic $`b` of (A2.1); and $`L(t)`, $`R(t)`
in the proof of Lemma C1.4 are not a latent or a contact.

Lean: a pair of distinct positive contacts of one feasible kernel is `CommonSupportPair S w P R`. Feasibility (C1.1) is
`stoch_to_det.Feasible` and the contact equation (C1.2), with $`P` a probability law zero
outside $`S`, is `stoch_to_det.IsContact` (`NaturalLatents/Upstream/Duality.lean`), both used directly, and positivity on $`S` is
`PositiveOn` (`NaturalLatents/General/Definitions.lean`). `Feasible` also
records $`w>0` on $`S`. Lean does not remove unused rows and columns: `Feasible` quantifies over probability vectors
on the full alphabets, and the conditional statements are restricted to the used symbols `xSupport S` and
`ySupport S`. Lean leaves $`w` outside $`S` unrestricted, because those values never enter the conditions. On unused
marginal symbols, its totalized division gives $`f=g=0` and hence $`U=V=-1`; these symbols contribute zero to every
expectation, and conditional identities are asserted only on used symbols. The fields
(C1.3) are `rootRatioX`, `rootRatioY`, `defectX`, `defectY`, `separation` and `quarticMoment`, with $`E_P` written
`expect P`, all in `NaturalLatents/General/Definitions.lean`, and $`U,V` are the upstream secants
`stoch_to_det.contactSecantX` and `stoch_to_det.contactSecantY` (`NaturalLatents/Upstream/Floor.lean`), with
`rootRatioX` defined as `contactSecantX + 1`.

:::theorem "C1.1" (parent := "contact") (lean := "NaturalLatents.General.contact_ratio_mul, NaturalLatents.General.contact_cond_rootRatioY_square, NaturalLatents.General.contact_cond_rootRatioX_square, NaturalLatents.General.contact_rootRatioX_cube, NaturalLatents.General.contact_rootRatioY_cube, NaturalLatents.General.contact_rootRatioX_square, NaturalLatents.General.contact_rootRatioY_square") (uses := "") (tags := "kernel-verified")
*Lemma C1.1 (contact ratios and conditional moments).* For every finite nonempty $`X,Y`, every nonempty
$`S\subseteq X\times Y` with all rows and columns used, every feasible kernel $`w>0` on $`S`, and every pair of
positive contacts $`P,R` of $`w`, the fields in (C1.3) satisfy, at every cell of $`S` and every used conditioning
symbol respectively,

$$`
\frac RP=f^2g^2,\qquad
E_P[g^2\mid X]=f,\qquad E_P[f^2\mid Y]=g,\qquad
E_Pf^3=E_Pg^3=1,\qquad E_Pf^2=E_Pg,\quad E_Pg^2=E_Pf.
\qquad \text{(C1.4)}
`
:::

:::proof "C1.1"
Divide the contact equations and sum along rows and columns, using normalization and the conditional expectation tower rule. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md#1-contact-moments-and-the-feasible-hessian).
:::

Lean: `contact_ratio_mul` (the ratio identity, stated as $`R=Pf^2g^2` at every cell), `contact_cond_rootRatioY_square`,
`contact_cond_rootRatioX_square`, `contact_rootRatioX_cube`, `contact_rootRatioY_cube`, `contact_rootRatioX_square` and `contact_rootRatioY_square`, all `NaturalLatents.General.*` in
`NaturalLatents/General/Contact.lean`. Their hypothesis is `CommonSupportPair S w P R`, which includes feasibility and
$`P\ne R`. The proof above uses neither feasibility nor distinctness; the stated lemma retains feasibility to match the
common contact domain.

:::theorem "C1.2" (parent := "contact") (lean := "NaturalLatents.General.contact_energy_identities, NaturalLatents.General.contact_quartic_identity, NaturalLatents.General.contact_separation, NaturalLatents.General.contact_upper_separation, NaturalLatents.General.pairCharge_separation_reverse") (uses := "C1.1") (tags := "kernel-verified")
*Lemma C1.2 (separation and the quartic moment list).* For every finite nonempty $`X,Y`, every nonempty common
support $`S` with all rows and columns used, every feasible $`w>0` on $`S`, and every pair of positive contacts
$`P,R`, the quantities in (C1.3) satisfy

$$`
A_0,B_0\geq0,\qquad
E_PU^2=2A_0-B_0,\qquad E_PV^2=2B_0-A_0,\qquad
J=4E_P[UV]-s,\qquad s(P,R)=s(R,P).
\qquad \text{(C1.9)}
`

If $`P\ne R`, then $`0<s<2`. If $`P=R`, then $`f=g=1` and $`s=J=0`.
:::

:::proof "C1.2"
Apply strict Jensen for separation, expand the quadratic and quartic moments, and change measure for reversal symmetry. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md#1-contact-moments-and-the-feasible-hessian).
:::

Lean: `contact_energy_identities` (the two identities for $`E_PU^2` and $`E_PV^2`, and their sum $`s`),
`contact_quartic_identity`, `contact_separation` ($`0<s`) and `contact_upper_separation` ($`s<2`) in
`NaturalLatents/General/Contact.lean`, and `pairCharge_separation_reverse` (the symmetry) in
`NaturalLatents/General/PairCharge/MomentBounds.lean`, all `NaturalLatents.General.*`.

These assume distinctness: the positive-separation lemma `contact_separation`, the symmetry `pairCharge_separation_reverse` and
`contact_moments`. `contact_separation` derives $`0<s` from $`s=E_PU^2+E_PV^2` rather than from strict Jensen.

These do not assume distinctness: the energy and quartic identities and the upper bound $`s<2`. `contact_energy_identities` assumes two contacts whose support is
exactly $`S`; `contact_quartic_identity` takes probability laws $`P,R` together with the ratio identity and the conditional and
second-moment identities of Lemma C1.1 as inputs; and `contact_upper_separation` takes a probability law $`P` and
nonnegativity of $`f,g` with positivity wherever $`P` is positive. Neither the energy nor the quartic lemma assumes
feasibility. The equal-pair conclusions are not collected into a separate Lean statement, and $`A_0,B_0\ge0` is not
stated separately, though it follows from the two energy identities.

:::theorem "C1.3" (parent := "contact") (lean := "stoch_to_det.contact_hypercontractive, NaturalLatents.General.contact_hessian_cube_test") (uses := "") (tags := "kernel-verified")
*Lemma C1.3 (feasibility for nonnegative marginal fields).* For every finite nonempty $`X,Y`, every nonempty
$`S\subseteq X\times Y` with all rows and columns used, every feasible $`w>0` on $`S`, every positive contact $`P` of
$`w`, and every pair of fields $`A:X\to[0,\infty)`, $`B:Y\to[0,\infty)`,

$$`
E_P[A(X)^2B(Y)^2]\leq(E_PA^3)^{2/3}(E_PB^3)^{2/3}.
\qquad \text{(C1.15)}
`
:::

:::proof "C1.3"
Handle a zero normalizer separately, then insert the normalized cubed marginal fields into feasibility. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md#1-contact-moments-and-the-feasible-hessian).
:::

Lean: (C1.15) is not stated separately; it is the case of `stoch_to_det.contact_hypercontractive`
(`NaturalLatents/Upstream/Duality.lean`) with the fields $`A^2` and $`B^2`, which assumes a feasible kernel and a
contact, without positivity on $`S`. `contact_hessian_cube_test` (`NaturalLatents/General/Contact.lean`) applies it to
the fields $`(1+tF)^2` and $`(1+tG)^2` in the proof of Lemma C1.4.

:::theorem "C1.4" (parent := "contact") (lean := "NaturalLatents.General.contact_hessian, NaturalLatents.General.contact_hessian_cube_test, NaturalLatents.General.contact_hessian_coefficient") (uses := "C1.3") (tags := "kernel-verified")
*Lemma C1.4 (the feasible Hessian test).* For every finite nonempty $`X,Y`, every nonempty support $`S` with all rows
and columns used, every feasible $`w>0` on $`S`, every positive contact $`P` of $`w`, and every real marginal fields
$`F:X\to\mathbb R`, $`G:Y\to\mathbb R` satisfying $`E_PF=E_PG=0`,

$$`
4E_P[FG]\leq E_PF^2+E_PG^2.
\qquad \text{(C1.18)}
`
:::

:::proof "C1.4"
Apply the feasibility inequality to small positive perturbations and extract the quadratic coefficient by a finite real limit. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md#1-contact-moments-and-the-feasible-hessian).
:::

Lean: `NaturalLatents.General.contact_hessian` (`NaturalLatents/General/Contact.lean`). It assumes a feasible kernel and
a contact, without positivity on $`S`. Its proof uses `contact_hessian_cube_test`, the cube of (C1.15) for the fields
$`1+tF` and $`1+tG`, and extracts the coefficient of $`t^2` by a one-sided limit (`contact_hessian_coefficient`)
instead of Taylor's formula for $`z^{2/3}`.

:::theorem "C1.5" (parent := "contact") (lean := "NaturalLatents.General.contact_quarticMoment_bound, NaturalLatents.General.contact_scalar_bound, NaturalLatents.General.contact_moments") (uses := "C1.1, C1.2, C1.4") (tags := "kernel-verified")
*Lemma C1.5 (the contact quartic bound).* For every finite nonempty $`X,Y`, every nonempty common support $`S` with
all rows and columns used, every feasible $`w>0` on $`S`, and every pair of positive contacts $`P,R`, the quantities
defined in (C1.3) satisfy

$$`
J\leq6A_0B_0-s^2\leq\frac{s^2}{2}.
\qquad \text{(C1.23)}
`
:::

:::proof "C1.5"
Center the shifted ratio fields, apply the Hessian test, and use square nonnegativity. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md#1-contact-moments-and-the-feasible-hessian).
:::

Lean: `contact_quarticMoment_bound` (the first inequality) and `contact_scalar_bound` (the second), both
`NaturalLatents.General.*` in `NaturalLatents/General/Contact.lean`. `contact_quarticMoment_bound` assumes only that $`P` is a
probability law, together with the energy and quartic identities of Lemma C1.2 and the Hessian test as hypotheses; $`R`
is an arbitrary real array and no contact hypothesis appears. `contact_scalar_bound` holds for arbitrary real arrays
$`P,R`, since it uses only $`s=A_0+B_0`. The contact-moment lemma is
`NaturalLatents.General.contact_moments` (`NaturalLatents/General/Contact.lean`): for every `CommonSupportPair S w P R`
it proves the structure `ContactMoments S P R` (`NaturalLatents/General/Definitions.lean`), whose fields are the
conditional identities, $`E_Pf^3=E_Pg^3=1`, the second-moment identities, $`0<s<2`, the two energy identities, the
quartic identity, the Hessian test and both inequalities of (C1.23). It does not include the ratio identity,
$`A_0,B_0\ge0` or the symmetry of $`s`.
