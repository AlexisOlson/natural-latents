import Verso
import VersoManual
import VersoBlueprint
import NaturalLatents.Main

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "The ledger" =>

:::group "ledger"
The ledger.
:::

This page proves the ledger inequality, in the notation of section 0 of the [contact page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md) (the posterior
$`r_z` and the optimum $`T` are defined in (D3)). Let $`L` be a finite latent of $`p` and let $`F` be a random
deterministic map from the cells to the labels of $`L`, independent of $`Z=(X,Y)`, such that at each cell $`z` of the
support the label $`F(z)` is distributed as the posterior $`r_z` of $`L`. With $`M` and $`B` the budgets of
(D3) and $`h` the average over $`F` of $`H(f(Z)\mid X)+H(f(Z)\mid Y)` computed with the map $`f` fixed,
$`T(p)\le M-B/2+3h/2`; the page also proves the exact average-score identity behind it. This is the first
inequality of the assembly (step 2 of the [route](https://github.com/AlexisOlson/natural-latents/blob/main/docs/overview.md#the-route)). For the supplied setup
latent, whose posteriors are positive, and every $`a>1`, the exponential race supplies such an $`F` with
$`h\le aB+2\,j(a)\,d`, where $`j(a)=a\ln\Gamma(1-1/a)-\gamma_E` with $`\gamma_E` Euler's
constant, and $`d` is the mismatch of (D3); the mismatch payment then bounds $`d`. The ledger lemma itself needs no
positivity. In the assembly
`NaturalLatents.General.T_le_of_connected` (`NaturalLatents/General/Pricing.lean`), `T_le_ledger` is applied to the
setup latent and the family given by `exists_race`.

# 4. The ledger

Units and conventions are those of section 0 of the [contact page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md): entropies and informations are in nats,
conditional sums range over positive-probability conditioning events, and $`D_p(f)=I(X;Y\mid f(Z))+H(f(Z)\mid X)+H(f(Z)\mid Y)`
is the deterministic score of a map $`f`, so that $`T(p)=\min_fD_p(f)` as in (D3). The random map $`F` is the one of
step 2 of the [route](https://github.com/AlexisOlson/natural-latents/blob/main/docs/overview.md#the-route), not the cap $`F` of the [cap page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/cap.md); $`Q=F(Z)`, $`U`, $`A` and $`\Delta`
below are local, and $`Q` is not the reference of the [race page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/race.md).

:::theorem "L4.1" (parent := "ledger") (lean := "NaturalLatents.General.T_le_ledger, NaturalLatents.General.ledger_calibrated_graph, NaturalLatents.General.ledger_detScore_coordinate_identity, NaturalLatents.General.ledger_information_balance, NaturalLatents.General.ledger_average_MI_lower, stoch_to_det.T_le_score") (uses := "") (tags := "partly kernel-verified")
*Lemma L4.1 (calibrated finite-map averaging and the ledger).* Let $`X,Y,L` be finite random variables, $`Z=(X,Y)`,
and let $`p` be the law of $`Z`. Let $`F` be a finite-valued random deterministic map from $`\mathrm{supp}\,p` to the
label set of $`L`, independent of $`Z`. Suppose $`\Pr(F(z)=i)=r_z(i)=\Pr(L=i\mid Z=z)` for every positive source atom
$`z`. Put $`Q=F(Z)`, $`M=I(X;Y\mid L)`, $`B=I(L;X\mid Y)+I(L;Y\mid X)`, and

$$`
h=H(Q\mid X,F)+H(Q\mid Y,F),\qquad
\Delta=I(F;X\mid Q)+I(F;Y\mid Q).
\qquad \text{(L1)}
`

Then $`\Delta\ge0`, and

$$`
\mathbb E_F D_p(F)
=M-\frac B2+\frac{3h}{2}-\frac{\Delta}{2},
\qquad
T(p)\le M-\frac B2+\frac{3h}{2}.
\qquad \text{(L2)}
`

Here $`D_p(f)` is the deterministic score of $`f(Z)`, as in section 0. No positivity, contact, optimality or
distinct-component hypothesis is needed. Fix a label $`i_0` and extend every map by $`i_0` outside
$`\mathrm{supp}\,p`. This does not change $`Q`, calibration, $`h`, $`\Delta` or any fixed-map score, and turns $`F`
into a random complete map, as used below.
:::

:::proof "L4.1"
Lean proves: $`T(p)\le M-B/2+3h/2` for a `CalibratedSeededFamily`, with the coordinate score and information-balance identities and the averaged mutual-information lower bound used to obtain it.

Use calibration and independence to identify the joint law, expand the entropy chain rules, and choose a map below the finite average. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/ledger.md#4-the-ledger).
:::

Lean: `NaturalLatents.General.T_le_ledger` (`NaturalLatents/General/Ledger.lean`) states only the inequality
$`T(p)\le M-B/2+3h/2`; Lean does not define $`\Delta` or state the identity for $`\mathbb E_FD_p(F)`. The
random map is a `CalibratedSeededFamily L` (`NaturalLatents/General/Definitions.lean`): a probability law on complete
maps from all of $`X\times Y` to the labels, calibrated at every cell of the support, whose independence from $`Z` is
the product law `seedSourceJoint`; $`h` is `seedEntropy` in the same file, the form (L7). The steps are in
`NaturalLatents/General/Ledger.lean`. (L5) is `ledger_calibrated_graph`. The final identity of (L4), in bits, is
`ledger_detScore_coordinate_identity`; conversion by `nats`, through `detScoreNat`, gives its page form. The final identity of (L3) with
$`U=L` is `ledger_information_balance`, stated in nats through `nats`. `ledger_average_MI_lower` is
bit-valued and states $`I(L;g(Z))\le\sum_f\Pr(F=f)I(f(Z);g(Z))` for every finite function $`g` of the cell; applying it
to each coordinate and converting by `nats` gives the lower bounds used from (L6), in place of the identities with
$`\Delta`. The proof averages
$`T(p)\le D_p(f)`, from `stoch_to_det.T_le_score` (`NaturalLatents/Upstream/Functionals.lean`), over the seed.
