import Verso
import VersoManual
import VersoBlueprint
import NaturalLatents.Main

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "The affinity bound" =>

:::group "affinity"
The affinity bound.
:::

This page proves that two distinct positive contacts of a common feasible kernel are separated in both marginals: each
marginal Bhattacharyya affinity is at most the quadratic $`b(s)`, so that $`-\ln BC_X-\ln BC_Y\ge\Psi(s)`, with the
separation $`s` defined below and $`b`, $`BC_X`, $`BC_Y` and $`\Psi` defined in (A2.1). The mismatch payment (step 6
of the [route](https://github.com/AlexisOlson/natural-latents/blob/main/docs/overview.md#the-route)) uses this for every pair of distinct components of the setup
latent: it combines this bound with the midpoint relative-entropy inequality and replica symmetry to bound the weighted
off-diagonal sum of separation prices $`\sum_{i\ne j}\mu_{ij}\Psi(s_{ij})` (with the pair masses $`\mu_{ij}` of
Lemma P5.1 and the separations $`s_{ij}` of Lemma P5.3 on the [payment page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/payment.md)) by the replica budget $`K`; the pair charge
then compares this sum with the mismatch $`d`. In the assembly `NaturalLatents.General.T_le_of_connected`
(`NaturalLatents/General/Pricing.lean`), the affinity hypothesis of `mismatch_payment` is discharged by
`affinity_bound` applied to the conclusion of `contact_moments`.

# 2. The affinity bound

Units and conventions are those of section 0 of the [contact page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md): logarithms are natural. Fix finite
nonempty alphabets $`X,Y`, a nonempty common support $`S\subseteq X\times Y` with all rows and columns used, a feasible
kernel $`w>0` on $`S` as in (C1.1), and two positive contacts $`P,R` of $`w` as in (C1.2). The fields of (C1.3) are the
cube-root marginal ratios $`f=(R_X/P_X)^{1/3}` and $`g=(R_Y/P_Y)^{1/3}`, their shifts $`U=f-1`
and $`V=g-1`, the mean losses $`A_0=1-E_Pf` and $`B_0=1-E_Pg`, the separation $`s=A_0+B_0`, and the quartic moment
$`J=E_P[U^2V^2]`; all expectations are under $`P`. For contacts as in section 1 define

$$`
\begin{aligned}
BC_X(P,R)&=\sum_x\sqrt{P_X(x)R_X(x)},&
BC_Y(P,R)&=\sum_y\sqrt{P_Y(y)R_Y(y)},\\
b(t)&=1-\frac{9t}{16}+\frac{3t^2}{64},&
\Psi(t)&=-2\ln b(t).
\end{aligned}
\qquad \text{(A2.1)}
`

The formula for $`\Psi(t)` is used only where $`b(t)>0`. This section uses the identities and the quartic estimate of
section 1 (Lemmas C1.1, C1.2 and C1.5 of the [contact page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md)); it establishes no further contact or Hessian
argument. The letters $`P,R`, $`f,g,U,V,A_0,B_0,s,J` are those of the contact page; $`h_X,h_Y` below are Hellinger
distances, not the seed entropy $`h`, and $`y=\sqrt f` is a local variable.

Lean: `affinityPoly` ($`b`), `separationPrice` ($`\Psi`) and `AffinityBound` (`NaturalLatents/General/Definitions.lean`),
all `NaturalLatents.General.*`; $`BC_X` and $`BC_Y` are `stoch_to_det.BC` (`NaturalLatents/Upstream/Toolkit.lean`)
applied to the $`X` and $`Y` marginals. `separationPrice` is defined for every real $`t` through Lean's totalized
logarithm, and agrees with (A2.1) where $`b(t)>0`.

:::theorem "A2.1" (parent := "affinity") (lean := "NaturalLatents.General.affinity_bhattacharyyaX_le, NaturalLatents.General.affinity_bhattacharyyaY_le, NaturalLatents.General.affinity_affinities_pos, NaturalLatents.General.affinity_conditional_square") (uses := "C1.1, C1.2, C1.5") (tags := "kernel-verified")
*Lemma A2.1 (each marginal affinity is at most the quadratic $`b` at $`s`).* For every finite nonempty $`X,Y`, every nonempty
common support $`S` with all rows and columns used, every feasible $`w>0` on $`S`, and every pair of distinct positive
contacts $`P,R`, assume the conclusions (C1.4), (C1.9), $`0<s<2`, and (C1.23) of section 1. Then the affinities defined in
(A2.1) satisfy

$$`
0<BC_X(P,R)\leq b(s),\qquad 0<BC_Y(P,R)\leq b(s).
\qquad \text{(A2.2)}
`
:::

:::proof "A2.1"
Factor the pointwise Hellinger deficit, use conditional Cauchy-Schwarz and the quartic bound, and expand the marginal Hellinger sums. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/affinity.md#2-the-affinity-bound).
:::

Lean: `NaturalLatents.General.affinity_bhattacharyyaX_le` and `NaturalLatents.General.affinity_bhattacharyyaY_le` (the upper bounds) and
`NaturalLatents.General.affinity_affinities_pos` (positivity), in `NaturalLatents/General/Affinity.lean`. They take
`CommonSupportPair S w P R` and, for the upper bounds, `ContactMoments S P R`, the conclusions of section 1 as stated in
Lean. In place of a named Cauchy-Schwarz theorem, `affinity_conditional_square` (same file) derives the conditional
comparison of (A2.6) and (A2.9) by expanding a nonnegative weighted square.

:::theorem "A2.2" (parent := "affinity") (lean := "NaturalLatents.General.affinity_bound, NaturalLatents.General.affinityPoly_pos") (uses := "C1.2, A2.1") (tags := "kernel-verified")
*Lemma A2.2 (the natural-log affinity payment and the equal-pair endpoint).* For every finite nonempty $`X,Y`, every
nonempty common support $`S` with all rows and columns used, every feasible $`w>0` on $`S`, and every pair of distinct
positive contacts $`P,R`, assume the conclusions of section 1 and of Lemma A2.1. Then $`\Psi(s)` is well defined and
nonnegative, and

$$`
-\ln BC_X(P,R)-\ln BC_Y(P,R)\geq\Psi(s).
\qquad \text{(A2.11)}
`

Distinct pairs and equal pairs are treated separately. For every equal pair $`P=R` on the same contact domain, (C1.3)
gives $`s=0`, so marginal normalization gives $`BC_X=BC_Y=b(0)=1` and $`\Psi(0)=0`, with equality in (A2.11).
:::

:::proof "A2.2"
Bound the quadratic on the scalar interval and apply monotonicity of the natural logarithm, treating equal contacts separately. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/affinity.md#2-the-affinity-bound).
:::

Lean: `NaturalLatents.General.affinity_bound` (`NaturalLatents/General/Affinity.lean`) proves `AffinityBound P R`, which
is (A2.11), for every `CommonSupportPair S w P R` given `ContactMoments S P R`. It obtains $`b(s)>0` from
`NaturalLatents.General.affinityPoly_pos` (`NaturalLatents/General/Definitions.lean`, positivity of $`b(t)` for $`t\le2`), and does
not state the range $`1/16\le b\le1`, the nonnegativity of $`\Psi(s)`, or the case of equal contacts.
