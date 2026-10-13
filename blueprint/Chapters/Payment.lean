import Verso
import VersoManual
import VersoBlueprint
import NaturalLatents.Main

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "The mismatch payment" =>

:::group "payment"
The mismatch payment.
:::

This page proves that the posterior mismatch $`d` of the supplied setup latent is paid by its budgets: for every
$`\beta\ge0` and $`\gamma>0` such that the pair charge $`PC(\beta,\gamma)` of section 0 of the
[contact page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md) holds, $`\gamma d\le(1+2\beta)M+\beta B`. The proof weights the pair charge of each pair of
distinct components by the probability $`\mu_{ij}` that two labels drawn independently from the posterior at the same
cell are $`i` and $`j`, bounds the separation prices by the replica budget $`K` through the
[affinity bound](https://github.com/AlexisOlson/natural-latents/blob/main/docs/affinity.md) and a midpoint relative-entropy inequality, and closes with the
[replica budget](https://github.com/AlexisOlson/natural-latents/blob/main/docs/replica.md) $`K\le2M+B`. The argument is generic in $`(\beta,\gamma)`; at the pair charge
$`PC(23/250,7/60)`, it gives $`(7/60)\,d\le(148/125)\,M+(23/250)\,B`. This is
step 6 of the [route](https://github.com/AlexisOlson/natural-latents/blob/main/docs/overview.md#the-route). In the assembly
`NaturalLatents.General.T_le_of_connected` (`NaturalLatents/General/Pricing.lean`), `mismatch_payment` is applied to the
setup latent, with its affinity hypothesis discharged by `affinity_bound` applied to `contact_moments`, its replica hypothesis by
`replica_budget`, and its pair-charge hypothesis by the pair charge $`PC(23/250,7/60)`, `pairCharge_C`.

Each lemma below states its hypotheses, so that it can be read alone. Units and conventions are those of section 0 of
the [contact page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md): information is in nats, $`M`, $`B` and $`d` are defined in (D3), the mutual
information $`I(q)` of a law on $`X\times Y` in (D2), and a relative entropy sums over the positive mass of its first
argument. The replicas $`L_1,L_2` are those of (Q3.2) on the [replica page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/replica.md), and $`K` is defined in (Q3.3)
there. Unless prefixed `stoch_to_det`, the Lean declarations named below are in the namespace `NaturalLatents.General`,
in `NaturalLatents/General/Payment.lean`; the `stoch_to_det` declarations are in `NaturalLatents/Upstream/`, adapted
from [DLorell/stoch_to_det](https://github.com/DLorell/stoch_to_det). In Lemma P5.2 the letters $`a,b,t,v` are
probability vectors and $`c` is their Bhattacharyya coefficient, not the race exponent $`a`, the quadratic $`b` of
(A2.1) or the constant of the theorem.

# 5. The mismatch payment

:::theorem "P5.1" (parent := "payment") (lean := "NaturalLatents.General.payment_pairMass_comm, NaturalLatents.General.payment_pairMass_rows, NaturalLatents.General.payment_pairMass_nonneg, NaturalLatents.General.payment_condMI_KL, NaturalLatents.General.payment_midpoint_profile, NaturalLatents.General.payment_pairMass_pos") (uses := "Q3.1") (tags := "kernel-verified")
*Lemma P5.1 (replica symmetry and the relative-entropy profile).* Let
$`p=\sum_i \pi_i q_i` be any finite latent with positive priors, and construct the
replicas by (Q3.2). Put $`\mu_{ij}=\Pr(L_1=i,L_2=j)` and
$`\Omega=\{(i,j):\mu_{ij}>0\}`. For $`(i,j)\in\Omega`, put
$`t_{ij}=\Pr(Z=\cdot\mid L_1=i,L_2=j)`; positive pair mass is where the
conditional law is defined, and a pair of zero mass is omitted. Then

$$`
\begin{aligned}
\mu_{ij}&=\sum_{z:p(z)>0}p(z)r_z(i)r_z(j)=\mu_{ji},\\
t_{ij}(z)&=\frac{p(z)r_z(i)r_z(j)}{\mu_{ij}}=t_{ji}(z),\\
\sum_j\mu_{ij}
 &=\sum_{z:p(z)>0}p(z)r_z(i)\sum_jr_z(j)
 =\sum_{z:p(z)>0}p(z)r_z(i)=\pi_i.
\end{aligned}
\qquad \text{(P5.1)}
`

Both marginal relative-entropy sums have an endpoint symmetrization:

$$`
\begin{aligned}
I(L_2;X\mid L_1)
 &=\sum_{(i,j)\in\Omega}\mu_{ij}
 D((t_{ij})_X\Vert(q_i)_X)\\
 &=\sum_{(i,j)\in\Omega}\mu_{ij}
 D((t_{ij})_X\Vert(q_j)_X)\\
 &=\frac12\sum_{(i,j)\in\Omega}\mu_{ij}
 \bigl[D((t_{ij})_X\Vert(q_i)_X)
       +D((t_{ij})_X\Vert(q_j)_X)\bigr],\\
I(L_2;Y\mid L_1)
 &=\sum_{(i,j)\in\Omega}\mu_{ij}
 D((t_{ij})_Y\Vert(q_i)_Y)\\
 &=\sum_{(i,j)\in\Omega}\mu_{ij}
 D((t_{ij})_Y\Vert(q_j)_Y)\\
 &=\frac12\sum_{(i,j)\in\Omega}\mu_{ij}
 \bigl[D((t_{ij})_Y\Vert(q_i)_Y)
       +D((t_{ij})_Y\Vert(q_j)_Y)\bigr].
\end{aligned}
\qquad \text{(P5.2)}
`
:::

:::proof "P5.1"
Expand the posterior pair masses and conditional relative entropies, then interchange the replica labels and average. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/payment.md#5-the-mismatch-payment).
:::

Lean: `pairMass` (`NaturalLatents/General/Definitions.lean`) is $`\mu_{ij}=\sum_zp(z)r_z(i)r_z(j)`, summing over all cells, those with $`p(z)=0` contributing zero, with `payment_pairMass_comm`
(symmetry), `payment_pairMass_rows` (row sums $`\pi_i`) and `payment_pairMass_nonneg`; `payment_condMI_KL` states the first line of
(P5.2), in bits, for any finite law of $`(L_1,L_2,W)` whose rows have the form $`\pi_iP_i` and whose pair masses are all
positive, and the symmetrization is a step inside `payment_midpoint_profile`. Lean names neither $`t_{ij}` nor
$`\Omega`: on the setup latent every posterior is positive, so every $`\mu_{ij}` is positive (`payment_pairMass_pos`) and
$`\Omega` contains every pair.

:::theorem "P5.2" (parent := "payment") (lean := "stoch_to_det.bhattacharyya_le") (uses := "") (tags := "kernel-verified")
*Lemma P5.2 (normalized midpoint; Gibbs' inequality).* Let $`a,b,t` be
probability vectors on a finite nonempty set, with $`a_x>0` and $`b_x>0` wherever
$`t_x>0`. Put $`c=BC(a,b)=\sum_x \sqrt{\smash[b]{a_x b_x}}` and $`v_x=\sqrt{\smash[b]{a_x b_x}}/c`.
Then $`c>0`, $`v` is a probability vector, and

$$`
\begin{aligned}
D(t\Vert v)
 &=\sum_{x:t_x>0}t_x\ln\frac{t_x}{\frac{\sqrt{a_xb_x}}{c}}\\
 &=\sum_{x:t_x>0}t_x\ln t_x
   -\frac12\sum_{x:t_x>0}t_x\ln a_x
   -\frac12\sum_{x:t_x>0}t_x\ln b_x+\ln c\\
 &=\frac{D(t\Vert a)+D(t\Vert b)}2+\ln c.
\end{aligned}
\qquad \text{(P5.3)}
`

Consequently

$$`
\frac{D(t\Vert a)+D(t\Vert b)}2
 =D(t\Vert v)-\ln BC(a,b)\ge-\ln BC(a,b).
\qquad \text{(P5.4)}
`
:::

:::proof "P5.2"
Normalize the geometric midpoint, expand its relative entropy, and apply the finite Gibbs inequality. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/payment.md#5-the-mismatch-payment).
:::

Lean: `stoch_to_det.bhattacharyya_le` (`NaturalLatents/Upstream/Toolkit.lean`) states (P5.4) in bits, as
$`-2\log_2BC(a,b)\le D_2(t\Vert a)+D_2(t\Vert b)` with $`D_2` the relative entropy in bits, under absolute continuity
of $`t` with respect to $`a` and $`b`; the reference $`v` and the identity (P5.3) appear only inside its proof.

:::theorem "P5.3" (parent := "payment") (lean := "NaturalLatents.General.payment_profile_payment, NaturalLatents.General.payment_coordinate_payment, NaturalLatents.General.payment_midpoint_profile, NaturalLatents.General.payment_bhattacharyya_self") (uses := "P5.1, P5.2, A2.2") (tags := "kernel-verified")
*Lemma P5.3 (separation-profile payment).* Let $`X,Y,L` be finite random
variables with latent decomposition $`p=\sum_i\pi_iq_i`, positive priors and
distinct components that are positive contacts of one feasible kernel on a
common support. Suppose the affinity bound, (A2.11) on the [affinity page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/affinity.md), holds for every distinct pair.
Let $`BC_X` and $`BC_Y` be the marginal affinities of (A2.1) on the affinity page, and put $`s_{ij}=s(q_i,q_j)` for
$`i\ne j`, with $`s` as in (C1.3) on the [contact page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md). The replicas (Q3.2) satisfy

$$`
K\ge\sum_{\substack{(i,j)\in\Omega\\i\ne j}}
\mu_{ij}\bigl[-\ln BC_X(q_i,q_j)-\ln BC_Y(q_i,q_j)\bigr]
\ge\sum_{\substack{(i,j)\in\Omega\\i\ne j}}
\mu_{ij}\Psi(s_{ij}).
\qquad \text{(P5.5)}
`
:::

:::proof "P5.3"
Delete the nonnegative diagonal relative entropy terms, apply the midpoint inequality, and then use the affinity bound. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/payment.md#5-the-mismatch-payment).
:::

Lean: `payment_profile_payment` states the outer inequality of (P5.5), $`\sum_{i\ne j}\mu_{ij}\Psi(s_{ij})\le K`, for the
setup latent given `AffinityBound` for every distinct pair, through `payment_coordinate_payment` (one coordinate at a
time) and `payment_midpoint_profile` (the sum over all pairs of (P5.4)); the middle expression of (P5.5) appears only
inside its proof. Lean keeps the diagonal pairs and applies (P5.4) to them too, where $`-\ln BC(q_i,q_i)=0`
(`payment_bhattacharyya_self`), instead of deleting the diagonal relative-entropy summands.

:::theorem "P5.4" (parent := "payment") (lean := "NaturalLatents.General.payment_mismatch, NaturalLatents.General.payment_mediation_average, NaturalLatents.General.payment_information_payment") (uses := "P5.1") (tags := "kernel-verified")
*Lemma P5.4 (mismatch mass and the exact information sum).* For every finite
latent $`p=\sum_i \pi_i q_i` with positive priors and replicas (Q3.2), with $`d` as in (D3) and $`I(q_i)` as in (D2),

$$`
\begin{aligned}
\sum_{i\ne j}\mu_{ij}
 &=\sum_{z:p(z)>0}p(z)\sum_{i\ne j}r_z(i)r_z(j)\\
 &=\sum_{z:p(z)>0}p(z)
 \left[\left(\sum_i r_z(i)\right)^2-\sum_i r_z(i)^2\right]\\
 &=\sum_{z:p(z)>0}p(z)\left[1-\sum_i r_z(i)^2\right]
 =E_Z\!\left[1-\sum_i r_Z(i)^2\right]=d.
\end{aligned}
\qquad \text{(P5.6)}
`

By the definition of conditional mutual information, $`M=I(X;Y\mid L)=\sum_i\pi_iI(q_i)`. The symmetric row and
column sums from (P5.1) also give

$$`
\begin{aligned}
\sum_{i\ne j}\mu_{ij}\frac{I(q_i)+I(q_j)}2
 &=\frac12\sum_i(\pi_i-\mu_{ii})I(q_i)
  +\frac12\sum_j(\pi_j-\mu_{jj})I(q_j)\\
 &=\sum_i(\pi_i-\mu_{ii})I(q_i)\\
 &=M-\sum_i\mu_{ii}I(q_i)\le M.
\end{aligned}
\qquad \text{(P5.7)}
`
:::

:::proof "P5.4"
Expand the finite posterior square sum and use symmetric pair-mass row sums with nonnegative component information. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/payment.md#5-the-mismatch-payment).
:::

Lean: `payment_mismatch` states (P5.6) as $`d=\sum_i\sum_{j\ne i}\mu_{ij}`, proved through $`d=1-\sum_i\mu_{ii}` and the
total mass $`\sum_{i,j}\mu_{ij}=1` rather than expanding $`\left(\sum_ir_z(i)\right)^2` cell by cell; `payment_mediation_average` states
$`M=\sum_i\pi_iI(q_i)`; and `payment_information_payment` states only the inequality of (P5.7), without the identity
with $`M-\sum_i\mu_{ii}I(q_i)`.

:::theorem "P5.5" (parent := "payment") (lean := "NaturalLatents.General.mismatch_payment") (uses := "P5.3, P5.4, Q3.1") (tags := "kernel-verified")
*Lemma P5.5 (the mismatch payment for every nonnegative charge coefficient).*
For every $`\beta\ge0`, $`\gamma>0`, let $`p=\sum_i \pi_i q_i` be a latent of the
setup of section 0 of the [contact page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md), with positive priors and distinct components, satisfying
$`M+B=\tau(p)`. Thus every $`q_i` is positive on $`S=\mathrm{supp}\,p` and is a
contact of one common feasible $`w>0` on $`S`. Assume the affinity bound for its
distinct pairs and $`PC(\beta,\gamma)` on the domain of their common feasible
kernel: for every two distinct positive contacts $`P,R` of such a kernel,

$$`
\frac{I(P)+I(R)}2+\beta\Psi(s(P,R))\ge\gamma.
\qquad \text{(P5.8)}
`

With $`M`, $`B` and $`d` as in (D3), and with the replica budget $`K\le2M+B`,

$$`
\gamma d\le(1+2\beta)M+\beta B.
\qquad \text{(P5.9)}
`
:::

:::proof "P5.5"
Weight each off-diagonal pair charge by its replica mass and close with the profile payment, information payment, and replica budget. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/payment.md#5-the-mismatch-payment).
:::

Lean: `mismatch_payment`, for a `CommonSetup p` and real $`\beta,\gamma` with $`\beta\ge0` and $`\gamma\ge0`, taking
as hypotheses `AffinityBound` for every distinct pair, the replica budget $`K\le2M+B`, and
`HasPairCharge CommonSupportPair beta gamma`, the pair charge on distinct positive contacts of any common feasible kernel; it
requires $`\gamma\ge0` where the page keeps $`\gamma>0`, and $`d_*` of (P5.D) has no counterpart, the off-diagonal sum
entering through `payment_mismatch`.

*The payment at the pair charge PC(23/250, 7/60).* The pair charge $`PC(23/250,7/60)` is inequality (P5.8) with
$`\beta=23/250` and $`\gamma=7/60`, on every two distinct positive contacts of a common feasible kernel. Since
$`1+2\cdot23/250=148/125`, Lemma P5.5 at these values gives

$$`
\frac7{60}\,d\le\frac{148}{125}\,M+\frac{23}{250}\,B,
\qquad\text{equivalently}\qquad
d\le\frac{1776}{175}\,M+\frac{138}{175}\,B.
\qquad \text{(P5.11)}
`

The second form divides by $`\gamma=7/60`: $`(60/7)(148/125)=1776/175` and
$`(60/7)(23/250)=138/175`.

Lean: `mismatch_payment` at `(23/250) (7/60)` with `pairCharge_C` (`NaturalLatents/General/PairCharge.lean`), the
pair charge $`PC(23/250,7/60)`, inside `T_le_of_connected` (`NaturalLatents/General/Pricing.lean`); the divided form of (P5.11)
is not stated.
