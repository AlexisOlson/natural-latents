import Verso
import VersoManual
import VersoBlueprint
import NaturalLatents.Main

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "The setup on a connected support" =>

:::group "setup"
The setup on a connected support.
:::

This page proves that every finite law $`p` whose support is connected has a setup latent: a finite latent $`L` that
attains $`\tau(p)`, with positive priors and pairwise distinct components, all of which are contacts of one common
feasible kernel, are positive on the whole support, and give positive posterior rows there. The proof has three steps:
an optimal latent and an affine minorant of the component functional $`\phi` (Lemma S1.2), a normalization that turns
the minorant into one feasible kernel whose contacts are exactly the components with zero gap (Lemma S1.3), and the
propagation of positivity along the connected support (Lemma S1.4); Lemma S1.1 is the cost identity they rest on. The
assembly `NaturalLatents.General.T_le_of_connected` (`NaturalLatents/General/Pricing.lean`) starts by obtaining this
setup from `exists_setup_of_connected`. It applies the race to the setup latent and its positive posterior rows, forms
each pair of distinct components as two positive contacts of the common kernel for the [contact moments](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md)
and the [affinity bound](https://github.com/AlexisOlson/natural-latents/blob/main/docs/affinity.md), passes the whole setup to the mismatch payment, and uses $`M+B=\tau(p)` in its
last step, as steps 1 to 8 of the [route](https://github.com/AlexisOlson/natural-latents/blob/main/docs/overview.md#the-route) describe.

Each lemma below states its hypotheses, so that it can be read alone. Unless prefixed `stoch_to_det`, the Lean
declarations named below are in the namespace `NaturalLatents.General`; the `stoch_to_det` declarations are in
`NaturalLatents/Upstream/`, adapted from [DLorell/stoch_to_det](https://github.com/DLorell/stoch_to_det) (see the
[upstream inputs](https://github.com/AlexisOlson/natural-latents/blob/main/docs/upstream.md)). The analytic content of Lemmas S1.2 to S1.4 is proved in Lean by that upstream code;
only the final assembly is in `NaturalLatents/General/Setup.lean`. The exceptions to the naming rule are the
declarations called private below (`Valid`, `exists_approx_valid_certificate`, `exists_optimal_valid_certificate`,
`exists_tau_optimal_kernel`, `valid_iff_feasible`, `maximizer_rpow_two_thirds`, `Gdef_eq_certificate_gap` and
`Gdef_eq_zero_iff`): they are Lean-private declarations in the namespace `stoch_to_det`, in the public file
`NaturalLatents/Upstream/Duality.lean`.

# 1. The setup on a connected support

> *Setup, connected support.* Given a law $`p` whose support $`S` is connected (as a bipartite row-column graph),
> there is an attained latent $`L` with $`M+B=\tau(p)`, priors $`\pi_i>0`, distinct components (duplicates merged),
> each a contact of one common feasible kernel $`w>0` on $`S` and positive on $`S`, and posterior rows positive on
> $`S`.

The proof is a supporting-plane argument and a normalization argument, with the support made explicit. Attainment and
the affine minorant hold for every finite law; connectedness is needed only to make all contacts positive.

Units and conventions are those of section 0 of the [contact page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md): entropies, mutual informations and
relative entropies are in nats, conditional sums range over positive-probability conditioning events, and
$`0\ln0=0`. The entropy $`H(q)` and the relative entropy $`D(a\Vert b)`, for probability laws $`a,b` with
$`\mathrm{supp}\,a\subseteq\mathrm{supp}\,b`, are as in (D2). All alphabets are finite and nonempty; $`X,Y` denote
both the coordinates and their alphabets, and $`Z=(X,Y)`. For a probability law $`p` on $`X\times Y` and any
probability law $`q` on $`X\times Y`, with marginals $`q_X,q_Y`, set

$$`
\phi(q)=2H(q_X)+2H(q_Y)-3H(q),\qquad
c(p)=2H(p)-H(p_X)-H(p_Y).
\qquad \text{(S1.A)}
`

A finite latent $`L` of $`p`, its budgets $`M_L=I(X;Y\mid L)` and $`B_L=I(L;X\mid Y)+I(L;Y\mid X)`, and the
stochastic optimum $`\tau(p)=\inf_L(M_L+B_L)` are as in (D3); concretely, a finite latent is a finite nonempty label set $`I`, probability weights
$`(\pi_i)_{i\in I}` and probability laws $`(q_i)_{i\in I}` on $`X\times Y` with $`p=\sum_i\pi_iq_i` and
$`\mathbb P(L=i,Z=z)=\pi_iq_i(z)`. Zero priors are allowed here; their component laws may be chosen arbitrarily.

Lean: a finite latent is `stoch_to_det.Latent` (`NaturalLatents/Upstream/Functionals.lean`); `mediation`,
`redundancy`, `negPhiNat` and `psiNat` are in `NaturalLatents/General/Definitions.lean`. `negPhiNat q` is
`-(nats (stoch_to_det.Phi q))` and `psiNat p` is `nats (stoch_to_det.Psi p)`, with `nats` the multiplication by
`Real.log 2` of `NaturalLatents/General/Nats.lean`, where the bit-valued
`stoch_to_det.Phi` $`=3H(q)-2H(q_X)-2H(q_Y)` and `stoch_to_det.Psi` are in `NaturalLatents/Upstream/Entropy.lean`;
the page's $`\phi` is therefore minus upstream's `Phi`, converted to nats.

Some letters on this page are local: $`a,b` in $`D(a\Vert b)` and (S1.P) are probability laws, not the race exponent
$`a` or the quadratic $`b` of (A2.1); $`u,v` are probability laws on $`X` and $`Y`, not the price bound $`u`;
$`c(p)` is the constant term of (S1.A), not the constant of the theorem; $`R(p)` is the value (S1.H), not a contact;
the $`d` of Carathéodory's theorem is a dimension, not the mismatch; $`E` is the set (S1.K) and $`\lambda` a
coefficient in (S1.L); and $`\Phi`, $`\Psi` in the Lean notes are upstream's bit-valued `Phi` and `Psi`, not the
separation price $`\Psi` of (A2.1).

Write $`S=\{z:p(z)>0\}`. This set is nonempty. Its active row and column alphabets are
$`X_S=\{x:\exists y,(x,y)\in S\}` and $`Y_S=\{y:\exists x,(x,y)\in S\}`. Connectedness means that the bipartite graph
with vertices $`X_S\sqcup Y_S` and edges $`S` is connected; equivalently, the cells of $`S` are connected by
shared-row and shared-column steps. Unused rows and columns do not create vertices in this graph. We keep the original
alphabets in the formulas, so all laws on an active alphabet are extended by zero on unused coordinates.

Lean: the support is `stoch_to_det.support`, and `stoch_to_det.IsConnected`
(`NaturalLatents/Upstream/Functionals.lean`) asks that any two cells of $`S` be joined by a chain of cells of $`S`,
each sharing a row or a column with the next (`stoch_to_det.Adj`); this is the cell form of the definition above.

For a kernel $`w` that is positive on $`S` and zero outside $`S`, and for probability laws $`u` on $`X` and $`v`
on $`Y`, write

$$`
\Lambda(w;u,v):=\sum_{(x,y)\in S}w(x,y)u(x)^{2/3}v(y)^{2/3}.
\qquad \text{(S1.B)}
`

Feasibility and contact are defined in (C1.1) and (C1.2) on the
[contact page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md#1-contact-moments-and-the-feasible-hessian): $`w` is feasible when $`\Lambda(w;u,v)\le1`
for every such $`u,v`, and a contact of $`w` is a probability law supported on $`S` that satisfies the contact
equation (C1.2) on $`S`. The contact equation then also holds off $`S`, where both sides vanish. On this page both are
read on the original alphabets: feasibility for all $`u,v` on $`X` and $`Y` implies the required feasibility on the
active alphabets, and allowing unused coordinates in $`u,v` does not impose any positivity requirement on them. Unlike
the positive contacts of the contact page, defined after unused rows and columns are removed, a contact here keeps the
original alphabets and is not assumed positive on $`S`; Lemma S1.4 proves that positivity.

Lean: $`\Lambda` is `stoch_to_det.Lambda`, feasibility is `stoch_to_det.Feasible`, which also records $`w>0` on
$`S`, and the contact property is `stoch_to_det.IsContact` (a probability law, zero off $`S`, satisfying the contact
equation on $`S`), all in `NaturalLatents/Upstream/Duality.lean`. Neither constrains $`w` outside $`S`.

:::theorem "S1.1" (parent := "setup") (lean := "NaturalLatents.General.score_nats, NaturalLatents.General.mediation_add_redundancy_eq_score, stoch_to_det.Latent.score_eq") (uses := "") (tags := "kernel-verified")
*Lemma S1.1 (universal finite entropy cost identity).* For every finite nonempty $`X,Y`, every probability law $`p`
on $`X\times Y`, and every finite latent $`L` of $`p`, including zero priors,

$$`
M_L+B_L=c(p)+\sum_{i\in I}\pi_i\phi(q_i).
\qquad \text{(S1.C)}
`
:::

:::proof "S1.1"
Expand the finite conditional entropies and collect the three mutual information terms. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/setup.md#1-the-setup-on-a-connected-support).
:::

Lean: `score_nats` (`NaturalLatents/General/Definitions.lean`), with `mediation_add_redundancy_eq_score` identifying
`mediation L + redundancy L` with `nats L.score`; it converts the bit-valued identity `stoch_to_det.Latent.score_eq`
(`NaturalLatents/Upstream/Envelope.lean`), score $`=\Psi(p)-\sum_i\pi_i\Phi(q_i)`, by `nats`, rather than expanding
the entropies as above.

:::theorem "S1.2" (parent := "setup") (lean := "stoch_to_det.exists_tau_optimal_latent, stoch_to_det.tau_eq_Psi_sub_envelope, stoch_to_det.exists_common_contact_pair") (uses := "S1.1") (tags := "partly kernel-verified")
*Lemma S1.2 (attainment and a finite affine minorant).* For every finite nonempty $`X,Y` and every probability law
$`p` on $`X\times Y`, there are a finite latent decomposition of $`p`, positive priors $`\pi_i`, pairwise distinct
component laws $`q_i` supported on $`S=\mathrm{supp}\,p`, and a real vector $`\ell` on the whole rectangle, such
that $`M_L+B_L=\tau(p)`, $`\ell=0` off $`S`, and

$$`
\phi(q)\ge\ell\cdot q\quad(q\in\Delta_S),\qquad
\ell\cdot p=R(p),\qquad
\phi(q_i)=\ell\cdot q_i\quad(i\in I).
\qquad \text{(S1.F)}
`

Here $`\Delta_S` denotes the probability simplex on $`S`, embedded by zero extension,
$`\ell\cdot q=\sum_{z\in S}\ell_zq(z)` on that simplex, and $`R(p)` is the infimum (S1.H) of the average of $`\phi`
over finite mixtures in $`\Delta_S` with barycenter $`p`, attained in the proof below. The minorant in (S1.F) is asserted only on $`\Delta_S`. No connectedness is assumed.
:::

:::proof "S1.2"
Lean proves: every finite law has an attaining latent and $`\tau=\Psi-\mathrm{concaveEnvelopePhi}` in bits, and an attaining latent with a common feasible kernel whose positive-prior components are contacts.

Use compactness and Carathéodory for attainment, merge equal components, and obtain the minorant by a supporting hyperplane on the support face. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/setup.md#1-the-setup-on-a-connected-support).
:::

Lean: attainment is `stoch_to_det.exists_tau_optimal_latent` and (S1.I) is `stoch_to_det.tau_eq_Psi_sub_envelope`, with
$`R(p)` equal to $`-\ln2` times `stoch_to_det.concaveEnvelopePhi` (all in `NaturalLatents/Upstream/Envelope.lean`);
the minorant is built inside `stoch_to_det.exists_common_contact_pair` (`NaturalLatents/Upstream/Duality.lean`),
through the private `exists_tau_optimal_kernel`. There it is a bit-valued certificate $`\kappa=-\ell/\ln2`
(the variable `c` in `Duality.lean`), and the minorant property is the private predicate `Valid`:
$`\Phi(q)\le\sum_{z\in S}\kappa_zq(z)`, with $`\Phi` upstream's bit-valued `Phi`, for every probability law $`q` supported on $`S`. An exact certificate is
obtained by the private `exists_approx_valid_certificate` and `exists_optimal_valid_certificate`. The Lean differs
from the page in five ways:

- *Attainment.* `exists_tau_optimal_latent` maximizes $`\sum_i\pi_i\Phi(q_i)` over the compact slice at $`p` of the
  convex hull of the graph of `Phi` over all laws on $`X\times Y`, and reads a latent off the maximizer; it records no
  bound on the number of labels.
- *Minorant.* Instead of a supporting hyperplane at the boundary point, the Lean strictly separates the point
  $`\varepsilon` beyond the optimal value over $`p` from the compact convex hull of the graph of `Phi` over the laws
  supported on $`S` (Mathlib's `geometric_hahn_banach_closed_point`), which makes the vertical coefficient positive
  without the perturbation $`p\pm\varepsilon v`, and then takes an exact certificate as a minimizer of the value at
  $`p` over the compact set of valid certificates that vanish off $`S`, are nonnegative on $`S` (since
  $`\phi(\delta_z)=0` for the point mass $`\delta_z`) and have value at $`p` at most the optimum plus one.
- *Positive priors.* Zero-prior labels are pruned by `stoch_to_det.exists_seedSetup`
  (`NaturalLatents/Upstream/Seed.lean`), after the contact step. In Lean the pruning, and the merging below, are done
  only for connected support (`exists_seedSetup` takes the connectedness hypothesis, and `exists_clustering` takes a
  `stoch_to_det.SeedSetup`); the unconditional Lean statement is `exists_common_contact_pair`, whose zero-prior
  components may be arbitrary.
- *Distinct components.* Duplicates are merged only at the end, by `stoch_to_det.exists_clustering`
  (`NaturalLatents/Upstream/Quotient.lean`) inside `exists_setup_of_connected` (`NaturalLatents/General/Setup.lean`),
  and not before the minorant as in (S1.J).
- *The equality case.* The zero gaps (S1.N) are proved for an arbitrary optimal latent given by
  `exists_tau_optimal_latent`, not for the latent built in the proof.

:::theorem "S1.3" (parent := "setup") (lean := "stoch_to_det.exists_common_contact_pair, stoch_to_det.exists_seedSetup, stoch_to_det.Gdef_nonneg") (uses := "S1.2") (tags := "partly kernel-verified")
*Lemma S1.3 (normalization gives one feasible kernel and its contacts).* For every finite nonempty $`X,Y`, every
probability law $`p` on $`X\times Y`, and every vector $`\ell` and optimal latent furnished by Lemma S1.2, the masked
kernel, defined by the two cases on and off the support,

$$`
w_z=
\begin{cases}
\exp(\ell_z/3),&z\in S,\\
0,&z\notin S
\end{cases}
\qquad \text{(S1.O)}
`

is feasible in the sense of (C1.1), and each $`q_i` is a contact of this same kernel. More generally, for every
$`q\in\Delta_S`, equality $`\phi(q)=\ell\cdot q` holds if and only if $`q` is a contact of $`w`.
:::

:::proof "S1.3"
Lean proves: an attaining latent has a common feasible kernel with contacts at positive-prior labels, connected support admits a positive-prior `SeedSetup`, and $`Gdef\ge0` for every supported probability law.

Normalize the exponential kernel and use Gibbs inequality to prove feasibility and identify the zero-gap contacts. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/setup.md#1-the-setup-on-a-connected-support).
:::

Lean: `stoch_to_det.exists_common_contact_pair` (`NaturalLatents/Upstream/Duality.lean`), which returns an attaining
latent, a feasible kernel, and the contact property of every component of positive prior; `stoch_to_det.exists_seedSetup`
(`NaturalLatents/Upstream/Seed.lean`) packages them, with zero priors pruned, as `stoch_to_det.SeedSetup`. The kernel is
$`2^{-\kappa/3}` for the bit-valued certificate $`\kappa` of Lemma S1.2, which equals $`\exp(\ell_z/3)` on $`S`. The
Lean differs from the page in three ways:

- *Feasibility.* Instead of normalizing at an arbitrary pair $`u,v` as in (S1.Q)–(S1.S), the private
  `valid_iff_feasible` maximizes $`\Lambda(w;u,v)` over pairs of probability vectors and applies validity at the
  normalized maximizer, whose marginals are the maximizing pair by the equality case of Young's inequality (the private
  `maximizer_rpow_two_thirds`).
- *The equality case.* The private `Gdef_eq_zero_iff` says that the defect
  $`3\sum_{z:q(z)>0}q(z)\ln\bigl(q(z)/m_q(z)\bigr)/\ln2` (in bits), taken against the unnormalized $`m_q`,
  vanishes exactly at contacts, and the private `Gdef_eq_certificate_gap` identifies the defect with the certificate
  gap, as in (S1.U); its nonnegativity is `stoch_to_det.Gdef_nonneg`.
- *Masking.* The upstream kernel is not masked: it equals one off $`S`, which neither `Feasible` nor `IsContact`
  reads. `exists_setup_of_connected` (`NaturalLatents/General/Setup.lean`) replaces it by the masked kernel (S1.O) and
  checks that $`\Lambda` is unchanged. `CommonSetup` does not record that $`w` vanishes off $`S`.

:::theorem "S1.4" (parent := "setup") (lean := "stoch_to_det.contact_support_eq, NaturalLatents.General.exists_setup_of_connected") (uses := "S1.2, S1.3") (tags := "kernel-verified")
*Lemma S1.4 (positivity propagation and the setup on a connected support).* For every finite nonempty $`X,Y`, every
law $`p` with connected support $`S`, every feasible kernel $`w` positive on $`S` and zero off $`S`, and every
contact probability law $`q` on $`S`, one has $`q(z)>0` for every $`z\in S`. In particular, the latent and kernel
furnished by Lemmas S1.2 and S1.3 attain $`\tau(p)`, have positive priors and distinct components, and have positive
posterior rows throughout $`S`.
:::

:::proof "S1.4"
Perturb a missing marginal toward a point mass and propagate positivity along the connected support; then divide the positive joint masses by the source mass. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/setup.md#1-the-setup-on-a-connected-support).
:::

Lean: the positivity claim is `stoch_to_det.contact_support_eq` (`NaturalLatents/Upstream/Duality.lean`), stating
`support q = S` for a contact `q` of a feasible kernel on a connected `S`, and the setup is
`exists_setup_of_connected` (`NaturalLatents/General/Setup.lean`), which proves `Nonempty (CommonSetup p)` for every
probability law `p` with connected support:

```
theorem exists_setup_of_connected {p : Law X Y} (hp : stoch_to_det.IsPMF p)
    (hconn : stoch_to_det.IsConnected (stoch_to_det.support p)) : Nonempty (CommonSetup p)
```

The structure `CommonSetup` (`NaturalLatents/General/Definitions.lean`) has the fields `L` (the latent), `w` (the
kernel), `feasible`, `attained` ($`M+B=\tau(p)`), `prior_pos`, `distinct`, `contact`, `positive` and `rows_pos`; the
last seven are the properties in the box above. The Lean differs from the page in four ways:

- *Positivity.* `stoch_to_det.contact_support_eq` does not assume $`w=0` off $`S`, and replaces the perturbations (S1.X) and
  (S1.Y) by the equality case of Young's inequality (the private `maximizer_rpow_two_thirds`) at $`(q_X,q_Y)`, which
  maximizes $`\Lambda` in each argument because $`\Lambda(w;q_X,q_Y)=1`, so that $`R_0=0` exactly when
  $`q_X(x_0)=0`, and likewise for columns.
- *Propagation.* Positivity is propagated along chains of cells sharing a row or a column (`stoch_to_det.Adj`),
  starting from one positive cell, rather than along the edges of the bipartite graph.
- *Assembly.* `exists_setup_of_connected` takes a `stoch_to_det.SeedSetup` from `stoch_to_det.exists_seedSetup` and a
  `stoch_to_det.Clustering` from `stoch_to_det.exists_clustering`, whose cluster laws are distinct contacts
  (`stoch_to_det.Clustering.Q_isContact`, `stoch_to_det.Clustering.Q_injective`). It then uses
  `setupConn_prior_pos` (cluster masses are positive) and `setupConn_sum_weighted` (cluster sums equal label sums,
  proved from `setupConn_comp_eq_Q`, which identifies each label's law with its cluster's), and `score_nats` with `mediation_add_redundancy_eq_score` to transfer $`M+B=\tau(p)` from the seed latent to the merged one.
- *Posterior rows.* `rows_pos` is proved by dividing $`\pi_iq_i(z)>0` by $`p(z)>0`; the row sum in (S1.Z) is not
  stated.
