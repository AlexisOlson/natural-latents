import Verso
import VersoManual
import VersoBlueprint
import NaturalLatents.Main

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "The extension by component split" =>

:::group "extension"
The extension by component split.
:::

This page proves that a bound $`T(q)\le C\tau(q)` with $`C\ge0`, known for every law $`q` whose support is connected,
holds for every finite law. Here $`T` is the deterministic optimum and $`\tau` the stochastic optimum of section 0 of
the [contact page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md). For a finite law $`p`, let $`k` index the connected components of its support; their
weights $`\rho_k` and normalized laws $`\bar p_k` are defined in Lemma E3.1. The page proves the two inequalities
$`\sum_k\rho_k\tau(\bar p_k)\le\tau(p)` and $`T(p)\le\sum_k\rho_kT(\bar p_k)`, and chains them with the bound on each
component. The assembly `NaturalLatents.General.T_le_of_connected` (`NaturalLatents/General/Pricing.lean`) proves
$`T(p)\le(13999/2000)\,\tau(p)` for laws with connected support only; `NaturalLatents.T_le_c_mul_tau`
(`NaturalLatents/Main.lean`) extends it to every finite law by `extension_of_connected` (step 9 of the
[route](https://github.com/AlexisOlson/natural-latents/blob/main/docs/overview.md#the-route)).

Each lemma below states its hypotheses, so that it can be read alone. Unless prefixed `stoch_to_det`, the Lean
declarations named below are in the namespace `NaturalLatents.General`; the `stoch_to_det` declarations are in
`NaturalLatents/Upstream/`, adapted from [DLorell/stoch_to_det](https://github.com/DLorell/stoch_to_det). The exceptions
are the declarations called private below (`componentIndex`, `restrict_score_gap`, `glueLatent_score`,
`Psi_eq_components`, `Phi_fiber_decomp`, `restrictLatent`, `restrict_score_le`, `glueLatent` and `glueLatent_isDet`): they
are Lean-private declarations in the namespace `stoch_to_det`, in the public file `NaturalLatents/Upstream/Connected.lean`.

# 3. The extension by component split

Units and conventions are those of section 0 of the [contact page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md): entropies and mutual informations are in
nats, conditional sums range over positive-probability conditioning events, and $`0\ln0=0`. A finite latent $`L` of a
law $`p`, its budgets $`M_L=I(X;Y\mid L)` and $`B_L=I(L;X\mid Y)+I(L;Y\mid X)`, the stochastic optimum
$`\tau(p)=\inf_L(M_L+B_L)`, the score $`D_p(f)` of a deterministic map $`f` and the deterministic optimum
$`T(p)=\min_fD_p(f)` are as in (D3). All alphabets are finite and nonempty; $`X,Y` and $`\mathcal X,\mathcal Y`
denote the same coordinate alphabets. Every law on this page is a law on the fixed rectangle $`\mathcal X\times\mathcal Y`.

Write $`S=\{z:p(z)>0\}`. This set is nonempty. Connectedness of the support, as a bipartite graph between the active
rows and the active columns of $`S`, is defined on the [setup page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/setup.md#1-the-setup-on-a-connected-support), together with its Lean
form `stoch_to_det.IsConnected`. On this page $`K` is the component label, not the replica budget $`K` of the
[replica page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/replica.md), and $`C` is any nonnegative constant.

> *Extension by component split.* Given some $`C\ge0` with $`T(q)\le C\tau(q)` for every law $`q` of connected
> support, the same inequality holds for every finite law.

Splitting at the common component label preserves the two leakage terms and isolates one nonnegative entropy term in the
mutual information. This gives an additive proof for every nonnegative coefficient, with no positivity assumption on the
resulting value of $`\tau`.

:::theorem "E3.1" (parent := "extension") (lean := "stoch_to_det.ComponentDecomp, stoch_to_det.exists_componentDecomp") (uses := "") (tags := "kernel-verified")
*Lemma E3.1 (component laws and their common label).* For every probability law $`p` on finite nonempty alphabets
$`\mathcal X\times\mathcal Y`, let $`S=\mathrm{supp}\,p` and let $`(S_k)_{k\in\mathcal K}` be its connected components
in the bipartite row-column graph. Put

$$`
\mathcal X_k=\{x:\exists y\ (x,y)\in S_k\},\qquad
\mathcal Y_k=\{y:\exists x\ (x,y)\in S_k\},\qquad
\rho_k=\sum_{z\in S_k}p(z)>0,
\qquad \text{(E3.A)}
`

and define $`\bar p_k` on $`\mathcal X\times\mathcal Y` by $`\bar p_k(z)=p(z)/\rho_k` on $`S_k` and zero elsewhere.
Then $`\bar p_k` is a probability law whose support $`S_k` is connected. If $`Z=(X,Y)` has law $`p` and $`K=k` when
$`Z\in S_k`, then $`K` is a function of $`X` alone and of $`Y` alone, almost surely.
:::

:::proof "E3.1"
Split the row-column support graph into components and normalize each positive component mass; either coordinate determines its component label. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/extension.md#3-the-extension-by-component-split).
:::

Lean: `stoch_to_det.ComponentDecomp` and `stoch_to_det.exists_componentDecomp`
(`NaturalLatents/Upstream/Connected.lean`). A component decomposition of $`p` is a finite family of weights forming a
probability vector and of probability laws on $`\mathcal X\times\mathcal Y` with connected supports whose mixture is
$`p`, such that support cells of two distinct parts share neither a row nor a column; its parts are the laws
$`\bar p_k`. The structure allows a zero weight, although the construction in `exists_componentDecomp` makes every
weight positive, and the label $`K` is the private function `componentIndex`.

:::theorem "E3.2" (parent := "extension") (lean := "_private.NaturalLatents.Upstream.Connected.0.stoch_to_det.restrict_score_gap, _private.NaturalLatents.Upstream.Connected.0.stoch_to_det.glueLatent_score") (uses := "E3.1") (tags := "kernel-verified")
*Lemma E3.2 (the three conditional mutual informations split).* For every $`p` and component label $`K` of
Lemma E3.1, and every finite latent $`L` of $`p`, let $`L^{(k)}` denote the same finite label under the conditional
joint law given $`K=k`. By (E3.B) it is a finite latent of $`\bar p_k`. Write $`\mathrm{cost}_p(L)=M_L+B_L`. Then

$$`
\mathrm{cost}_p(L)
 =H_p(K\mid L)+\sum_k\rho_k\,\mathrm{cost}_{\bar p_k}(L^{(k)}).
\qquad \text{(E3.C)}
`
:::

:::proof "E3.2"
Apply the entropy chain rule using the component label’s determinism from each coordinate to isolate its conditional entropy. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/extension.md#3-the-extension-by-component-split).
:::

Lean: there is no public statement of (E3.C). The private lemma `restrict_score_gap`
(`NaturalLatents/Upstream/Connected.lean`) states, for every latent of $`p`, that the weighted sum of the scores of its
conditional latents on the parts equals its score minus $`H_p(K\mid L)`, written as the prior average of the entropies
of the conditional laws of $`K` given each label; the private lemma `glueLatent_score` states the case of a latent glued
from latents of the parts, where $`H_p(K\mid L)=0`. Both are in bits and are proved from the score identity
`stoch_to_det.Latent.score_eq` (`NaturalLatents/Upstream/Envelope.lean`) and the split of the entropies of $`p` over the
parts (the private `Psi_eq_components` and `Phi_fiber_decomp`), not from the chain rule. On a part of weight zero the
private `restrictLatent` uses the constant latent.

:::theorem "E3.3" (parent := "extension") (lean := "stoch_to_det.sum_components_tau_le, stoch_to_det.T_le_sum_components, stoch_to_det.exists_tau_optimal_latent, stoch_to_det.exists_T_optimal_latent") (uses := "E3.1, E3.2") (tags := "kernel-verified")
*Lemma E3.3 (the two component inequalities).* For every finite law $`p` with component laws and weights as in
Lemma E3.1,

$$`
\sum_k\rho_k\tau(\bar p_k)\le\tau(p),\qquad
T(p)\le\sum_k\rho_k T(\bar p_k).
\qquad \text{(E3.F)}
`

The page and the Lean prove the same two directions, and the extension uses only these.
:::

:::proof "E3.3"
Restrict each stochastic latent to the components and glue minimizing deterministic codes with their component tags. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/extension.md#3-the-extension-by-component-split).
:::

Lean: `stoch_to_det.sum_components_tau_le` and `stoch_to_det.T_le_sum_components`
(`NaturalLatents/Upstream/Connected.lean`), in bits, for a component decomposition `D` of `p`:

```
theorem sum_components_tau_le {p : α × β → ℝ} (hp : IsPMF p) (D : ComponentDecomp p) :
    (∑ i, D.wt i * tau (D.part i)) ≤ tau p
theorem T_le_sum_components {p : α × β → ℝ} (hp : IsPMF p) (D : ComponentDecomp p) :
    T p ≤ ∑ i, D.wt i * T (D.part i)
```

The first restricts one attaining latent of $`p`, given by `stoch_to_det.exists_tau_optimal_latent`
(`NaturalLatents/Upstream/Envelope.lean`), rather than every latent, through the private `restrict_score_le`. In Lean
$`T` is an infimum over deterministic latents, and the second glues attaining deterministic latents of the parts, given
by `stoch_to_det.exists_T_optimal_latent`, with the private `glueLatent` and `glueLatent_isDet`; the glued labels are
pairs of a part and a label of that part.

:::theorem "E3.4" (parent := "extension") (lean := "NaturalLatents.General.extension_of_connected, stoch_to_det.reduce_to_connected") (uses := "E3.1, E3.3") (tags := "kernel-verified")
*Lemma E3.4 (the extension by component split).* Fix finite nonempty alphabets $`\mathcal X,\mathcal Y` and a real
number $`C\ge0`. Suppose $`T(q)\le C\tau(q)` for every probability law $`q` on these fixed alphabets whose support is
connected. Then $`T(p)\le C\tau(p)` for every probability law $`p` on the same alphabets, including those with
$`\tau(p)=0`.
:::

:::proof "E3.4"
Chain the two component inequalities with the connected-support bound and the nonnegativity of the constant. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/extension.md#3-the-extension-by-component-split).
:::

Lean: `NaturalLatents.General.extension_of_connected` (`NaturalLatents/General/Extension.lean`), in bits, which is
`stoch_to_det.reduce_to_connected` (`NaturalLatents/Upstream/Connected.lean`) applied to laws `Law X Y`:

```
theorem extension_of_connected (C : ℝ) (hC : 0 ≤ C)
    (hconnected : ∀ (q : Law X Y), stoch_to_det.IsPMF q →
      stoch_to_det.IsConnected (stoch_to_det.support q) →
      stoch_to_det.T q ≤ C * stoch_to_det.tau q)
    {p : Law X Y} (hp : stoch_to_det.IsPMF p) :
    stoch_to_det.T p ≤ C * stoch_to_det.tau p
theorem reduce_to_connected (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ q : α × β → ℝ, IsPMF q → IsConnected (support q) → T q ≤ C * tau q) :
    ∀ q : α × β → ℝ, IsPMF q → T q ≤ C * tau q
```

`reduce_to_connected` proves the chain (E3.J) from `T_le_sum_components` and `sum_components_tau_le`, using `hC` in the
last step exactly as the page does. `NaturalLatents.T_le_c_mul_tau` (`NaturalLatents/Main.lean`) applies
`extension_of_connected`, after `bits_of_nats` (`NaturalLatents/General/Nats.lean`) converts the connected bound to bits,
with `C = c`, the constant `NaturalLatents.c := 13999 / 2000`, and its nonnegativity
`c_nonneg`.
