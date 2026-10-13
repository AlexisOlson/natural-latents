import Verso
import VersoManual
import VersoBlueprint
import NaturalLatents.Main

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "The table form" =>

:::group "table-form"
The table form.
:::

This page describes how `NaturalLatents/Main.lean` derives the two propositions of `NaturalLatents/Statement.lean`,
`TableClaim` and `ScoreClaim`, from the bound in nats $`T(p)\le c\,\tau(p)` that the assembly
`NaturalLatents.General.T_le_of_connected` (`NaturalLatents/General/Pricing.lean`) proves on connected supports,
`bits_of_nats` converts to bits and `extension_of_connected` extends to every finite law. It is step 10 of the [route](https://github.com/AlexisOlson/natural-latents/blob/main/docs/overview.md#the-route). This chapter describes the formal argument. Its last section states exactly what the Lean proves about the
frozen optima and definitions. The bridge files in `NaturalLatents/Upstream/` are adapted from pull request #6 by Jeremy
Gillen to DLorell/stoch_to_det (see the [upstream page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/upstream.md)). Here $`c=13999/2000`, the constant
`NaturalLatents.c`.

# 6. From latents to probability tables

*The frozen definitions.* Let $`A,B` be finite alphabets, $`N=\lvert A\times B\rvert`, and $`[N]=\{0,\ldots,N-1\}`.
`Statement.lean` works with real tables and logarithms to base two. A table $`p` is a probability law if it is
nonnegative with total one (`Probability`). For tables of the appropriate shapes,

$$`
\begin{aligned}
H(p)&=-\sum_ap(a)\log_2p(a),\qquad
H(U\mid W)=H(p_{UW})-H(p_W),\qquad
I(U;V\mid W)=H(p_{UW})+H(p_{VW})-H(p_{UVW})-H(p_W),\\
\mathrm{SE}(q)&=I(X;Y\mid V)+I(V;X\mid Y)+I(V;Y\mid X),\qquad
\mathrm{DE}(t)=I(X;Y\mid\Gamma)+H(\Gamma\mid X)+H(\Gamma\mid Y),\\
t_{p,g}(x,y,\ell)&=p(x,y)\,\mathbf 1_{\{g(x,y)=\ell\}},\qquad
T_\star(p)=\min_{g:A\times B\to[N]}\mathrm{DE}(t_{p,g}),\qquad
\tau_\star(p)=\inf_{k,\,q}\mathrm{SE}(q),
\end{aligned}
\qquad \text{(T6.A)}
`

where every marginal is a table sum, $`\mathrm{SE}` is `StochasticError`, $`\mathrm{DE}` is `DeterministicError`,
$`t_{p,g}` is `deterministicTable p g`, and the infimum in $`\tau_\star` is over $`k\in\mathbb N` and probability
laws $`q` on $`A\times B\times[k]` with $`(X,Y)`-marginal $`p`; call such $`q` admissible. For a law $`r` on
$`K\times(A\times B)`, with $`K` finite, $`\mathrm{SE}(r)` is the same sum of three conditional mutual informations,
with $`V` in the first slot. `TableClaim` asks for one code $`g`, depending on
$`p` only, with $`\mathrm{DE}(t_{p,g})\le c\,\mathrm{SE}(q)` for every such $`q`; `ScoreClaim` asks for
$`T_\star(p)\le c\,\tau_\star(p)`. Inside the proof, $`T` and $`\tau` are the bit-valued `stoch_to_det.T` and
`stoch_to_det.tau` (`NaturalLatents/Upstream/Functionals.lean`), that is, the optima of (D3) on the
[contact page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md) divided by $`\ln2` (D1): $`\tau` is an infimum over latents with any finite label type, and $`T` an infimum
over deterministic latents, those in which each cell has positive joint mass with at most one label. On this page
$`\Gamma` is a code, not the Gamma function of the [race page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/race.md); $`A,B` are alphabets, not the budget $`B`;
and $`K` is a finite label set, not the replica budget $`K`.

:::theorem "T6.1" (parent := "table-form") (lean := "NaturalLatents.T_le_c_mul_tau, NaturalLatents.General.bits_of_nats, NaturalLatents.General.nats_le_nats_iff, NaturalLatents.General.extension_of_connected") (uses := "M5.4, E3.4") (tags := "kernel-verified")
*Lemma T6.1 (bits and nats).* For every finite law $`p`, $`T(p)\le c\,\tau(p)` in bits.
:::

:::proof "T6.1"
Cancel the positive bits-to-nats factor and extend the connected bound by the component split. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/table-form.md#6-from-latents-to-probability-tables).
:::

Lean: `NaturalLatents.T_le_c_mul_tau` (`NaturalLatents/Main.lean`), which cancels by
`NaturalLatents.General.bits_of_nats` (`NaturalLatents/General/Nats.lean`, through `nats_le_nats_iff`) and then applies
`extension_of_connected`.

:::theorem "T6.2" (parent := "table-form") (lean := "stoch_to_det.exists_T_optimal_code, stoch_to_det.exists_T_optimal_latent, stoch_to_det.Latent.ofFunction_score_eq_detScore, stoch_to_det.condMI_code_X_given_Y, stoch_to_det.condMI_code_Y_given_X, stoch_to_det.Latent.score_eq") (uses := "S1.1") (tags := "kernel-verified")
*Lemma T6.2 (an optimal code with N labels).* For every finite law $`p` there is a code $`\Gamma:A\times B\to[N]`,
depending on $`p` only, with $`D(\Gamma)=T(p)`, where $`D(\Gamma)` is the bit-valued error
$`I(X;Y\mid\Gamma)+H(\Gamma\mid X)+H(\Gamma\mid Y)`.
:::

:::proof "T6.2"
Relabel positive-prior deterministic labels injectively by source cells and minimize over the finite code space. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/table-form.md#6-from-latents-to-probability-tables).
:::

Lean: `stoch_to_det.exists_T_optimal_code` (`NaturalLatents/Upstream/Envelope.lean`), through
`stoch_to_det.exists_T_optimal_latent`, the private `Latent.detLabel`, `Latent.detCode`,
`Latent.detLabel_inj_of_prior_ne_zero` and `Latent.functionLatent_detCode_score_eq` in the same file, and
`stoch_to_det.Latent.ofFunction_score_eq_detScore` (same file), with `stoch_to_det.condMI_code_X_given_Y` and
`stoch_to_det.condMI_code_Y_given_X` (`NaturalLatents/Upstream/Functionals.lean`). The score equality uses
`stoch_to_det.Latent.score_eq` rather than the entropy expansion of Lemma S1.1.

:::theorem "T6.3" (parent := "table-form") (lean := "stoch_to_det.SourceCoarsening.ofJoint, stoch_to_det.SourceCoarsening.ofJoint_joint, stoch_to_det.SourceCoarsening.ofJoint_score") (uses := "") (tags := "kernel-verified")
*Lemma T6.3 (a joint table is a latent).* For every finite label set $`K` and every probability law $`r` on
$`K\times(A\times B)` with $`(X,Y)`-marginal $`p`, there is a latent of $`p` whose joint law is $`r`; its error is
the stochastic error of $`r`.
:::

:::proof "T6.3"
Normalize each positive row of the joint table and assign the source law to zero-prior rows. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/table-form.md#6-from-latents-to-probability-tables).
:::

Lean: `stoch_to_det.SourceCoarsening.ofJoint`, `ofJoint_joint` and `ofJoint_score`
(`NaturalLatents/Upstream/SourceCoarsening.lean`).

:::theorem "T6.4" (parent := "table-form") (lean := "NaturalLatents.finite_bound, stoch_to_det.exists_T_optimal_code, stoch_to_det.Latent.ofFunction_score_eq_detScore, stoch_to_det.tau_le_score, stoch_to_det.Latent.score_nonneg") (uses := "T6.1, T6.2, T6.3") (tags := "kernel-verified")
*Lemma T6.4 (one code for every joint law).* For every finite law $`p`, there is a code $`\Gamma` such that
$`D(\Gamma)\le c\,\mathrm{SE}(r)` for every finite $`K` and every law $`r` on $`K\times(A\times B)` with marginal $`p`.
:::

:::proof "T6.4"
Use the optimal code and the all-law bound, then compare the stochastic infimum with the joint table’s latent error. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/table-form.md#6-from-latents-to-probability-tables).
:::

Lean: `NaturalLatents.finite_bound` (`NaturalLatents/Main.lean`), which takes $`\Gamma` from
`stoch_to_det.exists_T_optimal_code` and rewrites its error by `stoch_to_det.Latent.ofFunction_score_eq_detScore`, with
`stoch_to_det.tau_le_score` (`NaturalLatents/Upstream/Functionals.lean`), whose lower bound is
`stoch_to_det.Latent.score_nonneg` (same file).

:::theorem "T6.5" (parent := "table-form") (lean := "NaturalLatents.table_bound, NaturalLatents.table_bound_entropy, NaturalLatents.table, TableBoundProof.deterministicTable_eq_push, TableBoundProof.deterministicTable_error, TableBoundProof.deterministicTable_entropy_error, TableBoundProof.deterministicTable_errors_equal, TableBoundProof.transpose_eq_push, TableInformationProof.entropy_eq_H, TableInformationProof.conditionalMutualInformation_push, TableInformationProof.latentError_eq_core, stoch_to_det.condMI_push_source, NaturalLatents.c_nonneg, NaturalLatents.c_lt_seven") (uses := "T6.4") (tags := "kernel-verified")
*Lemma T6.5 (the table form).* For every finite law $`p`, there is a code $`\Gamma` such that
$`\mathrm{DE}(t_{p,\Gamma})\le c\,\mathrm{SE}(q)` for every $`k` and every law $`q` on $`A\times B\times[k]` with
marginal $`p`; since $`0\le c<7`, `TableClaim` holds with $`c`.
:::

:::proof "T6.5"
Transpose the table slots and identify table entropies with pushforward entropies to apply the finite-law code bound. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/table-form.md#6-from-latents-to-probability-tables).
:::

Lean: `NaturalLatents.table_bound` (stochastic form on both sides), `NaturalLatents.table_bound_entropy` (conditional
entropies on the deterministic side) and `NaturalLatents.table` (`NaturalLatents/Main.lean`), through
`TableBoundProof.deterministicTable_eq_push`, `deterministicTable_error`, `deterministicTable_entropy_error`,
`deterministicTable_errors_equal` and `transpose_eq_push`, and `TableInformationProof.entropy_eq_H`,
`conditionalMutualInformation_push` and `latentError_eq_core`, with `stoch_to_det.condMI_push_source`
(`NaturalLatents/Upstream/Entropy.lean`). The identification lemmas hold for every code. The bound
$`0\le c<7` is `NaturalLatents.c_nonneg` and `NaturalLatents.c_lt_seven` (`NaturalLatents/Main.lean`). The frozen
definitions agree with these bridge definitions definitionally, by unfolding; the kernel checks this when it checks
`table`, and no separate lemma states it.

:::theorem "T6.6" (parent := "table-form") (lean := "NaturalLatents.T_le_mul_tau_of_code, NaturalLatents.score_of_table, NaturalLatents.T_le_mul_tau, NaturalLatents.score") (uses := "T6.5") (tags := "kernel-verified")
*Lemma T6.6 (the optimum form).* Let $`p` be a probability law on $`A\times B`. If a code $`g` and a constant
$`c\ge0` satisfy
$`\mathrm{DE}(t_{p,g})\le c\,\mathrm{SE}(q)` for every admissible $`q`, then $`T_\star(p)\le c\,\tau_\star(p)`. Hence
`TableClaim` implies `ScoreClaim`.
:::

:::proof "T6.6"
Compare the deterministic minimum with the supplied code, then take the stochastic infimum, treating a zero constant separately. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/table-form.md#6-from-latents-to-probability-tables).
:::

Lean: `NaturalLatents.T_le_mul_tau_of_code`, `score_of_table`, `T_le_mul_tau` and `score` (`NaturalLatents/Main.lean`).
`score` is proved from `T_le_mul_tau`, which applies `T_le_mul_tau_of_code` to the code of `table_bound_entropy`, not
through `score_of_table`. `NaturalLatents.T_le_mul_tau` states the constant as the literal `13999 / 2000`, as does its pinned example in
`Verify.lean`.

# What the formal argument proves

*The optima.* The Lean relates the frozen optima to the internal ones only by inequalities:
$`T_\star(p)\le D(\Gamma)=T(p)` for the code $`\Gamma` of Lemma T6.2, and $`D(\Gamma)\le c\,\mathrm{SE}(q)` for every
admissible $`q` (Lemmas T6.4 and T6.5). The formal argument needs only these inequalities; no theorem states
$`T_\star=T` or $`\tau_\star=\tau`.

*The definitions.* The frozen `Probability`, `H`, `Hcond`, `CMI`, `StochasticError`, `DeterministicError` and
`deterministicTable` agree with the definitions of `TableInformationProof.lean` and `TableBoundProof.lean`
definitionally, by unfolding. The kernel checks this when it checks `table`; no separate lemma states it.

*The two claims.* The repository proves the direction from the table claim to the score claim (`score_of_table`); the
further remarks in the docstrings of `Statement.lean` (attainment, relabelling, equivalence) are informal comments that
the proof does not use.

*Remark (equality of the optima; not formalized).* In fact $`T_\star(p)=T(p)` and $`\tau_\star(p)=\tau(p)` for every
finite law $`p`, with $`T` and $`\tau` in bits. First, all four optima are finite and lie below each of their members. Every admissible
$`\mathrm{SE}(q)` is a sum of three conditional mutual informations of a probability law, hence nonnegative
(`stoch_to_det.condMI_nonneg`, `NaturalLatents/Upstream/Entropy.lean`, after `latentError_eq_core`). Every latent error
is nonnegative (`stoch_to_det.Latent.score_nonneg`, `NaturalLatents/Upstream/Functionals.lean`), and $`T_\star` is an
infimum over finitely many codes. Every code $`g` into $`[N]` defines a deterministic latent of error $`D(g)`, and
$`D(g)=\mathrm{DE}(t_{p,g})` by the table identification in the description of Lemma T6.5, stated there for every code;
so $`T(p)\le T_\star(p)`, and $`T_\star(p)\le T(p)` by the first paragraph of this section. An admissible $`q`, with its slots reordered, is
the joint law of a latent of error $`\mathrm{SE}(q)` by Lemmas T6.3 and T6.5, so $`\tau(p)\le\tau_\star(p)`. Conversely, a
latent whose label set has $`k` elements becomes an admissible table on $`A\times B\times[k]` once its labels are
numbered; a one-to-one renaming of labels changes no entropy, so its error is that table's $`\mathrm{SE}`, and
$`\tau_\star(p)\le\tau(p)`.
