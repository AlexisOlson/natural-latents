# The table form

This page describes how `NaturalLatents/Main.lean` derives the two propositions of `NaturalLatents/Statement.lean`,
`TableClaim` and `ScoreClaim`, from the bound in nats $`T(p)\le c\,\tau(p)`$ that the assembly
`NaturalLatents.General.T_le_of_connected` (`NaturalLatents/General/Pricing.lean`) proves on connected supports,
`bits_of_nats` converts to bits and `extension_of_connected` extends to every finite law. It is step 10 of the [route](overview.md#the-route). **It is a description of
the formal argument, written directly from the Lean.** Its last section states exactly what the Lean proves about the
frozen optima and definitions. The bridge files in `NaturalLatents/Upstream/` are adapted from pull request #6 by Jeremy
Gillen to DLorell/stoch_to_det (see the [upstream page](upstream.md)). Here $`c=13999\text/2000`$, the constant
`NaturalLatents.c`.

## 6. From latents to probability tables

**The frozen definitions.** Let $`A,B`$ be finite alphabets, $`N=\lvert A\times B\rvert`$, and $`[N]=\{0,\ldots,N-1\}`$.
`Statement.lean` works with real tables and logarithms to base two. A table $`p`$ is a probability law if it is
nonnegative with total one (`Probability`). For tables of the appropriate shapes,

```math
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
```

where every marginal is a table sum, $`\mathrm{SE}`$ is `StochasticError`, $`\mathrm{DE}`$ is `DeterministicError`,
$`t_{p,g}`$ is `deterministicTable p g`, and the infimum in $`\tau_\star`$ is over $`k\in\mathbb N`$ and probability
laws $`q`$ on $`A\times B\times[k]`$ with $`(X,Y)`$-marginal $`p`$; call such $`q`$ admissible. For a law $`r`$ on
$`K\times(A\times B)`$, with $`K`$ finite, $`\mathrm{SE}(r)`$ is the same sum of three conditional mutual informations,
with $`V`$ in the first slot. `TableClaim` asks for one code $`g`$, depending on
$`p`$ only, with $`\mathrm{DE}(t_{p,g})\le c\,\mathrm{SE}(q)`$ for every such $`q`$; `ScoreClaim` asks for
$`T_\star(p)\le c\,\tau_\star(p)`$. Inside the proof, $`T`$ and $`\tau`$ are the bit-valued `stoch_to_det.T` and
`stoch_to_det.tau` (`NaturalLatents/Upstream/Functionals.lean`), that is, the optima of (D3) on the
[contact page](contact.md) divided by $`\ln2`$ (D1): $`\tau`$ is an infimum over latents with any finite label type, and $`T`$ an infimum
over deterministic latents, those in which each cell has positive joint mass with at most one label. On this page
$`\Gamma`$ is a code, not the Gamma function of the [race page](race.md); $`A,B`$ are alphabets, not the budget $`B`$;
and $`K`$ is a finite label set, not the replica budget $`K`$.

**Lemma T6.1 (bits and nats).** For every finite law $`p`$, $`T(p)\le c\,\tau(p)`$ in bits.

*Description.* The nat-valued optima of the assembly are $`\ln2`$ times the bit-valued ones (D1). For a law with
connected support, `T_le_of_connected` gives $`(\ln2)\,T(p)\le c\,(\ln2)\,\tau(p)`$, and $`\ln2>0`$ cancels. The bound
in bits then extends to every finite law by `extension_of_connected`, with $`c\ge0`$.

Lean: `NaturalLatents.T_le_c_mul_tau` (`NaturalLatents/Main.lean`), which cancels by
`NaturalLatents.General.bits_of_nats` (`NaturalLatents/General/Nats.lean`, through `nats_le_nats_iff`) and then applies
`extension_of_connected`.

**Lemma T6.2 (an optimal code with N labels).** For every finite law $`p`$ there is a code $`\Gamma:A\times B\to[N]`$,
depending on $`p`$ only, with $`D(\Gamma)=T(p)`$, where $`D(\Gamma)`$ is the bit-valued error
$`I(X;Y\mid\Gamma)+H(\Gamma\mid X)+H(\Gamma\mid Y)`$.

*Description.* Every code $`\Gamma`$ defines a deterministic latent, with prior the law of $`\Gamma(Z)`$ and components
the conditional laws of $`Z`$ given $`\Gamma(Z)`$; a value of $`\Gamma`$ with zero prior gets the component $`p`$, which
carries no weight. Its error is $`D(\Gamma)`$, because $`H(\Gamma\mid X,Y)=0`$ turns $`I(\Gamma;X\mid Y)`$ into
$`H(\Gamma\mid Y)`$ and $`I(\Gamma;Y\mid X)`$ into $`H(\Gamma\mid X)`$. Conversely, let $`V`$ be a deterministic latent
with any finite label set. For each label $`v`$ choose a cell $`z_v`$ where its component is positive (one exists, since
the component is a probability law), and send $`v`$ to the number of $`z_v`$ in a fixed enumeration of $`A\times B`$. Only
labels of positive prior matter: two of them cannot share that cell, by determinism, so the numbering is one-to-one on
them. At a cell of the support, the active label is the one label with positive joint mass there; at a cell outside the
support it is arbitrary, and that cell carries no mass. The code that sends each cell to the number of its active label
has the same prior mass and the same component at the number of every positive-prior label, hence the same error, by the
cost identity (Lemma S1.1 of the [setup page](setup.md)). There are finitely many codes into
$`[N]`$; a minimizer is below every deterministic latent by the relabelling, and at least $`T(p)`$ because it is one.

Lean: `stoch_to_det.exists_T_optimal_code` (`NaturalLatents/Upstream/Envelope.lean`), through
`stoch_to_det.exists_T_optimal_latent`, the private `Latent.detLabel`, `Latent.detCode`,
`Latent.detLabel_inj_of_prior_ne_zero` and `Latent.functionLatent_detCode_score_eq` in the same file, and
`stoch_to_det.Latent.ofFunction_score_eq_detScore` (same file), with `stoch_to_det.condMI_code_X_given_Y` and
`stoch_to_det.condMI_code_Y_given_X` (`NaturalLatents/Upstream/Functionals.lean`). The score equality uses
`stoch_to_det.Latent.score_eq` rather than the entropy expansion of Lemma S1.1.

**Lemma T6.3 (a joint table is a latent).** For every finite label set $`K`$ and every probability law $`r`$ on
$`K\times(A\times B)`$ with $`(X,Y)`$-marginal $`p`$, there is a latent of $`p`$ whose joint law is $`r`$; its error is
the stochastic error of $`r`$.

*Description.* Put $`\pi_k=\sum_zr(k,z)`$, and take the component $`r(k,\cdot)\text/\pi_k`$ when $`\pi_k>0`$ and $`p`$
otherwise. The mixture is $`p`$, and $`\pi_kq_k(z)=r(k,z)`$ for every $`k`$, since a row of zero total mass is zero. The
error depends on the joint law only. No label is merged or removed.

Lean: `stoch_to_det.SourceCoarsening.ofJoint`, `ofJoint_joint` and `ofJoint_score`
(`NaturalLatents/Upstream/SourceCoarsening.lean`).

**Lemma T6.4 (one code for every joint law).** For every finite law $`p`$, the code $`\Gamma`$ of Lemma T6.2 satisfies
$`D(\Gamma)\le c\,\mathrm{SE}(r)`$ for every finite $`K`$ and every law $`r`$ on $`K\times(A\times B)`$ with marginal $`p`$.

*Description.* Let $`L_r`$ be the latent of Lemma T6.3, whose error is $`\mathrm{SE}(r)`$. With $`c\ge0`$,
$`D(\Gamma)=T(p)\le c\,\tau(p)\le c\,\mathrm{SE}(r)`$ by Lemma T6.1 and because $`\tau(p)`$ is an infimum of latent errors
bounded below by zero.

Lean: `NaturalLatents.finite_bound` (`NaturalLatents/Main.lean`), which takes $`\Gamma`$ from
`stoch_to_det.exists_T_optimal_code` and rewrites its error by `stoch_to_det.Latent.ofFunction_score_eq_detScore`, with
`stoch_to_det.tau_le_score` (`NaturalLatents/Upstream/Functionals.lean`), whose lower bound is
`stoch_to_det.Latent.score_nonneg` (same file).

**Lemma T6.5 (the table form).** For every finite law $`p`$, the code $`\Gamma`$ satisfies
$`\mathrm{DE}(t_{p,\Gamma})\le c\,\mathrm{SE}(q)`$ for every $`k`$ and every law $`q`$ on $`A\times B\times[k]`$ with
marginal $`p`$; since $`0\le c<7`$, `TableClaim` holds with $`c`$.

*Description.* Reorder the slots of $`q`$ to $`[k]\times(A\times B)`$ and apply Lemma T6.4. Every table quantity in (T6.A)
equals the corresponding quantity of the law it tabulates: on a probability table, $`-\sum p\log_2p`$ is the upstream
entropy, and the entropy of a marginal table is the entropy of a pushforward. For every code $`g`$, the table
$`t_{p,g}`$ is the law of $`(X,Y,g(X,Y))`$, so $`\mathrm{DE}(t_{p,g})=D(g)`$, and the stochastic form of $`t_{p,g}`$ has
the same value, again because $`H(g\mid X,Y)=0`$; this table identification is used at $`g=\Gamma`$.

Lean: `NaturalLatents.table_bound` (stochastic form on both sides), `NaturalLatents.table_bound_entropy` (conditional
entropies on the deterministic side) and `NaturalLatents.table` (`NaturalLatents/Main.lean`), through
`TableBoundProof.deterministicTable_eq_push`, `deterministicTable_error`, `deterministicTable_entropy_error`,
`deterministicTable_errors_equal` and `transpose_eq_push`, and `TableInformationProof.entropy_eq_H`,
`conditionalMutualInformation_push` and `latentError_eq_core`, with `stoch_to_det.condMI_push_source`
(`NaturalLatents/Upstream/Entropy.lean`). The identification lemmas hold for every code. The bound
$`0\le c<7`$ is `NaturalLatents.c_nonneg` and `NaturalLatents.c_lt_seven` (`NaturalLatents/Main.lean`). The frozen
definitions agree with these bridge definitions definitionally, by unfolding; the kernel checks this when it checks
`table`, and no separate lemma states it.

**Lemma T6.6 (the optimum form).** Let $`p`$ be a probability law on $`A\times B`$. If a code $`g`$ and a constant
$`c\ge0`$ satisfy
$`\mathrm{DE}(t_{p,g})\le c\,\mathrm{SE}(q)`$ for every admissible $`q`$, then $`T_\star(p)\le c\,\tau_\star(p)`$. Hence
`TableClaim` implies `ScoreClaim`.

*Description.* $`T_\star(p)\le\mathrm{DE}(t_{p,g})`$, an infimum over finitely many codes. The admissible set is nonempty: $`k=1`$
and $`q(x,y,0)=p(x,y)`$. If $`c>0`$, then $`\mathrm{DE}(t_{p,g})\text/c`$ is a lower bound of every admissible
$`\mathrm{SE}(q)`$, hence of their infimum $`\tau_\star(p)`$. If $`c=0`$, any admissible $`q`$ gives
$`\mathrm{DE}(t_{p,g})\le0=c\,\tau_\star(p)`$.

Lean: `NaturalLatents.T_le_mul_tau_of_code`, `score_of_table`, `T_le_mul_tau` and `score` (`NaturalLatents/Main.lean`).
`score` is proved from `T_le_mul_tau`, which applies `T_le_mul_tau_of_code` to the code of `table_bound_entropy`, not
through `score_of_table`. `NaturalLatents.T_le_mul_tau` states the constant as the literal `13999 / 2000`, as does its pinned example in
`Verify.lean`.

## What the formal argument proves

**The optima.** The Lean relates the frozen optima to the internal ones only by inequalities:
$`T_\star(p)\le D(\Gamma)=T(p)`$ for the code $`\Gamma`$ of Lemma T6.2, and $`D(\Gamma)\le c\,\mathrm{SE}(q)`$ for every
admissible $`q`$ (Lemmas T6.4 and T6.5). The formal argument needs only these inequalities; no theorem states
$`T_\star=T`$ or $`\tau_\star=\tau`$.

**The definitions.** The frozen `Probability`, `H`, `Hcond`, `CMI`, `StochasticError`, `DeterministicError` and
`deterministicTable` agree with the definitions of `TableInformationProof.lean` and `TableBoundProof.lean`
definitionally, by unfolding. The kernel checks this when it checks `table`; no separate lemma states it.

**The two claims.** The repository proves the direction from the table claim to the score claim (`score_of_table`); the
further remarks in the docstrings of `Statement.lean` (attainment, relabelling, equivalence) are informal comments that
the proof does not use.

**Remark (equality of the optima; not formalized).** In fact $`T_\star(p)=T(p)`$ and $`\tau_\star(p)=\tau(p)`$ for every
finite law $`p`$, with $`T`$ and $`\tau`$ in bits. First, all four optima are finite and lie below each of their members. Every admissible
$`\mathrm{SE}(q)`$ is a sum of three conditional mutual informations of a probability law, hence nonnegative
(`stoch_to_det.condMI_nonneg`, `NaturalLatents/Upstream/Entropy.lean`, after `latentError_eq_core`). Every latent error
is nonnegative (`stoch_to_det.Latent.score_nonneg`, `NaturalLatents/Upstream/Functionals.lean`), and $`T_\star`$ is an
infimum over finitely many codes. Every code $`g`$ into $`[N]`$ defines a deterministic latent of error $`D(g)`$, and
$`D(g)=\mathrm{DE}(t_{p,g})`$ by the table identification in the description of Lemma T6.5, stated there for every code;
so $`T(p)\le T_\star(p)`$, and $`T_\star(p)\le T(p)`$ by the first paragraph of this section. An admissible $`q`$, with its slots reordered, is
the joint law of a latent of error $`\mathrm{SE}(q)`$ by Lemmas T6.3 and T6.5, so $`\tau(p)\le\tau_\star(p)`$. Conversely, a
latent whose label set has $`k`$ elements becomes an admissible table on $`A\times B\times[k]`$ once its labels are
numbered; a one-to-one renaming of labels changes no entropy, so its error is that table's $`\mathrm{SE}`$, and
$`\tau_\star(p)\le\tau(p)`$.
