import Verso
import VersoManual
import VersoBlueprint
import NaturalLatents.Main

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "The replica budget" =>

:::group "replica"
The replica budget.
:::

This page bounds the replica budget $`K` of a finite latent: draw two labels $`L_1,L_2` independently from the
posterior at the same cell, and let $`K` be the total information that $`L_2` carries about the two coordinates given $`L_1`.
With the budgets $`M`, $`B` defined in (Q3.1) and $`K` and the two nonnegative remainders $`C`, $`N` defined in
(Q3.3), the page proves the exact identity $`K=2M+B-C-2N`, and hence $`K\le2M+B`. The later mismatch-payment argument
(step 6 of the [route](https://github.com/AlexisOlson/natural-latents/blob/main/docs/overview.md#the-route)) compares a weighted sum of component separation
prices ($`\Psi(s)` of the [affinity page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/affinity.md)) with $`K`, and this inequality converts that comparison into the budgets $`M` and $`B`. In
the assembly `NaturalLatents.General.T_le_of_connected` (`NaturalLatents/General/Pricing.lean`), `replica_budget` is
passed to `mismatch_payment` as its replica hypothesis. The Lean statement is the inequality only.

# 3. The replica budget

Units and conventions are those of section 0 of the [contact page](https://github.com/AlexisOlson/natural-latents/blob/main/docs/contact.md): information is in nats, conditional
sums range over positive-probability conditioning events, and nonnegativity of conditional mutual information is Gibbs'
inequality. The budgets $`M`, $`B` of (Q3.1) are those of (D3); the remainders $`C` and $`N` of (Q3.3) are local to
this page, and $`C` is not the constant of the theorem.

:::theorem "Q3.1" (parent := "replica") (lean := "NaturalLatents.General.replica_budget, NaturalLatents.General.replica_total_chain_bound, NaturalLatents.General.replica_replica_markov, NaturalLatents.General.replica_push_first, NaturalLatents.General.replica_push_second") (uses := "") (tags := "partly kernel-verified")
*Lemma Q3.1 (exact replica budget; the mutual-information chain rule).* Let $`X,Y,L` be random variables on finite
nonempty alphabets, let $`Z=(X,Y)`, write $`p(z)=\Pr(Z=z)` for its law, and put

$$`
M=I(X;Y\mid L),\qquad B=I(L;X\mid Y)+I(L;Y\mid X).
\qquad \text{(Q3.1)}
`

For every $`z` of positive probability let $`r_z(i)=\Pr(L=i\mid Z=z)`. At a zero-probability cell choose any
probability vector $`r_z`; its choice affects no weighted sum. Define $`L_1,L_2` by

$$`
\Pr(Z=z,L_1=i,L_2=j)=p(z)r_z(i)r_z(j).
\qquad \text{(Q3.2)}
`

The two labels are conditionally independent given $`Z`, and each $`(Z,L_k)` has the law of $`(Z,L)`. Define

$$`
\begin{aligned}
K&=I(L_2;X\mid L_1)+I(L_2;Y\mid L_1),\\
C&=I(L_1;L_2\mid X)+I(L_1;L_2\mid Y),\\
N&=I(X;Y\mid L_1,L_2).
\end{aligned}
\qquad \text{(Q3.3)}
`

Then $`K=2M+B-C-2N`, and hence $`K\le2M+B`.
:::

:::proof "Q3.1"
Lean proves: $`K\le2M+B`, $`I(L_1;L_2\mid Z)=0`, equality of each replica source-label marginal with the original latent joint law, and the general two-coordinate chain-rule bound
$`I(b;x\mid a)+I(b;y\mid a)\le2I(x;y\mid a)+I(b;x\mid y)+I(b;y\mid x)+2I(a;b\mid x,y)` in bits (`replica_total_chain_bound`).

Expand the mutual information chain rule in two orders on both coordinates, use replica conditional independence, and discard the nonnegative remainders. See [the page section](https://github.com/AlexisOlson/natural-latents/blob/main/docs/replica.md#3-the-replica-budget).
:::

Lean: `NaturalLatents.General.replica_budget` (`NaturalLatents/General/Replica.lean`) states only the inequality
$`K\le2M+B`, for every finite latent of a probability law; Lean defines neither $`C` nor $`N` and does not state the
identity $`K=2M+B-C-2N`. The replica law (Q3.2) is the probability law `replicaJoint`, and $`K`, in nats, is `replicaBudget`, both
`NaturalLatents.General.*` in `NaturalLatents/General/Definitions.lean`; there the posterior at a zero-probability cell
is the zero vector rather than a probability vector, which changes no weighted sum. The proof in
`NaturalLatents/General/Replica.lean` combines a two-coordinate chain-rule inequality (`replica_total_chain_bound`,
stated for the bit-valued upstream conditional mutual informations and converted by `nats` in the proof of the
natural-log budget) with
the conditional independence of the two labels given $`Z` (`replica_replica_markov`) and the replica marginal laws
(`replica_push_first`, `replica_push_second`), dropping the nonnegative remainders as it goes instead of carrying them
to an identity.
