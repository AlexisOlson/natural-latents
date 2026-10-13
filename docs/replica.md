# The replica budget

This page bounds the replica budget $`K`$ of a finite latent: draw two labels $`L_1,L_2`$ independently from the
posterior at the same cell, and let $`K`$ be the total information that $`L_2`$ carries about the two coordinates given $`L_1`$.
With the budgets $`M`$, $`B`$ defined in (Q3.1) and $`K`$ and the two nonnegative remainders $`C`$, $`N`$ defined in
(Q3.3), the page proves the exact identity $`K=2M+B-C-2N`$, and hence $`K\le2M+B`$. The later mismatch-payment argument
(step 6 of the [route](overview.md#the-route)) compares a weighted sum of component separation
prices ($`\Psi(s)`$ of the [affinity page](affinity.md)) with $`K`$, and this inequality converts that comparison into the budgets $`M`$ and $`B`$. In
the assembly `NaturalLatents.General.T_le_of_connected` (`NaturalLatents/General/Pricing.lean`), `replica_budget` is
passed to `mismatch_payment` as its replica hypothesis. The Lean statement is the inequality only.

## 3. The replica budget

Units and conventions are those of section 0 of the [contact page](contact.md): information is in nats, conditional
sums range over positive-probability conditioning events, and nonnegativity of conditional mutual information is Gibbs'
inequality. The budgets $`M`$, $`B`$ of (Q3.1) are those of (D3); the remainders $`C`$ and $`N`$ of (Q3.3) are local to
this page, and $`C`$ is not the constant of the theorem.

**Lemma Q3.1 (exact replica budget; the mutual-information chain rule).** Let $`X,Y,L`$ be random variables on finite
nonempty alphabets, let $`Z=(X,Y)`$, write $`p(z)=\Pr(Z=z)`$ for its law, and put

```math
M=I(X;Y\mid L),\qquad B=I(L;X\mid Y)+I(L;Y\mid X).
\qquad \text{(Q3.1)}
```

For every $`z`$ of positive probability let $`r_z(i)=\Pr(L=i\mid Z=z)`$. At a zero-probability cell choose any
probability vector $`r_z`$; its choice affects no weighted sum. Define $`L_1,L_2`$ by

```math
\Pr(Z=z,L_1=i,L_2=j)=p(z)r_z(i)r_z(j).
\qquad \text{(Q3.2)}
```

The two labels are conditionally independent given $`Z`$, and each $`(Z,L_k)`$ has the law of $`(Z,L)`$. Define

```math
\begin{aligned}
K&=I(L_2;X\mid L_1)+I(L_2;Y\mid L_1),\\
C&=I(L_1;L_2\mid X)+I(L_1;L_2\mid Y),\\
N&=I(X;Y\mid L_1,L_2).
\end{aligned}
\qquad \text{(Q3.3)}
```

Then $`K=2M+B-C-2N`$, and hence $`K\le2M+B`$.

*Proof.* The first two-order chain-rule expansion is

```math
\begin{aligned}
I(X;Y,L_2\mid L_1)
 &=I(X;Y\mid L_1)+I(X;L_2\mid Y,L_1)\\
 &=I(X;L_2\mid L_1)+I(X;Y\mid L_1,L_2).
\end{aligned}
\qquad \text{(Q3.4)}
```

Because $`I(X;Y\mid L_1)=M`$, this gives

```math
N-M=I(L_2;X\mid Y,L_1)-I(L_2;X\mid L_1).
\qquad \text{(Q3.5)}
```

The second two-order expansion is

```math
\begin{aligned}
I(L_2;X,L_1\mid Y)
 &=I(L_2;L_1\mid Y)+I(L_2;X\mid Y,L_1)\\
 &=I(L_2;X\mid Y)+I(L_2;L_1\mid X,Y)\\
 &=I(L;X\mid Y).
\end{aligned}
\qquad \text{(Q3.6)}
```

The last line uses the replica marginal law and $`I(L_2;L_1\mid X,Y)=0`$. Substituting, then performing the same two
expansions with $`X,Y`$ exchanged, gives both coordinate identities:

```math
\begin{aligned}
N-M&=I(L;X\mid Y)-I(L_1;L_2\mid Y)-I(L_2;X\mid L_1),\\
N-M&=I(L;Y\mid X)-I(L_1;L_2\mid X)-I(L_2;Y\mid L_1).
\end{aligned}
\qquad \text{(Q3.7)}
```

Their sum is $`2N-2M=B-C-K`$, so

```math
K=2M+B-C-2N\le2M+B.
\qquad \text{(Q3.8)}
```

Nonnegativity of conditional mutual information follows from Gibbs' inequality for its conditional relative-entropy
representation. All replica pairs, including the diagonal, enter $`K`$. No contact or optimality hypothesis was used.
$`\square`$

Lean: `NaturalLatents.General.replica_budget` (`NaturalLatents/General/Replica.lean`) states only the inequality
$`K\le2M+B`$, for every finite latent of a probability law; Lean defines neither $`C`$ nor $`N`$ and does not state the
identity $`K=2M+B-C-2N`$. The replica law (Q3.2) is the probability law `replicaJoint`, and $`K`$, in nats, is `replicaBudget`, both
`NaturalLatents.General.*` in `NaturalLatents/General/Definitions.lean`; there the posterior at a zero-probability cell
is the zero vector rather than a probability vector, which changes no weighted sum. The proof in
`NaturalLatents/General/Replica.lean` combines a two-coordinate chain-rule inequality (`replica_total_chain_bound`,
stated for the bit-valued upstream conditional mutual informations and converted by `nats` in the proof of the
natural-log budget) with
the conditional independence of the two labels given $`Z`$ (`replica_replica_markov`) and the replica marginal laws
(`replica_push_first`, `replica_push_second`), dropping the nonnegative remainders as it goes instead of carrying them
to an identity.
