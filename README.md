# Natural Latents

A Lean 4 proof, depending on Mathlib only, that a stochastic natural latent can be replaced by a deterministic one
at a constant factor below seven.

## The theorem

Let $`p`$ be a probability law on $`X \times Y`$, where $`X`$ and $`Y`$ are finite sets. A finite stochastic latent
$`V`$ is a random variable with finitely many values whose joint law with $`(X,Y)`$ has $`(X,Y)`$-marginal $`p`$.
Its error is

```math
I(X;Y \mid V) + I(V;X \mid Y) + I(V;Y \mid X),
```

and $`\tau(p)`$ is the infimum of that error over all finite stochastic latents. A deterministic latent is a function
$`\Gamma = g(X,Y)`$. Its error is

```math
I(X;Y \mid \Gamma) + H(\Gamma \mid X) + H(\Gamma \mid Y),
```

and $`T(p)`$ is the minimum over all such functions. All quantities are in bits. This repository proves

```math
T(p) \le \tfrac{2789}{400}\,\tau(p) \quad\text{for every finite law } p, \qquad \tfrac{2789}{400} = 6.9725 < 7.
```

Equivalently, for each law $`p`$ there is one deterministic code $`g`$, depending on $`p`$ alone, whose error is at
most $`\tfrac{2789}{400}`$ times the error of every finite stochastic latent of $`p`$. No independence or positivity
assumption is made on $`p`$. The constant is not claimed to be the least possible.

## The formal statements

The definitions and both claims are in [NaturalLatents/Statement.lean](NaturalLatents/Statement.lean). That file is
written from probability tables using Mathlib's real logarithm, finite sums and infima, and it contains no
proofs:

- `TableClaim`: there is a real $`c`$ with $`0 \le c < 7`$ such that for every finite law $`p`$ some deterministic code
  $`g`$ satisfies `DeterministicError (deterministicTable p g) ≤ c * StochasticError q` for every finite joint law
  $`q`$ of $`(X, Y, V)`$ with marginal $`p`$;
- `ScoreClaim`: there is a real $`c`$ with $`0 \le c < 7`$ such that `T p ≤ c * tau p` for every finite law $`p`$.

[NaturalLatents/Main.lean](NaturalLatents/Main.lean) proves `NaturalLatents.table : TableClaim` and
`NaturalLatents.score : ScoreClaim`, both with $`c = 2789/400`$.

## The idea of the proof

The proof has four parts. An optimal stochastic latent yields a race code: a seeded family of deterministic codes
whose labels follow the posterior rows of the latent, chosen by an exponential race. A ledger prices that code
against the budgets of the latent. A mismatch payment, funded by a charge on pairs of contacts of one feasible
kernel, controls where the posterior rows and the race disagree. A cap on the race's entropy price closes the account.
The parts are assembled at the race exponent $`a = 93/20`$, the cap $`u = 199/1000`$ and the pair-charge parameters
$`(\beta, \gamma) = (1/10, 3/25)`$, which give the constant

```math
\max\left\{1 + \frac{3u(1+2\beta)}{\gamma},\ \frac{3a-1}{2} + \frac{3u\beta}{\gamma}\right\}
= \max\left\{\frac{697}{100},\ \frac{2789}{400}\right\} = \frac{2789}{400}.
```

The argument is first carried out for laws whose support is connected (as a bipartite graph between the values of
$`X`$ and the values of $`Y`$), and then extended to every finite law, because $`T`$ and $`\tau`$ both split over the
connected components of the support.

## Verify

Install [elan](https://github.com/leanprover/elan), then run from the repository root:

```sh
lake exe cache get
lake build
lake env lean -DrelaxedAutoImplicit=false Verify.lean
python3 scripts/check_statement.py
```

The audit passes when the last two commands exit with code 0 and print nothing. [Verify.lean](Verify.lean) pins the
type of each headline theorem and pins its axioms to exactly `[propext, Classical.choice, Quot.sound]`;
`scripts/check_statement.py` checks the SHA-256 of `Statement.lean`. Continuous integration runs the same steps,
together with a scan of every Lean file for `sorry`, `axiom`, `native_decide` and other trust shortcuts.

## Acknowledgments

This repository builds on [DLorell/stoch_to_det](https://github.com/DLorell/stoch_to_det) (Apache-2.0), which
formalized the problem and a proof of a finite constant. The files under `NaturalLatents/Upstream/` are adapted from
that project at the head of its [pull request #6](https://github.com/DLorell/stoch_to_det/pull/6) by Jeremy Gillen:
the finite information theory, the duality and the existence of optimal latents, the shared and coordinate races,
and the passage from latents to probability tables. The proof here follows pull request #6's method,
powered-reference race coding with a coordinate ledger, and the shape of the probability-table statement follows
its readable theorem. See [NOTICE](NOTICE) for the license terms; each adapted file names its source and revision in
its first line.

## How this was made

The proofs and the Lean code in this repository were produced with language models used as drafting, proof-search
and coding agents, under the direction and review of the repository owner, who decided what entered the tree. No
statement inherits verification status from that process: the two headline theorems are checked by the Lean kernel
as described under [Verify](#verify), against the statement file, which contains no proofs.

## License

Apache License 2.0; see [LICENSE](LICENSE).
