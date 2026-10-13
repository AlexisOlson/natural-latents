# Natural Latents

A Lean 4 proof, depending on Mathlib only, that a deterministic natural latent is never worse than a stochastic one
by more than a factor $`2789/400 < 7`$: the best function of the observations has error at most $`2789/400`$ times
the best error of any finite stochastic latent, with both errors as defined below.

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

Work in nats, and first suppose that the support of $`p`$ is connected, as a bipartite graph between the values of
$`X`$ and the values of $`Y`$. Then `exists_setup_of_connected` constructs a finite stochastic latent $`L`$ that
attains $`\tau(p)`$ and has two further properties: its components are distinct contacts of one feasible kernel (a
dual object from the optimality conditions), and every posterior probability $`\Pr[L = i \mid (X,Y) = z]`$ is
positive for $`z`$ in the support. Split the error of $`L`$ into the two budgets $`M = I(X;Y \mid L)`$ and
$`B = I(L;X \mid Y) + I(L;Y \mid X)`$, so that $`M + B = \tau(p)`$. The proof chains four inequalities, each a theorem
in `NaturalLatents/General/`.

1. **Ledger** (`T_le_ledger`). Let $`F`$ be a probability law on maps $`g`$ from $`X \times Y`$ to the labels of
   $`L`$ such that, at each cell $`z`$ of the support, $`g(z)`$ is distributed as the posterior of $`L`$ at $`z`$.
   Let $`h`$ be the $`F`$-average, over the maps $`g`$, of $`H(g \mid X) + H(g \mid Y)`$ computed for each fixed
   $`g`$. Then $`T(p) \le M - B/2 + 3h/2`$.
2. **Race** (`exists_race`). Since the posteriors are positive, for every $`a > 1`$ an exponential race among the
   labels gives such an $`F`$ with $`h \le aB + 2\,j(a)\,d`$. Here
   $`d = \sum_z p(z)\bigl(1 - \sum_i \Pr[L = i \mid (X,Y) = z]^2\bigr)`$ is the probability that two labels drawn
   independently from the posterior at a cell $`z \sim p`$ disagree, and
   $`j(a) = a \log \Gamma(1 - 1/a) - \gamma_{\mathrm{E}}`$, with $`\gamma_{\mathrm{E}}`$ Euler's constant.
3. **Cap** (`racePrice_lt_capC3a`). For $`a > 1`$,
   $`j(a) < \frac{79}{96a} + \frac{241}{600a^2} + \frac{6503}{24000a^2(a-1)}`$; at $`a = 93/20`$ the right side is
   below $`u = 199/1000`$.
4. **Payment** (`mismatch_payment`). For this latent, $`\gamma\,d \le (1+2\beta)M + \beta B`$ at
   $`(\beta, \gamma) = (1/10, 3/25)`$. The proof combines three separately proved bounds: an affinity bound for each
   pair of components, a budget for two independent posterior replicas, and a charge on pairs of contacts of one
   feasible kernel.

Since $`d \ge 0`$ and $`\gamma > 0`$, the four combine into

```math
T(p) \le \left(1 + \frac{3u(1+2\beta)}{\gamma}\right) M + \left(\frac{3a-1}{2} + \frac{3u\beta}{\gamma}\right) B
= \frac{697}{100}\,M + \frac{2789}{400}\,B \le \frac{2789}{400}\,\tau(p),
```

where the last step uses $`M \ge 0`$ and $`M + B = \tau(p)`$. Finally, $`T`$ and $`\tau`$ both split over the connected
components of the support, so the bound extends to every finite law (`extension_of_connected`).

## Verify

Install [elan](https://github.com/leanprover/elan), then run from the repository root:

```sh
lake exe cache get
lake build
lake env lean -DrelaxedAutoImplicit=false Verify.lean
python3 scripts/check_statement.py
```

Verification passes when all four commands exit with code 0; on success the last two print nothing. [Verify.lean](Verify.lean) pins the
type of each headline theorem and pins its axioms to exactly `[propext, Classical.choice, Quot.sound]`;
`scripts/check_statement.py` checks the SHA-256 of `Statement.lean`. Continuous integration checks the statement
hash, scans the Lean files of the proof (`NaturalLatents/`, `NaturalLatents.lean` and `Verify.lean`) for `sorry`,
`axiom`, `native_decide` and other trust shortcuts, fetches the Mathlib cache, builds, and runs the same silent audit.

## Acknowledgments

This repository builds on [DLorell/stoch_to_det](https://github.com/DLorell/stoch_to_det) (Apache-2.0), which
formalized the problem and a proof of a finite constant. The files under `NaturalLatents/Upstream/` are adapted from
that project at the head of its [pull request #6](https://github.com/DLorell/stoch_to_det/pull/6) by Jeremy Gillen:
the finite information theory, the duality and the existence of optimal latents, the shared and coordinate races,
and the passage from latents to probability tables. The proof here follows pull request #6's method,
powered-reference race coding with a coordinate ledger, and the probability-table statement and its bridge to
latents follow pull request #6's `TableInformationProof` and `TableBoundProof` (adapted here under
`NaturalLatents/Upstream/`).
See [LICENSE](LICENSE) for the Apache-2.0 terms and [NOTICE](NOTICE) for copyright and provenance; each adapted file
names its source and revision in its first line.

## How this was made

The proofs and the Lean code in this repository were produced with language models used as drafting, proof-search
and coding agents, under the direction and review of the repository owner, who decided what entered the tree. No
statement inherits verification status from that process: the two headline theorems are checked by the Lean kernel
as described under [Verify](#verify), against the statement file, which contains no proofs.

## License

Apache License 2.0; see [LICENSE](LICENSE).
