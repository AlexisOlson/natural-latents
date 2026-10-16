# Natural Latents

[![verify](https://github.com/AlexisOlson/natural-latents/actions/workflows/ci.yml/badge.svg)](https://github.com/AlexisOlson/natural-latents/actions/workflows/ci.yml)

A Lean 4 proof, with Mathlib as its only dependency (the upstream code it adapts is included under
`NaturalLatents/Upstream/`), that for every probability law on two finite alphabets some deterministic
natural latent is within a factor $`13999/2000 < 7`$ of every stochastic one: the best function of the observations has error at most $`13999/2000`$ times
the infimum $`\tau(p)`$ of the errors of finite stochastic latents, with both errors as defined below.

This is the problem stated in David Lorell's LessWrong post
[Redux: (∃ Stochastic Natural Latent) Implies (∃ Deterministic Natural Latent)](https://www.lesswrong.com/posts/TgboJpeN95bs84odk/redux-stochastic-natural-latent-implies-deterministic),
whose Lean proof in [DLorell/stoch_to_det](https://github.com/DLorell/stoch_to_det) gave $`C \le 1771`$; Jeremy
Gillen's [pull request #6](https://github.com/DLorell/stoch_to_det/pull/6) to that project brought it to
$`47/5 = 9.4`$. The constant here is not claimed to be sharp. A lower bound $`C \ge 1.960073002187`$ is proved in Lean,
using `native_decide`, in Satya Benson's [satchlj/stoch-to-det-lower](https://github.com/satchlj/stoch-to-det-lower);
it is not reproduced here.

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

and $`T(p)`$ is the minimum over all such functions. All quantities are in bits; $`T`$ and $`\tau`$ change units by
the same factor, so their ratio has no unit. This repository proves

```math
T(p) \le \tfrac{13999}{2000}\,\tau(p) \quad\text{for every finite law } p, \qquad \tfrac{13999}{2000} = 6.9995 < 7.
```

Equivalently, for each law $`p`$ there is one deterministic code $`g`$, depending on $`p`$ alone, whose error is at
most $`\tfrac{13999}{2000}`$ times the error of every finite stochastic latent of $`p`$. No independence or positivity
assumption is made on $`p`$. The written proof gives the exact constant $`5249623/750000 \approx 6.999497`$, and the
Lean theorems use its rounding up; neither constant is claimed to be the least possible.

Two remarks on scope. The latents are finite, as in the upstream formalization; for finite $`X`$ and $`Y`$ this loses
nothing, because the error of any latent depends only on its mixture of conditional laws of $`(X,Y)`$, and by
Carathéodory's theorem a latent with at most $`|X||Y|+1`$ values has the same $`(X,Y)`$-marginal and the same error
(a paper argument, not formalized). The bound compares sums of the three errors, as in the post; if instead each of
the three stochastic errors is at most $`\varepsilon`$, it gives each deterministic error at most
$`3 \cdot \tfrac{13999}{2000}\,\varepsilon`$.

The pair charge (step 3 below) has more than one proof, and the choice trades the constant against how the proof
reads. A first version of this repository proved the smaller constant $`2789/400 = 6.9725`$ with the pair charge
$`PC(1/10,\,3/25)`$, whose paper proof is by hand but long, with neither a fitted certificate nor interval-certified
input; the route is kernel-verified at commit
[`e18975a`](https://github.com/AlexisOlson/natural-latents/tree/e18975a). This version uses $`PC(23/250,\,7/60)`$: for
separations $`0<s\le1`$, the paper proof derives a lower bound on the information using a nonnegative quadratic form,
then reduces a scalar inequality to three one-variable quartics, certified by exact rational identities with fifteen
positive remainder coefficients; for $`1\le s<2`$ the separation price alone pays. It costs about $`0.027`$ in the
constant. [docs/landscape.md](docs/landscape.md) lists these and the other routes, with the status of each.

## The formal statements

The definitions and both claims are in [NaturalLatents/Statement.lean](NaturalLatents/Statement.lean), about 110
lines that import only Mathlib; reading it is the one Lean step worth taking to check what is claimed. Its
probability-table definitions are those of Jeremy Gillen's readable theorem in pull request #6. The file is written from
probability tables using Mathlib's real logarithm, finite sums and infima, and it contains no proofs:

- `TableClaim`: there is a real $`c`$ with $`0 \le c < 7`$ such that for every finite law $`p`$ some deterministic code
  $`g`$ satisfies `DeterministicError (deterministicTable p g) ≤ c * StochasticError q` for every finite joint law
  $`q`$ of $`(X, Y, V)`$ with marginal $`p`$;
- `ScoreClaim`: there is a real $`c`$ with $`0 \le c < 7`$ such that `T p ≤ c * tau p` for every finite law $`p`$.

[NaturalLatents/Main.lean](NaturalLatents/Main.lean) proves `NaturalLatents.table : TableClaim` and
`NaturalLatents.score : ScoreClaim`, both with $`c = 13999/2000`$; `NaturalLatents.T_le_mul_tau` states
`T p ≤ (13999 / 2000) * tau p` directly. `score_of_table` and `table_of_score` prove the two claims equivalent, with
the same constant.

What is machine-checked: the Lean kernel checks `table` and `score` end to end, and their axiom pins (see
[Verify](#verify)) cover every lemma they use, including the adapted upstream code. The pages under `docs/` are a
written proof of the same route; they are not machine-checked. The [blueprint](blueprint/README.md) ([site](https://alexisolson.github.io/natural-latents/))
pairs each page lemma with its Lean declarations; its tags `kernel-verified`, `partly kernel-verified` and
`paper proof` say how much of a page lemma's wording the cited declarations prove, and do not grade the headline.

## The idea of the proof

Work in nats on a law whose support is connected, as a bipartite graph between the values of $`X`$ and $`Y`$. The setup
(`exists_setup_of_connected`) gives a latent $`L`$ that attains $`\tau(p)`$, whose components are distinct contacts of
one feasible kernel (a dual object from the optimality conditions), with every posterior probability
$`\Pr[L = i \mid (X,Y) = z]`$ positive on the support. Split its error into the budgets $`M = I(X;Y \mid L)`$ and
$`B = I(L;X \mid Y) + I(L;Y \mid X)`$, so that $`M + B = \tau(p)`$, and let $`d`$ be the probability that two labels
drawn independently from the posterior at a cell $`z \sim p`$ disagree.

1. **Ledger and race.** An exponential race among the labels, with clocks shared by all cells and analyzed with a
   powered reference of exponent $`a > 1`$, gives a random deterministic code $`f`$ with $`T(p) \le M - B/2 + 3h/2`$
   and $`h \le aB + 2\,j(a)\,d`$ (`T_le_ledger`, `exists_race`). Here $`h`$ is the average over the race of
   $`H(f(X,Y) \mid X) + H(f(X,Y) \mid Y)`$ with $`f`$ fixed, in nats, and $`j(a) = a \ln \Gamma(1 - 1/a) - \gamma_{\mathrm{E}}`$,
   where $`\Gamma`$ is the Gamma function and $`\gamma_{\mathrm{E}}`$ is Euler's constant. This step is the method
   of pull request #6 by Jeremy Gillen (the coordinate ledger and powered-reference race coding), run on the shared
   race formalized in pull request #5 by Satya Benson; the price $`j(a)`$ for general $`a > 1`$ and its cap are worked
   out here.
2. **Cap.** $`j(a) < \frac{533}{648a} + \frac{241}{600a^2} + \frac{6503}{24000a^2(a-1)}`$ for $`a > 1`$
   (`racePrice_lt_capC3b`); at $`a = 211/45`$ the right side is below $`u = 3941/20000`$, an exact comparison made by
   the `norm_num [gammaPriceCap]` step in `T_le_of_connected`.
3. **Payment.** The pair charge $`PC(23/250,\,7/60)`$, proved for every two distinct positive contacts of one feasible
   kernel (`pairCharge_C`), combines with a Bhattacharyya affinity bound and a budget for two posterior replicas into
   $`\gamma\,d \le (1+2\beta)M + \beta B`$ at $`(\beta, \gamma) = (23/250,\, 7/60)`$ (`mismatch_payment`).

Since $`M, B, d \ge 0`$, these combine (`T_le_of_connected`) into

```math
T(p) \le \left(1 + \frac{3u(1+2\beta)}{\gamma}\right) M + \left(\frac{3a-1}{2} + \frac{3u\beta}{\gamma}\right) B
= \frac{218729}{31250}\,M + \frac{5249623}{750000}\,B \le \frac{5249623}{750000}\,\tau(p).
```

Over the connected components of the support, with weights $`\rho_k`$ and component laws $`\bar p_k`$,
$`T(p) \le \sum_k \rho_k T(\bar p_k)`$ and $`\sum_k \rho_k \tau(\bar p_k) \le \tau(p)`$, so the bound extends to every finite law
(`extension_of_connected`). [docs/overview.md](docs/overview.md) maps each step to its page and Lean declaration.

## Proof pages

The written proof, in reading order:

- [overview](docs/overview.md): the theorem, the route in ten steps, and where each step lives in Lean.
- [contact](docs/contact.md): read section 0 (units and notation) first; section 1, on contacts, comes after the cap.
- [setup](docs/setup.md): an attaining latent whose components are contacts of one feasible kernel.
- [ledger](docs/ledger.md): $`T(p)`$ bounded by the budgets and the entropy cost of a random code.
- [race](docs/race.md): the exponential race and its price $`j(a)`$.
- [cap](docs/cap.md): a rational upper bound on $`j(a)`$.
- [affinity](docs/affinity.md): the marginals of two distinct contacts are separated.
- [replica budget](docs/replica.md): the information cost of two independent posterior labels.
- [payment](docs/payment.md): a pair charge pays for the mismatch $`d`$.
- [pair charge](docs/pair-charge.md): the proof of $`PC(23/250,\,7/60)`$.
- [assembly](docs/assembly.md): the pricing and its exact arithmetic.
- [extension](docs/extension.md): from connected supports to every finite law.
- [table form](docs/table-form.md): bits, probability tables and the two statements.
- [upstream](docs/upstream.md): what the proof takes from the adapted upstream code.

[docs/landscape.md](docs/landscape.md) describes other routes, and what a smaller constant would cost.

## Verify

Install [elan](https://github.com/leanprover/elan), then run from the repository root the steps that continuous
integration runs. The recipe assumes a Bash shell with `python3`, `git`, `grep` and the usual shell utilities on
`PATH`, as on the Ubuntu runner that continuous integration uses:

```sh
python3 scripts/check_statement.py
bash scripts/trust_scan.sh
lake exe cache get
lake build --wfail
lake env lean -DrelaxedAutoImplicit=false Verify.lean
lake env leanchecker NaturalLatents.Main
```

On a Windows machine, use WSL or Git Bash (there `python3` may be `python`); `.gitattributes` keeps LF line endings
on `Statement.lean`, so its hash is the same on every checkout. On the continuous-integration runner the whole recipe
takes about four minutes, most of it downloading Mathlib's prebuilt cache.

Verification passes when all six exit with code 0, and the Verify.lean step prints nothing. `check_statement.py`
checks that `Statement.lean` is byte-identical to the approved file (its SHA-256 is fixed in the script), so later
edits to the statement are caught; it is no substitute for reading the file.
`trust_scan.sh` scans the Lean files (`NaturalLatents/`, `NaturalLatents.lean`, `Verify.lean`) for `sorry`, `axiom`,
`native_decide` and other trust shortcuts, including new syntax and notation. The build fails on any warning.
[Verify.lean](Verify.lean) pins the types of `table` and `score`, checks `T_le_mul_tau` by an example, and pins the
axioms of `table`, `score`, `table_of_score`, `T_le_mul_tau` and eight main proof steps to exactly
`[propext, Classical.choice, Quot.sound]`; `#print axioms` reports a theorem's whole dependency cone, so these pins
cover every lemma the headlines use. `leanchecker` replays the declarations of `NaturalLatents.Main` in the kernel. Optionally, and only locally (it is not part of continuous
integration), `bash scripts/mutation_check.sh` checks on a disposable copy that the first two gates catch an edited
statement, an added `axiom` and a `sorry`.

## Acknowledgments

This repository builds on David Lorell's [DLorell/stoch_to_det](https://github.com/DLorell/stoch_to_det) (Apache-2.0), which
formalized the problem and proved a finite constant, $`C \le 1771`$; its finite information theory, duality, existence of optimal
latents and reduction to connected supports are adapted here. The files under `NaturalLatents/Upstream/` are adapted from
that project at the head of its [pull request #6](https://github.com/DLorell/stoch_to_det/pull/6) by Jeremy Gillen,
which carries the shared-race formalization of [pull request #5](https://github.com/DLorell/stoch_to_det/pull/5) by
Satya Benson: the `SharedRace/` modules, the clock-race lemmas in `Race.lean`, the contact secants in `Floor.lean`, and
first versions of `DomFloorCore.lean` and `PhiBounds.lean`. The proof here follows pull request #6's method,
powered-reference race coding with a coordinate ledger, and uses its modules `ContactInformation`,
`CoordinateRace`, `PoweredRaceWinner`, `SourceCoarsening`, `TableBoundProof` and
`TableInformationProof`. The ledger inequality of the [ledger page](docs/ledger.md) is its coordinate-entropy ledger.
The probability-table definitions in `Statement.lean` are taken from its `ReadableStatement.lean`, and `TableClaim`
restates its readable theorem with $`c < 7`$ in place of $`47/5`$; the bridge proofs `finite_bound`, `table_bound` and
`table_bound_entropy` in `Main.lean` are adapted from its `FiniteBoundProof.lean` and `TableBoundProof.lean`. See
[LICENSE](LICENSE) for the Apache-2.0 terms and [NOTICE](NOTICE) for copyright and provenance; each file under
`NaturalLatents/Upstream/` names its source and revision in its first line, and so does `Main.lean` for its bridge
section. `Statement.lean` is frozen by its hash, so its provenance is stated here and in the NOTICE.

## How this was made

The proofs and the Lean code in this repository were produced with language models used as drafting, proof-search
and coding agents, under the direction and review of the repository owner, who decided what entered the tree. No
statement inherits verification status from that process: the two headline theorems are checked by the Lean kernel
as described under [Verify](#verify), against the statement file, which contains no proofs.

## License

Apache License 2.0; see [LICENSE](LICENSE).
