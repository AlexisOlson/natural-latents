# Other routes and the cost of tightening

## 1. What this page is

This repository proves $`T(p)\le(13999\text/2000)\,\tau(p)`$ for every finite law $`p`$ by the route outlined on the
[overview page](overview.md#the-route). This page collects other ways to prove a bound of that form, and what is
known about the price of a smaller constant. The main proof depends on nothing here. Sections 4 and 5 begin with
pointers to steps the main proof already uses (the race price, its cap and the replica budget); everything else is
an alternative. Each entry carries its exact status (see the [status key](#7-status-key-and-credit)). "The author" is
the author of this repository, Alexis Olson. Units and notation are those of
[contact moments §0](contact.md#0-units-notation-and-standing-inputs); in particular $`M`$, $`B`$ and $`h`$ are in nats.

Only the theorem for every finite law is treated here. Binary results, lower bounds on the constant and open problems
are at [AlexisOlson/stochastic-to-deterministic-latents](https://github.com/AlexisOlson/stochastic-to-deterministic-latents).

## 2. The cost of tightening

Each row is a bound $`T(p)\le C\,\tau(p)`$ for every finite law. In the rows whose composite "has no status of its
own", each step carries the status shown and the assembled pricing is exact arithmetic. The author's rows
keep PR #6's ledger and powered-reference race coding, priced by this repository's analysis of the race (the Gamma
value $`j(a)`$ and caps or tables for it); they differ in the pair charge, in how it is summed,
and in how the race price is capped. "Rests on" names the machine inputs, if any (defined in the
[status key](#7-status-key-and-credit)). PR #6 means [pull request #6](https://github.com/DLorell/stoch_to_det/pull/6)
of DLorell/stoch_to_det at its head `7b41957d`.

| $`C`$ (exact) | $`\approx`$ | Status | Rests on | Credit | Frontier |
|---|---|---|---|---|---|
| $`521115692681\text/75036146600`$ | 6.94486 | `paper proof` | fitted pair charge; 81 interval-certified caps on the race price | the author, unpublished | **yes**, both readings: lowest constant listed |
| $`500429818681873\text/72047805525880`$ | 6.94580 | `kernel-verified` in an unpublished standalone Lean file against PR #6; no pinned axiom audit | the same fitted pair charge; race prices from fitted tables checked in Lean; no interval input | the author, unpublished | **yes**, whole-route reading; also the lowest `kernel-verified` constant listed |
| $`18683211392538852259\text/2689172049828207160`$ | 6.94757 | `paper proof` | the same fitted pair charge; race cap by hand; no interval input | the author, unpublished | no: 6.94580 has the same kind of inputs and a smaller constant |
| $`6586364623667\text/947461643720`$ | 6.95159 | `paper proof` | computer algebra for the pair charge; interval-certified race caps | the author, unpublished | no |
| $`2789\text/400`$ | 6.9725 | `kernel-verified` in the first version of this repository; also `paper proof` | by hand, long; no fitted certificate and no interval-certified input | the first version of this repository, following PR #6's method | **yes**, both readings: lowest constant listed with neither kind of certificate |
| $`3259043\text/466400`$ | 6.98766 | pair charge and cap C4b `paper proof`; composite has no status of its own | by hand, long | the author, unpublished | no |
| $`612329\text/87500`$ and $`153077\text/21875`$ | 6.998046 and 6.997806 | pair charge (on a common support with holes) and cap C4b `paper proof`; composites have no status of their own | not rated | the author, unpublished | no on the whole-route reading; not placed on the charge reading (not rated) |
| $`5249623\text/750000`$, stated as $`13999\text/2000`$ | 6.999497 | pair charge C `paper proof` on the [pair-charge page](pair-charge.md); cap C3b `kernel-verified` here and `paper proof` on the [cap page](cap.md); the route `kernel-verified` in this repository, by its verification procedure run by the author, with `pairCharge_C` and `NaturalLatents.T_le_mul_tau` at $`13999\text/2000`$ | a pair-charge certificate with fifteen exact rational coefficients, checked by exact rational arithmetic; cap C3b by hand | this repository, following PR #6's method | no: 6.9725 has no machine input and a smaller constant, so it dominates on the whole-route reading whether or not charge C's certificate counts as a machine input; charge C has no rating, so it is not placed on the charge reading |
| $`174991\text/25000`$ | 6.99964 | `paper proof` | by hand, long; no interval cover | the author, unpublished | no |
| $`611449624681\text/86131759120`$ | 7.0990 | `paper proof`; its scalar steps are interval-certified | an 8050-leaf interval cover and 31 certified polynomial inequalities that rule out regions of the parameter space | the author, unpublished | no |
| $`262455475975567531769293\text/34940450429503539167584`$ | 7.5115 | `paper proof`; whether it counts as by hand is undecided (its correctness is accepted) | by hand, but a 20-monomial identity is left unprinted | the author, unpublished | charge reading only, if ruled by hand |
| $`263243861856755163277009\text/34940450429503539167584`$ | 7.5341 | `paper proof` | by hand; a short pair charge in seven parts | the author, unpublished | charge reading only, unless 7.5115 is ruled by hand |
| $`15943993687\text/2058091192`$ | 7.7470 | `paper proof` | by hand; a one-page pair charge | the author, unpublished | no (see below) |
| $`47\text/5`$ | 9.4 | `kernel-verified`: PR #6's own verification script, run by the author at head `7b41957d` | fitted certificates: Bernstein pieces of degree 26 to 28, and a closure with degree-7 Bernstein vectors whose coefficients run to about 70 digits | Jeremy Gillen, PR #6 | no |

The row at 6.999497 is this repository's route: charge C with cap C3b at $`a=211\text/45`$,
$`u=3941\text/20000`$. The row at 6.9725 is the first version of this repository, with charge A; it remains in the
commit history. The present version uses charge C, whose proof for $`s\le1`$ closes with one scalar certificate of
fifteen rational coefficients (for $`s\ge1`$ the separation price alone pays), although charge A gives the smaller
constant.

**The frontier.** Ease is compared by class, not by hours, in one of two readings. The charge reading rates the pair
charge alone: by hand, then by hand but long, then machine-assisted. The whole-route reading compares the machine inputs
used anywhere in the route: a route whose inputs are a subset of another's is at most as hard. Fitted certificates and
computer algebra count as one kind, and race-price tables checked in Lean count as fitted certificates checked by
machine. A point is on the frontier when no other point has a constant at most as large and a class at most as hard,
with one of the two strictly better. Rows without a rating are listed but not placed. Within a class, readers' time
estimates overlap and are not used: the one-page charge at 7.7470 is shorter on paper than the seven-part charge at
7.5341, but its estimates overlap, so it is not counted as easier. Being `kernel-verified` is reported but not ranked
as ease. Effort ratings are readers' estimates, not timed checks.

This is the frontier among the entries listed here, as of October 2026. It is not a proven trade-off: nothing rules
out a short proof with a smaller constant.

## 3. Three ways to reach every finite law

In this repository the ledger, race, cap and payment (steps 2, 3, 4 and 6 of the [route](overview.md#the-route)) are applied to
the setup latent: it attains $`\tau(p)`$, its distinct components are positive contacts of one feasible kernel on the common
support, and its posterior rows are positive there. The first two routes below produce such a latent; the third
produces a weaker one and adapts the race and the payment. All three were carried out with charge A, the pair charge
of the first version of this repository, and give $`2789\text/400`$.

**Connected support, then a component split (this repository).** `exists_setup_of_connected` builds the latent when the
support is connected, and `extension_of_connected` passes to every finite law because, over the connected components of the support, with
weights $`\rho_k`$ and normalized laws $`\bar p_k`$, $`\sum_k\rho_k\tau(\bar p_k)\le\tau(p)`$ and
$`T(p)\le\sum_k\rho_kT(\bar p_k)`$ ([extension](extension.md), (E3.F)). Status: `kernel-verified` in this repository
with charge C, at $`13999\text/2000`$; with charge A, at $`2789\text/400`$, it is `kernel-verified` in the first version.
The split itself does not depend on the constant.

**Positive laws, then continuity.** On a strictly positive law the support is the whole rectangle, which is connected,
so the setup applies with contacts positive everywhere. For a general $`p`$ and $`0<\varepsilon<1`$, set
$`p_\varepsilon=(1-\varepsilon)p+\varepsilon\,u`$ with $`u`$ uniform on $`X\times Y`$ (a law, not the price bound
$`u`$ of section 6). From any latent $`L`$ of $`p`$
with priors $`\pi_i`$ and components $`q_i`$, form the latent of $`p_\varepsilon`$ with components $`q_i`$ at priors
$`(1-\varepsilon)\pi_i`$ and one extra component $`u`$ at prior $`\varepsilon`$. Its joint law with $`(X,Y)`$ depends
continuously on $`\varepsilon`$, so by continuity of finite-alphabet entropies its score tends to that of $`L`$. Also
$`T(p_\varepsilon)\to T(p)`$, because $`T`$ is a minimum over one fixed finite family of partitions of $`X\times Y`$,
each with a score continuous in the law, whatever the support. Let $`\varepsilon\to0`$, then take the infimum over
$`L`$; no continuity of $`\tau`$ is needed. Status: `paper proof`; `kernel-verified` in the author's unpublished
standalone Lean file against PR #6, not in this repository.

**Every finite law at once.** For any finite $`p`$, whose support $`S`$ may be disconnected or have holes, the
optimality conditions give one feasible kernel $`w>0`$ on $`S`$ and an attained latent whose components are contacts of
$`w`$. Feasibility forces each component onto exactly one connected component of $`S`$, positive throughout it and zero
elsewhere, so the component split is a property of the optimum, not a step of the proof. Posterior rows therefore
vanish off a component. The written proof runs a race with zero posterior rates allowed (a label with zero rate never
wins) and prices it with the four-term cap
$`j(a)<\frac{3291}{4000a}+\frac{241}{600a^2}+\frac{271}{1000a^3}+\frac{26}{125a^3(a-1)}`$, valid for every $`a>1`$. In
the payment, components in different connected components never share a cell and add nothing to $`d`$; two components
in the same one, restricted to it, are positive contacts on a common support, where the pair charge applies. Status:
`paper proof`; `kernel-verified` in the same unpublished file, where the race step is proved instead by perturbing the
latent and passing to a limit.

## 4. The race price

The race price is a Gamma value, $`j(a)=a\ln\Gamma(1-1\text/a)-\gamma_E`$, derived from a one-sided stable law and
Frullani's integral on the [race](race.md) page (Lemmas R7 and R8; `race_gamma_price`, `kernel-verified` here).

It is bounded by elementary sums: the [cap page](cap.md) writes $`j(a)`$ as a series in the values
$`\zeta(k)`$ of the Riemann zeta function and bounds $`\zeta(2)`$, $`\zeta(3)`$ and $`\zeta(4)`$ by rational numbers,
which gives the cap C3b of step 4 of the [route](overview.md#the-route). Status: `kernel-verified` here
(`racePrice_lt_capC3b`), and `paper proof` on the cap page. The first
version of this repository used the cap C3a, the same cap with $`\zeta(2)<79\text/48`$ in place of
$`533\text/324`$; its written proof is `paper proof`, the author's unpublished work.

The race inequality underneath is universal: for every finite source with strictly positive posterior rows, with no
attainment or contact hypothesis, the race code $`A_E(Z)`$ has seed-averaged entropy
$`H(A_E(Z)\mid E)\le a\,I(Z;L)+j(a)\,d`$, with $`d`$ the mismatch of that source (race page, (R25) of Lemma R10;
`race_single_law`, `kernel-verified` here). For $`a>2`$ the coefficient $`j(a)`$ cannot be lowered in that universal
statement (`paper proof`, the author's unpublished work). This limits the race step as stated, not the theorem's
constant: keeping that inequality and the other accounting steps fixed, improvements come from the pair charge, the
accuracy of the cap and the choice of $`a`$. A race estimate that uses the structure of the setup latent is not ruled
out.

## 5. The budget and where the pair charge is needed

The replica budget $`K\le2M+B`$ is the inequality form of an exact identity $`K=2M+B-C-2N`$, proved on the
[replica](replica.md) page; there $`C`$ and $`N`$ are nonnegative replica terms, not the constant.

**Large budgets need no pair charge.** For every finite latent whose posterior rows are positive on the support, if
$`M\ge(3\text/20)\ln2`$ or $`M+B\ge(8\text/15)\ln2`$ (in nats; the thresholds are $`3\text/20`$ and $`8\text/15`$ bits),
the race alone gives $`h\le(499\text/100)B+(399\text/100)M`$: run the race on each $`X`$-fiber and each $`Y`$-fiber and
bound $`d`$ by 1, so that $`h\le aB+2j(a)`$ for every $`a>1`$, with $`j(a)<F(a)`$ by Lemma K13. If
$`M\ge(3\text/20)\ln2`$, take $`a=499\text/100`$: $`2F(499\text/100)<0.368<(399\text/100)(3\text/20)\ln2\le(399\text/100)M`$.
If $`M+B\ge(8\text/15)\ln2`$, take $`a=133\text/50`$: $`2F(133\text/50)<0.779<(233\text/100)(8\text/15)\ln2\le(233\text/100)(M+B)`$,
so $`h\le(133\text/50+233\text/100)B+(233\text/100)M\le(499\text/100)B+(399\text/100)M`$. With the ledger this gives
$`T(p)\le(1397\text/200)\,\tau(p)\approx6.985\,\tau(p)`$ **only for laws whose setup latent meets either threshold**,
never as a constant for every finite law. It locates the hard case: the pair charge is needed only below both
thresholds. Status: `paper proof`, a corollary of the race inequality.

## 6. Other pair charges

**Charges in this repository's form.** The pair charge $`PC(\beta,\gamma)`$ of
[contact moments §0](contact.md#0-units-notation-and-standing-inputs) can be replaced without changing the setup,
ledger, race or payment. A cap certifying $`j(a)<u`$ at the chosen $`a`$ gives

```math
C=\max\left\{1+\frac{3u(1+2\beta)}{\gamma},\ \frac{3a-1}{2}+\frac{3u\beta}{\gamma}\right\}.
```

| Charge | $`(\beta,\gamma)`$ | $`a`$ | $`u`$ | Cap | $`C`$ | Status |
|---|---|---|---|---|---|---|
| charge A (first version of this repository) | $`(1\text/10,3\text/25)`$ | $`93\text/20`$ | $`199\text/1000`$ | C3a | $`2789\text/400\approx6.9725`$ | `kernel-verified` in the first version of this repository |
| charge C (this repository) | $`(23\text/250,7\text/60)`$ | $`211\text/45`$ | $`3941\text/20000`$ | C3b | $`5249623\text/750000\approx6.99950`$ | charge `paper proof` and formalized as `pairCharge_C`; the pricing at this point formalized as `T_le_of_connected` |
| charge B | $`(3\text/32,15\text/128)`$ | $`1171\text/250`$ | $`3947\text/20000`$ | C3a | $`174991\text/25000\approx6.99964`$ | `paper proof`, charge, cap and composite |
| charge C | $`(23\text/250,7\text/60)`$ | $`75\text/16`$ | $`197\text/1000`$ | C4b | $`153077\text/21875\approx6.99781`$ | charge (common support with holes) and cap `paper proof`; composite has no status of its own |
| charge C | $`(23\text/250,7\text/60)`$ | $`586\text/125`$ | $`197\text/1000`$ | C4b | $`612329\text/87500\approx6.99805`$ | as above |
| charge D | $`(9\text/100,583\text/5000)`$ | $`75\text/16`$ | $`1971\text/10000`$ | C4b | $`3259043\text/466400\approx6.98766`$ | charge (common connected support) and cap `paper proof`; composite has no status of its own |

C3b is the cap of the [cap page](cap.md); C3a is the cap of the first version of this repository (C3b with
$`\zeta(2)<79\text/48`$ in place of $`533\text/324`$); C4b is the four-term cap above. All three hold for every
$`a>1`$: C3b is `kernel-verified` here (`racePrice_lt_capC3b`) and `paper proof` on the cap page; C3a and C4b
are `paper proof`; and at each listed point $`u`$ exceeds the cap in exact arithmetic. Four pair charges are `paper proof`, and each is priced
below 7 in the same skeleton. Three are complete checked routes: charge A (the first version of this repository),
charge C with cap C3b (this repository) and charge B (`paper proof` throughout); the C4b pricings of charges C and D
have no composite status. Charges A, B and D are rated by hand but
long. Charge C, the pair charge of this repository's route, is formalized here as `pairCharge_C`
(`NaturalLatents/General/PairCharge.lean`).

**By-hand charges in PR #6's form.** PR #6 states its charge one-sidedly, for distinct contacts $`q,q'`$ of one feasible
kernel with the same support (holes allowed), with $`BC(q,q')=\sum_z\sqrt{q(z)q'(z)}`$:

```math
1\le\kappa\,I(q)+\lambda\,[-2\ln BC(q,q')].
```

PR #6 writes $`(\alpha,\beta)`$; other letters are used here because this $`\lambda`$ is not the $`\beta`$ above. PR #6
proves $`(733\text/50,77\text/100)`$ by fitted certificates. The author has three charges with no machine step, two of
them rated by hand:
- $`(94\text/9,3\text/4)`$, on one page: 7.7470. It uses $`x\ln x-x+1\ge(3\text/2)(x-1)^2\text/(x+2)`$ with
  Cauchy–Schwarz, a second-order feasibility bound and one completed square; $`94\text/9`$ is the sharp constant of
  this argument's relaxation.
- $`(31\text/3,5\text/8)`$, in seven parts: 7.5341.
- $`(31\text/3,121\text/200)`$: 7.5115, `paper proof`; whether it counts as by hand is undecided.

None reaches 7. What they buy is a pair charge a reader can check in a few hours. Against 6.9725 the price is about
0.56 in $`C`$ for the seven-part charge and 0.77 for the one-page charge.

## 7. Status key and credit

- `kernel-verified`: checked by the Lean kernel in the place named: this repository (the verification
  procedure in its README, also run by continuous integration), PR #6's own tree, or the author's
  unpublished standalone file against PR #6, which this repository's audit does not cover.
- `paper proof`: a written proof checked step by step by readers other than the session that wrote it (language-model
  readers under the author's review; see "How this was made" in the README), not by the Lean kernel. For entries
  marked unpublished, neither the proof nor the checks are public.
- Machine inputs, which are not statuses:
  - interval-certified steps: inequalities proved by rigorous interval arithmetic with directed rounding over a finite
    cover, reproducible from a script;
  - fitted certificates: machine-produced inequalities whose coefficients a computer chose, such as polynomial bounds
    proved by the signs of their coefficients in the Bernstein basis, or certified polynomial inequalities that rule out
    regions of parameters;
  - computer algebra.

**Credit.** [DLorell/stoch_to_det](https://github.com/DLorell/stoch_to_det) formalized the problem and proved a finite
constant. Its pull request #6, by Jeremy Gillen, proved $`C=47\text/5`$ and introduced the method this repository's
main route follows: powered-reference race coding with a coordinate ledger, and a single continuous pair charge summed
against the latent's own information in place of upstream's near/far split. Its pull request #5, by Satya Benson, formalized the shared exponential race that this
repository's Lean uses. Every entry not credited to PR #6 is the author's.
