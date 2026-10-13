# Overview of the proof

This page proves nothing new. It states the theorem, gives the idea of the proof in one paragraph, and lists the steps
of the route in order, each with the page that proves it and the Lean declaration that formalizes it. Every step
except the extension and the table form meets in one place: the assembly `NaturalLatents.General.T_le_of_connected`
(`NaturalLatents/General/Pricing.lean`), which proves the bound for a law with connected support and is described on the
[assembly page](assembly.md). The notation is that of section 0 of the [contact page](contact.md).

## The theorem

Units and notation are fixed in section 0 of the [contact page](contact.md). Let $`X,Y`$ be random variables with finite
alphabets $`\mathcal X,\mathcal Y`$, and let $`p`$ be their joint law on $`\mathcal X\times\mathcal Y`$. A finite
stochastic latent is a finite random variable $`V`$ whose joint law with $`(X,Y)`$ has $`(X,Y)`$-marginal $`p`$, with
error $`I(X;Y\mid V)+I(V;X\mid Y)+I(V;Y\mid X)`$; $`\tau(p)`$ is the infimum of that error. A deterministic latent is a
code $`\Gamma=g(X,Y)`$, with error $`I(X;Y\mid\Gamma)+H(\Gamma\mid X)+H(\Gamma\mid Y)`$; $`T(p)`$ is its minimum. The
theorem is stated in bits and the proof works in nats; $`T`$ and $`\tau`$ scale by the same factor, so the constant has
no unit. The file `NaturalLatents/Statement.lean` defines these quantities from probability tables, in bits, and
contains no proofs. It states two propositions:

- `TableClaim`: there is a real $`c`$ with $`0\le c<7`$ such that for every finite law $`p`$ one deterministic code $`g`$
  with at most $`\lvert\mathcal X\times\mathcal Y\rvert`$ values, chosen from $`p`$ alone, satisfies
  `DeterministicError (deterministicTable p g) ≤ c * StochasticError q` for every finite joint law $`q`$ of
  $`(X,Y,V)`$ with marginal $`p`$;
- `ScoreClaim`: there is a real $`c`$ with $`0\le c<7`$ such that `T p ≤ c * tau p` for every finite law $`p`$.

The proof gives both with

```math
c=\frac{13999}{2000}=6.9995,
\qquad
T(p)\le\frac{5249623}{750000}\,\tau(p)\le\frac{13999}{2000}\,\tau(p)
\quad\text{for every finite law }p.
```

The exact constant $`5249623\text/750000\approx6.999497`$ is the one the pages prove; the formal statements carry its
rounding up, $`13999\text/2000`$. No positivity or independence assumption is made on $`p`$, and neither constant is
claimed to be least.

Lean: `NaturalLatents.table : TableClaim` and `NaturalLatents.score : ScoreClaim` (`NaturalLatents/Main.lean`), whose
types and axioms are pinned in `Verify.lean`, with the constant `NaturalLatents.c := 13999 / 2000`. The exact optimum
bound is `NaturalLatents.T_le_mul_tau`, which states `T p ≤ (13999 / 2000) * tau p` and is pinned in `Verify.lean`. In
`Statement.lean` the alphabets are the types `A` and `B` (the Lean `B` is an alphabet, not the budget $`B`$ below), and
the code takes values in `Fin (Fintype.card (A × B))`.

## The idea in one paragraph

Work in nats on a law whose support is connected: the bipartite graph joining each value of $`X`$ to each value of
$`Y`$ with which it has positive probability is connected. Write $`Z=(X,Y)`$ for a cell. Choose a latent $`L`$ that
attains $`\tau(p)`$ and whose components are distinct contacts of one feasible kernel, with every posterior row
$`r_z(i)=\Pr(L=i\mid Z=z)`$ positive on the support. Here a feasible kernel is a positive weight $`w`$ on the support with
$`\sum w(x,y)\mu(x)^{2\text/3}\nu(y)^{2\text/3}\le1`$ for all probability vectors $`\mu`$ on $`\mathcal X`$ and $`\nu`$
on $`\mathcal Y`$, and a contact of $`w`$ is a probability law $`q`$, positive on the support and zero outside it, with
$`q(x,y)=w(x,y)\,q_X(x)^{2\text/3}q_Y(y)^{2\text/3}`$ on the support, where $`q_X,q_Y`$ are its marginals ((C1.1) and
(C1.2) on the [contact page](contact.md)). Contacts appear because of optimality: the components of an optimal latent
are equality cases of one affine lower bound $`\phi(q)\ge\ell\cdot q`$ on the component functional
$`\phi(q)=2H(q_X)+2H(q_Y)-3H(q)`$, and the kernel equal to $`\exp(\ell\text/3)`$ on the support and zero off it is
feasible and has exactly those equality cases as its contacts ((S1.F), (S1.O) and (S1.U) on the
[setup page](setup.md)). Split the error of $`L`$ into the budgets $`M=I(X;Y\mid L)`$ and
$`B=I(L;X\mid Y)+I(L;Y\mid X)`$. Turn $`L`$ into a random deterministic code by an exponential race among its labels,
with an exponent $`a>1`$, run at each cell with the posterior as rates and one set of clocks shared by all cells. The exponent does not change
the winner, which at each cell $`z`$ is the label minimizing $`E_i\text/r_z(i)`$ for the clocks $`E_i`$ and so has law
$`r_z`$ (Lemma R4); it enters only the powered reference masses (R8) against which the entropy of the code is bounded.
The
ledger bounds $`T(p)`$ by the budgets and by $`h`$, the average over the race of $`H(f(Z)\mid X)+H(f(Z)\mid Y)`$ for the
fixed code $`f`$. The race costs $`aB`$ plus $`2j(a)`$ for each unit of the posterior mismatch $`d`$, the probability
that two labels drawn independently from the posterior at a cell drawn from $`p`$ disagree; the price $`j(a)`$ is
defined in step 3. The mismatch $`d`$ is paid back by $`M`$ and $`B`$: the affinity bound separates the marginals of two
distinct contacts of one feasible kernel, and the pair charge $`PC(\beta,\gamma)`$ of step 6 prices each such pair by its
information and that separation. A linear combination of these inequalities is the constant. The bound then passes to every finite law by splitting the support into its
connected components, and to bits and probability tables by a change of units and a relabelling.

## The route

1. **Setup.** For a law with connected support there is a latent attaining $`\tau(p)`$, with positive priors and distinct
   components that are contacts of one feasible kernel and give positive posterior rows ([setup](setup.md)).
2. **Ledger.** For any calibrated random deterministic map, that is, a random map independent of $`(X,Y)`$ whose value
   at each cell $`z`$ of the support has law $`r_z`$, $`T(p)\le M-B\text/2+3h\text/2`$ ([ledger](ledger.md)).
3. **Race.** For every $`a>1`$ the exponential race gives such a map with $`h\le aB+2\,j(a)\,d`$, where
   $`j(a)=a\ln\Gamma(1-1\text/a)-\gamma_E`$; here $`\Gamma`$ is the Gamma function and $`\gamma_E`$
   is Euler's constant ([race](race.md)).
4. **Cap.** For every $`a>1`$, $`j(a)`$ is below an explicit rational function of $`a`$, which at $`a=211\text/45`$ is
   below $`u=3941\text/20000`$ ([cap](cap.md)).
5. **Affinity and replicas.** For two distinct positive contacts $`P,R`$ of one feasible kernel, let $`s=s(P,R)`$ be
   their separation, defined in (C1.3) on the [contact page](contact.md), with $`0<s<2`$. Each marginal Bhattacharyya
   affinity of $`P`$ and $`R`$ is at most $`1-9s\text/16+3s^2\text/64`$, so the two together give
   $`-\ln BC_X-\ln BC_Y\ge\Psi(s)=-2\ln(1-9s\text/16+3s^2\text/64)`$ ([affinity](affinity.md), (A2.1)). For two labels
   $`L_1,L_2`$ drawn independently from the posterior at one cell, $`I(L_2;X\mid L_1)+I(L_2;Y\mid L_1)\le2M+B`$
   ([replica budget](replica.md)).
6. **Payment.** The pair charge $`PC(\beta,\gamma)`$, for $`\beta\ge0`$ and $`\gamma>0`$, is the inequality
   $`(I(P)+I(R))\text/2+\beta\Psi(s(P,R))\ge\gamma`$ for every two distinct positive contacts $`P,R`$ of one feasible
   kernel, where $`I(P)=D(P\Vert P_X\otimes P_Y)`$ is the mutual information of $`P`$ (section 0 of the
   [contact page](contact.md)). For the latent of step 1, if $`PC(\beta,\gamma)`$ holds and the affinity bound holds for
   each pair of its distinct components, the replica budget gives $`\gamma d\le(1+2\beta)M+\beta B`$
   ([payment](payment.md)).
7. **Pair charge.** Every two distinct positive contacts of one feasible kernel satisfy
   $`PC(23\text/250,7\text/60)`$ ([pair charge](pair-charge.md)).
8. **Pricing.** Steps 1 to 7 combine into $`T(p)\le(13999\text/2000)\,\tau(p)`$ for every law with connected support
   ([assembly](assembly.md)).
9. **Extension.** $`T`$ and $`\tau`$ are compared across the connected components of the support, so the bound holds
   for every finite law ([extension](extension.md)).
10. **Bits and tables.** Dividing by $`\ln2`$ and relabelling an optimal code into a code with at most
    $`\lvert\mathcal X\times\mathcal Y\rvert`$ values gives the two propositions of `Statement.lean`
    ([table form](table-form.md)).

## The pricing in one display

Substitute the race and the cap into the ledger, and the payment into the mismatch term:

```math
\begin{aligned}
T(p)&\le M+\frac{3a-1}{2}B+3ud
\le C_M\,M+C_B\,B,\\
C_M&=1+\frac{3u(1+2\beta)}{\gamma}=\frac{218729}{31250},\qquad
C_B=\frac{3a-1}{2}+\frac{3u\beta}{\gamma}=\frac{5249623}{750000},\\
T(p)&\le\max\{C_M,C_B\}\,(M+B)=\frac{5249623}{750000}\,\tau(p)\le\frac{13999}{2000}\,\tau(p),
\end{aligned}
```

at $`(a,u,\beta,\gamma)=(211\text/45,\,3941\text/20000,\,23\text/250,\,7\text/60)`$, using $`M,B,d\ge0`$ and
$`M+B=\tau(p)`$. The [assembly page](assembly.md) gives the derivation and the exact arithmetic.

## Where each step lives in Lean

Unless prefixed otherwise, the declarations are in the namespace `NaturalLatents.General`, in `NaturalLatents/General/`.

| Step | Declaration | File |
|---|---|---|
| Setup | `exists_setup_of_connected` | `Setup.lean` |
| Ledger | `T_le_ledger` | `Ledger.lean` |
| Race | `exists_race` | `ExponentialRace.lean`, with `RaceLaplace.lean` and `RaceTransport.lean` |
| Cap | `racePrice_lt_capC3b` | `Cap.lean` |
| Contact moments | `contact_moments` | `Contact.lean` |
| Affinity | `affinity_bound` | `Affinity.lean` |
| Replica budget | `replica_budget` | `Replica.lean` |
| Payment | `mismatch_payment` | `Payment.lean` |
| Pair charge | `pairCharge_C` | `PairCharge.lean`, with `PairCharge/Correction.lean` and `PairCharge/Certificate.lean` |
| Pricing | `T_le_of_connected` | `Pricing.lean` |
| Extension | `extension_of_connected`, with `stoch_to_det.reduce_to_connected` | `Extension.lean`, `NaturalLatents/Upstream/Connected.lean` |
| Bits and tables | `bits_of_nats` (`Nats.lean`), `NaturalLatents.T_le_c_mul_tau`, `NaturalLatents.table`, `NaturalLatents.score`, `NaturalLatents.c`, `NaturalLatents.T_le_mul_tau` | `NaturalLatents/Main.lean`, with `Envelope.lean`, `SourceCoarsening.lean`, `TableBoundProof.lean` and `TableInformationProof.lean` in `NaturalLatents/Upstream/` |

## Reading order

Read section 0 of the [contact page](contact.md) first; it fixes units and notation for every page, and the
introduction of that page lists the page prefixes of lemma and equation numbers (for example, Lemma S1.4 is on the setup page). Then follow the route
in order: [setup](setup.md), [ledger](ledger.md), [race](race.md), [cap](cap.md), section 1 of the
[contact page](contact.md), [affinity](affinity.md), [replica budget](replica.md), [payment](payment.md),
[pair charge](pair-charge.md), [assembly](assembly.md), [extension](extension.md) and [table form](table-form.md). The
ledger, payment and assembly pages are short and show how the pieces fit; a first reading can take the race, cap and
pair-charge statements on trust and return to their proofs. Other routes, and what a smaller constant would cost, are on
the [landscape page](landscape.md).

The formal proof builds on DLorell/stoch_to_det, on its pull request #6 by Jeremy Gillen, whose method,
powered-reference race coding with a coordinate ledger, this route follows, and on its pull request #5 by Satya Benson,
the shared-race formalization it uses; the
[upstream page](upstream.md) lists what is taken from each.
