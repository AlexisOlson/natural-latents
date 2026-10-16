# Upstream inputs

This page proves nothing. It lists what the proof takes from the Lean code under `NaturalLatents/Upstream/`, adapted
from [DLorell/stoch_to_det](https://github.com/DLorell/stoch_to_det) (Apache-2.0), and which page relies on each part.
The assembly `NaturalLatents.General.T_le_of_connected` (`NaturalLatents/General/Pricing.lean`) reaches this code
through the setup, the contact estimates, the race, the payment and the ledger. `NaturalLatents/Main.lean` reaches
`reduce_to_connected` through the extension `extension_of_connected`, uses the table modules directly to restate
the bound for probability tables, and contains bridge proofs adapted from pull request #6's `FiniteBoundProof.lean` and
`TableBoundProof.lean`.

Nothing here is taken on citation: these files are compiled with the rest of the repository, scanned by
`scripts/trust_scan.sh`, and lie inside the dependency cone whose axioms `Verify.lean` pins for `table`, `score` and
`T_le_mul_tau`, so they are `kernel-verified` here.

## Provenance

Every file under `NaturalLatents/Upstream/` is adapted from DLorell/stoch_to_det at revision
`7b41957da9500716102cba323b3a48af0f23751c`, the head of its
[pull request #6](https://github.com/DLorell/stoch_to_det/pull/6) by Jeremy Gillen. Each file's header names its source
path and that revision, states the common modifications (module paths renamed, declarations unused by the main theorems
removed, documentation revised), and names in a `Source:` line the layer below that the file comes from. Eighteen of
the twenty-five files also carry a `Local changes:` line listing the helper lemmas they add, move or re-prove, among
them the re-proof of `reduce_to_connected` in `Connected.lean`. The namespace `stoch_to_det` is kept. The code at that revision comes in three
layers:

- **The DLorell/stoch_to_det main branch**, which formalized the problem and a proof of a finite constant: the finite
  information theory, the score functionals, the duality, the existence of optimal latents, the seed and clustering
  data, and the reduction to connected supports.
- **The shared exponential race**, first written in
  [pull request #5](https://github.com/DLorell/stoch_to_det/pull/5) by Satya Benson and included in pull request #6:
  the `SharedRace/` modules (byte-identical at the two pull-request heads), the clock-race lemmas added
  to `Race.lean`, the contact secants added to `Floor.lean`, and first versions of `DomFloorCore.lean` and
  `PhiBounds.lean`, which pull request #6 revises. `Seed.lean`, `Race.lean` and `Floor.lean` also differ between the
  two pull-request heads; pull request #6 makes some of pull request #5's lemmas public, and the versions here follow
  pull request #6.
- **Pull request #6 itself**: the coordinate race, the powered-race winner, the contact-information estimates, and
  the passage to probability tables.

The assembly follows pull request #6's method, powered-reference race coding with a coordinate ledger. The
probability-table definitions in `Statement.lean` are taken from its `ReadableStatement.lean`, and `TableClaim`
restates its readable theorem with $`c<7`$ in place of $`47\text/5`$. See `NOTICE` and `LICENSE` for the terms.

## What each module provides

**Foundations** (main branch).

- `Prelude.lean`, `Entropy.lean`: the base-2 logarithm, finite measures and pushforwards, entropy, conditional entropy,
  mutual and conditional mutual information, and the component functionals `Psi` and `Phi`. Every page relies on them;
  section 0 of the [contact page](contact.md) fixes the notation built on them.
- `Functionals.lean`: latents, the stochastic score, $`\tau`$ and $`T`$, the score of a deterministic map, the support
  and its connectedness. These are the objects of every page; the [ledger](ledger.md) uses `T_le_score`.

**Optima and duality** (main branch).

- `Envelope.lean`: the score identity `Latent.score_eq`, the envelope form of $`\tau`$, attainment of $`\tau`$ and of
  $`T`$, and latents defined by functions. The [setup](setup.md) (Lemmas S1.1 and S1.2), the [extension](extension.md),
  the [ledger](ledger.md) and the conversion to tables in `Main.lean` rely on it.
- `Duality.lean`: feasible kernels and contacts, `exists_common_contact_pair` (an attaining latent whose components are
  contacts of one feasible kernel), `contact_support_eq` (full support on a connected support) and
  `contact_hypercontractive`. The [setup](setup.md) relies on all but `contact_hypercontractive` (Lemmas S1.2 to S1.4); the
  [contact page](contact.md) takes its definitions of feasibility and contact from here, and its Lemma C1.3 is a case of
  `contact_hypercontractive`, on which the Lean proof of its Hessian test, and through it the pair charge, rests.

**Setup and extension** (main branch).

- `Seed.lean`, `Quotient.lean`: `SeedSetup` and `exists_seedSetup`, which package the attaining latent and kernel with
  positive priors, and `exists_clustering`, which merges duplicate components; the [setup](setup.md) relies on both.
  `Seed.lean`, whose retained declarations are all from the main branch although both pull requests change the file,
  also supplies the exponential clocks and the Gumbel seed law of the [race](race.md), and local
  conditional-information identities used by the [ledger](ledger.md) and the [replica budget](replica.md).
- `Connected.lean`: component decompositions and `reduce_to_connected` (main branch), here re-proved from two one-sided
  component inequalities in place of upstream's two equalities, on which the [extension](extension.md) rests.

**Contact estimates.**

- `Floor.lean` (main branch, with the contact secants from pull request #5): the cube-root contact secants and their
  ratio and mean identities, used by the Lean proofs of the [contact page](contact.md)'s lemmas.
- `Toolkit.lean` (main branch): the Bhattacharyya affinity, relative entropy and the Bhattacharyya inequality, used by
  the [affinity bound](affinity.md) and the payment.
- `DomFloorCore.lean`, `PhiBounds.lean` (pull requests #5 and #6) and `ContactInformation.lean` (pull request #6): the
  natural-log mutual information `Knat` and its identification with mutual information, the function $`r\ln r-r+1`$,
  and nonnegativity and absolute-continuity facts for `Knat`. The [contact page](contact.md) defines $`I(q)`$ through
  `Knat`; the payment and the pair charge use the rest.

**The race.**

- `SharedRace/Definitions.lean`, `Clock.lean`, `ClockLaw.lean`, `PairClockLaw.lean`, `Information.lean` (pull request
  #5): the shared-race winner, the posterior mean, the categorical mismatch $`d`$, the clock argmin and its law, the unit
  exponential density, a cross-entropy bound, and the identity of a posterior mutual information with an expected
  relative entropy. The [race](race.md) relies on
  them, and the mismatch $`d`$ of (D3) is the categorical mismatch.
- `Race.lean` (main branch, with the clock-race lemmas from pull request #5) and `Scalar.lean` (main branch): the
  identification of the shared-race winner with the clock argmin, integration over strict clock wins, the winner's
  residual clock, and the logarithmic moment $`\int_0^\infty\ln t\,e^{-t}\,dt=-\gamma_E`$; the
  [race](race.md) relies on them.
- `CoordinateRace.lean`, `PoweredRaceWinner.lean` (pull request #6): the split of a conditional mutual information over
  an observed coordinate, the conditioning of a uniform shared-race entropy bound on a function of the source,
  integrability of the shared-winner code, and measurability of the clock argmin. The [race](race.md), the [replica budget](replica.md) and the payment
  rely on them.

**Probability tables** (pull request #6).

- `SourceCoarsening.lean`, `TableInformationProof.lean`, `TableBoundProof.lean`: the latent built from a joint table,
  the table form of each information quantity and its agreement with the latent form, and the deterministic table of a
  code. `Main.lean` uses them to derive the two theorems of `NaturalLatents/Statement.lean` from the bound on $`T`$
  and $`\tau`$.
