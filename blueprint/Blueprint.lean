import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import Chapters.Setup
import Chapters.Contact
import Chapters.Ledger
import Chapters.Race
import Chapters.Cap
import Chapters.Affinity
import Chapters.Replica
import Chapters.Payment
import Chapters.PairCharge
import Chapters.Assembly
import Chapters.Extension
import Chapters.TableForm

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.externalCode.strictResolve true

#doc (Manual) "Natural latents: a bound below seven" =>

For every joint law $`p` on finite alphabets, the minimum deterministic latent
error $`T(p)` and the infimum finite stochastic latent error $`\tau(p)` satisfy
$`T(p)\le (13999/2000)\,\tau(p)`, with $`13999/2000=6.9995<7`.
The pages prove the exact bound $`T(p)\le(5249623/750000)\,\tau(p)`;
Lean carries its rounding up to $`13999/2000`.
One deterministic code, chosen from $`p` alone and with at most
$`|\mathcal X\times\mathcal Y|` values, has error at most
$`(13999/2000)` times the error of every finite stochastic latent of $`p`.
Both bounds are invariant under changing between nats and bits; no positivity
or independence assumption is imposed on $`p`.

The proof builds on [DLorell/stoch_to_det](https://github.com/DLorell/stoch_to_det),
[pull request #5 by Satya Benson](https://github.com/DLorell/stoch_to_det/pull/5),
and [pull request #6 by Jeremy Gillen](https://github.com/DLorell/stoch_to_det/pull/6),
whose method this route follows.

Read the [proof overview](https://github.com/AlexisOlson/natural-latents/blob/main/docs/overview.md).
The chapters reproduce the page statements and link their cited Lean
counterparts with strict resolution. The retained Lean notes describe exactly
which conclusions each declaration states.

`kernel-verified`: the cited Lean declarations together prove the whole statement.

`partly kernel-verified`: the cited Lean declarations prove only part of the statement; the proof block opens with "Lean proves: ..." and names that part.

`paper proof`: the node has no cited Lean declaration and relies on the paper proof.

The component cost identity links the declaration names of its private Lean proofs,
as identified in the page notes.
Information quantities are in nats until the table-form chapter, which uses bits.

{include 0 Chapters.Setup}

{include 0 Chapters.Contact}

{include 0 Chapters.Ledger}

{include 0 Chapters.Race}

{include 0 Chapters.Cap}

{include 0 Chapters.Affinity}

{include 0 Chapters.Replica}

{include 0 Chapters.Payment}

{include 0 Chapters.PairCharge}

{include 0 Chapters.Assembly}

{include 0 Chapters.Extension}

{include 0 Chapters.TableForm}

{blueprint_graph (direction := LR)}
{blueprint_summary}
