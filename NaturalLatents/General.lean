-- Adapted from the author's earlier repository (StochasticToDeterministicLatents);
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised; namespace renamed to NaturalLatents.General.
import NaturalLatents.Upstream.Entropy
import NaturalLatents.Upstream.Functionals
import NaturalLatents.Upstream.Envelope
import NaturalLatents.Upstream.Duality
import NaturalLatents.Upstream.Seed
import NaturalLatents.Upstream.Quotient
import NaturalLatents.General.Pricing
import NaturalLatents.General.Extension

/-!
# The bound in nats

This module gathers the development under `NaturalLatents/General/`. For every finite law `p`
on `X × Y` it provides, in nats,

    T p ≤ (13999/2000) * tau p,

as `General.T_le_of_connected` on connected supports together with
`General.extension_of_connected`; `NaturalLatents.Main` converts the bound to bits.
The constant `13999/2000 = 6.9995` is below seven and is not claimed to be least.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
This file retains that source's definitions and lemmas where cited, together with
material adapted from the author's earlier repository.
-/
