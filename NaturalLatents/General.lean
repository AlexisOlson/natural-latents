-- Original work by Alexis Olson, Apache-2.0 (see NOTICE), first developed in
-- github.com/AlexisOlson/stochastic-to-deterministic-latents; reorganised for this repository
-- (namespace NaturalLatents.General, declarations renamed, unused material removed).
-- This file builds on and cites the definitions of DLorell/stoch_to_det (Apache-2.0).
import NaturalLatents.Upstream.Entropy
import NaturalLatents.Upstream.Functionals
import NaturalLatents.Upstream.Envelope
import NaturalLatents.Upstream.Duality
import NaturalLatents.Upstream.Seed
import NaturalLatents.Upstream.Quotient
import NaturalLatents.General.Pricing
import NaturalLatents.General.Extension

/-!
# The bound for finite laws

This module gathers the development under `NaturalLatents/General/`.
`General.T_le_of_connected` proves the connected optimum bound in nats:

    TNat p ≤ (13999/2000) * tauNat p.

`NaturalLatents.Main` applies `bits_of_nats` once, then
`General.extension_of_connected` extends the bound in bits to every finite law.
The constant `13999/2000 = 6.9995` is below seven and is not claimed to be least.

## Attribution

Original work by Alexis Olson, first developed in
github.com/AlexisOlson/stochastic-to-deterministic-latents.
This file builds on and cites the definitions of
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
-/
