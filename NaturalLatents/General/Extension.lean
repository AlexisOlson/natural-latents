-- Original work by Alexis Olson, Apache-2.0 (see NOTICE), first developed in
-- github.com/AlexisOlson/stochastic-to-deterministic-latents; reorganised for this repository
-- (namespace NaturalLatents.General, declarations renamed, unused material removed).
-- This file builds on and cites the definitions of DLorell/stoch_to_det (Apache-2.0).
import NaturalLatents.General.Definitions

/-!
# From connected laws to all laws

For `0 ≤ C`, if `stoch_to_det.T q ≤ C * stoch_to_det.tau q` holds for every law `q` with connected support, then
`extension_of_connected` gives the same bound for every probability law. It applies
`stoch_to_det.reduce_to_connected` in bits, after the connected bound has been converted once.

## Attribution

Original work by Alexis Olson, first developed in
github.com/AlexisOlson/stochastic-to-deterministic-latents.
This file builds on and cites the definitions of
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
-/

namespace NaturalLatents.General

noncomputable section

open scoped BigOperators
open MeasureTheory ProbabilityTheory

variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- For `0 ≤ C`, a connected optimum bound in bits extends to every probability law. -/
theorem extension_of_connected (C : ℝ) (hC : 0 ≤ C)
    (hconnected : ∀ (q : Law X Y), stoch_to_det.IsPMF q →
      stoch_to_det.IsConnected (stoch_to_det.support q) →
      stoch_to_det.T q ≤ C * stoch_to_det.tau q)
    {p : Law X Y} (hp : stoch_to_det.IsPMF p) :
    stoch_to_det.T p ≤ C * stoch_to_det.tau p := by
  exact stoch_to_det.reduce_to_connected C hC hconnected p hp

end

end NaturalLatents.General
