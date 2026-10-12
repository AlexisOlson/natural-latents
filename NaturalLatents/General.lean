-- Adapted from the author's earlier repository (StochasticToDeterministicLatents);
-- modified: module paths renamed; declarations unused by the main theorems removed.
import NaturalLatents.Upstream.Entropy
import NaturalLatents.Upstream.Functionals
import NaturalLatents.Upstream.Envelope
import NaturalLatents.Upstream.Duality
import NaturalLatents.Upstream.Seed
import NaturalLatents.Upstream.Quotient
import NaturalLatents.General.Pricing
import NaturalLatents.General.Extension

/-!
# Factor 2789/400 for every finite law

For every finite law `p` on `X × Y`, with `X` and `Y` finite types in `Type`,

    T p ≤ (2789/400) * tau p,

in bits (`General.T_le_mul_tau`); the constant `2789/400 = 6.9725` is below seven. The internal development
in `General/` works in nats; the factor `Real.log 2` cancels, which is `bits_of_nats_bound`.
The same bound for every law is also derived through the positive-law route
(`General.T_le_mul_tau_via_pos`) and through the connected-support route
(`General.T_le_mul_tau_via_connected`), which avoid the zero-rate race.

The proof depends on the shared-race, coordinate-race, floor and scalar modules of upstream's open
pull request #6; the result is `kernel-verified` here only relative to that revision, and the
statement does not claim that the constant is least.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
The upstream definitions and lemmas used here come from that project, including
its open pull request #6 (`jezgillen`, head `7b41957d`) at the pinned revision.
The rest is adapted from unpublished working material with public names and
module boundaries; that material supplies attribution only, not verification evidence.
-/

namespace StochasticToDeterministicLatents.General

variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- The nats bound gives the bits bound: the factor `Real.log 2` cancels. -/
theorem bits_of_nats_bound {p : Law X Y} {C : ℝ} (hb : T p ≤ C * tau p) :
    stoch_to_det.T p ≤ C * stoch_to_det.tau p := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  apply (mul_le_mul_iff_of_pos_left hlog).mp
  simpa only [T, tau, mul_left_comm] using hb

end StochasticToDeterministicLatents.General
