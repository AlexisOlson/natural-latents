-- Adapted from the author's earlier repository (StochasticToDeterministicLatents);
-- modified: module paths renamed; declarations unused by the main theorems removed.
import NaturalLatents.General.Definitions

/-!
# From positive and connected laws to all laws

If `T q ≤ C * tau q` holds for all positive laws `q` (resp. all laws with connected support), it holds for
every probability law `p`.

* `extension_of_pos` mixes `p` with the uniform law, applies the hypothesis to the mixtures,
  and passes to the limit using the continuity of the entropies, of `c`, and of `T`, with the
  score identity `cost_identity` supplying the cost of the mixed latent.
* `extension_of_connected` is the corresponding reduction through upstream's
  `reduce_to_connected`.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
The upstream definitions and lemmas used here come from that project, including
its open pull request #6 (`jezgillen`, head `7b41957d`) at the pinned revision.
The rest is adapted from unpublished working material with public names and
module boundaries; that material supplies attribution only, not verification evidence.
-/

namespace StochasticToDeterministicLatents.General

noncomputable section

open scoped BigOperators
open MeasureTheory ProbabilityTheory

variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- A bound `T q ≤ C * tau q` on laws with connected support extends to every probability law. -/
theorem extension_of_connected (C : ℝ) (hC : 0 ≤ C)
    (hconnected : ∀ (q : Law X Y), stoch_to_det.IsPMF q →
      stoch_to_det.IsConnected (stoch_to_det.support q) → T q ≤ C*tau q)
    {p : Law X Y} (hp : stoch_to_det.IsPMF p) : T p ≤ C*tau p := by
  have _hC := hC
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hbits : stoch_to_det.T p ≤ C * stoch_to_det.tau p := by
    refine stoch_to_det.reduce_to_connected C ?_ p hp
    intro q hq hconn
    apply (mul_le_mul_iff_of_pos_left hlog).mp
    simpa only [T_eq_upstream, tau_eq_upstream, mul_left_comm] using hconnected q hq hconn
  simpa only [T_eq_upstream, tau_eq_upstream, mul_left_comm] using
    mul_le_mul_of_nonneg_left hbits hlog.le

end

end StochasticToDeterministicLatents.General
