-- Adapted from the author's earlier repository (StochasticToDeterministicLatents);
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised; namespace renamed to NaturalLatents.General.
import NaturalLatents.General.Definitions

/-!
# From connected laws to all laws

For `0 ≤ C`, if `T q ≤ C * tau q` holds for every law `q` with connected support, then
`extension_of_connected` gives the same bound for every probability law. It applies
`stoch_to_det.reduce_to_connected` and converts between the bit- and nat-valued functionals.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
This file retains that source's definitions and lemmas where cited, together with
material adapted from the author's earlier repository.
-/

namespace NaturalLatents.General

noncomputable section

open scoped BigOperators
open MeasureTheory ProbabilityTheory

variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- For `0 ≤ C`, a bound `T q ≤ C * tau q` on connected laws extends to every probability law. -/
theorem extension_of_connected (C : ℝ) (hC : 0 ≤ C)
    (hconnected : ∀ (q : Law X Y), stoch_to_det.IsPMF q →
      stoch_to_det.IsConnected (stoch_to_det.support q) → T q ≤ C*tau q)
    {p : Law X Y} (hp : stoch_to_det.IsPMF p) : T p ≤ C*tau p := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hbits : stoch_to_det.T p ≤ C * stoch_to_det.tau p := by
    refine stoch_to_det.reduce_to_connected C hC ?_ p hp
    intro q hq hconn
    apply (mul_le_mul_iff_of_pos_left hlog).mp
    simpa only [T_eq_upstream, tau_eq_upstream, mul_left_comm] using hconnected q hq hconn
  simpa only [T_eq_upstream, tau_eq_upstream, mul_left_comm] using
    mul_le_mul_of_nonneg_left hbits hlog.le

end

end NaturalLatents.General
