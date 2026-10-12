-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/PoweredRaceWinner.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed.
import NaturalLatents.Upstream.Race

/-! A fourth-power clock reference. Its winning log score is an exact KL
identity; only the bounded partition-function expectation remains to bound. -/

namespace stoch_to_det.SharedRace

open Finset MeasureTheory

variable {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]

lemma measurable_clockArgmin [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (π : κ → ℝ) : Measurable (clockArgmin π) := by
  unfold clockArgmin
  apply measurable_lexMax
  intro i
  change Measurable (fun E : κ → ℝ => -(E i / π i))
  fun_prop

end stoch_to_det.SharedRace
