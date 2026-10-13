-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/SharedRace/Clock.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised.
-- Source: pull request #5 by Satya Benson, included in pull request #6 by Jeremy Gillen at the revision above.
-- Local changes: Retained clockArgmin; moved its measurability proof to PoweredRaceWinner.
import NaturalLatents.Upstream.SharedRace.Definitions
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Normalized exponential-clock quantities

These bounded normalized quantities are the analytic core of the all-label
shared-race theorem.  Their distributional estimates are proved using the
winner-cell factorization in `Race.lean`.
-/

namespace stoch_to_det
namespace SharedRace

open Finset

variable {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]

/-- A total lexicographic argmin of `E_i / π_i`. -/
noncomputable def clockArgmin (π E : κ → ℝ) : κ :=
  lexMax (fun E i => -(E i / π i)) E

/-! ### The bounded reference law -/

end SharedRace
end stoch_to_det
