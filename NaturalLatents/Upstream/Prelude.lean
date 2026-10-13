-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/Prelude.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised.
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Basic conventions and analytic facts

Information quantities in the files under `Upstream/` are measured in bits
unless a name or statement explicitly uses natural logarithms; the files under
`General/` work in nats. This file defines the base-2 logarithm `lg` and its
conversion to the natural logarithm.
-/

namespace stoch_to_det

open scoped BigOperators

/-- Base-2 logarithm. All information quantities in this development are in
**bits** unless the name says `_nats`. -/
noncomputable abbrev lg (x : ℝ) : ℝ := Real.logb 2 x

@[simp] lemma lg_one : lg 1 = 0 := by simp [lg]

/-- Conversion factor between the two unit systems: `lg x = Real.log x / Real.log 2`. -/
lemma lg_eq_log_div (x : ℝ) : lg x = Real.log x / Real.log 2 := rfl

end stoch_to_det
