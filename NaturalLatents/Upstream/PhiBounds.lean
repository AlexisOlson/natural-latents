-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/PhiBounds.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed.
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Elementary bounds for `r * log r - r + 1`

All logarithms are natural logarithms.  At `r = 0`, Lean's convention
`Real.log 0 = 0` gives `phi 0 = 1`, matching the continuous extension of
`r * log r - r + 1` from the positive half-line.
-/

namespace stoch_to_det

/-- The scalar relative-entropy integrand, with its continuous value at zero. -/
noncomputable def phi (r : ℝ) : ℝ := r * Real.log r - r + 1

lemma continuous_phi : Continuous phi := by
  exact (Real.continuous_mul_log.sub continuous_id).add continuous_const

lemma hasDerivAt_phi {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt phi (Real.log r) r := by
  have hraw := ((Real.hasDerivAt_mul_log hr).sub (hasDerivAt_id r)).add_const 1
  refine (hraw.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with y
    rfl
  · ring

/-- `phi` is nonnegative on the nonnegative half-line. -/
theorem phi_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ phi r := by
  by_cases hr0 : r = 0
  · simp [phi, hr0]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hrpos)
    rw [Real.log_inv] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hr
    rw [mul_sub, mul_inv_cancel₀ hr0, mul_one] at hmul
    unfold phi
    nlinarith

end stoch_to_det
