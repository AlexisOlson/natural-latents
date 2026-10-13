-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/PhiBounds.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised.
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.InformationTheory.KullbackLeibler.KLFun
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

lemma phi_eq_klFun : phi = InformationTheory.klFun := by
  funext r
  simp [phi, InformationTheory.klFun]
  ring

lemma continuous_phi : Continuous phi := by
  rw [phi_eq_klFun]
  exact InformationTheory.continuous_klFun

lemma hasDerivAt_phi {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt phi (Real.log r) r := by
  rw [phi_eq_klFun]
  exact InformationTheory.hasDerivAt_klFun hr

/-- `phi` is nonnegative on the nonnegative half-line. -/
theorem phi_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ phi r := by
  rw [phi_eq_klFun]
  exact InformationTheory.klFun_nonneg hr

end stoch_to_det
