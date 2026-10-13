-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/ContinuousMismatch.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised.
import NaturalLatents.Upstream.Floor
import NaturalLatents.Upstream.Quotient
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Continuous pair charges avoid the loss from a fixed near/far threshold. -/

namespace stoch_to_det

open Finset

theorem log_le_quadratic_at_one {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    Real.log x ≤ x - 1 - (x - 1)^2 / 2 := by
  let F : ℝ → ℝ := fun x => Real.log x - (x - 1) + (x - 1)^2 / 2
  have hderiv (x : ℝ) (hx : 0 < x) :
      HasDerivAt F ((x - 1)^2 / x) x := by
    have hsub : HasDerivAt (fun y : ℝ => y - 1) 1 x := by
      simpa using (hasDerivAt_id x).sub_const 1
    convert ((Real.hasDerivAt_log hx.ne').sub hsub).add
      ((hsub.pow 2).div_const 2) using 1; try rfl
    field_simp
    ring
  have hm : MonotoneOn F (Set.Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi (0 : ℝ))
    · exact fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      have hx0 : 0 < x := by simpa using hx
      exact (hderiv x hx0).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx0 : 0 < x := by simpa using hx
      rw [(hderiv x hx0).deriv]
      exact div_nonneg (sq_nonneg _) hx0.le
  have h := hm hx (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num) hx1
  dsimp [F] at h
  norm_num at h
  linarith

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)

end stoch_to_det
