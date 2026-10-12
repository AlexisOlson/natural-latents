-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/ContactInformation.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed.
import NaturalLatents.Upstream.DomFloorCore
import NaturalLatents.Upstream.Toolkit
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import NaturalLatents.Upstream.Floor
import Mathlib.Data.Real.Basic

/-! Information bounds using the full contact moment and a scalar exponential estimate. -/

namespace stoch_to_det

open Finset

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- The product of marginals dominates the joint support. -/
theorem joint_absCont_product {q : α × β → ℝ} (hq : IsPMF q) :
    AbsCont q (fun z => mX q z.1 * mY q z.2) := by
  intro z hz
  by_contra hqz
  have hp := joint_pos_marginals hq (lt_of_le_of_ne (hq.nonneg z) (Ne.symm hqz))
  exact (mul_ne_zero hp.1.ne' hp.2.ne') hz

/-- Nonnegativity of the natural mutual-information budget. -/
theorem Knat_nonneg {q : α × β → ℝ} (hq : IsPMF q) : 0 ≤ Knat q := by
  apply Finset.sum_nonneg
  intro z _
  have hm : 0 ≤ mX q z.1 * mY q z.2 :=
    mul_nonneg ((isPMF_push hq).nonneg _) ((isPMF_push hq).nonneg _)
  exact mul_nonneg hm (phi_nonneg (div_nonneg (hq.nonneg z) hm))

end stoch_to_det
