-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/SharedRace/ClockLaw.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised.
-- Source: pull request #5 by Satya Benson, included in pull request #6 by Jeremy Gillen at the revision above.
-- Local changes: Retained the almost-sure positivity lemma for the shared exponential clocks; reorganised its imports.
import NaturalLatents.Upstream.SharedRace.Clock
import NaturalLatents.Upstream.Prelude
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Probability.Distributions.Beta
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Probability.Independence.Integration

/-!
# One-coordinate law of normalized iid exponential clocks

The key input is proved directly from exponential tails and product
independence: one normalized coordinate has the `Beta(1,k-1)` tail.  This
avoids depending on a Dirichlet-distribution API.
-/

namespace stoch_to_det
namespace SharedRace

open Finset MeasureTheory ProbabilityTheory Set

variable {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]

omit [DecidableEq κ] [Nonempty κ] in
/-- Every coordinate of the iid exponential clock is strictly positive
almost surely. -/
lemma ae_clockLaw_pos : ∀ᵐ E ∂(clockLaw κ), ∀ i, 0 < E i := by
  let _ : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  have hone : ∀ᵐ x : ℝ ∂(expMeasure 1), 0 < x := by
    have hnot := measure_eq_zero_iff_ae_notMem.mp expMeasure_one_Iic_zero
    filter_upwards [hnot] with x hx
    simpa only [Set.mem_Iic, not_le] using hx
  unfold clockLaw
  exact ae_forall_fintype fun i =>
    Measure.tendsto_eval_ae_ae.eventually hone

/-! ### Explicit scaled-Beta density interface -/

/-! ### First moments and logarithmic moments -/

end SharedRace
end stoch_to_det
