-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/SharedRace/PairClockLaw.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised.
import NaturalLatents.Upstream.SharedRace.ClockLaw
import NaturalLatents.Upstream.Prelude
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Probability.Distributions.Beta
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The two-clock sum/ratio law

This file proves the pair-clock factorization used by the loser-coordinate
estimate.  The proof starts from the product of two unit exponential laws;
it does not use a Dirichlet-distribution API.
-/

namespace stoch_to_det
namespace SharedRace

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal Interval


/-- Positive part of the unit exponential density. -/
noncomputable def unitExpDensity (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-x))

/-- The library unit exponential measure in positive-density form. -/
lemma expMeasure_one_eq_restrict_withDensity :
    expMeasure 1 =
      (volume.restrict (Ioi (0 : ℝ))).withDensity unitExpDensity := by
  unfold expMeasure gammaMeasure
  calc
    volume.withDensity (gammaPDF 1 1) =
        volume.withDensity ((Ioi (0 : ℝ)).indicator unitExpDensity) := by
      apply withDensity_congr_ae
      filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx
      by_cases hxpos : 0 < x
      · rw [Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hxpos)]
        simp [unitExpDensity, gammaPDF, gammaPDFReal, hxpos.le]
      · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hx
        rw [Set.indicator_of_notMem
          (show x ∉ Ioi (0 : ℝ) from hxpos), gammaPDF_of_neg hxneg]
    _ = (volume.restrict (Ioi (0 : ℝ))).withDensity unitExpDensity :=
      withDensity_indicator measurableSet_Ioi unitExpDensity

/- Tail law of the scaled normalized sum of two exponential clocks, after
grouping the other clocks into an independent product. -/
/-! ### Literal scaled-Beta(2,k-2) law -/

/-! ### Transport back to a finite family of iid clocks -/

/-! ### Clock-ready loser-moment corollaries -/

end SharedRace
end stoch_to_det
