-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/Scalar.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised.
-- Source: the DLorell/stoch_to_det main branch, taken from the head of pull request #6 by Jeremy Gillen at the revision above.
import NaturalLatents.Upstream.Floor
import NaturalLatents.Upstream.Quotient
import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# Analytic estimates for the scalar race channel

This file proves logarithmic integrability and exponential-density estimates
used in the scalar-channel part of `exists_raceQuantities`. Its bounds combine
with the finite clustering identities in `Race.lean`.
-/

namespace stoch_to_det

open Finset MeasureTheory ProbabilityTheory InformationTheory

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable {p : α × β → ℝ} {D : SeedSetup p} {K : Clustering D}

private lemma integrableOn_log_mul_exp_neg_Ioi :
    IntegrableOn (fun t : ℝ => Real.log t * Real.exp (-t)) (Set.Ioi 0) := by
  have hconv :=
    (mellin_hasDerivAt_of_isBigO_rpow (E := ℂ) (s := (1 : ℂ))
      (a := (2 : ℝ)) (b := (0 : ℝ))
      (f := fun t : ℝ => (Real.exp (-t) : ℂ))
      (by
        refine (Continuous.continuousOn ?_).locallyIntegrableOn measurableSet_Ioi
        exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg))
      (by
        apply Complex.isBigO_ofReal_left.mpr
        simpa only [neg_one_mul] using
          (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one (-2)).isBigO)
      (by norm_num)
      (by
        have htend : Filter.Tendsto (fun t : ℝ => (Real.exp (-t) : ℂ))
            (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 : ℂ)) := by
          have hc : Continuous (fun t : ℝ => (Real.exp (-t) : ℂ)) := by fun_prop
          have hc0 : ContinuousAt (fun t : ℝ => (Real.exp (-t) : ℂ)) 0 :=
            hc.continuousAt
          have hmono : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 := inf_le_left
          simpa using hc0.mono_left hmono
        simpa only [neg_zero, Real.rpow_zero] using
          (Asymptotics.isBigO_const_of_tendsto
            (c := (1 : ℝ)) htend one_ne_zero))
      (by norm_num)).1
  rw [MellinConvergent] at hconv
  change Integrable (fun t : ℝ => Real.log t * Real.exp (-t))
    (volume.restrict (Set.Ioi 0))
  simpa [IntegrableOn, smul_eq_mul, ← Complex.ofReal_neg, Complex.exp_ofReal_re] using hconv.re

/-- The signed logarithmic moment of an `Exp(1)` variable. -/
theorem integral_log_mul_exp_neg_Ioi :
    ∫ t : ℝ in Set.Ioi 0, Real.log t * Real.exp (-t) =
      -Real.eulerMascheroniConstant := by
  let J : ℂ :=
    ∫ t : ℝ in Set.Ioi 0,
      (t : ℂ) ^ ((1 : ℂ) - 1) * (Real.log t * Real.exp (-t))
  have hJderiv : HasDerivAt Complex.GammaIntegral J 1 := by
    simpa only [J] using
      (Complex.hasDerivAt_GammaIntegral (s := (1 : ℂ)) (by norm_num))
  have hrealDeriv :
      HasDerivAt (fun s : ℝ => (Complex.GammaIntegral s).re) J.re 1 :=
    hJderiv.real_of_complex
  have hGamma_eq :
      Real.Gamma =ᶠ[nhds (1 : ℝ)]
        (fun s : ℝ => (Complex.GammaIntegral s).re) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with s hs
    change (Complex.Gamma (s : ℂ)).re = (Complex.GammaIntegral (s : ℂ)).re
    rw [Complex.Gamma_eq_integral (by simpa using hs)]
  have hGammaDeriv : HasDerivAt Real.Gamma J.re 1 :=
    hrealDeriv.congr_of_eventuallyEq hGamma_eq
  have hJvalue : J.re = -Real.eulerMascheroniConstant := by
    rw [← hGammaDeriv.deriv]
    linarith [Real.eulerMascheroniConstant_eq_neg_deriv]
  have hJInt : Integrable
      (fun t : ℝ =>
        (t : ℂ) ^ ((1 : ℂ) - 1) * (Real.log t * Real.exp (-t)))
      (volume.restrict (Set.Ioi 0)) := by
    simpa only [sub_self, Complex.cpow_zero, one_mul, RCLike.ofReal_mul, RCLike.ofReal_eq_complex_ofReal] using
      (integrableOn_log_mul_exp_neg_Ioi.integrable.ofReal (𝕜 := ℂ))
  have hJreal :
      (∫ t : ℝ in Set.Ioi 0, Real.log t * Real.exp (-t)) = J.re := by
    calc
      (∫ t : ℝ in Set.Ioi 0, Real.log t * Real.exp (-t)) =
          ∫ t : ℝ in Set.Ioi 0,
            ((t : ℂ) ^ ((1 : ℂ) - 1) *
              (Real.log t * Real.exp (-t))).re := by
                refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
                simp only [sub_self, Complex.cpow_zero, one_mul, Complex.mul_re,
                  Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      _ = (∫ t : ℝ in Set.Ioi 0,
          (t : ℂ) ^ ((1 : ℂ) - 1) *
            (Real.log t * Real.exp (-t))).re := integral_re hJInt
      _ = J.re := by rfl
  exact hJreal.trans hJvalue

theorem integrableOn_abs_log_mul_exp_neg_Ioi :
    IntegrableOn (fun t : ℝ => |Real.log t| * Real.exp (-t)) (Set.Ioi 0) := by
  have hnorm := integrableOn_log_mul_exp_neg_Ioi.norm
  refine hnorm.congr (ae_of_all _ fun t => ?_)
  change |Real.log t * Real.exp (-t)| = |Real.log t| * Real.exp (-t)
  rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]

end stoch_to_det
