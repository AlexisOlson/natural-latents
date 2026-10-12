-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/Scalar.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed.
import NaturalLatents.Upstream.Floor
import NaturalLatents.Upstream.Quotient
import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# §8. The scalar channel theorem


`scalar = I(σ_B(Z) T ; Z ∣ B, C₀) ≤ S + κ d`, with `κ = (1 + ln 8 − γ)/ln 2`.

The statement of Theorem 8.1 is the `RaceQuantities.scalar_le` obligation;
this module keeps the scalar analytic ingredients and the `Ksc` assembly bound.

## Proof structure

The calculation is performed in nats and converted at the end; nats-valued statements
here carry the `_nats` suffix. Fix a context `(g,b)` and write `R := p/σ_b(Z)` under the source
posterior `ν`, `C := −E_ν ln R = D(ν ‖ q_g) ≥ 0`. Then:

* **Off-diagonal `b ≠ g`.** The bijection
  `W := ln(U/p) = X + N` with `X := −ln R` a function of `Z` and `N := ln T`
  independent turns the problem into a scalar additive-noise channel:
  `I(U;Z ∣ b,g) = h(X+N) − h(N)`. Then `h(N) = γ + 1` (an explicit integral),
  `E|N| ≤ 1 + e⁻¹ ≤ 2`, `E|X| ≤ C + 2`, and the max-entropy bound (T4) gives
  `≤ C + ln 8 − γ`. This is the only place `(T4)` — and hence differential
  entropy — is used here.
* **Diagonal `b = g`.** The golden formula against the
  reference `Exp(mean p)`, using
  `D(Exp(mean s) ‖ Exp(mean p)) = ln(p/s) + s/p − 1`. Gives `p·I ≤ 1 − p`.
* **Assembly.** The mixture identity
  `∑_b p_{gb} C_{gb} = I(B;Z ∣ C₀=g)` collapses the off-diagonal sum, and
  cluster-level calibration gives `I(B;Z ∣ C₀) = S`, `P(B ≠ C₀) = d`.

## Mathlib support

`ProbabilityTheory.expMeasure` and `InformationTheory.klDiv` cover the diagonal
case. The off-diagonal case additionally needs `h(N) = γ + 1` for `N = ln T`,
`T ~ Exp(1)` — obtained from the derivative of the Gamma integral at one — and
`stoch_to_det.Toolkit.diffEntropy_le_of_abs_le`.
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
  simpa [smul_eq_mul, ← Complex.ofReal_neg, Complex.exp_ofReal_re] using hconv.re

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
    convert integrableOn_log_mul_exp_neg_Ioi.ofReal using 1
    all_goals norm_num
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

theorem integrableOn_abs_log_mul_exp_neg_Ioi_1771 :
    IntegrableOn (fun t : ℝ => |Real.log t| * Real.exp (-t)) (Set.Ioi 0) := by
  have hnorm := integrableOn_log_mul_exp_neg_Ioi.norm
  refine hnorm.congr (ae_of_all _ fun t => ?_)
  change |Real.log t * Real.exp (-t)| = |Real.log t| * Real.exp (-t)
  rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]

end stoch_to_det
