-- Adapted from the author's earlier repository (StochasticToDeterministicLatents);
-- modified: module paths renamed; declarations unused by the main theorems removed.
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.StrongLaw
import NaturalLatents.General.Definitions

/-!
# Arrival sums and Laplace transforms of the race

Analytic core of the exponential race. Writing `T_n` for the arrival times of a rate-one
Poisson process, the module studies `Vtail a t = t^a ∑ (t + T_n)^(-a)` and the mean of
`log (1 + Vtail a t)`: measurability and integrability of the arrival sums, the Laplace
transform of the shifted arrival measure through a renewal argument, and the identification of
the unit-time price `jET a` with the Gamma form `j a` once the unit-arrival Laplace
transform and log-integrability are available (`race_gamma_price`).

Every statement is a real-analysis statement about the explicit probability space
`ℕ → ℝ` with product exponential increments.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
The upstream definitions and lemmas used here come from that project, including
its open pull request #6 (`jezgillen`, head `7b41957d`) at the pinned revision.
The rest is adapted from unpublished working material with public names and
module boundaries; that material supplies attribution only, not verification evidence.
-/

namespace StochasticToDeterministicLatents.General

noncomputable section

open scoped BigOperators
open MeasureTheory ProbabilityTheory

variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

lemma race_scalar_exp_log_integrable_mean :
    MeasureTheory.Integrable Real.log (ProbabilityTheory.expMeasure 1) ∧
      (∫ t, Real.log t ∂ProbabilityTheory.expMeasure 1) =
        -Real.eulerMascheroniConstant := by
  let ν : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let f : ℝ → ENNReal := stoch_to_det.SharedRace.unitExpDensity
  have hf : Measurable f := by
    change Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-x)))
    fun_prop
  have hflt : ∀ᵐ t ∂ν, f t < ⊤ := by
    filter_upwards [] with t
    exact ENNReal.ofReal_lt_top
  have hweight : Integrable (fun t : ℝ => Real.exp (-t) * Real.log t) ν := by
    have h := stoch_to_det.integrableOn_abs_log_mul_exp_neg_Ioi_1771
    apply h.mono' (by fun_prop : Measurable
      (fun t : ℝ => Real.exp (-t) * Real.log t)).aestronglyMeasurable
    filter_upwards [] with t
    simp [Real.norm_eq_abs, mul_comm]
  have hconv : (fun t : ℝ => (f t).toReal • Real.log t) =
      (fun t : ℝ => Real.exp (-t) * Real.log t) := by
    funext t
    simp [f, stoch_to_det.SharedRace.unitExpDensity,
      ENNReal.toReal_ofReal, Real.exp_nonneg]
  have hmeasure : ProbabilityTheory.expMeasure 1 = ν.withDensity f := by
    exact stoch_to_det.SharedRace.expMeasure_one_eq_restrict_withDensity
  constructor
  · rw [hmeasure]
    apply (integrable_withDensity_iff_integrable_smul' hf hflt).2
    rwa [hconv]
  · rw [hmeasure, integral_withDensity_eq_integral_toReal_smul hf hflt,
      hconv]
    simpa [ν, mul_comm] using stoch_to_det.integral_log_mul_exp_neg_Ioi

lemma race_scalar_exp_ae_pos :
    ∀ᵐ t ∂ProbabilityTheory.expMeasure 1, 0 < t := by
  have h := measure_eq_zero_iff_ae_notMem.mp
    stoch_to_det.expMeasure_one_Iic_zero
  simpa only [Set.mem_Iic, not_le] using h

/-- The stable Laplace transform of a positive random variable determines its logarithmic mean. Only
`0 < alpha` is needed; the race uses `0 < alpha < 1`. -/
lemma race_scalar_log_ratio_law_of_stable_laplace
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (R : Ω → ℝ) (hR : Measurable R)
    (hRpos : ∀ᵐ ω ∂μ, 0 < R ω)
    (alpha c : ℝ) (halpha : 0 < alpha) (hc : 0 < c)
    (hLaplace : ∀ v : ℝ, 0 < v →
      (∫ ω, Real.exp (-(v * R ω)) ∂μ) =
        Real.exp (-(c * v ^ alpha))) :
    let ν : Measure ℝ := expMeasure 1
    let H : Ω × ℝ → ℝ := fun z => Real.log z.2 - Real.log (R z.1)
    let K : ℝ → ℝ := fun t => (Real.log t - Real.log c) / alpha
    (μ.prod ν).map H = ν.map K := by
  let ν : Measure ℝ := expMeasure 1
  let : IsProbabilityMeasure ν := isProbabilityMeasure_expMeasure zero_lt_one
  let H : Ω × ℝ → ℝ := fun z => Real.log z.2 - Real.log (R z.1)
  let K : ℝ → ℝ := fun t => (Real.log t - Real.log c) / alpha
  have hH : Measurable H := by
    dsimp [H]
    exact (Real.measurable_log.comp measurable_snd).sub
      (Real.measurable_log.comp (hR.comp measurable_fst))
  have hK : Measurable K := by dsimp [K]; fun_prop
  have hνpos : ∀ᵐ t ∂ν, 0 < t := race_scalar_exp_ae_pos
  have hLapInt (v : ℝ) (hv : 0 < v) :
      Integrable (fun ω => Real.exp (-(v * R ω))) μ := by
    apply Integrable.of_bound (by fun_prop : Measurable
      (fun ω => Real.exp (-(v * R ω)))).aestronglyMeasurable 1
    filter_upwards [hRpos] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hSurvH (x : ℝ) :
      ((μ.prod ν).map H) (Set.Ioi x) =
        ENNReal.ofReal (Real.exp (-(c * Real.exp (alpha * x)))) := by
    rw [Measure.map_apply hH measurableSet_Ioi,
      Measure.prod_apply (hH measurableSet_Ioi)]
    change (∫⁻ ω, ν {t | x < Real.log t - Real.log (R ω)} ∂μ) = _
    have hsection (ω : Ω) (hω : 0 < R ω) :
        ν {t | x < Real.log t - Real.log (R ω)} =
          ν (Set.Ioi (Real.exp x * R ω)) := by
      apply measure_congr
      filter_upwards [hνpos] with t ht
      apply propext
      change (x < Real.log t - Real.log (R ω)) ↔ (Real.exp x * R ω < t)
      rw [lt_sub_iff_add_lt, Real.lt_log_iff_exp_lt ht,
        Real.exp_add, Real.exp_log hω]
    calc
      (∫⁻ ω, ν {t | x < Real.log t - Real.log (R ω)} ∂μ) =
          ∫⁻ ω, ENNReal.ofReal (Real.exp (-(Real.exp x * R ω))) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hRpos] with ω hω
        rw [hsection ω hω]
        exact stoch_to_det.expMeasure_one_Ioi _ (by positivity)
      _ = ENNReal.ofReal (Real.exp (-(c * (Real.exp x) ^ alpha))) := by
        rw [← ofReal_integral_eq_lintegral_ofReal (hLapInt _ (Real.exp_pos x))
          (ae_of_all _ fun ω => (Real.exp_pos _).le),
          hLaplace _ (Real.exp_pos x)]
      _ = _ := by rw [← Real.exp_mul, mul_comm x alpha]
  have hSurvK (x : ℝ) :
      (ν.map K) (Set.Ioi x) =
        ENNReal.ofReal (Real.exp (-(c * Real.exp (alpha * x)))) := by
    rw [Measure.map_apply hK measurableSet_Ioi]
    have hsection : ν {t | x < (Real.log t - Real.log c) / alpha} =
        ν (Set.Ioi (c * Real.exp (alpha * x))) := by
      apply measure_congr
      filter_upwards [hνpos] with t ht
      apply propext
      change (x < (Real.log t - Real.log c) / alpha) ↔ (c * Real.exp (alpha * x) < t)
      rw [lt_div_iff₀ halpha, lt_sub_iff_add_lt,
        Real.lt_log_iff_exp_lt ht, Real.exp_add, Real.exp_log hc]
      simp only [mul_comm]
    change ν {t | x < (Real.log t - Real.log c) / alpha} = _
    rw [hsection]
    exact stoch_to_det.expMeasure_one_Ioi _ (by positivity)
  let : IsProbabilityMeasure ((μ.prod ν).map H) :=
    Measure.isProbabilityMeasure_map hH.aemeasurable
  let : IsProbabilityMeasure (ν.map K) :=
    Measure.isProbabilityMeasure_map hK.aemeasurable
  have hLaw : (μ.prod ν).map H = ν.map K := by
    apply Measure.ext_of_Iic
    intro x
    have hcompl : Set.Iic x = (Set.Ioi x)ᶜ := by ext y; simp
    rw [hcompl, measure_compl measurableSet_Ioi (measure_ne_top _ _),
      measure_compl measurableSet_Ioi (measure_ne_top _ _),
      measure_univ, measure_univ, hSurvH, hSurvK]
  exact hLaw

lemma race_scalar_log_integrable_of_stable_laplace
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (R : Ω → ℝ) (hR : Measurable R)
    (hRpos : ∀ᵐ ω ∂μ, 0 < R ω)
    (alpha c : ℝ) (halpha : 0 < alpha) (hc : 0 < c)
    (hLaplace : ∀ v : ℝ, 0 < v →
      (∫ ω, Real.exp (-(v * R ω)) ∂μ) =
        Real.exp (-(c * v ^ alpha))) : Integrable (fun ω => Real.log (R ω)) μ := by
  let ν : Measure ℝ := expMeasure 1
  let : IsProbabilityMeasure ν := isProbabilityMeasure_expMeasure zero_lt_one
  let H : Ω × ℝ → ℝ := fun z => Real.log z.2 - Real.log (R z.1)
  let K : ℝ → ℝ := fun t => (Real.log t - Real.log c) / alpha
  have hH : Measurable H := by
    dsimp [H]
    exact (Real.measurable_log.comp measurable_snd).sub
      (Real.measurable_log.comp (hR.comp measurable_fst))
  have hK : Measurable K := by dsimp [K]; fun_prop
  have hνlog : Integrable Real.log ν := race_scalar_exp_log_integrable_mean.1
  have hKInt : Integrable K ν := (hνlog.sub (integrable_const _)).div_const alpha
  have hLaw := race_scalar_log_ratio_law_of_stable_laplace
    μ R hR hRpos alpha c halpha hc hLaplace
  dsimp only at hLaw
  have hIdK : Integrable (fun u : ℝ => u) (ν.map K) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hK.aemeasurable).mpr hKInt
  have hIdH : Integrable (fun u : ℝ => u) ((μ.prod ν).map H) := by
    rw [hLaw]
    exact hIdK
  have hHInt : Integrable H (μ.prod ν) := by
    simpa only [Function.comp_def] using hIdH.comp_measurable hH
  have hprod : Integrable (fun z : Ω × ℝ => Real.log (R z.1)) (μ.prod ν) := by
    apply ((hνlog.comp_snd μ).sub hHInt).congr
    filter_upwards [] with z
    change Real.log z.2 - (Real.log z.2 - Real.log (R z.1)) = Real.log (R z.1)
    ring
  exact (measurePreserving_fst.integrable_comp
    (Real.measurable_log.comp hR).aestronglyMeasurable).mp hprod

lemma race_scalar_log_mean_of_stable_laplace
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (R : Ω → ℝ) (hR : Measurable R)
    (hRpos : ∀ᵐ ω ∂μ, 0 < R ω)
    (hlogR : MeasureTheory.Integrable (fun ω => Real.log (R ω)) μ)
    (alpha c : ℝ) (halpha : 0 < alpha) (hc : 0 < c)
    (hLaplace : ∀ v : ℝ, 0 < v →
      (∫ ω, Real.exp (-(v * R ω)) ∂μ) =
        Real.exp (-(c * v ^ alpha))) :
    (∫ ω, Real.log (R ω) ∂μ) =
      Real.log c / alpha + (1 / alpha - 1) * Real.eulerMascheroniConstant := by
  let ν : Measure ℝ := expMeasure 1
  let : IsProbabilityMeasure ν := isProbabilityMeasure_expMeasure zero_lt_one
  let H : Ω × ℝ → ℝ := fun z => Real.log z.2 - Real.log (R z.1)
  let K : ℝ → ℝ := fun t => (Real.log t - Real.log c) / alpha
  have hH : Measurable H := by
    dsimp [H]
    exact (Real.measurable_log.comp measurable_snd).sub
      (Real.measurable_log.comp (hR.comp measurable_fst))
  have hK : Measurable K := by dsimp [K]; fun_prop
  have hνlog : Integrable Real.log ν := race_scalar_exp_log_integrable_mean.1
  have hνmean : (∫ t, Real.log t ∂ν) = -Real.eulerMascheroniConstant :=
    race_scalar_exp_log_integrable_mean.2
  have hLaw := race_scalar_log_ratio_law_of_stable_laplace
    μ R hR hRpos alpha c halpha hc hLaplace
  dsimp only at hLaw
  have hHInt : Integrable H (μ.prod ν) :=
    (hνlog.comp_snd μ).sub (hlogR.comp_fst ν)
  have hHmean : (∫ z, H z ∂μ.prod ν) =
      -Real.eulerMascheroniConstant - ∫ ω, Real.log (R ω) ∂μ := by
    dsimp only [H]
    rw [integral_sub (hνlog.comp_snd μ) (hlogR.comp_fst ν),
      integral_fun_snd, integral_fun_fst (f := fun ω => Real.log (R ω))]
    simp [hνmean]
  have hKmean : (∫ t, K t ∂ν) =
      (-Real.eulerMascheroniConstant - Real.log c) / alpha := by
    dsimp only [K]
    rw [integral_div, integral_sub hνlog (integrable_const _)]
    simp [hνmean]
  have hmeans : (∫ z, H z ∂μ.prod ν) = ∫ t, K t ∂ν := by
    calc
      _ = ∫ u : ℝ, u ∂(μ.prod ν).map H :=
        (integral_map hH.aemeasurable measurable_id.aestronglyMeasurable).symm
      _ = ∫ u : ℝ, u ∂ν.map K := by rw [hLaw]
      _ = _ := integral_map hK.aemeasurable measurable_id.aestronglyMeasurable
  rw [hHmean, hKmean] at hmeans
  field_simp [ne_of_gt halpha] at hmeans ⊢
  nlinarith

lemma race_arrival_probability : IsProbabilityMeasure arrivalLaw := by
  let : IsProbabilityMeasure expOne :=
    isProbabilityMeasure_expMeasure zero_lt_one
  change IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => expOne))
  infer_instance

lemma race_arrival_ae_nonneg :
    ∀ᵐ ω ∂arrivalLaw, ∀ n : ℕ, 0 ≤ ω n := by
  let : IsProbabilityMeasure expOne :=
    isProbabilityMeasure_expMeasure zero_lt_one
  apply ae_all_iff.2
  intro n
  have heval : arrivalLaw.map (fun ω : ℕ → ℝ => ω n) = expOne := by
    change (Measure.infinitePi (fun _ : ℕ => expOne)).map
      (fun ω : ℕ → ℝ => ω n) = expOne
    exact Measure.infinitePi_map_eval (fun _ : ℕ => expOne) n
  have hpos : ∀ᵐ t ∂arrivalLaw.map (fun ω : ℕ → ℝ => ω n), 0 < t := by
    rw [heval]
    exact race_scalar_exp_ae_pos
  exact (ae_of_ae_map (measurable_pi_apply n).aemeasurable hpos).mono
    (fun _ ht => ht.le)

lemma race_Vtail_nonneg_of_nonneg (a t : ℝ) (ht : 0 ≤ t)
    (ω : ℕ → ℝ) (hω : ∀ n, 0 ≤ ω n) : 0 ≤ Vtail a t ω := by
  unfold Vtail
  apply mul_nonneg (Real.rpow_nonneg ht a)
  apply tsum_nonneg
  intro n
  apply Real.rpow_nonneg
  apply add_nonneg ht
  unfold arrival
  exact Finset.sum_nonneg (fun k _ => hω k)

/-- The logarithmic mean of the unit-prior appended mass is a*gamma+jET.
The only analytic hypothesis needed here is log integrability of that mass.
The max extension is inactive on the proved a.e. nonnegative-increment event. -/
lemma race_unit_log_mean_eq_jET (a : ℝ)
    (hInt : Integrable (fun z : ℝ × (ℕ → ℝ) =>
      Real.log (z.1 ^ (-a) * (1 + max 0 (Vtail a z.1 z.2))))
      (expOne.prod arrivalLaw)) :
    (∫ z : ℝ × (ℕ → ℝ),
      Real.log (z.1 ^ (-a) * (1 + max 0 (Vtail a z.1 z.2)))
      ∂expOne.prod arrivalLaw) =
        a * Real.eulerMascheroniConstant + jET a := by
  let : IsProbabilityMeasure expOne :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let : IsProbabilityMeasure arrivalLaw := race_arrival_probability
  let R : ℝ × (ℕ → ℝ) → ℝ :=
    fun z => z.1 ^ (-a) * (1 + max 0 (Vtail a z.1 z.2))
  let gain : ℝ × (ℕ → ℝ) → ℝ :=
    fun z => Real.log (1 + Vtail a z.1 z.2)
  have hlogR : Integrable (fun z => Real.log (R z))
      (expOne.prod arrivalLaw) := hInt
  have hlogT : Integrable Real.log expOne :=
    race_scalar_exp_log_integrable_mean.1
  have hlogTmean : (∫ t, Real.log t ∂expOne) =
      -Real.eulerMascheroniConstant := race_scalar_exp_log_integrable_mean.2
  have htpos : ∀ᵐ z : ℝ × (ℕ → ℝ) ∂expOne.prod arrivalLaw, 0 < z.1 :=
    Measure.quasiMeasurePreserving_fst.ae race_scalar_exp_ae_pos
  have hωnonneg : ∀ᵐ z : ℝ × (ℕ → ℝ) ∂expOne.prod arrivalLaw,
      ∀ n : ℕ, 0 ≤ z.2 n :=
    Measure.quasiMeasurePreserving_snd.ae race_arrival_ae_nonneg
  have hgainEq : gain =ᵐ[expOne.prod arrivalLaw]
      (fun z => Real.log (R z) + a * Real.log z.1) := by
    filter_upwards [htpos, hωnonneg] with z hzt hzω
    have hV : 0 ≤ Vtail a z.1 z.2 :=
      race_Vtail_nonneg_of_nonneg a z.1 hzt.le z.2 hzω
    have hgainpos : 0 < 1 + Vtail a z.1 z.2 := by linarith
    dsimp only [gain, R]
    rw [max_eq_right hV,
      Real.log_mul (Real.rpow_pos_of_pos hzt (-a)).ne' hgainpos.ne',
      Real.log_rpow hzt (-a)]
    ring
  have hgainInt : Integrable gain (expOne.prod arrivalLaw) :=
    (hlogR.add ((hlogT.comp_fst arrivalLaw).const_mul a)).congr hgainEq.symm
  have hFubini : jET a = ∫ z, gain z ∂expOne.prod arrivalLaw := by
    simpa only [jET, m, gain] using
      (integral_integral (f := fun t ω => Real.log (1 + Vtail a t ω)) hgainInt)
  have hmeans := integral_congr_ae hgainEq
  rw [integral_add hlogR ((hlogT.comp_fst arrivalLaw).const_mul a),
    integral_const_mul, integral_fun_fst] at hmeans
  simp only [probReal_univ, one_smul, hlogTmean] at hmeans
  rw [← hFubini] at hmeans
  change (∫ z, Real.log (R z) ∂expOne.prod arrivalLaw) = _
  linarith

/-- Explicit unit-arrival stable Laplace and log-integrability inputs imply `jET a = j a`. -/
lemma race_gamma_price_of_unit_laplace (a : ℝ) (ha : 1 < a) :
    let R : ℝ × (ℕ → ℝ) → ℝ :=
      fun z => z.1 ^ (-a) * (1 + max 0 (Vtail a z.1 z.2))
    Measurable R →
    Integrable (fun z => Real.log (R z)) (expOne.prod arrivalLaw) →
    (∀ v : ℝ, 0 < v →
      (∫ z, Real.exp (-(v * R z)) ∂expOne.prod arrivalLaw) =
        Real.exp (-(Real.Gamma (1 - 1/a) * v ^ (1/a)))) →
    jET a = j a := by
  let R : ℝ × (ℕ → ℝ) → ℝ :=
    fun z => z.1 ^ (-a) * (1 + max 0 (Vtail a z.1 z.2))
  change Measurable R →
    Integrable (fun z => Real.log (R z)) (expOne.prod arrivalLaw) →
    (∀ v : ℝ, 0 < v →
      (∫ z, Real.exp (-(v * R z)) ∂expOne.prod arrivalLaw) =
        Real.exp (-(Real.Gamma (1 - 1/a) * v ^ (1/a)))) →
    jET a = j a
  intro hMeas hInt hLap
  let : IsProbabilityMeasure expOne :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let : IsProbabilityMeasure arrivalLaw := race_arrival_probability
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hα : 0 < 1/a := one_div_pos.mpr ha0
  have harg : 0 < 1 - 1/a := by
    have hlt : 1/a < 1 := (div_lt_one ha0).2 ha
    linarith
  have hG : 0 < Real.Gamma (1 - 1/a) := Real.Gamma_pos_of_pos harg
  have htpos : ∀ᵐ z : ℝ × (ℕ → ℝ) ∂expOne.prod arrivalLaw, 0 < z.1 :=
    Measure.quasiMeasurePreserving_fst.ae race_scalar_exp_ae_pos
  have hRpos : ∀ᵐ z ∂expOne.prod arrivalLaw, 0 < R z := by
    filter_upwards [htpos] with z hzt
    dsimp only [R]
    apply mul_pos (Real.rpow_pos_of_pos hzt (-a))
    linarith [le_max_left (0 : ℝ) (Vtail a z.1 z.2)]
  have hStable := race_scalar_log_mean_of_stable_laplace
    (expOne.prod arrivalLaw) R hMeas hRpos hInt
    (1/a) (Real.Gamma (1 - 1/a)) hα hG hLap
  have hStableMean : (∫ z, Real.log (R z) ∂expOne.prod arrivalLaw) =
      a * Real.log (Real.Gamma (1 - 1/a)) +
        (a - 1) * Real.eulerMascheroniConstant := by
    rw [hStable]
    field_simp [ha0.ne']
  have hET := race_unit_log_mean_eq_jET a hInt
  change (∫ z, Real.log (R z) ∂expOne.prod arrivalLaw) =
      a * Real.eulerMascheroniConstant + jET a at hET
  unfold j
  linarith

lemma race_measurable_real_tsum {Z ι : Type*} [MeasurableSpace Z]
    [Countable ι] (f : ι → Z → ℝ) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun z => ∑' i, f i z) := by
  exact Measurable.tsum hf

lemma race_measurable_arrival (n : ℕ) :
    Measurable (fun ω : ℕ → ℝ => arrival ω n) := by
  unfold arrival
  exact (Finset.range n).measurable_fun_sum
    (fun k _ => measurable_pi_apply k)

lemma race_measurable_Vtail (a : ℝ) :
    Measurable (fun z : ℝ × (ℕ → ℝ) => Vtail a z.1 z.2) := by
  unfold Vtail
  apply Measurable.mul
  · exact measurable_fst.pow measurable_const
  · apply race_measurable_real_tsum
    intro n
    exact (measurable_fst.add
      ((race_measurable_arrival (n+1)).comp measurable_snd)).pow
        measurable_const

lemma race_measurable_unit_mass (a : ℝ) :
    Measurable (fun z : ℝ × (ℕ → ℝ) =>
      z.1 ^ (-a) * (1 + max 0 (Vtail a z.1 z.2))) := by
  exact (measurable_fst.pow measurable_const).mul
    (measurable_const.add (measurable_const.max (race_measurable_Vtail a)))

lemma race_exp_rpow_moment (p : ℝ) (hp : -1 < p) :
    Integrable (fun y : ℝ => y ^ p) (expMeasure 1) ∧
      (∫ y : ℝ, y ^ p ∂expMeasure 1) = Real.Gamma (1 + p) := by
  let ν : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let f : ℝ → ENNReal := stoch_to_det.SharedRace.unitExpDensity
  have hf : Measurable f := by
    change Measurable (fun y : ℝ => ENNReal.ofReal (Real.exp (-y)))
    fun_prop
  have hflt : ∀ᵐ y ∂ν, f y < ⊤ := by
    filter_upwards [] with y
    exact ENNReal.ofReal_lt_top
  have hs : 0 < 1 + p := by linarith
  have hweight : Integrable (fun y : ℝ => Real.exp (-y) * y ^ p) ν := by
    simpa [ν, IntegrableOn] using (Real.GammaIntegral_convergent hs)
  have hconv : (fun y : ℝ => (f y).toReal • y ^ p) =
      (fun y : ℝ => Real.exp (-y) * y ^ p) := by
    funext y
    simp [f, stoch_to_det.SharedRace.unitExpDensity,
      ENNReal.toReal_ofReal, Real.exp_nonneg]
  have hmeasure : expMeasure 1 = ν.withDensity f := by
    exact stoch_to_det.SharedRace.expMeasure_one_eq_restrict_withDensity
  constructor
  · rw [hmeasure]
    apply (integrable_withDensity_iff_integrable_smul' hf hflt).2
    rwa [hconv]
  · rw [hmeasure, integral_withDensity_eq_integral_toReal_smul hf hflt, hconv]
    simpa [ν] using (Real.Gamma_eq_integral hs).symm

lemma race_rpow_tail_iff {a v t y : ℝ}
    (ha : 0 < a) (hv : 0 < v) (ht : 0 < t) (hy : 0 < y) :
    t ≤ v ^ (1 / a) * y ^ (-(1 / a)) ↔ y ≤ v * t ^ (-a) := by
  have hleft : 0 < v ^ (1 / a) * y ^ (-(1 / a)) :=
    mul_pos (Real.rpow_pos_of_pos hv _) (Real.rpow_pos_of_pos hy _)
  have hright : 0 < v * t ^ (-a) :=
    mul_pos hv (Real.rpow_pos_of_pos ht _)
  have hlogleft : Real.log (v ^ (1 / a) * y ^ (-(1 / a))) =
      (Real.log v - Real.log y) / a := by
    rw [Real.log_mul (Real.rpow_pos_of_pos hv _).ne'
      (Real.rpow_pos_of_pos hy _).ne', Real.log_rpow hv, Real.log_rpow hy]
    ring
  have hlogright : Real.log (v * t ^ (-a)) = Real.log v - a * Real.log t := by
    rw [Real.log_mul hv.ne' (Real.rpow_pos_of_pos ht _).ne', Real.log_rpow ht]
    ring
  rw [← Real.log_le_log_iff ht hleft, ← Real.log_le_log_iff hy hright,
    hlogleft, hlogright, le_div_iff₀ ha]
  constructor <;> intro h <;> linarith

/-- The Poisson Laplace exponent, evaluated without a Poisson theorem:
    layer cake applied to v^(1/a) E^(-1/a), E ~ Exp(1). -/
lemma race_integral_laplace_exponent (a v : ℝ) (ha : 1 < a) (hv : 0 < v) :
    (∫ t : ℝ in Set.Ioi 0, 1 - Real.exp (-(v * t ^ (-a)))) =
      Real.Gamma (1 - 1 / a) * v ^ (1 / a) := by
  let : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hrec : 1 / a < 1 := (div_lt_one ha0).2 ha
  have hp : -1 < -(1 / a) := by linarith
  obtain ⟨hpow, hpowmean⟩ := race_exp_rpow_moment (-(1 / a)) hp
  let f : ℝ → ℝ := fun y => v ^ (1 / a) * y ^ (-(1 / a))
  have hfi : Integrable f (expMeasure 1) := hpow.const_mul _
  have hypos : ∀ᵐ y ∂expMeasure (1 : ℝ), 0 < y := by
    have h := measure_eq_zero_iff_ae_notMem.mp stoch_to_det.expMeasure_one_Iic_zero
    simpa only [Set.mem_Iic, not_le] using h
  have hfnn : 0 ≤ᵐ[expMeasure (1 : ℝ)] f := by
    filter_upwards [hypos] with y hy
    exact (mul_pos (Real.rpow_pos_of_pos hv _) (Real.rpow_pos_of_pos hy _)).le
  have htail (t : ℝ) (ht : 0 < t) :
      (expMeasure (1 : ℝ)).real {y : ℝ | t ≤ f y} =
        1 - Real.exp (-(v * t ^ (-a))) := by
    have hset : expMeasure (1 : ℝ) {y : ℝ | t ≤ f y} =
        expMeasure (1 : ℝ) (Set.Iic (v * t ^ (-a))) := by
      apply measure_congr
      filter_upwards [hypos] with y hy
      apply propext
      exact race_rpow_tail_iff ha0 hv ht hy
    have hsetreal : (expMeasure (1 : ℝ)).real {y : ℝ | t ≤ f y} =
        (expMeasure (1 : ℝ)).real (Set.Iic (v * t ^ (-a))) :=
      congrArg ENNReal.toReal hset
    rw [hsetreal, ← cdf_eq_real,
      cdf_expMeasure_eq zero_lt_one, if_pos
        (mul_pos hv (Real.rpow_pos_of_pos ht _)).le]
    simp
  calc
    (∫ t : ℝ in Set.Ioi 0, 1 - Real.exp (-(v * t ^ (-a)))) =
        ∫ t : ℝ in Set.Ioi 0, (expMeasure (1 : ℝ)).real {y : ℝ | t ≤ f y} := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact (htail t ht).symm
    _ = ∫ y : ℝ, f y ∂expMeasure 1 :=
      (hfi.integral_eq_integral_meas_le hfnn).symm
    _ = Real.Gamma (1 - 1 / a) * v ^ (1 / a) := by
      dsimp [f]
      rw [integral_const_mul, hpowmean]
      simp only [sub_eq_add_neg, mul_comm]

/-- Exact product-factorization step for renewal, independent of any tail
    shift or arrival-process theorem. -/
lemma race_product_laplace_factorization
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure ℝ) (μ : Measure Ω) [SigmaFinite ν] [SigmaFinite μ]
    (v : ℝ) (B : ℝ → ℝ) (C : ℝ → Ω → ℝ)
    (hInt : Integrable (fun z : ℝ × Ω =>
      Real.exp (-(v * (B z.1 + C z.1 z.2)))) (ν.prod μ)) :
    (∫ z : ℝ × Ω, Real.exp (-(v * (B z.1 + C z.1 z.2))) ∂ν.prod μ) =
      ∫ t, Real.exp (-(v * B t)) *
        (∫ ω, Real.exp (-(v * C t ω)) ∂μ) ∂ν := by
  rw [integral_prod _ hInt]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [← Real.exp_add]
  congr 1
  ring

/-- Shifting one coordinate preserves the iid exponential product law. -/
lemma race_shift_arrival_law :
    arrivalLaw.map (fun ω : ℕ → ℝ => fun n : ℕ => ω (n + 1)) = arrivalLaw := by
  let : IsProbabilityMeasure expOne := isProbabilityMeasure_expMeasure zero_lt_one
  unfold arrivalLaw
  exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => expOne)
    (f := fun n : ℕ => n + 1) (fun _ _ h => Nat.add_right_cancel h)

/-- The deterministic head/tail decomposition of partial arrival times. -/
lemma race_arrival_head (ω : ℕ → ℝ) (n : ℕ) :
    arrival ω (n + 1) = ω 0 + arrival (fun k => ω (k + 1)) n := by
  simp only [arrival, Finset.sum_range_succ', add_comm]

/-- The deterministic renewal decomposition of the convergent arrival mass. -/
lemma race_arrival_mass_head
    (a t : ℝ) (ω : ℕ → ℝ)
    (hs : Summable (fun n : ℕ => (t + arrival ω (n + 1)) ^ (-a))) :
    (∑' n : ℕ, (t + arrival ω (n + 1)) ^ (-a)) =
      (t + ω 0) ^ (-a) +
        ∑' n : ℕ, ((t + ω 0) + arrival (fun k => ω (k + 1)) (n + 1)) ^ (-a) := by
  rw [hs.tsum_eq_zero_add]
  congr 1
  · simp [arrival]
  · apply tsum_congr
    intro n
    rw [race_arrival_head ω (n + 1)]
    congr 1
    ring

lemma race_arrival_ratio_tendsto :
    ∀ᵐ ω ∂arrivalLaw,
      Filter.Tendsto (fun n : ℕ => arrival ω n / (n : ℝ)) Filter.atTop (nhds 1) := by
  let : IsProbabilityMeasure expOne := isProbabilityMeasure_expMeasure zero_lt_one
  let X : ℕ → (ℕ → ℝ) → ℝ := fun n ω => ω n
  have hexp : Integrable (fun y : ℝ => y) expOne := by
    have h := (race_exp_rpow_moment 1 (by norm_num)).1
    simpa [expOne] using h
  have hmean : (∫ y : ℝ, y ∂expOne) = 1 := by
    have h := (race_exp_rpow_moment 1 (by norm_num)).2
    simpa [expOne, Real.Gamma_add_one (by norm_num : (1 : ℝ) ≠ 0)] using h
  have hmap (n : ℕ) : arrivalLaw.map (X n) = expOne := by
    change (Measure.infinitePi (fun _ : ℕ => expOne)).map (fun ω => ω n) = expOne
    exact Measure.infinitePi_map_eval (fun _ : ℕ => expOne) n
  have hid (n : ℕ) : IdentDistrib (X n) (fun y : ℝ => y) arrivalLaw expOne := by
    refine ⟨(by fun_prop), (by fun_prop), ?_⟩
    simpa using hmap n
  have hint : Integrable (X 0) arrivalLaw := (hid 0).integrable_iff.2 hexp
  have hident (n : ℕ) : IdentDistrib (X n) (X 0) arrivalLaw arrivalLaw :=
    (hid n).trans (hid 0).symm
  have hi : iIndepFun X arrivalLaw := by
    change iIndepFun X (Measure.infinitePi (fun _ : ℕ => expOne))
    exact iIndepFun_infinitePi (X := fun _ : ℕ => fun y : ℝ => y) (by fun_prop)
  have hindep : Pairwise (fun i j => IndepFun (X i) (X j) arrivalLaw) := by
    intro i j hij
    exact hi.indepFun hij
  have hmeanX : (∫ ω, X 0 ω ∂arrivalLaw) = 1 := (hid 0).integral_eq.trans hmean
  have h := ProbabilityTheory.strong_law_ae_real X hint hindep hident
  simpa [arrival, X, hmeanX] using h

/-- Deterministic comparison with a p-series. Positivity of every increment
    is unnecessary here: the strong-law lower bound handles all sufficiently
    late arrivals, and the finitely many earlier real powers are finite. -/
lemma race_summable_of_arrival_ratio
    (a : ℝ) (ha : 1 < a) (ω : ℕ → ℝ)
    (hlim : Filter.Tendsto (fun n : ℕ => arrival ω n / (n : ℝ))
      Filter.atTop (nhds 1)) :
    ∀ t : ℝ, 0 ≤ t →
      Summable (fun n : ℕ => (t + arrival ω (n + 1)) ^ (-a)) := by
  intro t ht
  have hp : Summable (fun n : ℕ => (n : ℝ) ^ (-a)) :=
    Real.summable_nat_rpow.2 (by linarith)
  have hps : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-a)) :=
    (summable_nat_add_iff 1).2 hp
  have hmajor : Summable (fun n : ℕ =>
      (1 / 2 : ℝ) ^ (-a) * ((n + 1 : ℕ) : ℝ) ^ (-a)) := hps.mul_left _
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      (1 / 2 : ℝ) < arrival ω n / (n : ℝ) :=
    hlim.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  apply hmajor.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hnpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlow := (lt_div_iff₀ hnpos).1 (hN (n + 1) (by omega))
  have hbasepos : 0 < (1 / 2 : ℝ) * ((n + 1 : ℕ) : ℝ) := by positivity
  have hbasele : (1 / 2 : ℝ) * ((n + 1 : ℕ) : ℝ) ≤
      t + arrival ω (n + 1) := by linarith
  have hpos : 0 < t + arrival ω (n + 1) := hbasepos.trans_le hbasele
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_pos_of_pos hpos (-a)).le]
  have hpowle := Real.rpow_le_rpow_of_nonpos hbasepos hbasele
    (by linarith : -a ≤ 0)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) (Nat.cast_nonneg (n + 1))] at hpowle
  exact hpowle

lemma race_arrival_mass_ae_summable (a : ℝ) (ha : 1 < a) :
    ∀ᵐ ω ∂arrivalLaw, ∀ t : ℝ, 0 ≤ t →
      Summable (fun n : ℕ => (t + arrival ω (n + 1)) ^ (-a)) := by
  filter_upwards [race_arrival_ratio_tendsto] with ω hω
  exact race_summable_of_arrival_ratio a ha ω hω

lemma race_arrival_head_tail_independent :
    IndepFun (fun ω : ℕ → ℝ => ω 0)
      (fun ω : ℕ → ℝ => fun n : ℕ => ω (n + 1)) arrivalLaw := by
  let : IsProbabilityMeasure expOne := isProbabilityMeasure_expMeasure zero_lt_one
  let M : ℕ → MeasurableSpace (ℕ → ℝ) := fun n =>
    MeasurableSpace.comap (fun ω : ℕ → ℝ => ω n) inferInstance
  let S : Set ℕ := {0}
  let T : Set ℕ := {n | n ≠ 0}
  have hi : iIndepFun (fun n : ℕ => fun ω : ℕ → ℝ => ω n) arrivalLaw := by
    change iIndepFun _ (Measure.infinitePi (fun _ : ℕ => expOne))
    exact iIndepFun_infinitePi (X := fun _ : ℕ => fun y : ℝ => y) (by fun_prop)
  have hle (n : ℕ) : M n ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
    measurable_iff_comap_le.mp (measurable_pi_apply n)
  have hST : Disjoint S T := by
    apply Set.disjoint_left.2
    intro n hn ht
    have hn0 : n = 0 := by simpa [S] using hn
    exact ht hn0
  have hleft : (⨆ n ∈ S, M n) = M 0 := by simp [S]
  have hright : (⨆ n ∈ T, M n) =
      MeasurableSpace.comap (fun ω : ℕ → ℝ => fun n : ℕ => ω (n + 1))
        inferInstance := by
    rw [MeasurableSpace.comap_process_pi]
    change (⨆ n ∈ T, M n) = ⨆ n : ℕ, M (n + 1)
    apply le_antisymm
    · apply iSup_le
      intro n
      apply iSup_le
      intro hn
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
      subst n
      simpa only [Nat.succ_eq_add_one] using (le_iSup (fun n : ℕ => M (n + 1)) k)
    · apply iSup_le
      intro n
      exact le_iSup_of_le (n + 1) (le_iSup_of_le (by simp [T]) le_rfl)
  have h := indep_iSup_of_disjoint hle hi.iIndep hST
  rw [hleft, hright] at h
  exact h

lemma race_arrival_head_tail_law :
    arrivalLaw.map (fun ω : ℕ → ℝ => (ω 0, fun n : ℕ => ω (n + 1))) =
      expOne.prod arrivalLaw := by
  let : IsProbabilityMeasure arrivalLaw := race_arrival_probability
  let : IsProbabilityMeasure expOne := isProbabilityMeasure_expMeasure zero_lt_one
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map
    ((measurable_pi_apply 0).aemeasurable : AEMeasurable (fun ω : ℕ → ℝ => ω 0) arrivalLaw)
    ((by fun_prop : Measurable (fun ω : ℕ → ℝ => fun n : ℕ => ω (n + 1))).aemeasurable : AEMeasurable
      (fun ω : ℕ → ℝ => fun n : ℕ => ω (n + 1)) arrivalLaw)).1
        race_arrival_head_tail_independent
  rw [race_shift_arrival_law] at hmap
  have hfirst : arrivalLaw.map (fun ω : ℕ → ℝ => ω 0) = expOne := by
    change (Measure.infinitePi (fun _ : ℕ => expOne)).map (fun ω => ω 0) = expOne
    exact Measure.infinitePi_map_eval (fun _ : ℕ => expOne) 0
  simpa [hfirst] using hmap

lemma race_arrival_mass_measurable (a : ℝ) :
    Measurable (fun z : ℝ × (ℕ → ℝ) =>
      ∑' n : ℕ, (z.1 + arrival z.2 (n + 1)) ^ (-a)) := by
  apply Measurable.tsum
  intro n
  dsimp [arrival]
  fun_prop

/-- The actual exponential renewal identity of the arrival process.
    No Poisson interval theorem or Laplace-functional axiom is used. -/
lemma race_arrival_laplace_renewal (a v : ℝ) (ha : 1 < a) (hv : 0 < v) :
    let F : ℝ → ℝ := fun t =>
      ∫ ω, Real.exp (-(v *
        ∑' n : ℕ, (t + arrival ω (n + 1)) ^ (-a))) ∂arrivalLaw
    ∀ t : ℝ, 0 ≤ t → F t =
      ∫ s : ℝ in Set.Ioi 0,
        Real.exp (-s) * Real.exp (-(v * (t + s) ^ (-a))) * F (t + s) := by
  let : IsProbabilityMeasure arrivalLaw := race_arrival_probability
  let : IsProbabilityMeasure expOne := isProbabilityMeasure_expMeasure zero_lt_one
  let A : ℝ → (ℕ → ℝ) → ℝ := fun t ω =>
    ∑' n : ℕ, (t + arrival ω (n + 1)) ^ (-a)
  let F : ℝ → ℝ := fun t => ∫ ω, Real.exp (-(v * A t ω)) ∂arrivalLaw
  change ∀ t : ℝ, 0 ≤ t → F t = _
  intro t ht
  let K : ℝ × (ℕ → ℝ) → ℝ := fun z =>
    Real.exp (-(v * ((t + z.1) ^ (-a) + A (t + z.1) z.2)))
  have hA : Measurable (fun z : ℝ × (ℕ → ℝ) => A z.1 z.2) :=
    race_arrival_mass_measurable a
  have hK : Measurable K := by
    have hAc : Measurable (fun z : ℝ × (ℕ → ℝ) => A (t + z.1) z.2) :=
      hA.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
    dsimp [K]
    fun_prop
  have hAnonneg (u : ℝ) (hu : 0 ≤ u) (ω : ℕ → ℝ) (hω : ∀ n, 0 ≤ ω n) :
      0 ≤ A u ω := by
    apply tsum_nonneg
    intro n
    apply Real.rpow_nonneg
    apply add_nonneg hu
    unfold arrival
    exact Finset.sum_nonneg (fun k _ => hω k)
  have hexp : ∀ᵐ z ∂expOne.prod arrivalLaw, 0 < z.1 :=
    Measure.quasiMeasurePreserving_fst.ae race_scalar_exp_ae_pos
  have hω : ∀ᵐ z ∂expOne.prod arrivalLaw, ∀ n, 0 ≤ z.2 n :=
    Measure.quasiMeasurePreserving_snd.ae race_arrival_ae_nonneg
  have hKi : Integrable K (expOne.prod arrivalLaw) := by
    apply (integrable_const (1 : ℝ)).mono' hK.aestronglyMeasurable
    filter_upwards [hexp, hω] with z hz hzw
    have hu : 0 < t + z.1 := add_pos_of_nonneg_of_pos ht hz
    have hmass : 0 ≤ (t + z.1) ^ (-a) + A (t + z.1) z.2 :=
      add_nonneg (Real.rpow_nonneg hu.le _) (hAnonneg _ hu.le _ hzw)
    dsimp [K]
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hv.le hmass))
  have hdecomp : F t = ∫ z, K z ∂expOne.prod arrivalLaw := by
    have hfirst : F t =
        ∫ ω, K (ω 0, fun n : ℕ => ω (n + 1)) ∂arrivalLaw := by
      apply integral_congr_ae
      filter_upwards [race_arrival_mass_ae_summable a ha] with ω hsum
      dsimp [K, A]
      rw [race_arrival_mass_head a t ω (hsum t ht)]
    rw [hfirst, ← race_arrival_head_tail_law]
    exact (integral_map (by fun_prop) hK.aestronglyMeasurable).symm
  have hfactor : F t = ∫ s : ℝ,
      Real.exp (-(v * (t + s) ^ (-a))) * F (t + s) ∂expOne := by
    rw [hdecomp]
    exact race_product_laplace_factorization expOne arrivalLaw v
      (fun s => (t + s) ^ (-a)) (fun s ω => A (t + s) ω) hKi
  rw [hfactor]
  let ν : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let f : ℝ → ENNReal := stoch_to_det.SharedRace.unitExpDensity
  have hf : Measurable f := by
    change Measurable (fun s : ℝ => ENNReal.ofReal (Real.exp (-s)))
    fun_prop
  have hflt : ∀ᵐ s ∂ν, f s < ⊤ := by
    filter_upwards [] with s
    exact ENNReal.ofReal_lt_top
  have hmeasure : expOne = ν.withDensity f := by
    exact stoch_to_det.SharedRace.expMeasure_one_eq_restrict_withDensity
  rw [hmeasure, integral_withDensity_eq_integral_toReal_smul hf hflt]
  apply integral_congr_ae
  filter_upwards [] with s
  simp [f, stoch_to_det.SharedRace.unitExpDensity,
    ENNReal.toReal_ofReal, Real.exp_nonneg, mul_assoc, F, A]

lemma race_shifted_mass_tendsto_zero
    (a : ℝ) (ha : 0 < a) (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hsum : Summable (fun n : ℕ => (1 + u n) ^ (-a))) :
    Filter.Tendsto (fun t : ℝ => ∑' n : ℕ, (t + u n) ^ (-a))
      Filter.atTop (nhds 0) := by
  have hterm (n : ℕ) :
      Filter.Tendsto (fun t : ℝ => (t + u n) ^ (-a))
        Filter.atTop (nhds 0) := by
    apply (tendsto_rpow_neg_atTop ha).comp
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [Filter.eventually_ge_atTop (b - u n)] with t ht
    linarith
  have hbound : ∀ᶠ t : ℝ in Filter.atTop,
      ∀ n : ℕ, ‖(t + u n) ^ (-a)‖ ≤ (1 + u n) ^ (-a) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
    intro n
    have hone : 0 < 1 + u n := by linarith [hu n]
    have hbase : 0 ≤ t + u n := by linarith [hu n]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hbase (-a))]
    exact Real.rpow_le_rpow_of_nonpos hone (by linarith) (by linarith)
  simpa only [tsum_zero] using
    (tendsto_tsum_of_dominated_convergence
      (f := fun t : ℝ => fun n : ℕ => (t + u n) ^ (-a))
      (g := fun _ : ℕ => (0 : ℝ)) hsum hterm hbound)

lemma race_shifted_mass_laplace_tendsto_one
    (a : ℝ) (ha : 1 < a) (v : ℝ) (hv : 0 ≤ v) :
    Filter.Tendsto
      (fun t : ℝ => ∫ ω : ℕ → ℝ,
        Real.exp (-(v * ∑' n : ℕ, (t + arrival ω (n+1)) ^ (-a)))
          ∂arrivalLaw)
      Filter.atTop (nhds 1) := by
  let : IsProbabilityMeasure arrivalLaw := race_arrival_probability
  have hm (t : ℝ) : Measurable (fun ω : ℕ → ℝ =>
      Real.exp (-(v * ∑' n : ℕ, (t + arrival ω (n+1)) ^ (-a)))) := by
    apply Real.measurable_exp.comp
    apply Measurable.neg
    apply Measurable.mul measurable_const
    apply Measurable.tsum
    intro n
    exact (measurable_const.add (race_measurable_arrival (n+1))).pow
      measurable_const
  have hu (ω : ℕ → ℝ) (hω : ∀ n : ℕ, 0 ≤ ω n) (n : ℕ) :
      0 ≤ arrival ω (n+1) := by
    unfold arrival
    exact Finset.sum_nonneg (fun k _ => hω k)
  have hbound : ∀ᶠ t : ℝ in Filter.atTop,
      ∀ᵐ ω : ℕ → ℝ ∂arrivalLaw,
        ‖Real.exp (-(v * ∑' n : ℕ, (t + arrival ω (n+1)) ^ (-a)))‖ ≤ 1 := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    filter_upwards [race_arrival_ae_nonneg] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    apply neg_nonpos.mpr
    apply mul_nonneg hv
    exact tsum_nonneg (fun n =>
      Real.rpow_nonneg (add_nonneg ht (hu ω hω n)) (-a))
  have hlim : ∀ᵐ ω : ℕ → ℝ ∂arrivalLaw,
      Filter.Tendsto
        (fun t : ℝ =>
          Real.exp (-(v * ∑' n : ℕ, (t + arrival ω (n+1)) ^ (-a))))
        Filter.atTop (nhds 1) := by
    filter_upwards [race_arrival_ae_nonneg,
      race_arrival_mass_ae_summable a ha] with ω hω hsum
    have hmass := race_shifted_mass_tendsto_zero a
      (lt_trans zero_lt_one ha) (fun n => arrival ω (n+1))
      (hu ω hω) (hsum 1 (by norm_num))
    have hzero : Filter.Tendsto
        (fun t : ℝ => -(v * ∑' n : ℕ, (t + arrival ω (n+1)) ^ (-a)))
        Filter.atTop (nhds 0) := by
      simpa only [mul_zero, neg_zero] using
        (((tendsto_const_nhds (x := v)).mul hmass).neg)
    simpa only [Real.exp_zero, Function.comp_def] using
      (Real.continuous_exp.tendsto 0).comp hzero
  have hresult := tendsto_integral_filter_of_norm_le_const
    (μ := arrivalLaw) (l := Filter.atTop)
    (F := fun t : ℝ => fun ω : ℕ → ℝ =>
      Real.exp (-(v * ∑' n : ℕ, (t + arrival ω (n+1)) ^ (-a))))
    (f := fun _ : ℕ → ℝ => (1 : ℝ))
    (Filter.Eventually.of_forall (fun t => (hm t).aestronglyMeasurable))
    ⟨1, hbound⟩ hlim
  simpa using hresult

lemma race_hasDerivAt_tail_integral
    (f : ℝ → ℝ) (hint : IntegrableOn f (Set.Ioi 0))
    (hcont : ContinuousOn f (Set.Ioi 0)) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => ∫ u in Set.Ioi x, f u) (-f t) t := by
  have hinterval : IntervalIntegrable f volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).2
      (hint.mono_set Set.Ioc_subset_Ioi_self)
  have hmeas : StronglyMeasurableAtFilter f (nhds t) volume :=
    AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
      hint.aestronglyMeasurable (Ioi_mem_nhds ht)
  have hct : ContinuousAt f t := hcont.continuousAt (Ioi_mem_nhds ht)
  have hprimitive := intervalIntegral.integral_hasDerivAt_right hinterval hmeas hct
  have hder : HasDerivAt
      (fun x : ℝ => (∫ u in Set.Ioi 0, f u) - ∫ u in 0..x, f u) (-f t) t := by
    simpa only [zero_sub] using
      (hasDerivAt_const t (∫ u in Set.Ioi 0, f u)).fun_sub hprimitive
  apply hder.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with x hx
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hint hx.le
  linarith

/-- Solves the exponential renewal equation from its deterministic integral
    form and its boundary at infinity. q is the loss 1-p. The hypotheses
    concern ordinary functions on the real line, not any random process. -/
lemma race_renewal_unique
    (q F : ℝ → ℝ) (hq : ContinuousOn q (Set.Ioi 0))
    (hqInt : IntegrableOn q (Set.Ioi 0))
    (hkInt : IntegrableOn
      (fun u : ℝ => Real.exp (-u) * (1 - q u) * F u) (Set.Ioi 0))
    (hrenew : ∀ t : ℝ, 0 ≤ t →
      F t = Real.exp t *
        ∫ u in Set.Ioi t, Real.exp (-u) * (1 - q u) * F u)
    (hlim : Filter.Tendsto F Filter.atTop (nhds 1)) :
    ∀ t : ℝ, 0 ≤ t → F t =
      Real.exp (-(∫ u in Set.Ioi t, q u)) := by
  let k : ℝ → ℝ := fun u => Real.exp (-u) * (1 - q u) * F u
  let H : ℝ → ℝ := fun t => ∫ u in Set.Ioi t, q u
  have hFc : ContinuousOn F (Set.Ici 0) := by
    apply ((Real.continuous_exp.continuousOn).mul
      hkInt.continuousOn_Ici_primitive_Ioi).congr
    intro t ht
    exact hrenew t ht
  have hFcp : ContinuousOn F (Set.Ioi 0) := hFc.mono Set.Ioi_subset_Ici_self
  have hkc : ContinuousOn k (Set.Ioi 0) := by
    exact (((Real.continuous_exp.comp continuous_neg).continuousOn.mul
      (continuousOn_const.sub hq)).mul hFcp)
  have hFd (t : ℝ) (ht : 0 < t) : HasDerivAt F (q t * F t) t := by
    have htail := race_hasDerivAt_tail_integral k hkInt hkc t ht
    have heq : F =ᶠ[nhds t] (fun x : ℝ => Real.exp x * ∫ u in Set.Ioi x, k u) := by
      filter_upwards [Ioi_mem_nhds ht] with x hx
      exact hrenew x hx.le
    have hd := ((Real.hasDerivAt_exp t).mul htail).congr_of_eventuallyEq heq
    have hexp : Real.exp t * Real.exp (-t) = 1 := by
      rw [← Real.exp_add]
      simp
    have hvalue : Real.exp t * (∫ u in Set.Ioi t, k u) +
        Real.exp t * (-k t) = q t * F t := by
      calc
        Real.exp t * (∫ u in Set.Ioi t, k u) + Real.exp t * (-k t) =
            F t - (Real.exp t * Real.exp (-t)) * ((1 - q t) * F t) := by
          rw [← hrenew t ht.le]
          dsimp [k]
          ring
        _ = q t * F t := by rw [hexp]; ring
    exact hvalue ▸ hd
  have hHd (t : ℝ) (ht : 0 < t) : HasDerivAt H (-q t) t :=
    race_hasDerivAt_tail_integral q hqInt hq t ht
  have hPd (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun x : ℝ => F x * Real.exp (H x)) 0 t := by
    exact ((hFd t ht).fun_mul (HasDerivAt.exp (hHd t ht))).congr_deriv (by ring)
  have hPc : DifferentiableOn ℝ (fun x : ℝ => F x * Real.exp (H x)) (Set.Ioi 0) := by
    intro t ht
    exact (hPd t ht).differentiableAt.differentiableWithinAt
  have hPzero : (Set.Ioi (0 : ℝ)).EqOn
      (deriv (fun x : ℝ => F x * Real.exp (H x))) 0 := by
    intro t ht
    exact (hPd t ht).deriv
  have hconst (t s : ℝ) (ht : 0 < t) (hs : 0 < s) :
      F t * Real.exp (H t) = F s * Real.exp (H s) := by
    exact isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (𝕜 := ℝ) (0 : ℝ)).isPreconnected
      hPc hPzero ht hs
  have hHlim : Filter.Tendsto H Filter.atTop (nhds 0) := by
    exact tendsto_integral_Ioi_zero Filter.tendsto_id
  have hPlim : Filter.Tendsto (fun x : ℝ => F x * Real.exp (H x))
      Filter.atTop (nhds 1) := by
    simpa using hlim.mul ((Real.continuous_exp.tendsto 0).comp hHlim)
  have hpositive (t : ℝ) (ht : 0 < t) : F t = Real.exp (-H t) := by
    have heq : (fun x : ℝ => F x * Real.exp (H x)) =ᶠ[Filter.atTop]
        (fun _ => F t * Real.exp (H t)) := by
      filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
      exact hconst x t (zero_lt_one.trans_le hx) ht
    have hPt : Filter.Tendsto (fun x : ℝ => F x * Real.exp (H x))
        Filter.atTop (nhds (F t * Real.exp (H t))) :=
      (Filter.tendsto_congr' heq).2 tendsto_const_nhds
    have hvalue : F t * Real.exp (H t) = 1 :=
      (tendsto_nhds_unique hPlim hPt).symm
    calc
      F t = (F t * Real.exp (H t)) * Real.exp (-H t) := by
        rw [mul_assoc, ← Real.exp_add]
        simp
      _ = Real.exp (-H t) := by rw [hvalue, one_mul]
  intro t ht
  obtain rfl | ht := eq_or_lt_of_le ht
  · have hFzero : Filter.Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds (F 0)) :=
      (hFc 0 (by simp)).mono Set.Ioi_subset_Ici_self
    have hHzero : Filter.Tendsto H (nhdsWithin 0 (Set.Ioi 0)) (nhds (H 0)) :=
      (hqInt.continuousOn_Ici_primitive_Ioi 0 (by simp)).mono Set.Ioi_subset_Ici_self
    have hGzero : Filter.Tendsto (fun x : ℝ => Real.exp (-H x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.exp (-H 0))) := by
      simpa only [Function.comp_def] using
        (Real.continuous_exp.tendsto (-H 0)).comp hHzero.neg
    have heq : F =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun x : ℝ => Real.exp (-H x)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact hpositive x hx
    exact tendsto_nhds_unique ((Filter.tendsto_congr' heq).1 hFzero) hGzero
  · exact hpositive t ht

lemma race_integral_positive_translate (g : ℝ → ℝ) (t : ℝ) :
    (∫ s : ℝ in Set.Ioi 0, g (t + s)) = ∫ u : ℝ in Set.Ioi t, g u := by
  have hfunc : (fun s : ℝ => (Set.Ioi t).indicator g (t + s)) =
      (Set.Ioi (0 : ℝ)).indicator (fun s : ℝ => g (t + s)) := by
    funext s
    simp [Set.indicator, Set.mem_Ioi]
  have h := integral_add_left_eq_self (μ := (volume : Measure ℝ))
    ((Set.Ioi t).indicator g) t
  rw [hfunc, integral_indicator measurableSet_Ioi,
    integral_indicator measurableSet_Ioi] at h
  exact h

lemma race_translate_exponential_renewal (p F : ℝ → ℝ) (t : ℝ) :
    (∫ s : ℝ in Set.Ioi 0, Real.exp (-s) * p (t + s) * F (t + s)) =
      Real.exp t * ∫ u : ℝ in Set.Ioi t, Real.exp (-u) * p u * F u := by
  calc
    (∫ s : ℝ in Set.Ioi 0, Real.exp (-s) * p (t + s) * F (t + s)) =
        ∫ s : ℝ in Set.Ioi 0,
          Real.exp t * (Real.exp (-(t + s)) * p (t + s) * F (t + s)) := by
      apply integral_congr_ae
      filter_upwards [] with s
      have he : Real.exp t * Real.exp (-(t + s)) = Real.exp (-s) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← mul_assoc, ← mul_assoc, he]
    _ = Real.exp t * ∫ u : ℝ in Set.Ioi t, Real.exp (-u) * p u * F u := by
      rw [integral_const_mul]
      exact congrArg (fun x : ℝ => Real.exp t * x)
        (race_integral_positive_translate
          (fun u : ℝ => Real.exp (-u) * p u * F u) t)

lemma race_unit_mass_eq_arrival_tail
    (a t : ℝ) (ht : 0 < t) (ω : ℕ → ℝ) (hω : ∀ n, 0 ≤ ω n) :
    t ^ (-a) * (1 + max 0 (Vtail a t ω)) =
      t ^ (-a) + ∑' n : ℕ, (t + arrival ω (n + 1)) ^ (-a) := by
  have hV : 0 ≤ Vtail a t ω := race_Vtail_nonneg_of_nonneg a t ht.le ω hω
  rw [max_eq_right hV]
  unfold Vtail
  rw [mul_add, mul_one, ← mul_assoc, ← Real.rpow_add ht,
    neg_add_cancel, Real.rpow_zero, one_mul]

lemma race_unit_laplace_eq_arrival_laplace (a v : ℝ) (ha : 1 < a) :
    let R : ℝ × (ℕ → ℝ) → ℝ := fun z =>
      z.1 ^ (-a) * (1 + max 0 (Vtail a z.1 z.2))
    (∫ z, Real.exp (-(v * R z)) ∂expOne.prod arrivalLaw) =
      ∫ ω, Real.exp (-(v *
        ∑' n : ℕ, arrival ω (n + 1) ^ (-a))) ∂arrivalLaw := by
  let : IsProbabilityMeasure expOne := isProbabilityMeasure_expMeasure zero_lt_one
  let : IsProbabilityMeasure arrivalLaw := race_arrival_probability
  let R : ℝ × (ℕ → ℝ) → ℝ := fun z =>
    z.1 ^ (-a) * (1 + max 0 (Vtail a z.1 z.2))
  change (∫ z, Real.exp (-(v * R z)) ∂expOne.prod arrivalLaw) = _
  have hA : Measurable (fun z : ℝ × (ℕ → ℝ) =>
      ∑' n : ℕ, (z.1 + arrival z.2 (n + 1)) ^ (-a)) :=
    race_arrival_mass_measurable a
  have hVm : Measurable (fun z : ℝ × (ℕ → ℝ) => Vtail a z.1 z.2) := by
    unfold Vtail
    fun_prop
  have hRm : Measurable R := by
    dsimp [R]
    fun_prop
  have hzeroMap : arrivalLaw.map (fun ω : ℕ → ℝ => ω 0) = expOne := by
    change (Measure.infinitePi (fun _ : ℕ => expOne)).map (fun ω => ω 0) = expOne
    exact Measure.infinitePi_map_eval (fun _ : ℕ => expOne) 0
  have hzero : ∀ᵐ ω ∂arrivalLaw, 0 < ω 0 := by
    have h : ∀ᵐ t ∂arrivalLaw.map (fun ω : ℕ → ℝ => ω 0), 0 < t := by
      rw [hzeroMap]
      exact race_scalar_exp_ae_pos
    exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable h
  rw [← race_arrival_head_tail_law,
    integral_map (by fun_prop) (by fun_prop)]
  apply integral_congr_ae
  filter_upwards [hzero, race_arrival_ae_nonneg,
    race_arrival_mass_ae_summable a ha] with ω h0 hω hsum
  dsimp [R]
  rw [race_unit_mass_eq_arrival_tail a (ω 0) h0
    (fun n => ω (n + 1)) (fun n => hω (n + 1))]
  congr 2
  have hhead := race_arrival_mass_head a 0 ω (hsum 0 le_rfl)
  simpa using congrArg (fun x : ℝ => Real.exp (-(v * x))) hhead.symm

lemma race_shifted_arrival_laplace
    (a v : ℝ) (ha : 1 < a) (hv : 0 < v) :
    ∀ t : ℝ, 0 ≤ t →
      (∫ ω : ℕ → ℝ, Real.exp (-(v *
        ∑' n : ℕ, (t + arrival ω (n + 1)) ^ (-a))) ∂arrivalLaw) =
        Real.exp (-(∫ u : ℝ in Set.Ioi t,
          1 - Real.exp (-(v * u ^ (-a))))) := by
  let : IsProbabilityMeasure arrivalLaw := race_arrival_probability
  let A : ℝ → (ℕ → ℝ) → ℝ := fun t ω =>
    ∑' n : ℕ, (t + arrival ω (n + 1)) ^ (-a)
  let F : ℝ → ℝ := fun t => ∫ ω, Real.exp (-(v * A t ω)) ∂arrivalLaw
  let p : ℝ → ℝ := fun u => Real.exp (-(v * u ^ (-a)))
  let q : ℝ → ℝ := fun u => 1 - p u
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hαlt : 1/a < 1 := (div_lt_one ha0).2 ha
  have harg : 0 < 1 - 1/a := by linarith
  have hGamma : 0 < Real.Gamma (1 - 1/a) := Real.Gamma_pos_of_pos harg
  have hqmean : (∫ u : ℝ in Set.Ioi 0, q u) =
      Real.Gamma (1 - 1/a) * v ^ (1/a) := by
    simpa only [q, p] using race_integral_laplace_exponent a v ha hv
  have hqInt : IntegrableOn q (Set.Ioi 0) := by
    by_contra hn
    have hzero : (∫ u : ℝ in Set.Ioi 0, q u) = 0 := integral_undef hn
    have hpos : 0 < Real.Gamma (1 - 1/a) * v ^ (1/a) :=
      mul_pos hGamma (Real.rpow_pos_of_pos hv _)
    rw [hzero] at hqmean
    exact hpos.ne' hqmean.symm
  have hpowCont : ContinuousOn (fun u : ℝ => u ^ (-a)) (Set.Ioi 0) :=
    continuousOn_id.rpow_const (fun u hu => Or.inl (ne_of_gt hu))
  have hpCont : ContinuousOn p (Set.Ioi 0) := by
    exact ((continuousOn_const.mul hpowCont).neg).rexp
  have hqCont : ContinuousOn q (Set.Ioi 0) := continuousOn_const.sub hpCont
  have hAm : Measurable (fun z : ℝ × (ℕ → ℝ) => A z.1 z.2) :=
    race_arrival_mass_measurable a
  have hGm : Measurable (fun z : ℝ × (ℕ → ℝ) => Real.exp (-(v * A z.1 z.2))) :=
    Real.measurable_exp.comp ((measurable_const.mul hAm).neg)
  have hFm : Measurable F :=
    (hGm.stronglyMeasurable.integral_prod_right' (ν := arrivalLaw)).measurable
  have hAnonneg (t : ℝ) (ht : 0 ≤ t) (ω : ℕ → ℝ) (hω : ∀ n, 0 ≤ ω n) :
      0 ≤ A t ω := by
    apply tsum_nonneg
    intro n
    apply Real.rpow_nonneg
    apply add_nonneg ht
    unfold arrival
    exact Finset.sum_nonneg (fun k _ => hω k)
  have hFbound (t : ℝ) (ht : 0 ≤ t) : 0 ≤ F t ∧ F t ≤ 1 := by
    have hnonneg : 0 ≤ᵐ[arrivalLaw] (fun ω => Real.exp (-(v * A t ω))) := by
      filter_upwards [] with ω
      exact (Real.exp_pos _).le
    have hle : (fun ω => Real.exp (-(v * A t ω))) ≤ᵐ[arrivalLaw]
        (fun _ => (1 : ℝ)) := by
      filter_upwards [race_arrival_ae_nonneg] with ω hω
      exact Real.exp_le_one_iff.2
        (neg_nonpos.2 (mul_nonneg hv.le (hAnonneg t ht ω hω)))
    refine ⟨integral_nonneg_of_ae hnonneg, ?_⟩
    have h := integral_mono_of_nonneg hnonneg (integrable_const (1 : ℝ)) hle
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hpMeas : Measurable p := by
    have hpow : Measurable (fun u : ℝ => u ^ (-a)) := measurable_id.pow measurable_const
    exact Real.measurable_exp.comp ((measurable_const.mul hpow).neg)
  have hqMeas : Measurable q := measurable_const.sub hpMeas
  have hOneq (u : ℝ) : 1 - q u = p u := by dsimp [q]; ring
  have hpbound (u : ℝ) (hu : 0 ≤ u) : 0 ≤ p u ∧ p u ≤ 1 := by
    refine ⟨(Real.exp_pos _).le, ?_⟩
    exact Real.exp_le_one_iff.2
      (neg_nonpos.2 (mul_nonneg hv.le (Real.rpow_nonneg hu (-a))))
  have hexpInt : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Set.Ioi 0) := by
    simpa only [sub_self, Real.rpow_zero, mul_one] using
      (Real.GammaIntegral_convergent (s := (1 : ℝ)) zero_lt_one)
  have hkMeas : Measurable (fun u : ℝ => Real.exp (-u) * (1 - q u) * F u) :=
    ((Real.measurable_exp.comp measurable_id.neg).mul
      (measurable_const.sub hqMeas)).mul hFm
  have hkInt : IntegrableOn
      (fun u : ℝ => Real.exp (-u) * (1 - q u) * F u) (Set.Ioi 0) := by
    apply hexpInt.mono' hkMeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hp := hpbound u hu.le
    have hF := hFbound u hu.le
    rw [hOneq, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg
        (mul_nonneg (Real.exp_nonneg _) hp.1) hF.1)]
    calc
      Real.exp (-u) * p u * F u ≤ Real.exp (-u) * p u * 1 :=
        mul_le_mul_of_nonneg_left hF.2 (mul_nonneg (Real.exp_nonneg _) hp.1)
      _ = Real.exp (-u) * p u := mul_one _
      _ ≤ Real.exp (-u) * 1 := mul_le_mul_of_nonneg_left hp.2 (Real.exp_nonneg _)
      _ = Real.exp (-u) := mul_one _
  have hraw := race_arrival_laplace_renewal a v ha hv
  dsimp only at hraw
  have hrenew : ∀ t : ℝ, 0 ≤ t →
      F t = Real.exp t *
        ∫ u in Set.Ioi t, Real.exp (-u) * (1 - q u) * F u := by
    intro t ht
    calc
      F t = ∫ s : ℝ in Set.Ioi 0, Real.exp (-s) * p (t + s) * F (t + s) :=
        hraw t ht
      _ = Real.exp t * ∫ u : ℝ in Set.Ioi t, Real.exp (-u) * p u * F u :=
        race_translate_exponential_renewal p F t
      _ = _ := by simp_rw [hOneq]
  have hlim : Filter.Tendsto F Filter.atTop (nhds 1) :=
    race_shifted_mass_laplace_tendsto_one a ha v hv.le
  exact race_renewal_unique q F hqCont hqInt hkInt hrenew hlim

/-- At shift zero, the integral exponent already checked in ArrivalCore
becomes the exact stable transform of the full arrival mass. -/
lemma race_arrival_laplace
    (a v : ℝ) (ha : 1 < a) (hv : 0 < v) :
    (∫ ω : ℕ → ℝ, Real.exp (-(v *
      ∑' n : ℕ, arrival ω (n + 1) ^ (-a))) ∂arrivalLaw) =
        Real.exp (-(Real.Gamma (1 - 1/a) * v ^ (1/a))) := by
  have h := race_shifted_arrival_laplace a v ha hv 0 le_rfl
  simpa only [zero_add, race_integral_laplace_exponent a v ha hv] using h

/-- Final unit mass transform, once the actual head/tail transport helper
is checked. This supplies the Laplace component of the old analytic primitive. -/
lemma race_unit_arrival_laplace
    (a v : ℝ) (ha : 1 < a) (hv : 0 < v) :
    (∫ z : ℝ × (ℕ → ℝ),
      Real.exp (-(v * (z.1 ^ (-a) * (1 + max 0 (Vtail a z.1 z.2)))))
      ∂expOne.prod arrivalLaw) =
        Real.exp (-(Real.Gamma (1 - 1/a) * v ^ (1/a))) := by
  rw [race_unit_laplace_eq_arrival_laplace a v ha]
  exact race_arrival_laplace a v ha hv

lemma race_unit_log_integrable (a : ℝ) (ha : 1 < a) :
    Integrable (fun z : ℝ × (ℕ → ℝ) =>
      Real.log (z.1 ^ (-a) * (1 + max 0 (Vtail a z.1 z.2))))
      (expOne.prod arrivalLaw) := by
  let : IsProbabilityMeasure expOne :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let : IsProbabilityMeasure arrivalLaw := race_arrival_probability
  let R : ℝ × (ℕ → ℝ) → ℝ := fun z =>
    z.1 ^ (-a) * (1 + max 0 (Vtail a z.1 z.2))
  have hRmeas : Measurable R := race_measurable_unit_mass a
  have htpos : ∀ᵐ z : ℝ × (ℕ → ℝ) ∂expOne.prod arrivalLaw, 0 < z.1 :=
    Measure.quasiMeasurePreserving_fst.ae race_scalar_exp_ae_pos
  have hRpos : ∀ᵐ z ∂expOne.prod arrivalLaw, 0 < R z := by
    filter_upwards [htpos] with z hz
    dsimp only [R]
    apply mul_pos (Real.rpow_pos_of_pos hz (-a))
    linarith [le_max_left (0 : ℝ) (Vtail a z.1 z.2)]
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hα : 0 < 1/a := one_div_pos.mpr ha0
  have harg : 0 < 1 - 1/a := by
    have hlt : 1/a < 1 := (div_lt_one ha0).2 ha
    linarith
  have hG : 0 < Real.Gamma (1 - 1/a) := Real.Gamma_pos_of_pos harg
  have hLap : ∀ v : ℝ, 0 < v →
      (∫ z, Real.exp (-(v * R z)) ∂expOne.prod arrivalLaw) =
        Real.exp (-(Real.Gamma (1 - 1/a) * v ^ (1/a))) := by
    intro v hv
    exact race_unit_arrival_laplace a v ha hv
  exact race_scalar_log_integrable_of_stable_laplace
    (expOne.prod arrivalLaw) R hRmeas hRpos
    (1/a) (Real.Gamma (1 - 1/a)) hα hG hLap

lemma race_gamma_price (a : ℝ) (ha : 1 < a) : jET a = j a := by
  exact race_gamma_price_of_unit_laplace a ha
    (race_measurable_unit_mass a) (race_unit_log_integrable a ha)
    (fun v hv => race_unit_arrival_laplace a v ha hv)

end

end StochasticToDeterministicLatents.General
