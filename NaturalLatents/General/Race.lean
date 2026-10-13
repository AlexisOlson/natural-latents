-- Adapted from the author's earlier repository (StochasticToDeterministicLatents);
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised; namespace renamed to NaturalLatents.General.
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
import NaturalLatents.General.RaceTransport
import NaturalLatents.General.RaceLaplace

/-!
# The race bound and its limit

For `a > 1` and a latent with positive prior and positive posterior rows, the exponential race
gives a calibrated seeded family `F` with

    h F ≤ a * B L + 2 * j a * d L

(`exists_race`), the entropy of the winner paid by the arrival-sum price `j a` times the
categorical mismatch. This module assembles the gain, scaling, superposition, and transport
lemmas for the appended clock sequence and proves `exists_race`. The analytic inputs about
arrival sums and their Gamma-form price come from `NaturalLatents.General.RaceLaplace`.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
This file retains that source's definitions and lemmas where cited, together with
material adapted from the author's earlier repository.
-/

namespace NaturalLatents.General

noncomputable section

open scoped BigOperators
open MeasureTheory ProbabilityTheory

variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/- Product log-integrability supplies an integrable gain slice for almost every positive shift. A finite
positive shift is dominated by one such slice, whose exponential mass is positive, so no further
gain-section hypothesis is needed. -/
lemma race_gain_joint_integrable_of_unit_log
    (a : ℝ) (ha : 1 < a) :
    Integrable (fun z : ℝ × (ℕ → ℝ) =>
      Real.log (1 + Vtail a z.1 z.2)) (expOne.prod arrivalLaw) := by
  have hlogT : Integrable Real.log expOne :=
    race_scalar_exp_log_integrable_mean.1
  have htpos : ∀ᵐ z : ℝ × (ℕ → ℝ) ∂expOne.prod arrivalLaw, 0 < z.1 :=
    Measure.quasiMeasurePreserving_fst.ae race_scalar_exp_ae_pos
  have hωnonneg : ∀ᵐ z : ℝ × (ℕ → ℝ) ∂expOne.prod arrivalLaw,
      ∀ n : ℕ, 0 ≤ z.2 n :=
    Measure.quasiMeasurePreserving_snd.ae race_arrival_ae_nonneg
  have hgainEq :
      (fun z : ℝ × (ℕ → ℝ) => Real.log (1 + Vtail a z.1 z.2))
        =ᵐ[expOne.prod arrivalLaw]
      (fun z =>
        Real.log (z.1 ^ (-a) * (1 + max 0 (Vtail a z.1 z.2)))
          + a * Real.log z.1) := by
    filter_upwards [htpos, hωnonneg] with z hzt hzω
    have hV : 0 ≤ Vtail a z.1 z.2 :=
      race_Vtail_nonneg_of_nonneg a z.1 hzt.le z.2 hzω
    have hgainpos : 0 < 1 + Vtail a z.1 z.2 := by linarith
    rw [max_eq_right hV,
      Real.log_mul (Real.rpow_pos_of_pos hzt (-a)).ne' hgainpos.ne',
      Real.log_rpow hzt (-a)]
    ring
  exact ((race_unit_log_integrable a ha).add
    ((hlogT.comp_fst arrivalLaw).const_mul a)).congr hgainEq.symm

/-- The actual summable tail gain is monotone in its positive shift.
    The two summability hypotheses prevent the totalized tsum from hiding
    nonsummable points where an order comparison would not be justified. -/
lemma race_Vtail_mono_of_summable
    (a : ℝ) (ha : 0 ≤ a) (ω : ℕ → ℝ) (hω : ∀ n, 0 ≤ ω n)
    (t u : ℝ) (ht : 0 < t) (htu : t ≤ u)
    (hst : Summable (fun n : ℕ => (t + arrival ω (n+1)) ^ (-a)))
    (hsu : Summable (fun n : ℕ => (u + arrival ω (n+1)) ^ (-a))) :
    Vtail a t ω ≤ Vtail a u ω := by
  have hu : 0 < u := ht.trans_le htu
  have hA (n : ℕ) : 0 ≤ arrival ω (n+1) := by
    unfold arrival
    exact Finset.sum_nonneg (fun k _ => hω k)
  have hterm (n : ℕ) :
      t ^ a * (t + arrival ω (n+1)) ^ (-a) ≤
        u ^ a * (u + arrival ω (n+1)) ^ (-a) := by
    have htA : 0 < t + arrival ω (n+1) :=
      add_pos_of_pos_of_nonneg ht (hA n)
    have huA : 0 < u + arrival ω (n+1) :=
      add_pos_of_pos_of_nonneg hu (hA n)
    have hratio : t / (t + arrival ω (n+1)) ≤
        u / (u + arrival ω (n+1)) := by
      apply (div_le_div_iff₀ htA huA).2
      nlinarith only [mul_nonneg (sub_nonneg.mpr htu) (hA n)]
    have hp := Real.rpow_le_rpow (div_nonneg ht.le htA.le) hratio ha
    rw [Real.div_rpow ht.le htA.le a, Real.div_rpow hu.le huA.le a] at hp
    simpa only [Real.rpow_neg htA.le, Real.rpow_neg huA.le,
      div_eq_mul_inv] using hp
  unfold Vtail
  rw [← tsum_mul_left, ← tsum_mul_left]
  exact (hst.mul_left (t ^ a)).tsum_le_tsum hterm (hsu.mul_left (u ^ a))

lemma race_gain_sections_of_unit_log_integrable
    (a : ℝ) (ha : 1 < a) :
    ∀ t : ℝ, 0 ≤ t →
      Integrable (fun ω : ℕ → ℝ => Real.log (1 + Vtail a t ω)) arrivalLaw :=  by
  have hjoint := race_gain_joint_integrable_of_unit_log a ha
  intro t ht
  obtain rfl | ht := eq_or_lt_of_le ht
  · have ha0 : a ≠ 0 := (lt_trans zero_lt_one ha).ne'
    simp [Vtail, Real.zero_rpow ha0]
  have htail : expOne (Set.Ioi t) ≠ 0 := by
    have he : expOne (Set.Ioi t) = ENNReal.ofReal (Real.exp (-t)) :=
      stoch_to_det.expMeasure_one_Ioi t ht.le
    rw [he]
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos (-t))).ne'
  have hslices : ∀ᵐ u : ℝ ∂expOne,
      Integrable (fun ω : ℕ → ℝ => Real.log (1 + Vtail a u ω)) arrivalLaw :=
    hjoint.prod_right_ae
  obtain ⟨u, htu, huInt⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae htail (ae_restrict_of_ae hslices)
  have hu : 0 < u := lt_trans ht htu
  have hmeas : Measurable (fun ω : ℕ → ℝ => Real.log (1 + Vtail a t ω)) := by
    exact Real.measurable_log.comp
      (measurable_const.add
        ((race_measurable_Vtail a).comp (measurable_const.prodMk measurable_id)))
  apply huInt.mono' hmeas.aestronglyMeasurable
  filter_upwards [race_arrival_ae_nonneg,
    race_arrival_mass_ae_summable a ha] with ω hω hsum
  have hVt := race_Vtail_nonneg_of_nonneg a t ht.le ω hω
  have hmono := race_Vtail_mono_of_summable a
    (lt_trans zero_lt_one ha).le ω hω t u ht htu.le
    (hsum t ht.le) (hsum u hu.le)
  have hnonneg : 0 ≤ Real.log (1 + Vtail a t ω) :=
    Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact Real.log_le_log (by linarith : 0 < 1 + Vtail a t ω) (by linarith)

lemma race_m_zero (a : ℝ) (ha : a ≠ 0) : m a 0 = 0 := by
  simp [m, Vtail, Real.zero_rpow ha]

lemma race_m_nonneg (a t : ℝ) (ht : 0 ≤ t) : 0 ≤ m a t := by
  unfold m
  apply integral_nonneg_of_ae
  filter_upwards [race_arrival_ae_nonneg] with ω hω
  have hV := race_Vtail_nonneg_of_nonneg a t ht ω hω
  exact Real.log_nonneg (by linarith)

lemma race_measurable_m (a : ℝ) : Measurable (m a) := by
  have hgain : Measurable (fun z : ℝ × (ℕ → ℝ) =>
      Real.log (1 + Vtail a z.1 z.2)) :=
    Real.measurable_log.comp (measurable_const.add (race_measurable_Vtail a))
  change Measurable (fun t : ℝ => ∫ ω, Real.log (1 + Vtail a t ω) ∂arrivalLaw)
  exact (hgain.stronglyMeasurable.integral_prod_right' (ν := arrivalLaw)).measurable

lemma race_m_mono_of_unit_log
    (a : ℝ) (ha : 1 < a)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    m a s ≤ m a t := by
  have ht : 0 ≤ t := hs.trans hst
  obtain rfl | hs := eq_or_lt_of_le hs
  · rw [race_m_zero a (lt_trans zero_lt_one ha).ne']
    exact race_m_nonneg a t ht
  have hsections := race_gain_sections_of_unit_log_integrable a ha
  unfold m
  apply integral_mono_ae (hsections s hs.le) (hsections t ht)
  filter_upwards [race_arrival_ae_nonneg,
    race_arrival_mass_ae_summable a ha] with ω hω hsum
  have hVs := race_Vtail_nonneg_of_nonneg a s hs.le ω hω
  have hVmono := race_Vtail_mono_of_summable a
    (lt_trans zero_lt_one ha).le ω hω s t hs hst
    (hsum s hs.le) (hsum t ht)
  exact Real.log_le_log (by linarith : 0 < 1 + Vtail a s ω) (by linarith)

lemma race_scaled_m_integrable_of_unit_log
    (a : ℝ) (ha : 1 < a)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Integrable (fun t : ℝ => m a (r * t)) expOne := by
  have hjoint := race_gain_joint_integrable_of_unit_log a ha
  have hmint : Integrable (m a) expOne := by
    change Integrable (fun t : ℝ => ∫ ω, Real.log (1 + Vtail a t ω) ∂arrivalLaw) expOne
    exact hjoint.integral_prod_left
  have hscaledmeas : Measurable (fun t : ℝ => m a (r * t)) :=
    (race_measurable_m a).comp (measurable_const.mul measurable_id)
  apply hmint.mono' hscaledmeas.aestronglyMeasurable
  filter_upwards [race_scalar_exp_ae_pos] with t ht
  have hrt0 : 0 ≤ r * t := mul_nonneg hr0 ht.le
  have hrtle : r * t ≤ t := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hr1 ht.le
  have hnonneg := race_m_nonneg a (r * t) hrt0
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact race_m_mono_of_unit_log a ha (r * t) t hrt0 hrtle

lemma race_frullani_gain_kernel_bounds {x v : ℝ} (hx : 0 ≤ x) (hv : 0 < v) :
    0 ≤ Real.exp (-v) * v⁻¹ * (1 - Real.exp (-(v * x))) ∧
    Real.exp (-v) * v⁻¹ * (1 - Real.exp (-(v * x))) ≤
      x * Real.exp (-v) := by
  have hsmall : Real.exp (-(v * x)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hv.le hx))
  have hlinear : 1 - Real.exp (-(v * x)) ≤ v * x := by
    linarith [Real.one_sub_le_exp_neg (v * x)]
  have hweight : 0 ≤ Real.exp (-v) * v⁻¹ :=
    mul_nonneg (Real.exp_pos _).le (inv_nonneg.2 hv.le)
  constructor
  · exact mul_nonneg hweight (sub_nonneg.2 hsmall)
  · calc
      _ ≤ Real.exp (-v) * v⁻¹ * (v * x) :=
        mul_le_mul_of_nonneg_left hlinear hweight
      _ = x * Real.exp (-v) := by field_simp [hv.ne']

lemma race_frullani_log_one_add (x : ℝ) (hx : 0 ≤ x) :
    (∫⁻ v : ℝ in Set.Ioi 0,
      ENNReal.ofReal (Real.exp (-v) * v⁻¹ *
        (1 - Real.exp (-(v * x))))) = ENNReal.ofReal (Real.log (1 + x)) := by
  let K : ℝ → ℝ := fun v =>
    Real.exp (-v) * v⁻¹ * (1 - Real.exp (-(v * x)))
  have hKm : Measurable K := by dsimp [K]; fun_prop
  have hKnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] K := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact (race_frullani_gain_kernel_bounds hx hv).1
  have hKi : IntegrableOn K (Set.Ioi 0) := by
    apply ((integrableOn_exp_neg_Ioi (0 : ℝ)).const_mul x).mono_nonneg
      hKm.aestronglyMeasurable hKnn
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact (race_frullani_gain_kernel_bounds hx hv).2
  have hform (v : ℝ) :
      v⁻¹ • (Real.exp (-(1 * v)) - Real.exp (-((1 + x) * v))) = K v := by
    have he : Real.exp (-((1 + x) * v)) =
        Real.exp (-v) * Real.exp (-(v * x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [one_mul, he, smul_eq_mul]
    dsimp [K]
    ring
  have hFi : IntegrableOn
      (fun v : ℝ => v⁻¹ • (Real.exp (-(1 * v)) - Real.exp (-((1 + x) * v))))
      (Set.Ioi 0) := by
    exact hKi.congr (ae_of_all _ (fun v => (hform v).symm))
  have hL : Filter.Tendsto (fun v : ℝ => Real.exp (-v))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 : ℝ)) := by
    have hcont : ContinuousAt (fun v : ℝ => Real.exp (-v)) (0 : ℝ) :=
      (Real.continuous_exp.comp continuous_neg).continuousAt
    have hL0 : Filter.Tendsto (fun v : ℝ => Real.exp (-v))
        (nhds (0 : ℝ)) (nhds (1 : ℝ)) := by
      simpa only [neg_zero, Real.exp_zero] using hcont.tendsto
    exact hL0.mono_left nhdsWithin_le_nhds
  have hF : (∫ v : ℝ in Set.Ioi 0,
      v⁻¹ • (Real.exp (-(1 * v)) - Real.exp (-((1 + x) * v)))) =
        Real.log (1 + x) := by
    simpa only [div_one, sub_zero, smul_eq_mul, mul_one] using
      (Frullani.integral_Ioi_eq (f := fun v : ℝ => Real.exp (-v))
        (integrableOn_exp_neg_Ioi (0 : ℝ)).locallyIntegrableOn
        (a := (1 : ℝ)) (b := 1 + x) (L := (1 : ℝ)) (R := (0 : ℝ))
        (by norm_num) (by linarith) hL Real.tendsto_exp_neg_atTop_nhds_zero hFi)
  have hreal : (∫ v : ℝ in Set.Ioi 0, K v) = Real.log (1 + x) := by
    calc
      _ = ∫ v : ℝ in Set.Ioi 0,
          v⁻¹ • (Real.exp (-(1 * v)) - Real.exp (-((1 + x) * v))) :=
        setIntegral_congr_fun measurableSet_Ioi (fun v _ => (hform v).symm)
      _ = _ := hF
  rw [← ofReal_integral_eq_lintegral_ofReal hKi hKnn, hreal]

/-- Expected log gain from its Laplace transform. The identity is stated in
    ENNReal so that Tonelli needs no product integrability hypothesis. -/
lemma race_expected_log_one_add_laplace
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → ℝ) (hVm : Measurable V) (hVnn : 0 ≤ᵐ[μ] V)
    (hlog : Integrable (fun ω => Real.log (1 + V ω)) μ) :
    ENNReal.ofReal (∫ ω, Real.log (1 + V ω) ∂μ) =
      ∫⁻ v : ℝ in Set.Ioi 0,
        ENNReal.ofReal (Real.exp (-v) * v⁻¹ *
          (1 - ∫ ω, Real.exp (-(v * V ω)) ∂μ)) := by
  let ν : Measure ℝ := volume.restrict (Set.Ioi 0)
  let K : ℝ → ℝ → ℝ := fun v x =>
    Real.exp (-v) * v⁻¹ * (1 - Real.exp (-(v * x)))
  have hlognn : 0 ≤ᵐ[μ] (fun ω => Real.log (1 + V ω)) := by
    filter_upwards [hVnn] with ω hω
    change 0 ≤ V ω at hω
    exact Real.log_nonneg (by linarith)
  have hKm : Measurable (fun z : Ω × ℝ => ENNReal.ofReal (K z.2 (V z.1))) := by
    have hVc : Measurable (fun z : Ω × ℝ => V z.1) := hVm.comp measurable_fst
    dsimp [K]
    fun_prop
  have hsection (v : ℝ) (hv : 0 < v) :
      (∫⁻ ω, ENNReal.ofReal (K v (V ω)) ∂μ) =
        ENNReal.ofReal (Real.exp (-v) * v⁻¹ *
          (1 - ∫ ω, Real.exp (-(v * V ω)) ∂μ)) := by
    have he : Integrable (fun ω => Real.exp (-(v * V ω))) μ := by
      apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
      filter_upwards [hVnn] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hv.le hω))
    have hKi : Integrable (fun ω => K v (V ω)) μ :=
      ((integrable_const (1 : ℝ)).sub he).const_mul _
    have hKnn : 0 ≤ᵐ[μ] (fun ω => K v (V ω)) := by
      filter_upwards [hVnn] with ω hω
      exact (race_frullani_gain_kernel_bounds hω hv).1
    rw [← ofReal_integral_eq_lintegral_ofReal hKi hKnn]
    congr 1
    dsimp [K]
    rw [integral_const_mul, integral_sub (integrable_const _) he]
    simp
  calc
    ENNReal.ofReal (∫ ω, Real.log (1 + V ω) ∂μ) =
        ∫⁻ ω, ENNReal.ofReal (Real.log (1 + V ω)) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal hlog hlognn
    _ = ∫⁻ ω, ∫⁻ v, ENNReal.ofReal (K v (V ω)) ∂ν ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hVnn] with ω hω
      exact (race_frullani_log_one_add (V ω) hω).symm
    _ = ∫⁻ v, ∫⁻ ω, ENNReal.ofReal (K v (V ω)) ∂μ ∂ν :=
      lintegral_lintegral_swap hKm.aemeasurable
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact hsection v hv

/-- Scalar concavity of 1-exp(-x), valid for every real x. -/
lemma race_laplace_gain_scalar_concavity (x r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    r * (1 - Real.exp (-x)) ≤ 1 - Real.exp (-(r * x)) := by
  have hc : Real.exp (r * (-x) + (1 - r) * 0) ≤
      r * Real.exp (-x) + (1 - r) * Real.exp 0 :=
    convexOn_exp.2 (Set.mem_univ (-x)) (Set.mem_univ (0 : ℝ))
      hr0 (by linarith : 0 ≤ 1 - r) (by ring : r + (1 - r) = 1)
  simp only [mul_zero, add_zero, Real.exp_zero, mul_one] at hc
  have he : Real.exp (r * -x) = Real.exp (-(r * x)) := by congr 1; ring
  rw [he] at hc
  calc
    r * (1 - Real.exp (-x)) =
        1 - (r * Real.exp (-x) + (1 - r)) := by ring
    _ ≤ 1 - Real.exp (-(r * x)) := sub_le_sub_left hc 1

/-- Sublinear clock scaling of expected log gain, assuming a linear
    Laplace exponent in clock intensity. No condition on Phi is necessary:
    nonnegativity of V already makes both kernels nonnegative. -/
lemma race_expected_log_gain_scaling_of_laplace
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : ℝ → Ω → ℝ) (Φ : ℝ → ℝ)
    (hVm : ∀ t, 0 ≤ t → Measurable (V t))
    (hVnn : ∀ t, 0 ≤ t → 0 ≤ᵐ[μ] V t)
    (hlog : ∀ t, 0 ≤ t → Integrable (fun ω => Real.log (1 + V t ω)) μ)
    (hlap : ∀ t, 0 ≤ t → ∀ v, 0 < v →
      (∫ ω, Real.exp (-(v * V t ω)) ∂μ) = Real.exp (-(t * Φ v)))
    (t r : ℝ) (ht : 0 ≤ t) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    r * (∫ ω, Real.log (1 + V t ω) ∂μ) ≤
      ∫ ω, Real.log (1 + V (r * t) ω) ∂μ := by
  have hrt : 0 ≤ r * t := mul_nonneg hr0 ht
  have hid (s : ℝ) (hs : 0 ≤ s) :
      ENNReal.ofReal (∫ ω, Real.log (1 + V s ω) ∂μ) =
        ∫⁻ v : ℝ in Set.Ioi 0,
          ENNReal.ofReal (Real.exp (-v) * v⁻¹ *
            (1 - Real.exp (-(s * Φ v)))) := by
    rw [race_expected_log_one_add_laplace μ (V s) (hVm s hs) (hVnn s hs) (hlog s hs)]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [hlap s hs v hv]
  have hrightnn : 0 ≤ ∫ ω, Real.log (1 + V (r * t) ω) ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hVnn (r * t) hrt] with ω hω
    change 0 ≤ V (r * t) ω at hω
    exact Real.log_nonneg (by linarith)
  apply (ENNReal.ofReal_le_ofReal_iff hrightnn).1
  rw [ENNReal.ofReal_mul hr0, hid t ht, hid (r * t) hrt]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  rw [← ENNReal.ofReal_mul hr0]
  apply ENNReal.ofReal_le_ofReal
  have hw : 0 ≤ Real.exp (-v) * v⁻¹ :=
    mul_nonneg (Real.exp_pos _).le (inv_nonneg.2 hv.le)
  have hc := mul_le_mul_of_nonneg_left
    (race_laplace_gain_scalar_concavity (t * Φ v) r hr0 hr1) hw
  calc
    r * (Real.exp (-v) * v⁻¹ * (1 - Real.exp (-(t * Φ v)))) =
        (Real.exp (-v) * v⁻¹) * (r * (1 - Real.exp (-(t * Φ v)))) := by ring
    _ ≤ (Real.exp (-v) * v⁻¹) *
        (1 - Real.exp (-(r * (t * Φ v)))) := hc
    _ = (Real.exp (-v) * v⁻¹) *
        (1 - Real.exp (-((r * t) * Φ v))) := by rw [mul_assoc r t (Φ v)]

lemma race_shifted_laplace_exponent_scaling (a v t : ℝ) (ht : 0 < t) :
    (∫ s : ℝ in Set.Ioi t,
      1 - Real.exp (-(v * t ^ a * s ^ (-a)))) =
        t * ∫ u : ℝ in Set.Ioi 0,
          1 - Real.exp (-(v * (1 + u) ^ (-a))) := by
  let g : ℝ → ℝ := fun s => 1 - Real.exp (-(v * t ^ a * s ^ (-a)))
  have hcancel : t ^ a * t ^ (-a) = 1 := by
    rw [← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero]
  have hscale := integral_comp_mul_left_Ioi' g (1 : ℝ) ht
  calc
    (∫ s : ℝ in Set.Ioi t, 1 - Real.exp (-(v * t ^ a * s ^ (-a)))) =
        t * ∫ u : ℝ in Set.Ioi 1,
          1 - Real.exp (-(v * t ^ a * (t * u) ^ (-a))) := by
      simpa only [g, smul_eq_mul, mul_one] using hscale.symm
    _ = t * ∫ u : ℝ in Set.Ioi 1,
          1 - Real.exp (-(v * u ^ (-a))) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      dsimp only
      have hu0 : 0 ≤ u := le_trans zero_le_one hu.le
      rw [Real.mul_rpow ht.le hu0]
      have hmass : v * t ^ a * (t ^ (-a) * u ^ (-a)) = v * u ^ (-a) := by
        calc
          _ = v * (t ^ a * t ^ (-a)) * u ^ (-a) := by ring
          _ = _ := by rw [hcancel]; ring
      rw [hmass]
    _ = _ := by
      rw [← race_integral_positive_translate
        (fun u : ℝ => 1 - Real.exp (-(v * u ^ (-a)))) (1 : ℝ)]

/-- The renewal transform implies a linear-in-t Laplace exponent for the
    scaled shifted tail Vtail. t=0 is handled directly from a>1. -/
lemma race_Vtail_laplace_of_shifted_transform (a : ℝ) (ha : 1 < a) :
    ∀ t : ℝ, 0 ≤ t → ∀ v : ℝ, 0 < v →
      (∫ ω : ℕ → ℝ, Real.exp (-(v * Vtail a t ω)) ∂arrivalLaw) =
        Real.exp (-(t * ∫ u : ℝ in Set.Ioi 0,
          1 - Real.exp (-(v * (1 + u) ^ (-a))))) := by
  intro t ht v hv
  rcases ht.eq_or_lt with rfl | htpos
  · have ha0 : a ≠ 0 := (lt_trans zero_lt_one ha).ne'
    simp [Vtail, Real.zero_rpow ha0]
  · have hvscaled : 0 < v * t ^ a :=
      mul_pos hv (Real.rpow_pos_of_pos htpos a)
    have hpoint (ω : ℕ → ℝ) :
        v * Vtail a t ω =
          (v * t ^ a) * ∑' n : ℕ, (t + arrival ω (n + 1)) ^ (-a) := by
      unfold Vtail
      ring
    calc
      (∫ ω, Real.exp (-(v * Vtail a t ω)) ∂arrivalLaw) =
          ∫ ω, Real.exp (-((v * t ^ a) *
            ∑' n : ℕ, (t + arrival ω (n + 1)) ^ (-a))) ∂arrivalLaw := by
        congr 1
        funext ω
        rw [hpoint]
      _ = Real.exp (-(∫ s : ℝ in Set.Ioi t,
            1 - Real.exp (-((v * t ^ a) * s ^ (-a))))) :=
        race_shifted_arrival_laplace a (v * t ^ a) ha hvscaled t htpos.le
      _ = _ := by rw [race_shifted_laplace_exponent_scaling a v t htpos]

lemma race_gain_scaling_of_shifted_transform (a : ℝ) (ha : 1 < a)
    (t r : ℝ) (ht : 0 ≤ t) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    r * m a t ≤ m a (r * t) := by
  have hVm (s : ℝ) (_hs : 0 ≤ s) : Measurable (Vtail a s) := by
    have hA : Measurable (fun ω : ℕ → ℝ =>
        ∑' n : ℕ, (s + arrival ω (n + 1)) ^ (-a)) :=
      (race_arrival_mass_measurable a).comp measurable_prodMk_left
    unfold Vtail
    exact measurable_const.mul hA
  have hVnn (s : ℝ) (hs : 0 ≤ s) : 0 ≤ᵐ[arrivalLaw] Vtail a s := by
    filter_upwards [race_arrival_ae_nonneg] with ω hω
    exact race_Vtail_nonneg_of_nonneg a s hs ω hω
  exact race_expected_log_gain_scaling_of_laplace arrivalLaw
    (fun s ω => Vtail a s ω)
    (fun v => ∫ u : ℝ in Set.Ioi 0, 1 - Real.exp (-(v * (1 + u) ^ (-a))))
    hVm hVnn (race_gain_sections_of_unit_log_integrable a ha)
    (race_Vtail_laplace_of_shifted_transform a ha)
    t r ht hr0 hr1

/-- A general coordinate statistic selected by the race can be averaged
by first integrating the independent appendages and then using the exact
winning-cell residual-clock law. No cardinality lower bound is needed. -/
lemma race_selected_coordinate_average
    {κ Ξ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ] [MeasurableSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (r : κ → ℝ) (hrpos : ∀ i, 0 < r i) (hrtotal : ∑ i, r i = 1)
    (f : κ → ℝ × Ξ → ℝ)
    (hfmeas : ∀ i, Measurable (f i))
    (hfint : ∀ i, Integrable (f i) (expOne.prod ν)) :
    let νκ : Measure (κ → Ξ) := Measure.pi (fun _ : κ => ν)
    let ρ := (stoch_to_det.clockLaw κ).prod νκ
    let selected : (κ → ℝ) × (κ → Ξ) → ℝ := fun w =>
      f (stoch_to_det.SharedRace.clockArgmin r w.1)
        (w.1 (stoch_to_det.SharedRace.clockArgmin r w.1),
         w.2 (stoch_to_det.SharedRace.clockArgmin r w.1))
    Integrable selected ρ ∧
      (∫ w, selected w ∂ρ) =
        ∑ i, r i * (∫ t, (∫ ξ, f i (r i * t, ξ) ∂ν) ∂expOne) := by
  dsimp only
  let : MeasurableSpace κ := ⊤
  let νκ : Measure (κ → Ξ) := Measure.pi (fun _ : κ => ν)
  let ρ := (stoch_to_det.clockLaw κ).prod νκ
  let : IsProbabilityMeasure νκ := by dsimp [νκ]; infer_instance
  let : ∀ _ : κ, IsProbabilityMeasure expOne := fun _ => inferInstance
  let W : (κ → ℝ) → κ := stoch_to_det.SharedRace.clockArgmin r
  let selected : (κ → ℝ) × (κ → Ξ) → ℝ := fun w => f (W w.1) (w.1 (W w.1), w.2 (W w.1))
  let F : κ → ℝ → ℝ := fun i t => ∫ ξ, f i (t, ξ) ∂ν
  have hW : Measurable W := stoch_to_det.SharedRace.measurable_clockArgmin r
  have hpClock (i : κ) : MeasurePreserving (Function.eval i)
      (stoch_to_det.clockLaw κ) expOne := by
    simpa only [stoch_to_det.clockLaw, expOne] using
      (measurePreserving_eval (fun _ : κ => expOne) i)
  have hpAppend (i : κ) : MeasurePreserving (Function.eval i) νκ ν := by
    exact measurePreserving_eval (fun _ : κ => ν) i
  have hcoordInt (i : κ) : Integrable
      (fun w : (κ → ℝ) × (κ → Ξ) => f i (w.1 i, w.2 i)) ρ := by
    simpa only [Function.comp_def, Prod.map] using
      ((hpClock i).prod (hpAppend i)).integrable_comp_of_integrable (hfint i)
  have htermInt (i : κ) : Integrable
      (fun w : (κ → ℝ) × (κ → Ξ) => if W w.1 = i then f i (w.1 i, w.2 i) else 0) ρ := by
    have hs : MeasurableSet {w : (κ → ℝ) × (κ → Ξ) | W w.1 = i} :=
      (measurableSet_singleton i).preimage (hW.comp measurable_fst)
    apply ((hcoordInt i).indicator hs).congr
    filter_upwards [] with w
    by_cases hw : W w.1 = i <;> simp [Set.indicator, hw]
  have hselectedInt : Integrable selected ρ := by
    have hsum := integrable_finsetSum (Finset.univ : Finset κ) (fun i _ => htermInt i)
    apply hsum.congr
    filter_upwards [] with w
    simp [selected]
  have hFmeas (i : κ) : Measurable (F i) :=
    (hfmeas i).stronglyMeasurable.integral_prod_right'.measurable
  have hinner (E : κ → ℝ) :
      (∫ D : κ → Ξ, selected (E,D) ∂νκ) = F (W E) (E (W E)) := by
    let g : Ξ → ℝ := fun ξ => f (W E) (E (W E), ξ)
    have hg : Measurable g := (hfmeas (W E)).comp measurable_prodMk_left
    change (∫ D : κ → Ξ, g (D (W E)) ∂νκ) = ∫ ξ, g ξ ∂ν
    rw [← (hpAppend (W E)).map_eq]
    exact (integral_map (hpAppend (W E)).measurable.aemeasurable hg.aestronglyMeasurable).symm
  have hselectedFInt : Integrable (fun E : κ → ℝ => F (W E) (E (W E)))
      (stoch_to_det.clockLaw κ) := by
    apply hselectedInt.integral_prod_left.congr
    filter_upwards [] with E
    exact hinner E
  refine ⟨hselectedInt, ?_⟩
  change (∫ w, selected w ∂ρ) = _
  rw [integral_prod _ hselectedInt]
  simp_rw [hinner]
  rw [stoch_to_det.integral_clock_eq_sum_strictClockWin r hrpos hrtotal _ hselectedFInt]
  apply Finset.sum_congr rfl
  intro i _
  let g : (κ → ℝ) → ℝ := fun V => F i (r i * V i)
  have hg : Measurable g :=
    (hFmeas i).comp (measurable_const.mul (measurable_pi_apply i))
  calc
    (∫ E : κ → ℝ, F (W E) (E (W E))
        ∂(stoch_to_det.clockLaw κ).restrict {E | stoch_to_det.strictClockWin r i E}) =
        ∫ E : κ → ℝ, g (stoch_to_det.winnerResidualClock r i E)
          ∂(stoch_to_det.clockLaw κ).restrict {E | stoch_to_det.strictClockWin r i E} := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (stoch_to_det.strictClockWin_measurableSet r i)] with E hE
      have hwin : W E = i := stoch_to_det.clockArgmin_eq_of_strictClockWin r E i hE
      rw [hwin]
      dsimp only [g]
      rw [stoch_to_det.winnerResidualClock_apply_winner]
      congr 1
      field_simp [(hrpos i).ne']
    _ = r i * ∫ V : κ → ℝ, g V ∂stoch_to_det.clockLaw κ :=
      stoch_to_det.integral_comp_winnerResidualClock r hrpos hrtotal i g hg
    _ = r i * ∫ t, F i (r i * t) ∂expOne := by
      congr 1
      have hgscalar : Measurable (fun t : ℝ => F i (r i * t)) :=
        (hFmeas i).comp (measurable_const.mul measurable_id)
      rw [← (hpClock i).map_eq]
      exact (integral_map (hpClock i).measurable.aemeasurable hgscalar.aestronglyMeasurable).symm
    _ = _ := rfl

/-- Mean of the explicit totalized appended mass at one fixed positive clock. -/
lemma race_selected_logmass_inner
    (a π t : ℝ) (hπ : 0 < π) (ht : 0 < t)
    (hgain : Integrable (fun D => Real.log (1 + Vtail a t D)) arrivalLaw) :
    (∫ D, Real.log (π^a * t^(-a) * (1 + max 0 (Vtail a t D))) ∂arrivalLaw) =
      a * Real.log π - a * Real.log t + m a t := by
  have hpoint : (fun D => Real.log (π^a * t^(-a) * (1 + max 0 (Vtail a t D)))) =ᵐ[arrivalLaw]
      fun D => (a * Real.log π - a * Real.log t) + Real.log (1 + Vtail a t D) := by
    filter_upwards [race_arrival_ae_nonneg] with D hD
    have hV := race_Vtail_nonneg_of_nonneg a t ht.le D hD
    have hone : 0 < 1 + Vtail a t D := by linarith
    rw [max_eq_right hV,
      Real.log_mul (mul_pos (Real.rpow_pos_of_pos hπ a) (Real.rpow_pos_of_pos ht (-a))).ne' hone.ne',
      Real.log_mul (Real.rpow_pos_of_pos hπ a).ne' (Real.rpow_pos_of_pos ht (-a)).ne',
      Real.log_rpow hπ a, Real.log_rpow ht (-a)]
    ring
  rw [integral_congr_ae hpoint, integral_add (integrable_const _) hgain]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  rfl

/-- Exact selected-log identity, with only measurable/integrable coordinate
log mass and gain assumptions. This isolates winner conditioning from the
countable-arrival normalizer and Gamma price evaluation. -/
lemma race_selected_appended_log_mean
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (a : ℝ) (ha : 1 < a) (π r : κ → ℝ)
    (hπpos : ∀ i, 0 < π i) (hr : stoch_to_det.IsPMF r) (hrpos : ∀ i, 0 < r i) :
    let ν : Measure (κ → ℕ → ℝ) := Measure.pi (fun _ : κ => arrivalLaw)
    let ρ := (stoch_to_det.clockLaw κ).prod ν
    let S : (κ → ℝ) × (κ → ℕ → ℝ) → κ → ℝ := fun w i =>
      (π i)^a * (w.1 i)^(-a) * (1 + max 0 (Vtail a (w.1 i) (w.2 i)))
    Integrable (fun w => Real.log (S w (stoch_to_det.SharedRace.clockArgmin r w.1))) ρ ∧
      (∫ w, Real.log (S w (stoch_to_det.SharedRace.clockArgmin r w.1)) ∂ρ) =
        -a * (∑ i, r i * Real.log (r i / π i)) + a * Real.eulerMascheroniConstant +
          ∑ i, r i * (∫ t, m a (r i * t) ∂expOne) := by
  dsimp only
  let f : κ → ℝ × (ℕ → ℝ) → ℝ := fun i tD =>
    Real.log ((π i)^a * tD.1^(-a) * (1 + max 0 (Vtail a tD.1 tD.2)))
  have hmeas (i : κ) : Measurable (f i) := by
    have hscaled : Measurable (fun z : ℝ × (ℕ → ℝ) =>
        (π i)^a * (z.1 ^ (-a) * (1 + max 0 (Vtail a z.1 z.2)))) :=
      measurable_const.mul (race_measurable_unit_mass a)
    simpa only [f, mul_assoc, Function.comp_def] using
      (Real.measurable_log.comp hscaled)
  have hint (i : κ) : Integrable (f i) (expOne.prod arrivalLaw) := by
    have hunitlog := race_unit_log_integrable a ha
    apply ((integrable_const (a * Real.log (π i))).add hunitlog).congr
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae race_scalar_exp_ae_pos]
      with z hz
    have hmass : 0 < z.1 ^ (-a) * (1 + max 0 (Vtail a z.1 z.2)) :=
      mul_pos (Real.rpow_pos_of_pos hz (-a)) (by
        linarith [le_max_left (0 : ℝ) (Vtail a z.1 z.2)])
    dsimp only [Pi.add_apply, f]
    rw [mul_assoc, Real.log_mul
      (Real.rpow_pos_of_pos (hπpos i) a).ne'
      hmass.ne', Real.log_rpow (hπpos i) a]
  have hgainSection (t : ℝ) (ht : 0 < t) :=
    race_gain_sections_of_unit_log_integrable a ha t ht.le
  have hgainScaled (i : κ) := race_scaled_m_integrable_of_unit_log a ha (r i)
    (hr.nonneg i) (stoch_to_det.SharedRace.pmf_apply_le_one hr i)
  have hrtotal : ∑ i, r i = 1 := by simpa [stoch_to_det.mass] using hr.total
  have he := race_selected_coordinate_average arrivalLaw r hrpos hrtotal f hmeas hint
  dsimp only at he
  refine ⟨he.1, ?_⟩
  rw [he.2]
  have hlogInt : Integrable Real.log expOne := race_scalar_exp_log_integrable_mean.1
  have hlogMean : (∫ t, Real.log t ∂expOne) = -Real.eulerMascheroniConstant :=
    race_scalar_exp_log_integrable_mean.2
  have hmean (i : κ) :
      (∫ t, (∫ D, f i (r i * t,D) ∂arrivalLaw) ∂expOne) =
        a * Real.log (π i) - a * Real.log (r i) + a * Real.eulerMascheroniConstant +
          ∫ t, m a (r i * t) ∂expOne := by
    have hpoint : (fun t => ∫ D, f i (r i * t,D) ∂arrivalLaw) =ᵐ[expOne]
        fun t => (a * Real.log (π i) - a * Real.log (r i)) - a * Real.log t + m a (r i * t) := by
      filter_upwards [race_scalar_exp_ae_pos] with t ht
      have hrt : 0 < r i * t := mul_pos (hrpos i) ht
      change (∫ D, Real.log ((π i)^a * (r i * t)^(-a) *
        (1 + max 0 (Vtail a (r i * t) D))) ∂arrivalLaw) = _
      rw [race_selected_logmass_inner a (π i) (r i * t) (hπpos i) hrt
        (hgainSection _ hrt), Real.log_mul (hrpos i).ne' ht.ne']
      ring
    rw [integral_congr_ae hpoint]
    have hbase : Integrable (fun t : ℝ =>
        (a * Real.log (π i) - a * Real.log (r i)) - a * Real.log t) expOne :=
      (integrable_const _).sub (hlogInt.const_mul a)
    rw [integral_add hbase (hgainScaled i),
      integral_sub (f := fun _ : ℝ => a * Real.log (π i) - a * Real.log (r i))
        (g := fun t : ℝ => a * Real.log t) (integrable_const _) (hlogInt.const_mul a),
      integral_const_mul, hlogMean]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    ring
  simp_rw [hmean]
  calc
    (∑ i, r i * (a * Real.log (π i) - a * Real.log (r i) +
        a * Real.eulerMascheroniConstant + ∫ t, m a (r i * t) ∂expOne)) =
      -a * (∑ i, r i * Real.log (r i / π i)) +
        (∑ i, r i) * (a * Real.eulerMascheroniConstant) +
        ∑ i, r i * (∫ t, m a (r i * t) ∂expOne) := by
      rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.log_div (hrpos i).ne' (hπpos i).ne']
      ring
    _ = _ := by rw [hrtotal, one_mul]

/-- Scaling each iid stable mass by π_i^a preserves its stable law when
π is a PMF, because (π_i^a)^(1/a)=π_i. -/
lemma race_superposition_pi_laplace
    {κ Ω : Type} [Fintype κ] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Ω → ℝ) (a : ℝ) (ha : 0 < a)
    (π : κ → ℝ) (hπ : stoch_to_det.IsPMF π) (hπpos : ∀ i, 0 < π i)
    (G : ℝ)
    (hLaplace : ∀ v, 0 < v → (∫ ω, Real.exp (-(v * R ω)) ∂μ) =
      Real.exp (-(G * v^(1/a))))
    (v : ℝ) (hv : 0 < v) :
    (∫ ω : κ → Ω, Real.exp (-(v * ∑ i, (π i)^a * R (ω i)))
      ∂Measure.pi (fun _ : κ => μ)) = Real.exp (-(G * v^(1/a))) := by
  classical
  let : ∀ _ : κ, SigmaFinite μ := fun _ => inferInstance
  have hscale (i : κ) : (v * (π i)^a)^(1/a) = v^(1/a) * π i := by
    rw [Real.mul_rpow hv.le (Real.rpow_nonneg (hπpos i).le a),
      ← Real.rpow_mul (hπpos i).le]
    rw [show a * (1/a) = 1 by field_simp [ha.ne'], Real.rpow_one]
  have hpoint (ω : κ → Ω) :
      Real.exp (-(v * ∑ i, (π i)^a * R (ω i))) =
        ∏ i, Real.exp (-((v * (π i)^a) * R (ω i))) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hfactor (i : κ) : (∫ ω, Real.exp (-((v * (π i)^a) * R ω)) ∂μ) =
      Real.exp (-(G * (v^(1/a) * π i))) := by
    rw [hLaplace _ (mul_pos hv (Real.rpow_pos_of_pos (hπpos i) a)), hscale]
  have htotal : ∑ i, π i = 1 := by simpa [stoch_to_det.mass] using hπ.total
  calc
    (∫ ω : κ → Ω, Real.exp (-(v * ∑ i, (π i)^a * R (ω i)))
      ∂Measure.pi (fun _ : κ => μ)) =
        ∫ ω : κ → Ω, ∏ i, Real.exp (-((v * (π i)^a) * R (ω i)))
          ∂Measure.pi (fun _ : κ => μ) := by
      exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∏ i, ∫ u : Ω, Real.exp (-((v * (π i)^a) * R u)) ∂μ :=
      integral_fintype_prod_eq_prod
        (μ := fun _ : κ => μ)
        (fun i (u : Ω) => Real.exp (-((v * (π i)^a) * R u)))
    _ = ∏ i, Real.exp (-(G * (v^(1/a) * π i))) :=
      Finset.prod_congr rfl (fun i _ => hfactor i)
    _ = Real.exp (-(G * v^(1/a))) := by
      rw [← Real.exp_sum]
      congr 1
      calc
        (∑ i, -(G * (v^(1/a) * π i))) = -(G * v^(1/a)) * (∑ i, π i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [htotal, mul_one]

lemma race_superposition_clock_append_laplace
    {κ : Type} [Fintype κ]
    (R : ℝ × (ℕ → ℝ) → ℝ) (a : ℝ) (ha : 0 < a)
    (π : κ → ℝ) (hπ : stoch_to_det.IsPMF π) (hπpos : ∀ i, 0 < π i)
    (G : ℝ)
    (hLaplace : ∀ v, 0 < v → (∫ w, Real.exp (-(v * R w)) ∂expOne.prod arrivalLaw) =
      Real.exp (-(G * v^(1/a))))
    (v : ℝ) (hv : 0 < v) :
    (∫ w : (κ → ℝ) × (κ → ℕ → ℝ),
      Real.exp (-(v * ∑ i, (π i)^a * R (w.1 i, w.2 i)))
      ∂(stoch_to_det.clockLaw κ).prod (Measure.pi (fun _ : κ => arrivalLaw))) =
        Real.exp (-(G * v^(1/a))) := by
  let : ∀ _ : κ, IsProbabilityMeasure expOne := fun _ => inferInstance
  let : ∀ _ : κ, IsProbabilityMeasure arrivalLaw := fun _ => inferInstance
  let P := Measure.pi (fun _ : κ => expOne.prod arrivalLaw)
  let ρ := (stoch_to_det.clockLaw κ).prod (Measure.pi (fun _ : κ => arrivalLaw))
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ (ℕ → ℝ) κ
  have hp : MeasurePreserving e P ρ := by
    simpa only [P, ρ, stoch_to_det.clockLaw, expOne] using
      (measurePreserving_arrowProdEquivProdArrow ℝ (ℕ → ℝ) κ
        (fun _ : κ => expOne) (fun _ : κ => arrivalLaw))
  calc
    (∫ w : (κ → ℝ) × (κ → ℕ → ℝ),
        Real.exp (-(v * ∑ i, (π i)^a * R (w.1 i, w.2 i))) ∂ρ) =
      ∫ ω : κ → ℝ × (ℕ → ℝ),
        Real.exp (-(v * ∑ i, (π i)^a * R (ω i))) ∂P := by
      exact (hp.integral_comp' (fun w =>
        Real.exp (-(v * ∑ i, (π i)^a * R (w.1 i, w.2 i))))).symm
    _ = _ := race_superposition_pi_laplace (expOne.prod arrivalLaw) R a ha π hπ hπpos G hLaplace v hv

lemma race_clock_appended_logloss_of_unit_laplace
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (a : ℝ) (ha : 1 < a) (π r : κ → ℝ)
    (hπ : stoch_to_det.IsPMF π) (hπpos : ∀ i, 0 < π i)
    (hr : stoch_to_det.IsPMF r) (hrpos : ∀ i, 0 < r i) :
    let ν : Measure (κ → ℕ → ℝ) := Measure.pi (fun _ : κ => arrivalLaw)
    let ρ := (stoch_to_det.clockLaw κ).prod ν
    let S : (κ → ℝ) × (κ → ℕ → ℝ) → κ → ℝ := fun w i =>
      (π i)^a * (w.1 i)^(-a) * (1 + max 0 (Vtail a (w.1 i) (w.2 i)))
    let Q := fun w i => S w i / ∑ k, S w k
    Integrable (fun w => Real.log (1 / Q w
      (stoch_to_det.SharedRace.clockArgmin r w.1))) ρ ∧
    (∫ w, Real.log (1 / Q w (stoch_to_det.SharedRace.clockArgmin r w.1)) ∂ρ) =
      a * (∑ i, r i * Real.log (r i / π i)) + jET a -
        ∑ i, r i * (∫ t, m a (r i * t) ∂expOne) := by
  classical
  dsimp only
  let ν : Measure (κ → ℕ → ℝ) := Measure.pi (fun _ : κ => arrivalLaw)
  let ρ := (stoch_to_det.clockLaw κ).prod ν
  let R : ℝ × (ℕ → ℝ) → ℝ :=
    fun z => z.1 ^ (-a) * (1 + max 0 (Vtail a z.1 z.2))
  have hunitlog := race_unit_log_integrable a ha
  have hunitLap := fun v hv => race_unit_arrival_laplace a v ha hv
  let S : (κ → ℝ) × (κ → ℕ → ℝ) → κ → ℝ := fun w i =>
    (π i)^a * (w.1 i)^(-a) * (1 + max 0 (Vtail a (w.1 i) (w.2 i)))
  let Q := fun w i => S w i / ∑ k, S w k
  have hRmeas : Measurable R := race_measurable_unit_mass a
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have harg : 0 < 1 - 1/a := by
    have hlt : 1/a < 1 := (div_lt_one ha0).2 ha
    linarith
  have hG : 0 < Real.Gamma (1 - 1/a) := Real.Gamma_pos_of_pos harg
  let : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  let Z : (κ → ℝ) × (κ → ℕ → ℝ) → ℝ := fun w => ∑ i, S w i
  have hSmeas (i : κ) : Measurable (fun w => S w i) := by
    have hpair : Measurable (fun w : (κ → ℝ) × (κ → ℕ → ℝ) => (w.1 i, w.2 i)) :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)
    have hscaled : Measurable (fun w : (κ → ℝ) × (κ → ℕ → ℝ) =>
        (π i)^a * R (w.1 i, w.2 i)) :=
      measurable_const.mul (hRmeas.comp hpair)
    simpa only [S, R, mul_assoc] using hscaled
  have hZmeas : Measurable Z := by
    change Measurable (fun w => ∑ i, S w i)
    exact Finset.measurable_sum (Finset.univ : Finset κ) (fun i _ => hSmeas i)
  have hclockpos : ∀ᵐ w : (κ → ℝ) × (κ → ℕ → ℝ) ∂ρ,
      ∀ i, 0 < w.1 i :=
    Measure.quasiMeasurePreserving_fst.ae
      (stoch_to_det.SharedRace.ae_clockLaw_pos (κ := κ))
  have hZpos : ∀ᵐ w ∂ρ, 0 < Z w := by
    filter_upwards [hclockpos] with w hw
    have hS (i : κ) : 0 < S w i := by
      dsimp only [S]
      apply mul_pos (mul_pos (Real.rpow_pos_of_pos (hπpos i) a)
        (Real.rpow_pos_of_pos (hw i) (-a)))
      linarith [le_max_left (0 : ℝ) (Vtail a (w.1 i) (w.2 i))]
    exact Finset.sum_pos' (fun i _ => (hS i).le)
      ⟨Classical.choice inferInstance, Finset.mem_univ _, hS _⟩
  have hZLap : ∀ v : ℝ, 0 < v →
      (∫ w, Real.exp (-(v * Z w)) ∂ρ) =
        Real.exp (-(Real.Gamma (1 - 1/a) * v ^ (1/a))) := by
    intro v hv
    simpa only [Z, S, R, mul_assoc] using
      (race_superposition_clock_append_laplace R a ha0 π hπ hπpos
        (Real.Gamma (1 - 1/a)) hunitLap v hv)
  have hα : 0 < 1/a := one_div_pos.mpr ha0
  have hnormInt : Integrable (fun w => Real.log (∑ i, S w i)) ρ :=
    race_scalar_log_integrable_of_stable_laplace ρ Z hZmeas hZpos
      (1/a) (Real.Gamma (1 - 1/a)) hα hG hZLap
  have hnormMean : (∫ w, Real.log (∑ i, S w i) ∂ρ) =
      a * Real.log (Real.Gamma (1 - 1/a)) +
        (a - 1) * Real.eulerMascheroniConstant := by
    have hstable := race_scalar_log_mean_of_stable_laplace
      ρ Z hZmeas hZpos hnormInt
      (1/a) (Real.Gamma (1 - 1/a)) hα hG hZLap
    change (∫ w, Real.log (Z w) ∂ρ) = _
    rw [hstable]
    field_simp [ha0.ne']
  have hselected := race_selected_appended_log_mean a ha π r hπpos hr hrpos
  dsimp only at hselected
  have hselectedInt : Integrable (fun w =>
      Real.log (S w (stoch_to_det.SharedRace.clockArgmin r w.1))) ρ := hselected.1
  have hselectedMean : (∫ w, Real.log (S w
      (stoch_to_det.SharedRace.clockArgmin r w.1)) ∂ρ) =
      -a * (∑ i, r i * Real.log (r i / π i)) + a * Real.eulerMascheroniConstant +
        ∑ i, r i * (∫ t, m a (r i * t) ∂expOne) := hselected.2
  have hLossEq : (fun w => Real.log (1 / Q w
      (stoch_to_det.SharedRace.clockArgmin r w.1))) =ᵐ[ρ]
      fun w => Real.log (∑ i, S w i) -
        Real.log (S w (stoch_to_det.SharedRace.clockArgmin r w.1)) := by
    filter_upwards [hclockpos] with w hw
    have hS (i : κ) : 0 < S w i := by
      dsimp only [S]
      apply mul_pos (mul_pos (Real.rpow_pos_of_pos (hπpos i) a)
        (Real.rpow_pos_of_pos (hw i) (-a)))
      linarith [le_max_left (0 : ℝ) (Vtail a (w.1 i) (w.2 i))]
    have hsum : 0 < ∑ i, S w i :=
      Finset.sum_pos' (fun i _ => (hS i).le)
        ⟨Classical.choice inferInstance, Finset.mem_univ _, hS _⟩
    dsimp only [Q]
    rw [one_div, Real.log_inv, Real.log_div (hS _).ne' hsum.ne']
    ring
  refine ⟨(hnormInt.sub hselectedInt).congr hLossEq.symm, ?_⟩
  rw [integral_congr_ae hLossEq, integral_sub hnormInt hselectedInt,
    hnormMean, hselectedMean,
    race_gamma_price_of_unit_laplace a ha hRmeas hunitlog hunitLap]
  unfold j
  ring

/-- The exponential/Gumbel map transports the proved clock loss to the original-seed expression,
including the exact lexicographic winner. -/
lemma race_appended_logloss_of_unit_laplace
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (a : ℝ) (ha : 1 < a) (π : κ → ℝ)
    (hπ : stoch_to_det.IsPMF π) (hπpos : ∀ i, 0 < π i)
    (r : κ → ℝ) (hr : stoch_to_det.IsPMF r) (hrpos : ∀ i, 0 < r i)
    :
    let ν : Measure (κ → ℕ → ℝ) := Measure.pi (fun _ : κ => arrivalLaw)
    let ρ := (stoch_to_det.seedLaw κ).prod ν
    let S : (κ → ℝ) × (κ → ℕ → ℝ) → κ → ℝ := fun w i =>
      (π i)^a * (Real.exp (-w.1 i))^(-a) *
        (1 + max 0 (Vtail a (Real.exp (-w.1 i)) (w.2 i)))
    let Q := fun w i => S w i / ∑ k, S w k
    Integrable (fun w => Real.log (1 / Q w
      (stoch_to_det.SharedRace.weightedLexWinner r w.1))) ρ ∧
    (∫ w, Real.log (1 / Q w (stoch_to_det.SharedRace.weightedLexWinner r w.1)) ∂ρ) =
      a * (∑ i, r i * Real.log (r i / π i)) + jET a -
        ∑ i, r i * (∫ t, m a (r i * t) ∂expOne) := by
  classical
  dsimp only
  let : MeasurableSpace κ := ⊤
  let ν : Measure (κ → ℕ → ℝ) := Measure.pi (fun _ : κ => arrivalLaw)
  let : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  let ρc := (stoch_to_det.clockLaw κ).prod ν
  let ρs := (stoch_to_det.seedLaw κ).prod ν
  let R : ℝ × (ℕ → ℝ) → ℝ :=
    fun z => z.1 ^ (-a) * (1 + max 0 (Vtail a z.1 z.2))
  let Sc : (κ → ℝ) × (κ → ℕ → ℝ) → κ → ℝ := fun w i =>
    (π i)^a * (w.1 i)^(-a) * (1 + max 0 (Vtail a (w.1 i) (w.2 i)))
  let Ss : (κ → ℝ) × (κ → ℕ → ℝ) → κ → ℝ := fun w i =>
    (π i)^a * (Real.exp (-w.1 i))^(-a) *
      (1 + max 0 (Vtail a (Real.exp (-w.1 i)) (w.2 i)))
  let Qc := fun w i => Sc w i / ∑ k, Sc w k
  let Qs := fun w i => Ss w i / ∑ k, Ss w k
  let Lc : (κ → ℝ) × (κ → ℕ → ℝ) → ℝ := fun w =>
    Real.log (1 / Qc w (stoch_to_det.SharedRace.clockArgmin r w.1))
  let Ls : (κ → ℝ) × (κ → ℕ → ℝ) → ℝ := fun w =>
    Real.log (1 / Qs w (stoch_to_det.SharedRace.weightedLexWinner r w.1))
  have hc := race_clock_appended_logloss_of_unit_laplace
    a ha π r hπ hπpos hr hrpos
  dsimp only at hc
  have hcInt : Integrable Lc ρc := hc.1
  have hcMean : (∫ w, Lc w ∂ρc) =
      a * (∑ i, r i * Real.log (r i / π i)) + jET a -
        ∑ i, r i * (∫ t, m a (r i * t) ∂expOne) := hc.2
  let G : (κ → ℝ) → (κ → ℝ) := fun E i => -Real.log (E i)
  let T : (κ → ℝ) × (κ → ℕ → ℝ) → (κ → ℝ) × (κ → ℕ → ℝ) :=
    Prod.map G id
  have hGmeas : Measurable G :=
    Measurable.of_eval (fun i =>
      (Real.measurable_log.comp (measurable_pi_apply i)).neg)
  have hpG : MeasurePreserving G (stoch_to_det.clockLaw κ) (stoch_to_det.seedLaw κ) :=
    ⟨hGmeas, rfl⟩
  have hpId : MeasurePreserving (id : (κ → ℕ → ℝ) → (κ → ℕ → ℝ)) ν ν :=
    ⟨measurable_id, by simp⟩
  have hpT : MeasurePreserving T ρc ρs := hpG.prod hpId
  have hRmeas : Measurable R := race_measurable_unit_mass a
  have hSsmeas (i : κ) : Measurable (fun w => Ss w i) := by
    have hexp : Measurable (fun w : (κ → ℝ) × (κ → ℕ → ℝ) =>
        Real.exp (-w.1 i)) :=
      Real.measurable_exp.comp (((measurable_pi_apply i).comp measurable_fst).neg)
    have hpair : Measurable (fun w : (κ → ℝ) × (κ → ℕ → ℝ) =>
        (Real.exp (-w.1 i), w.2 i)) :=
      hexp.prodMk ((measurable_pi_apply i).comp measurable_snd)
    have hscaled : Measurable (fun w : (κ → ℝ) × (κ → ℕ → ℝ) =>
        (π i)^a * R (Real.exp (-w.1 i), w.2 i)) :=
      measurable_const.mul (hRmeas.comp hpair)
    simpa only [Ss, R, mul_assoc] using hscaled
  have hSumMeas : Measurable (fun w => ∑ k, Ss w k) :=
    Finset.measurable_sum _ (fun i _ => hSsmeas i)
  have hQsmeas (i : κ) : Measurable (fun w => Qs w i) :=
    (hSsmeas i).div hSumMeas
  have hW : Measurable (stoch_to_det.SharedRace.weightedLexWinner r) := by
    unfold stoch_to_det.SharedRace.weightedLexWinner
    apply stoch_to_det.measurable_lexMax
    intro i
    exact measurable_const.add (measurable_pi_apply i)
  have hterm (i : κ) : Measurable (fun w : (κ → ℝ) × (κ → ℕ → ℝ) =>
      if stoch_to_det.SharedRace.weightedLexWinner r w.1 = i
      then Real.log (1 / Qs w i) else 0) := by
    have hs : MeasurableSet {w : (κ → ℝ) × (κ → ℕ → ℝ) |
        stoch_to_det.SharedRace.weightedLexWinner r w.1 = i} :=
      (measurableSet_singleton i).preimage (hW.comp measurable_fst)
    have hfixed : Measurable (fun w => Real.log (1 / Qs w i)) :=
      Real.measurable_log.comp (measurable_const.div (hQsmeas i))
    exact Measurable.ite hs hfixed measurable_const
  have hLsmeas : Measurable Ls := by
    have hsum := Finset.measurable_sum (Finset.univ : Finset κ) (fun i _ => hterm i)
    convert hsum using 1
    funext w
    simp [Ls]
  have hclockpos : ∀ᵐ w : (κ → ℝ) × (κ → ℕ → ℝ) ∂ρc,
      ∀ i, 0 < w.1 i :=
    Measure.quasiMeasurePreserving_fst.ae
      (stoch_to_det.SharedRace.ae_clockLaw_pos (κ := κ))
  have hLossEq : Ls ∘ T =ᵐ[ρc] Lc := by
    filter_upwards [hclockpos] with w hw
    have hmass (i : κ) : Ss (T w) i = Sc w i := by
      dsimp only [Ss, Sc, T, Prod.map, G, id_eq]
      simp only [neg_neg, Real.exp_log (hw i)]
    have hQ (i : κ) : Qs (T w) i = Qc w i := by
      dsimp only [Qs, Qc]
      simp_rw [hmass]
    have hwin : stoch_to_det.SharedRace.weightedLexWinner r (T w).1 =
        stoch_to_det.SharedRace.clockArgmin r w.1 :=
      by
        change stoch_to_det.SharedRace.weightedLexWinner r
          (fun i => -Real.log (w.1 i)) = stoch_to_det.SharedRace.clockArgmin r w.1
        exact stoch_to_det.SharedRace.weightedLexWinner_clock_eq_argmin r w.1 hrpos hw
    change Real.log (1 / Qs (T w)
      (stoch_to_det.SharedRace.weightedLexWinner r (T w).1)) = _
    rw [hwin, hQ]
  have hsInt : Integrable Ls ρs :=
    (hpT.integrable_comp hLsmeas.aestronglyMeasurable).mp
      (hcInt.congr hLossEq.symm)
  refine ⟨hsInt, ?_⟩
  change (∫ w, Ls w ∂ρs) = _
  calc
    (∫ w, Ls w ∂ρs) = ∫ w, Ls (T w) ∂ρc := by
      rw [← hpT.map_eq]
      exact integral_map_of_stronglyMeasurable (μ := ρc)
        hpT.measurable hLsmeas.stronglyMeasurable
    _ = ∫ w, Lc w ∂ρc := integral_congr_ae hLossEq
    _ = _ := hcMean

lemma race_gain_average (a : ℝ) (ha : 1 < a) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    r * j a ≤ ∫ t, m a (r * t) ∂expOne := by
  have hscale : Integrable (fun t => m a (r * t)) expOne ∧
      ∀ t, 0 ≤ t → r * m a t ≤ m a (r * t) := by
    refine ⟨race_scaled_m_integrable_of_unit_log a ha r hr0 hr1, ?_⟩
    intro t ht
    exact race_gain_scaling_of_shifted_transform a ha t r ht hr0 hr1
  have hint : Integrable (m a) expOne := by
    simpa using race_scaled_m_integrable_of_unit_log a ha 1 (by norm_num) (by norm_num)
  have hpos : ∀ᵐ t ∂expOne, 0 ≤ t := by
    have he : expOne (Set.Iic 0) = 0 := stoch_to_det.expMeasure_one_Iic_zero
    have hn := measure_eq_zero_iff_ae_notMem.mp he
    filter_upwards [hn] with t ht
    exact (lt_of_not_ge ht).le
  have hle : (∫ t, r * m a t ∂expOne) ≤ ∫ t, m a (r * t) ∂expOne := by
    apply integral_mono_ae (hint.const_mul r) hscale.1
    filter_upwards [hpos] with t ht
    exact hscale.2 t ht
  rw [integral_const_mul] at hle
  change r * jET a ≤ _ at hle
  rwa [race_gamma_price a ha] at hle

lemma race_reference_loss_bound {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (a : ℝ) (ha : 1 < a) (π : κ → ℝ)
    (hπ : stoch_to_det.IsPMF π) (hπpos : ∀ i, 0 < π i)
    (r : κ → ℝ) (hr : stoch_to_det.IsPMF r) (hrpos : ∀ i, 0 < r i) :
    let ν : Measure (κ → ℕ → ℝ) := Measure.pi (fun _ : κ => arrivalLaw)
    let ρ := (stoch_to_det.seedLaw κ).prod ν
    let S : (κ → ℝ) × (κ → ℕ → ℝ) → κ → ℝ := fun w i =>
      (π i)^a * (Real.exp (-w.1 i))^(-a) *
        (1 + max 0 (Vtail a (Real.exp (-w.1 i)) (w.2 i)))
    let Q := fun w i => S w i / ∑ k, S w k
    Integrable (fun w =>
      Real.log (1 / Q w (stoch_to_det.SharedRace.weightedLexWinner r w.1))) ρ ∧
    (∫ w, Real.log (1 / Q w (stoch_to_det.SharedRace.weightedLexWinner r w.1)) ∂ρ) ≤
      a * (∑ i, r i * Real.log (r i / π i)) + j a * (1 - ∑ i, (r i)^2) := by
  dsimp only
  have he := race_appended_logloss_of_unit_laplace a ha π hπ hπpos r hr hrpos
  dsimp only at he
  refine ⟨he.1, ?_⟩
  rw [he.2, race_gamma_price a ha]
  have hsum : j a * (∑ i, (r i)^2) ≤
      ∑ i, r i * (∫ t, m a (r i * t) ∂expOne) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi := race_gain_average a ha (r i) (hr.nonneg i)
      (stoch_to_det.SharedRace.pmf_apply_le_one hr i)
    have hm := mul_le_mul_of_nonneg_left hi (hr.nonneg i)
    nlinarith only [hm]
  nlinarith only [hsum]

lemma race_single_law {Ω κ : Type} [Fintype Ω] [Fintype κ]
    [DecidableEq Ω] [DecidableEq κ] [Nonempty κ]
    (a : ℝ) (ha : 1 < a) {μ : Ω → ℝ} {r : Ω → κ → ℝ}
    (hμ : stoch_to_det.IsPMF μ)
    (hr : ∀ z, μ z ≠ 0 → stoch_to_det.IsPMF (r z))
    (hrpos : ∀ z, μ z ≠ 0 → ∀ i, 0 < r z i) :
    stoch_to_det.SharedRace.sharedRaceEntropy μ r ≤
      a * stoch_to_det.MI Prod.fst Prod.snd (stoch_to_det.SharedRace.posteriorJoint μ r) +
      (j a / Real.log 2) * stoch_to_det.SharedRace.categoricalMismatch μ r := by
  let π := stoch_to_det.SharedRace.posteriorMean μ r
  have hπ := stoch_to_det.SharedRace.posteriorMean_isPMF_of_support hμ hr
  have hπpos := stoch_to_det.SharedRace.posteriorMean_pos_of_support hμ hrpos
  let ν : Measure (κ → ℕ → ℝ) := Measure.pi (fun _ : κ => arrivalLaw)
  let : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  let S : (κ → ℝ) × (κ → ℕ → ℝ) → κ → ℝ := fun w i =>
    (π i)^a * (Real.exp (-w.1 i))^(-a) *
      (1 + max 0 (Vtail a (Real.exp (-w.1 i)) (w.2 i)))
  let Q := fun w i => S w i / ∑ k, S w k
  have hQ : ∀ᵐ w ∂(stoch_to_det.seedLaw κ).prod ν,
      stoch_to_det.IsPMF (Q w) ∧ ∀ i, 0 < Q w i := by
    filter_upwards [] with w
    exact race_reference_isPMF π hπpos a w
  have hrow (z : Ω) (hz : μ z ≠ 0) :=
    race_reference_loss_bound a ha π hπ hπpos (r z) (hr z hz) (hrpos z hz)
  have hn := race_entropy_from_reference ν a (j a) hμ hr hrpos Q hQ
    (fun z hz => (hrow z hz).1) (fun z hz => (hrow z hz).2)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (mul_le_mul_iff_of_pos_left hlog).mp
  convert hn using 1 ; first | rfl | field_simp [hlog.ne']

/-- The exponential race: for `a > 1`, a latent with positive prior and positive posterior rows has a
calibrated seeded family `F` with `h F ≤ a * B L + 2 * j a * d L`. -/
theorem exists_race {p : Law X Y} (hp : stoch_to_det.IsPMF p) (L : FiniteLatent p)
    (hrows : ∀ z ∈ stoch_to_det.support p, ∀ i, 0 < post L i z)
    (a : ℝ) (ha : 1 < a) : ∃ F : CalibratedSeededFamily L, h F ≤ a*B L + 2*j a*d L := by
  obtain ⟨F, hF⟩ := race_of_single_law hp L hrows a (j a / Real.log 2)
    (fun μ r hμ hr hrpos => race_single_law a ha hμ hr hrpos)
  refine ⟨F, ?_⟩
  have hc : Real.log 2 * (j a / Real.log 2) = j a := by
    field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  simpa only [hc] using hF

end

end NaturalLatents.General
