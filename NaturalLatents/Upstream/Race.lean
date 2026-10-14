-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/Race.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised; proofs shortened.
-- Source: the main branch and the shared-race/contact additions of pull request #5 by Satya Benson, as included in pull request #6 by Jeremy Gillen.
-- Local changes: Added clockReindex_law and reorganised the clock-law and residual-clock helper chain; retained required public clock-race lemmas.
import NaturalLatents.Upstream.Scalar
import NaturalLatents.Upstream.SharedRace.Definitions
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
import NaturalLatents.Upstream.SharedRace.Clock
import NaturalLatents.Upstream.SharedRace.Information
import NaturalLatents.Upstream.SharedRace.PairClockLaw
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# Construction of the race quantities

This file constructs `RaceQuantities` from a `SeedSetup` and `Clustering`.
It proves the exponential-clock conditioning and factorization identities,
the scalar and losing-vector estimates, and the fixed-seed residual bound used
by the final table inequality.
-/

namespace stoch_to_det

universe u

open Finset MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-! ### Concrete realizations of the four quantities

The continuous informations are written in the finite-context KL form exposed
by `condMIcts`.  In both cases the final measure argument is the *true*
conditional mixture of the source laws, not an arbitrary reference measure.
-/

/-! #### The exact duplicate grouping

`clusterFiber K c` is the set of labels in cluster `c`.  The grouped seed is
the within-fibre maximum of `log π + ε`; subtracting that maximum from every
coordinate records the within-cluster winner and all excesses, so no seed
information is discarded.
-/

/-! #### The conditional losing-clock channel

The cone calculation keeps the whole losing vector intact.  At fixed
`(g,b,u,z)` its law is a product of shifted unit exponentials; the marginal
below is again the true source mixture used by the golden formula.
-/

/-! ### Elementary positivity and definitional identities -/

/-! ### Finiteness of the KL expansions

Only positive-mass summands need a finiteness assertion; all remaining
summands have zero coefficient in `condMIcts`.
-/

/-! ### Exact race-law components -/

/- The `Seed` race calibration is phrased for a `SeedSetup`.  The
cluster race only needs its underlying finite positive-weight theorem, which
we derive here from the same public exponential-clock API. -/

private noncomputable def weightedValue {κ : Type}
    (t : κ → ℝ) (G : κ → ℝ) (c : κ) : ℝ :=
  Real.log (t c) + G c

private noncomputable def weightedLexWinner {κ : Type} [Fintype κ]
    [DecidableEq κ] [Nonempty κ] (t : κ → ℝ) (G : κ → ℝ) : κ :=
  lexMax (fun G c => weightedValue t G c) G

private lemma expMeasure_one_tilt {t : ℝ} (ht : 0 < t) :
    (expMeasure 1).withDensity
        (fun y => ENNReal.ofReal
          (Real.exp (-((1 / t - 1) * y)))) =
      ENNReal.ofReal t • expMeasure (1 / t) := by
  have hpdf (r : ℝ) : Measurable (gammaPDF 1 r) := by
    unfold gammaPDF
    exact ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 r)
  have hweight : Measurable
      (fun y : ℝ => ENNReal.ofReal
        (Real.exp (-((1 / t - 1) * y)))) := by fun_prop
  unfold expMeasure gammaMeasure
  rw [← withDensity_mul volume (hpdf 1) hweight,
    ← withDensity_smul (μ := volume) (ENNReal.ofReal t) (hpdf (1 / t))]
  apply withDensity_congr_ae
  filter_upwards [] with y
  rw [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  simp only [gammaPDF_eq, Real.rpow_one, Real.Gamma_one, div_one,
    sub_self, Real.rpow_zero, mul_one, one_mul]
  by_cases hy : 0 ≤ y
  · simp only [ite_eq_left hy]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),
      ← ENNReal.ofReal_mul ht.le]
    congr 1
    rw [← Real.exp_add]
    field_simp [ht.ne']
    ring_nf
  · simp [ite_eq_right hy]

private lemma map_div_expMeasure {t : ℝ} (ht : 0 < t) :
    Measure.map (fun x : ℝ => x / t) (expMeasure (1 / t)) =
      expMeasure 1 := by
  let : IsProbabilityMeasure (expMeasure (1 / t)) :=
    isProbabilityMeasure_expMeasure (one_div_pos.mpr ht)
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let : IsProbabilityMeasure
      (Measure.map (fun x : ℝ => x / t) (expMeasure (1 / t))) :=
    inferInstance
  apply Measure.eq_of_cdf
  ext x
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def,
    Measure.map_apply (f := fun y : ℝ => y / t)
      (measurable_id.div_const t) measurableSet_Iic]
  rw [show (fun y : ℝ => y / t) ⁻¹' Set.Iic x = Set.Iic (t * x) by
    ext y
    simp only [Set.mem_preimage, Set.mem_Iic]
    exact (div_le_iff₀ ht).trans (by ring_nf)]
  rw [← ofReal_cdf (expMeasure (1 / t)) (t * x),
    ← ofReal_cdf (expMeasure 1) x,
    ENNReal.toReal_ofReal (cdf_nonneg _ _),
    ENNReal.toReal_ofReal (cdf_nonneg _ _)]
  rw [cdf_expMeasure_eq (one_div_pos.mpr ht), cdf_expMeasure_eq zero_lt_one]
  by_cases hx : 0 ≤ x
  · rw [ite_eq_left hx, ite_eq_left (mul_nonneg ht.le hx)]
    congr 2
    field_simp [ht.ne']
  · have htx : ¬ 0 ≤ t * x := by nlinarith
    rw [ite_eq_right hx, ite_eq_right htx]

/- Scaling and memorylessness in the orientation used by the within-cluster
excess vector. -/
private lemma map_mul_expMeasure {t : ℝ} (ht : 0 < t) :
    Measure.map (fun x : ℝ => t * x) (expMeasure t) = expMeasure 1 := by
  simpa [div_eq_mul_inv, ht.ne', mul_comm] using
    (map_div_expMeasure (t := 1 / t) (one_div_pos.mpr ht))

private lemma map_div_expMeasure_one {t : ℝ} (ht : 0 < t) :
    Measure.map (fun x : ℝ => x / t) (expMeasure 1) = expMeasure t := by
  rw [← map_mul_expMeasure ht,
    Measure.map_map (g := fun x : ℝ => x / t) (f := fun x : ℝ => t * x)
      (by fun_prop) (by fun_prop)]
  have : ((fun x : ℝ => x / t) ∘ fun x : ℝ => t * x) = id := by
    funext x
    simp [Function.comp, ht.ne']
  rw [this, Measure.map_id]

private lemma map_sub_restrict_expMeasure_one {a : ℝ} (ha : 0 ≤ a) :
    Measure.map (fun x : ℝ => x - a)
        ((expMeasure 1).restrict (Set.Ioi a)) =
      ENNReal.ofReal (Real.exp (-a)) • expMeasure 1 := by
  let ν : Measure ℝ := expMeasure 1
  let : IsProbabilityMeasure ν :=
    isProbabilityMeasure_expMeasure zero_lt_one
  apply Measure.ext_of_Iic
  intro x
  have hpre : (fun y : ℝ => y - a) ⁻¹' Set.Iic x = Set.Iic (x + a) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Iic, sub_le_iff_le_add]
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic, hpre,
    Measure.restrict_apply measurableSet_Iic,
    Measure.smul_apply, smul_eq_mul]
  by_cases hx : 0 ≤ x
  · have hxa : a ≤ x + a := by linarith
    have hxapos : 0 ≤ x + a := ha.trans hxa
    have hIoc : ν (Set.Ioc a (x + a)) =
        ENNReal.ofReal (cdf ν (x + a) - cdf ν a) := by
      simpa only [measure_cdf] using (cdf ν).measure_Ioc a (x + a)
    rw [Set.inter_comm (Set.Iic (x + a)), Set.Ioi_inter_Iic,
      hIoc, ← ofReal_cdf ν x]
    dsimp [ν]
    rw [cdf_expMeasure_eq zero_lt_one,
      cdf_expMeasure_eq zero_lt_one,
      cdf_expMeasure_eq zero_lt_one]
    simp only [ite_eq_left hxapos, ite_eq_left ha, ite_eq_left hx, one_mul]
    have hnonneg : 0 ≤ 1 - Real.exp (-x) :=
      sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg (-a))]
    congr 1
    rw [show -(x + a) = -a + -x by ring, Real.exp_add]
    ring
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hnot : ¬a < x + a := by linarith
    rw [Set.inter_comm (Set.Iic (x + a)), Set.Ioi_inter_Iic,
      Set.Ioc_eq_empty hnot, measure_empty, ← ofReal_cdf ν x]
    dsimp [ν]
    rw [cdf_expMeasure_eq zero_lt_one, ite_eq_right (not_le.mpr hxneg)]
    simp

private lemma map_scaled_excess_restrict_expMeasure_one
    {t u : ℝ} (ht : 0 < t) (hu : 0 ≤ u) :
    Measure.map (fun x : ℝ => x / t - u)
        ((expMeasure 1).restrict (Set.Ioi (t * u))) =
      ENNReal.ofReal (Real.exp (-(t * u))) • expMeasure t := by
  have hcomp : (fun x : ℝ => x / t - u) =
      (fun y : ℝ => y / t) ∘ (fun x : ℝ => x - t * u) := by
    funext x
    dsimp only [Function.comp_apply]
    field_simp [ht.ne']
  rw [hcomp, ← Measure.map_map (g := fun y : ℝ => y / t)
      (f := fun x : ℝ => x - t * u) (measurable_id.div_const t)
      (measurable_id.sub_const (t * u)),
    map_sub_restrict_expMeasure_one (mul_nonneg ht.le hu),
    Measure.map_smul (f := fun y : ℝ => y / t) _
      (measurable_id.div_const t).aemeasurable,
    map_div_expMeasure_one ht]

private noncomputable def weightedLosingExcessLaw
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (a : κ) : Measure ({i : κ // i ≠ a} → ℝ) :=
  Measure.pi fun i : {i : κ // i ≠ a} => expMeasure (t i.1)

private lemma map_losing_scaled_excess
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (a : κ)
    {u : ℝ} (hu : 0 ≤ u) :
    Measure.map
        (fun E : {i : κ // i ≠ a} → ℝ =>
          fun i => E i / t i.1 - u)
        ((Measure.pi (fun _ : {i : κ // i ≠ a} => expMeasure 1)).restrict
          (Set.pi Set.univ
            (fun i : {i : κ // i ≠ a} => Set.Ioi (t i.1 * u)))) =
      (∏ i : {i : κ // i ≠ a},
          ENNReal.ofReal (Real.exp (-(t i.1 * u)))) •
        weightedLosingExcessLaw t a := by
  let d : {i : κ // i ≠ a} → ℝ≥0∞ := fun i =>
    ENNReal.ofReal (Real.exp (-(t i.1 * u)))
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let (i : {i : κ // i ≠ a}) : IsProbabilityMeasure
      (expMeasure (t i.1)) := isProbabilityMeasure_expMeasure (ht i.1)
  have hmap :
      Measure.map
          (fun E : {i : κ // i ≠ a} → ℝ =>
            fun i => E i / t i.1 - u)
          (Measure.pi (fun i : {i : κ // i ≠ a} =>
            (expMeasure 1).restrict (Set.Ioi (t i.1 * u)))) =
        Measure.pi (fun i : {i : κ // i ≠ a} =>
          Measure.map (fun x : ℝ => x / t i.1 - u)
            ((expMeasure 1).restrict (Set.Ioi (t i.1 * u)))) := by
    exact Measure.pi_map_pi fun (i : {i : κ // i ≠ a}) =>
      ((measurable_id.div_const (t i.1)).sub_const u).aemeasurable
  have hcoord (i : {i : κ // i ≠ a}) :
      Measure.map (fun x : ℝ => x / t i.1 - u)
          ((expMeasure 1).restrict (Set.Ioi (t i.1 * u))) =
        d i • expMeasure (t i.1) := by
    exact map_scaled_excess_restrict_expMeasure_one (ht i.1) hu
  let (i : {i : κ // i ≠ a}) : IsFiniteMeasure
      (d i • expMeasure (t i.1)) := ⟨by simp [d]⟩
  have hscaled :
      Measure.pi (fun i : {i : κ // i ≠ a} =>
          d i • expMeasure (t i.1)) =
        (∏ i : {i : κ // i ≠ a}, d i) •
          weightedLosingExcessLaw t a := by
    unfold weightedLosingExcessLaw
    apply Measure.pi_eq
    intro s hs
    rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
    simp_rw [Measure.smul_apply, smul_eq_mul]
    rw [Finset.prod_mul_distrib]
  rw [Measure.restrict_pi_pi, hmap]
  simp_rw [hcoord]
  exact hscaled

lemma strictClockWin_measurableSet
    {κ : Type} [Fintype κ]
    (t : κ → ℝ) (a : κ) :
    MeasurableSet {E : κ → ℝ | strictClockWin t a E} := by
  unfold strictClockWin
  measurability

/-- Reassemble a distinguished clock and the remaining coordinates into one
full clock vector. -/
private noncomputable def winnerClockJoin
    {κ : Type} [DecidableEq κ] (a : κ)
    (sr : ℝ × ({i : κ // i ≠ a} → ℝ)) : κ → ℝ :=
  fun i => if h : i = a then sr.1 else sr.2 ⟨i, h⟩

private lemma winnerClockJoin_measurable
    {κ : Type} [Fintype κ] [DecidableEq κ] (a : κ) :
    Measurable (winnerClockJoin a) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i = a
  · simp only [winnerClockJoin, hi, dite_true]
    exact measurable_fst
  · simp only [winnerClockJoin, hi, dite_false]
    exact (measurable_pi_apply (⟨i, hi⟩ : {j : κ // j ≠ a})).comp measurable_snd

private lemma clockReindex_law
    {κ : Type} [Fintype κ] [DecidableEq κ] (a : κ) :
    let e : Option {i : κ // i ≠ a} ≃ κ := Equiv.optionSubtypeNe a
    let f := (MeasurableEquiv.piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => ℝ)).symm
    let g := MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e
    let q := (Measure.pi (fun _ : {i : κ // i ≠ a} => expMeasure 1)).prod
      (expMeasure 1)
    Measure.map (g ∘ f) q = clockLaw κ := by
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let e : Option {i : κ // i ≠ a} ≃ κ := Equiv.optionSubtypeNe a
  let f := (MeasurableEquiv.piOptionEquivProd
    (fun _ : Option {i : κ // i ≠ a} => ℝ)).symm
  let g := MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e
  let q := (Measure.pi (fun _ : {i : κ // i ≠ a} => expMeasure 1)).prod
    (expMeasure 1)
  have hfirst : Measure.map f q =
      Measure.pi (fun _ : Option {i : κ // i ≠ a} => expMeasure 1) := by
    dsimp [f, q]
    exact Measure.pi_map_piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => expMeasure 1)
  have hsecond : Measure.map g
      (Measure.pi (fun _ : Option {i : κ // i ≠ a} => expMeasure 1)) =
      Measure.pi (fun _ : κ => expMeasure 1) := by
    dsimp [g]
    simpa [e] using Measure.pi_map_piCongrLeft e
      (fun _ : κ => expMeasure 1)
  dsimp only
  unfold clockLaw
  rw [← Measure.map_map g.measurable f.measurable, hfirst, hsecond]

private lemma map_eval_restrict_strictClockWin
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) :
    Measure.map (fun E : κ → ℝ => E a)
        ((clockLaw κ).restrict {E | strictClockWin t a E}) =
      ENNReal.ofReal (t a) • expMeasure (1 / t a) := by
  let : ∀ _ : κ, IsProbabilityMeasure (expMeasure 1) :=
    fun _ => isProbabilityMeasure_expMeasure zero_lt_one
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let e : Option {i : κ // i ≠ a} ≃ κ := Equiv.optionSubtypeNe a
  let f := (MeasurableEquiv.piOptionEquivProd
    (fun _ : Option {i : κ // i ≠ a} => ℝ)).symm
  let g := MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e
  let q := (Measure.pi (fun _ : {i : κ // i ≠ a} => expMeasure 1)).prod
    (expMeasure 1)
  have hmap : Measure.map (g ∘ f) q =
      Measure.pi (fun _ : κ => expMeasure 1) := by
    simpa [clockLaw, e, f, g, q] using clockReindex_law a
  have hwin := strictClockWin_measurableSet t a
  have hcoord (xy : ({i : κ // i ≠ a} → ℝ) × ℝ) :
      (g (f xy)) a = xy.2 := by
    have hf_pair := (MeasurableEquiv.piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => ℝ)).apply_symm_apply xy
    have hf_none : f xy none = xy.2 := congrArg Prod.snd hf_pair
    dsimp [g]
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    simp [e, hf_none]
  have hsectionWin (y : ℝ) :
      (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹'
          ((g ∘ f) ⁻¹' {E : κ → ℝ | strictClockWin t a E}) =
        Set.pi Set.univ
          (fun i : {i : κ // i ≠ a} => Set.Ioi (t i.1 / t a * y)) := by
    ext x
    have hf_pair := (MeasurableEquiv.piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => ℝ)).apply_symm_apply (x, y)
    have hf_some (i : {i : κ // i ≠ a}) : f (x, y) (some i) = x i :=
      congrFun (congrArg Prod.fst hf_pair) i
    have hf_none : f (x, y) none = y := congrArg Prod.snd hf_pair
    have he_i (i : {i : κ // i ≠ a}) : (g (f (x, y))) i.1 = x i := by
      dsimp [g]
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
      simp [e, Equiv.optionSubtypeNe_symm_of_ne i.2, hf_some]
    have he_a : (g (f (x, y))) a = y := by
      dsimp [g]
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
      simp [e, hf_none]
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_Ioi]
    constructor
    · intro h i
      have hrel := h i.1 i.2
      change g (f (x, y)) a / t a < g (f (x, y)) i.1 / t i.1 at hrel
      rw [he_a, he_i] at hrel
      rw [div_mul_eq_mul_div, div_lt_iff₀ (ht a)]
      simpa only [mul_comm] using (div_lt_div_iff₀ (ht a) (ht i.1)).1 hrel
    · intro h b hba
      let i : {i : κ // i ≠ a} := ⟨b, hba⟩
      change g (f (x, y)) a / t a < g (f (x, y)) b / t b
      rw [he_a, he_i i, div_lt_div_iff₀ (ht a) (ht b)]
      have hdiv := h i
      rw [div_mul_eq_mul_div, div_lt_iff₀ (ht a)] at hdiv
      simpa only [i, mul_comm] using hdiv
  have hsplit := Fintype.sum_eq_add_sum_subtype_ne t a
  have hsubsum : (∑ i : {i : κ // i ≠ a}, t i.1) = 1 - t a := by
    linarith
  have hratio : (∑ i : {i : κ // i ≠ a}, t i.1 / t a) =
      1 / t a - 1 := by
    rw [← Finset.sum_div, hsubsum]
    field_simp [(ht a).ne']
  have hypos : ∀ᵐ y : ℝ ∂(expMeasure 1), 0 < y := by
    have hnot := measure_eq_zero_iff_ae_notMem.mp expMeasure_one_Iic_zero
    filter_upwards [hnot] with y hy
    simpa only [Set.mem_Iic, not_le] using hy
  have hprod : ∀ᵐ y : ℝ ∂(expMeasure 1),
      (∏ i : {i : κ // i ≠ a},
          expMeasure 1 (Set.Ioi (t i.1 / t a * y))) =
        ENNReal.ofReal (Real.exp (-((1 / t a - 1) * y))) := by
    filter_upwards [hypos] with y hy
    simp_rw [expMeasure_one_Ioi _
      (mul_nonneg (div_nonneg (ht _).le (ht a).le) hy.le)]
    rw [← ENNReal.ofReal_prod_of_nonneg
      (fun i _ => Real.exp_nonneg (-(t i.1 / t a * y))), ← Real.exp_sum]
    congr 2
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul, hratio]
  have hclock :
      Measure.map (fun E : κ → ℝ => E a)
          ((clockLaw κ).restrict {E | strictClockWin t a E}) =
        (expMeasure 1).withDensity
          (fun y => ENNReal.ofReal
            (Real.exp (-((1 / t a - 1) * y)))) := by
    unfold clockLaw
    rw [← hmap, Measure.restrict_map (g.measurable.comp f.measurable) hwin,
      Measure.map_map (measurable_pi_apply a) (g.measurable.comp f.measurable)]
    have hmapcoord :
        Measure.map ((fun E : κ → ℝ => E a) ∘ (g ∘ f))
            (q.restrict ((g ∘ f) ⁻¹' {E : κ → ℝ | strictClockWin t a E})) =
          Measure.map Prod.snd
            (q.restrict ((g ∘ f) ⁻¹' {E : κ → ℝ | strictClockWin t a E})) := by
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun xy => hcoord xy
    rw [hmapcoord]
    ext s hs
    rw [Measure.map_apply measurable_snd hs,
      Measure.restrict_apply (measurable_snd hs)]
    have hset : MeasurableSet
        (Prod.snd ⁻¹' s ∩
          (g ∘ f) ⁻¹' {E : κ → ℝ | strictClockWin t a E}) :=
      (measurable_snd hs).inter (hwin.preimage (g.measurable.comp f.measurable))
    rw [Measure.prod_apply_symm hset]
    have hsections : ∀ᵐ y : ℝ ∂(expMeasure 1),
        Measure.pi (fun _ : {i : κ // i ≠ a} => expMeasure 1)
            ((fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹'
              (Prod.snd ⁻¹' s ∩
                (g ∘ f) ⁻¹'
                  {E : κ → ℝ | strictClockWin t a E})) =
          s.indicator (fun y => ENNReal.ofReal
            (Real.exp (-((1 / t a - 1) * y)))) y := by
      filter_upwards [hprod] with y hpy
      by_cases hys : y ∈ s
      · have hsec :
            (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹'
                (Prod.snd ⁻¹' s ∩
                  (g ∘ f) ⁻¹'
                    {E : κ → ℝ | strictClockWin t a E}) =
              Set.pi Set.univ
                (fun i : {i : κ // i ≠ a} =>
                  Set.Ioi (t i.1 / t a * y)) := by
            ext x
            simp only [Set.mem_preimage, Set.mem_inter_iff]
            have hmem :
                (g ∘ f) (x, y) ∈
                    {E : κ → ℝ | strictClockWin t a E} ↔
                  x ∈ Set.pi Set.univ
                    (fun i : {i : κ // i ≠ a} =>
                      Set.Ioi (t i.1 / t a * y)) :=
              Set.ext_iff.mp (hsectionWin y) x
            simpa only [hys, true_and] using hmem
        rw [hsec, Measure.pi_pi, hpy, Set.indicator_of_mem hys]
      · have hsec :
            (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹'
                (Prod.snd ⁻¹' s ∩
                  (g ∘ f) ⁻¹'
                    {E : κ → ℝ | strictClockWin t a E}) = ∅ := by
            ext x
            simp [hys]
        rw [hsec, measure_empty, Set.indicator_of_notMem hys]
    rw [lintegral_congr_ae hsections, lintegral_indicator hs,
      ← withDensity_apply _ hs]
  rw [hclock, expMeasure_one_tilt (ht a)]

/- On a fixed strict-winner cell, the scaled minimum has law
`t_a • Exp(1)` and is independent of the full excess vector. -/
private theorem clock_min_excess_restrict_factorization
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) :
    Measure.map
        (fun E : κ → ℝ =>
          (E a / t a, fun i => E i / t i - E a / t a))
        ((clockLaw κ).restrict {E | strictClockWin t a E}) =
      (ENNReal.ofReal (t a) • expMeasure 1).prod
        (Measure.map (fun r => winnerClockJoin a (0, r)) (weightedLosingExcessLaw t a)) := by
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let (i : {i : κ // i ≠ a}) : IsProbabilityMeasure
      (expMeasure (t i.1)) := isProbabilityMeasure_expMeasure (ht i.1)
  let e : Option {i : κ // i ≠ a} ≃ κ := Equiv.optionSubtypeNe a
  let f := (MeasurableEquiv.piOptionEquivProd
    (fun _ : Option {i : κ // i ≠ a} => ℝ)).symm
  let g := MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e
  let loseμ : Measure ({i : κ // i ≠ a} → ℝ) :=
    Measure.pi fun _ : {i : κ // i ≠ a} => expMeasure 1
  let q := loseμ.prod (expMeasure 1)
  let P := (g ∘ f) ⁻¹' {E : κ → ℝ | strictClockWin t a E}
  let J : (({i : κ // i ≠ a} → ℝ) × ℝ) → ℝ × (κ → ℝ) :=
    fun xy =>
      (xy.2 / t a,
        winnerClockJoin a (0, fun i => xy.1 i / t i.1 - xy.2 / t a))
  have hmap : Measure.map (g ∘ f) q = clockLaw κ := by
    simpa [e, f, g, q, loseμ] using clockReindex_law a
  have hcoordA (xy : ({i : κ // i ≠ a} → ℝ) × ℝ) :
      (g (f xy)) a = xy.2 := by
    have hfPair := (MeasurableEquiv.piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => ℝ)).apply_symm_apply xy
    have hfNone : f xy none = xy.2 := congrArg Prod.snd hfPair
    dsimp [g]
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    simp [e, hfNone]
  have hcoordNe (xy : ({i : κ // i ≠ a} → ℝ) × ℝ)
      (i : {i : κ // i ≠ a}) : (g (f xy)) i.1 = xy.1 i := by
    have hfPair := (MeasurableEquiv.piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => ℝ)).apply_symm_apply xy
    have hfSome : f xy (some i) = xy.1 i :=
      congrFun (congrArg Prod.fst hfPair) i
    dsimp [g]
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    simp [e, Equiv.optionSubtypeNe_symm_of_ne i.2, hfSome]
  have hwin := strictClockWin_measurableSet t a
  have hP : MeasurableSet P :=
    hwin.preimage (g.measurable.comp f.measurable)
  have hsectionP (y : ℝ) :
      (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' P =
        Set.pi Set.univ
          (fun i : {i : κ // i ≠ a} =>
            Set.Ioi (t i.1 / t a * y)) := by
    ext x
    simp only [P, Set.mem_preimage, Set.mem_ofPred_eq, strictClockWin,
      Set.mem_pi, Set.mem_univ, true_implies, Function.comp_apply,
      Set.mem_Ioi]
    constructor
    · intro h i
      have hrel := h i.1 i.2
      rw [hcoordA, hcoordNe (x, y) i] at hrel
      rw [div_mul_eq_mul_div, div_lt_iff₀ (ht a)]
      simpa only [mul_comm] using (div_lt_div_iff₀ (ht a) (ht i.1)).1 hrel
    · intro h b hba
      let i : {i : κ // i ≠ a} := ⟨b, hba⟩
      rw [hcoordA, hcoordNe (x, y) i, div_lt_div_iff₀ (ht a) (ht b)]
      have hdiv := h i
      rw [div_mul_eq_mul_div, div_lt_iff₀ (ht a)] at hdiv
      simpa only [i, mul_comm] using hdiv
  have hJ : Measurable J := by
    dsimp only [J]
    apply Measurable.prodMk
    · fun_prop
    · exact (winnerClockJoin_measurable a).comp (by fun_prop)
  have horig : Measurable (fun E : κ → ℝ =>
      (E a / t a, fun i => E i / t i - E a / t a)) := by fun_prop
  have hJcomp :
      (fun E : κ → ℝ =>
        (E a / t a, fun i => E i / t i - E a / t a)) ∘ (g ∘ f) = J := by
    funext xy
    apply Prod.ext
    · simp only [Function.comp_apply, J]
      rw [hcoordA]
    · funext i
      by_cases hi : i = a
      · subst i
        simp [J, winnerClockJoin, hcoordA]
      · simp only [Function.comp_apply, J, winnerClockJoin, hi, dite_false]
        rw [hcoordNe xy ⟨i, hi⟩, hcoordA]
  have hsplit :
      Measure.map
          (fun E : κ → ℝ =>
            (E a / t a, fun i => E i / t i - E a / t a))
          ((clockLaw κ).restrict {E | strictClockWin t a E}) =
        Measure.map J (q.restrict P) := by
    rw [← hmap, Measure.restrict_map
      (g.measurable.comp f.measurable) hwin,
      Measure.map_map horig (g.measurable.comp f.measurable), hJcomp]
  have hminLaw :
      Measure.map (fun E : κ → ℝ => E a / t a)
          ((clockLaw κ).restrict {E | strictClockWin t a E}) =
        ENNReal.ofReal (t a) • expMeasure 1 := by
    change Measure.map ((fun y : ℝ => y / t a) ∘ (fun E : κ → ℝ => E a)) _ = _
    rw [← Measure.map_map (g := fun y : ℝ => y / t a)
        (measurable_id.div_const (t a)) (measurable_pi_apply a),
      map_eval_restrict_strictClockWin t ht htotal a,
      Measure.map_smul (f := fun y : ℝ => y / t a) _
        (measurable_id.div_const (t a)).aemeasurable,
      map_div_expMeasure (ht a)]
  have hminSplit :
      Measure.map
          (fun xy : ({i : κ // i ≠ a} → ℝ) × ℝ => xy.2 / t a)
          (q.restrict P) =
        ENNReal.ofReal (t a) • expMeasure 1 := by
    rw [← hminLaw, ← hmap, Measure.restrict_map
      (g.measurable.comp f.measurable) hwin,
      Measure.map_map (g := fun E : κ → ℝ => E a / t a)
        (by fun_prop)
        (g.measurable.comp f.measurable)]
    apply Measure.map_congr
    filter_upwards [] with xy
    dsimp only [Function.comp_apply]
    rw [hcoordA]
  rw [hsplit]
  let ρ : Measure ({i : κ // i ≠ a} → ℝ) :=
    weightedLosingExcessLaw t a
  let embed : ({i : κ // i ≠ a} → ℝ) → κ → ℝ := fun r => winnerClockJoin a (0, r)
  let ρfull : Measure (κ → ℝ) := Measure.map embed ρ
  have hρprob : IsProbabilityMeasure ρ := by
    dsimp [ρ, weightedLosingExcessLaw]
    infer_instance
  let : IsProbabilityMeasure ρ := hρprob
  have hembed : Measurable embed := (winnerClockJoin_measurable a).comp (measurable_const.prodMk measurable_id)
  let : IsProbabilityMeasure ρfull := by
    dsimp [ρfull]
    infer_instance
  change Measure.map J (q.restrict P) =
    (ENNReal.ofReal (t a) • expMeasure 1).prod ρfull
  apply Measure.ext_prod
  intro s r hs hr
  let first : (({i : κ // i ≠ a} → ℝ) × ℝ) → ℝ :=
    fun xy => xy.2 / t a
  let B : Set (({i : κ // i ≠ a} → ℝ) × ℝ) := first ⁻¹' s ∩ P
  let A : Set (({i : κ // i ≠ a} → ℝ) × ℝ) := J ⁻¹' (s ×ˢ r) ∩ P
  have hfirstMeas : Measurable first := measurable_snd.div_const (t a)
  have hB : MeasurableSet B :=
    (hs.preimage hfirstMeas).inter hP
  have hA : MeasurableSet A :=
    ((hs.prod hr).preimage hJ).inter hP
  have hone : ∀ᵐ y : ℝ ∂(expMeasure 1), 0 < y := by
    have hnot := measure_eq_zero_iff_ae_notMem.mp expMeasure_one_Iic_zero
    filter_upwards [hnot] with y hy
    simpa only [Set.mem_Iic, not_le] using hy
  have hsections : ∀ᵐ y : ℝ ∂(expMeasure 1),
      loseμ ((fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' A) =
        ρfull r *
          loseμ ((fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' B) := by
    filter_upwards [hone] with y hy
    by_cases hys : y / t a ∈ s
    · let u : ℝ := y / t a
      let loseMap : ({i : κ // i ≠ a} → ℝ) →
          ({i : κ // i ≠ a} → ℝ) :=
        fun x i => x i / t i.1 - u
      let orth : Set ({i : κ // i ≠ a} → ℝ) :=
        Set.pi Set.univ
          (fun i : {i : κ // i ≠ a} => Set.Ioi (t i.1 * u))
      let rpre : Set ({i : κ // i ≠ a} → ℝ) := embed ⁻¹' r
      have hu : 0 ≤ u := div_nonneg hy.le (ht a).le
      have hloseMap : Measurable loseMap := by
        fun_prop
      have hrpre : MeasurableSet rpre := hr.preimage hembed
      have hPsec :
          (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' P = orth := by
        rw [hsectionP]
        congr 1
        funext i
        congr 1
        dsimp only [u]
        field_simp [(ht a).ne']
      have hAsec :
          (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' A =
            loseMap ⁻¹' rpre ∩ orth := by
        ext x
        have hpiff : (x, y) ∈ P ↔ x ∈ orth := by
          exact Set.ext_iff.mp hPsec x
        simp only [A, Set.mem_preimage, Set.mem_inter_iff,
          Set.mem_prod, J, rpre, embed, loseMap]
        dsimp only [u]
        simp only [hys, true_and, hpiff]
      have hBsec :
          (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' B = orth := by
        ext x
        have hpiff : (x, y) ∈ P ↔ x ∈ orth := by
          exact Set.ext_iff.mp hPsec x
        simp only [B, Set.mem_preimage, Set.mem_inter_iff, first]
        simp only [hys, true_and, hpiff]
      have hlaw := map_losing_scaled_excess t ht a hu
      change Measure.map loseMap (loseμ.restrict orth) =
          (∏ i : {i : κ // i ≠ a},
            ENNReal.ofReal (Real.exp (-(t i.1 * u)))) • ρ at hlaw
      have hlawR := congrArg (fun μ : Measure ({i : κ // i ≠ a} → ℝ) =>
        μ rpre) hlaw
      rw [Measure.map_apply hloseMap hrpre,
        Measure.restrict_apply (hrpre.preimage hloseMap),
        Measure.smul_apply, smul_eq_mul] at hlawR
      have horthMass : loseμ orth =
          ∏ i : {i : κ // i ≠ a},
            ENNReal.ofReal (Real.exp (-(t i.1 * u))) := by
        have hlawU := congrArg
          (fun μ : Measure ({i : κ // i ≠ a} → ℝ) => μ Set.univ) hlaw
        rw [Measure.map_apply hloseMap MeasurableSet.univ] at hlawU
        simp only [Set.preimage_univ] at hlawU
        rw [Measure.restrict_apply MeasurableSet.univ,
          Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] at hlawU
        simpa using hlawU
      have hρfull : ρfull r = ρ rpre := by
        dsimp only [ρfull]
        rw [Measure.map_apply hembed hr]
      rw [hAsec, hBsec, hlawR, horthMass, hρfull]
      ac_rfl
    · have hAempty :
          (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' A = ∅ := by
        ext x
        simp [A, J, hys]
      have hBempty :
          (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' B = ∅ := by
        ext x
        simp [B, first, hys]
      rw [hAempty, hBempty, measure_empty, mul_zero]
  rw [Measure.map_apply hJ (hs.prod hr),
    Measure.restrict_apply ((hs.prod hr).preimage hJ)]
  change q A = _
  rw [Measure.prod_apply_symm hA, lintegral_congr_ae hsections,
    lintegral_const_mul _ (measurable_measure_prodMk_right hB),
    ← Measure.prod_apply_symm hB]
  have hqB : q B = (ENNReal.ofReal (t a) • expMeasure 1) s := by
    rw [← hminSplit, Measure.map_apply hfirstMeas hs,
      Measure.restrict_apply (hs.preimage hfirstMeas)]
  rw [Measure.prod_prod, hqB]
  ac_rfl

/- The one-block independence statement behind the one-block factorization.  It is proved
by partitioning the exponential clocks according to their strict winner and
then summing the fixed-cell factorization above. -/
/-! ### Lemmas 7.2 and 7.3: grouping and winner entropy -/

/- Reindex the iid label seeds by their cluster fibres.  This is the
measure-theoretic independence input for the grouping identities. -/
/-! ### The scalar channel -/

/-! ### The losing-vector cone -/

private lemma map_weightedLosingExcess_scale
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (a : κ) :
    Measure.map
        (fun R : {i : κ // i ≠ a} → ℝ => fun i => t i.1 * R i)
        (weightedLosingExcessLaw t a) =
      Measure.pi fun _ : {i : κ // i ≠ a} => expMeasure 1 := by
  let (i : {i : κ // i ≠ a}) : IsProbabilityMeasure (expMeasure (t i.1)) :=
    isProbabilityMeasure_expMeasure (ht i.1)
  let r : {i : κ // i ≠ a} → ℝ := fun i => t i.1
  unfold weightedLosingExcessLaw
  change Measure.map (fun R i => r i * R i)
      (Measure.pi fun i : {i : κ // i ≠ a} => expMeasure (r i)) = _
  rw [Measure.pi_map_pi fun i => (by fun_prop :
    AEMeasurable (fun x : ℝ => r i * x) (expMeasure (r i)))]
  congr 1
  funext i
  exact map_mul_expMeasure (ht i.1)

/-- A fresh distinguished `Exp(1)` clock together with fresh iid losing
clocks is just the original iid clock vector. -/
private lemma winnerClockJoin_law
    {κ : Type} [Fintype κ] [DecidableEq κ] (a : κ) :
    Measure.map (winnerClockJoin a)
        ((expMeasure 1).prod
          (Measure.pi fun _ : {i : κ // i ≠ a} => expMeasure 1)) =
      clockLaw κ := by
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let loseμ : Measure ({i : κ // i ≠ a} → ℝ) :=
    Measure.pi fun _ : {i : κ // i ≠ a} => expMeasure 1
  let : IsProbabilityMeasure loseμ := by
    dsimp [loseμ]
    infer_instance
  let e : Option {i : κ // i ≠ a} ≃ κ := Equiv.optionSubtypeNe a
  let f := (MeasurableEquiv.piOptionEquivProd
    (fun _ : Option {i : κ // i ≠ a} => ℝ)).symm
  let g := MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e
  let q := loseμ.prod (expMeasure 1)
  have hmap : Measure.map (g ∘ f) q = clockLaw κ := by
    simpa [e, f, g, q, loseμ] using clockReindex_law a
  have hjoinSwap : winnerClockJoin a ∘ Prod.swap = g ∘ f := by
    funext xy i
    have hfPair := (MeasurableEquiv.piOptionEquivProd
      (fun _ : Option {j : κ // j ≠ a} => ℝ)).apply_symm_apply xy
    by_cases hi : i = a
    · subst i
      have hfNone : f xy none = xy.2 := congrArg Prod.snd hfPair
      dsimp only [Function.comp_apply, winnerClockJoin]
      simp only [dite_true]
      dsimp [g]
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
      simp [e, hfNone]
    · have hfSome : f xy (some ⟨i, hi⟩) = xy.1 ⟨i, hi⟩ :=
        congrFun (congrArg Prod.fst hfPair) ⟨i, hi⟩
      dsimp only [Function.comp_apply, winnerClockJoin]
      simp only [hi, dite_false]
      dsimp [g]
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
      simp [e, Equiv.optionSubtypeNe_symm_of_ne hi, hfSome]
  change Measure.map (winnerClockJoin a) ((expMeasure 1).prod loseμ) = _
  rw [← hmap, ← hjoinSwap,
    ← Measure.map_map (winnerClockJoin_measurable a) measurable_swap,
    Measure.prod_swap]

/-- On the cell where `a` wins, remove the common weighted-race minimum from
every losing raw clock and retain that minimum in coordinate `a`. -/
noncomputable def winnerResidualClock
    {κ : Type} [DecidableEq κ] (t : κ → ℝ) (a : κ)
    (E : κ → ℝ) : κ → ℝ :=
  fun i => if _h : i = a then E a / t a else E i - t i * (E a / t a)

lemma winnerResidualClock_measurable
    {κ : Type} [DecidableEq κ]
    (t : κ → ℝ) (a : κ) :
    Measurable (winnerResidualClock t a) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i = a <;> simp only [winnerResidualClock, hi, dite_true, dite_false]
    <;> fun_prop

/-- Fixed-winner exponential memorylessness in full-vector form.  The
residual vector consists of fresh iid `Exp(1)` clocks, with total mass equal
to the probability `t a` of the winner cell. -/
theorem winnerResidualClock_restrict_law
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) :
    Measure.map (winnerResidualClock t a)
        ((clockLaw κ).restrict {E | strictClockWin t a E}) =
      ENNReal.ofReal (t a) • clockLaw κ := by
  let ρ : Measure ({i : κ // i ≠ a} → ℝ) :=
    weightedLosingExcessLaw t a
  let loseμ : Measure ({i : κ // i ≠ a} → ℝ) :=
    Measure.pi fun _ : {i : κ // i ≠ a} => expMeasure 1
  let A : Measure ℝ := ENNReal.ofReal (t a) • expMeasure 1
  let embed : ({i : κ // i ≠ a} → ℝ) → κ → ℝ := fun r => winnerClockJoin a (0, r)
  let norm : (κ → ℝ) → ℝ × (κ → ℝ) := fun E =>
    (E a / t a, fun i => E i / t i - E a / t a)
  let out : (ℝ × (κ → ℝ)) → κ → ℝ := fun sr i =>
    if i = a then sr.1 else t i * sr.2 i
  let assemble : (ℝ × ({i : κ // i ≠ a} → ℝ)) → κ → ℝ := fun sr =>
    winnerClockJoin a (sr.1, fun i => t i.1 * sr.2 i)
  let loseScale : ({i : κ // i ≠ a} → ℝ) →
      ({i : κ // i ≠ a} → ℝ) := fun R i => t i.1 * R i
  let scale : (ℝ × ({i : κ // i ≠ a} → ℝ)) →
      ℝ × ({i : κ // i ≠ a} → ℝ) := Prod.map id loseScale
  have hnorm : Measurable norm := by fun_prop
  have hout : Measurable out := by
    apply Measurable.of_eval
    intro i
    by_cases hi : i = a <;> simp only [out, hi, ite_true, ite_false] <;> fun_prop
  have hembed : Measurable embed := (winnerClockJoin_measurable a).comp (measurable_const.prodMk measurable_id)
  have hloseScale : Measurable loseScale := by fun_prop
  have hscale : Measurable scale := measurable_id.prodMap hloseScale
  have hresidualNorm : winnerResidualClock t a = out ∘ norm := by
    funext E i
    by_cases hi : i = a
    · subst i
      simp [winnerResidualClock, out, norm]
    · simp only [winnerResidualClock, hi, dite_false, Function.comp_apply,
        out, norm, ite_false]
      field_simp [(ht i).ne', (ht a).ne']
  have houtEmbed : out ∘ Prod.map id embed = assemble := by
    funext sr i
    by_cases hi : i = a
    · subst i
      simp [out, assemble, winnerClockJoin]
    · simp [out, assemble, embed, winnerClockJoin, hi]
  have hassembleScale : assemble = winnerClockJoin a ∘ scale := by
    rfl
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let (i : {i : κ // i ≠ a}) : IsProbabilityMeasure
      (expMeasure (t i.1)) := isProbabilityMeasure_expMeasure (ht i.1)
  let : IsProbabilityMeasure ρ := by
    dsimp [ρ, weightedLosingExcessLaw]
    infer_instance
  let : IsProbabilityMeasure loseμ := by
    dsimp [loseμ]
    infer_instance
  let : SFinite A := by
    dsimp [A]
    infer_instance
  have hscaleLaw : Measure.map scale (A.prod ρ) = A.prod loseμ := by
    rw [← Measure.map_prod_map A ρ measurable_id hloseScale, Measure.map_id]
    congr 1
    exact map_weightedLosingExcess_scale t ht a
  have hAprod : A.prod loseμ =
      ENNReal.ofReal (t a) • ((expMeasure 1).prod loseμ) := by
    dsimp only [A]
    rw [Measure.prod_smul_left]
  have hprod : A.prod (Measure.map embed ρ) =
      Measure.map (Prod.map id embed) (A.prod ρ) := by
    simpa only [Measure.map_id] using Measure.map_prod_map A ρ measurable_id hembed
  calc
    Measure.map (winnerResidualClock t a)
        ((clockLaw κ).restrict {E | strictClockWin t a E}) =
        Measure.map out
          (Measure.map norm
            ((clockLaw κ).restrict {E | strictClockWin t a E})) := by
      rw [hresidualNorm]
      exact (Measure.map_map hout hnorm).symm
    _ = Measure.map out
        (A.prod (Measure.map embed ρ)) := by
      rw [clock_min_excess_restrict_factorization t ht htotal a]
    _ = Measure.map (winnerClockJoin a) (A.prod loseμ) := by
      rw [hprod, Measure.map_map hout (measurable_id.prodMap hembed),
        houtEmbed, hassembleScale,
        ← Measure.map_map (winnerClockJoin_measurable a) hscale, hscaleLaw]
    _ = ENNReal.ofReal (t a) • clockLaw κ := by
      rw [hAprod, Measure.map_smul _ (winnerClockJoin_measurable a).aemeasurable]
      congr 1
      exact winnerClockJoin_law a

@[simp] lemma winnerResidualClock_apply_winner
    {κ : Type} [DecidableEq κ] (t : κ → ℝ) (a : κ) (E : κ → ℝ) :
    winnerResidualClock t a E a = E a / t a := by
  simp [winnerResidualClock]

/-! ### Normalized clock moments on the fixed-winner cells -/

/-- A strict weighted-clock winner is also the lexicographic minimizer used
by the normalized shared-race quantities. Strictness makes the tie-break
irrelevant. -/
lemma clockArgmin_eq_of_strictClockWin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t E : κ → ℝ) (a : κ) (ha : strictClockWin t a E) :
    SharedRace.clockArgmin t E = a := by
  by_contra hne
  have hmax := lexMax_max (fun E i => -(E i / t i)) E a
  have hstrict := ha (SharedRace.clockArgmin t E) hne
  change -(E a / t a) ≤
    -(E (SharedRace.clockArgmin t E) /
      t (SharedRace.clockArgmin t E)) at hmax
  linarith

namespace SharedRace

end SharedRace

private lemma strictClockWin_pairwise_disjoint
    {κ : Type}
    (t : κ → ℝ) : Pairwise fun a b : κ => Disjoint
      {E : κ → ℝ | strictClockWin t a E}
      {E : κ → ℝ | strictClockWin t b E} := by
  intro a b hab
  rw [Set.disjoint_left]
  intro E ha hb
  have hab' := ha b hab.symm
  have hba' := hb a hab
  linarith

/-- The strict winner cells exhaust iid exponential clocks up to a null set.
This is the measure-level partition used by all subsequent cellwise moment
identities. -/
private theorem clockLaw_eq_sum_restrict_strictClockWin
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1) :
    clockLaw κ = Measure.sum fun a : κ =>
      (clockLaw κ).restrict {E | strictClockWin t a E} := by
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let : IsProbabilityMeasure (clockLaw κ) := by
    unfold clockLaw
    infer_instance
  let S : κ → Set (κ → ℝ) := fun a => {E | strictClockWin t a E}
  have hS (a : κ) : MeasurableSet (S a) :=
    strictClockWin_measurableSet t a
  have hdisj : Pairwise fun a b => Disjoint (S a) (S b) :=
    strictClockWin_pairwise_disjoint t
  have hcell (a : κ) : clockLaw κ (S a) = ENNReal.ofReal (t a) := by
    unfold clockLaw S
    exact pi_exp_strictClockWin t ht htotal a
  have hmass : clockLaw κ (⋃ a, S a) = 1 := by
    rw [measure_iUnion hdisj hS, tsum_fintype]
    simp_rw [hcell]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => (ht a).le), htotal]
    norm_num
  have hUnion : ∀ᵐ E ∂(clockLaw κ), E ∈ ⋃ a, S a :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion hS)).2 hmass
  calc
    clockLaw κ = (clockLaw κ).restrict (⋃ a, S a) :=
      (Measure.restrict_eq_self_of_ae_mem hUnion).symm
    _ = Measure.sum fun a : κ => (clockLaw κ).restrict (S a) :=
      Measure.restrict_iUnion hdisj hS

lemma integral_clock_eq_sum_strictClockWin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (f : (κ → ℝ) → ℝ) (hf : Integrable f (clockLaw κ)) :
    (∫ E, f E ∂(clockLaw κ)) =
      ∑ a, ∫ E, f E
        ∂((clockLaw κ).restrict {E | strictClockWin t a E}) := by
  have hdecomp := clockLaw_eq_sum_restrict_strictClockWin t ht htotal
  rw [hdecomp] at hf
  conv_lhs => rw [hdecomp]
  simpa only [tsum_fintype] using integral_sum_measure hf

/-- Integrating a measurable residual-clock statistic on one strict winner
cell gives the winner mass times its expectation under fresh iid clocks. -/
lemma integral_comp_winnerResidualClock
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) (f : (κ → ℝ) → ℝ) (hf : Measurable f) :
    (∫ E, f (winnerResidualClock t a E)
        ∂((clockLaw κ).restrict {E | strictClockWin t a E})) =
      t a * ∫ W, f W ∂(clockLaw κ) := by
  rw [← integral_map (winnerResidualClock_measurable t a).aemeasurable
      hf.aestronglyMeasurable,
    winnerResidualClock_restrict_law t ht htotal a, integral_smul_measure,
    ENNReal.toReal_ofReal (ht a).le, smul_eq_mul]

namespace SharedRace

private lemma lexMax_eq_of_le_iff
    {Ω Ω' ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (F : Ω → ι → ℝ) (G : Ω' → ι → ℝ) (ω : Ω) (ω' : Ω')
    (hord : ∀ a b, F ω a ≤ F ω b ↔ G ω' a ≤ G ω' b) :
    lexMax F ω = lexMax G ω' := by
  let a : ι := lexMax G ω'
  apply (lexMax_eq_iff F ω a).2
  have ha : List.argmax (G ω') Finset.univ.toList = some a :=
    (lexMax_eq_iff G ω' a).1 rfl
  rw [List.argmax_eq_some_iff] at ha ⊢
  refine ⟨ha.1, ?_, ?_⟩
  · intro b hb
    exact (hord b a).2 (ha.2.1 b hb)
  · intro b hb hFab
    exact ha.2.2 b hb ((hord a b).1 hFab)

/-- The shared lexicographic tie-break is preserved exactly by the
exponential-clock/Gumbel change of variables. -/
theorem weightedLexWinner_clock_eq_argmin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t E : κ → ℝ) (ht : ∀ i, 0 < t i) (hE : ∀ i, 0 < E i) :
    weightedLexWinner t (fun i => -Real.log (E i)) = clockArgmin t E := by
  let Fs : (κ → ℝ) → κ → ℝ := fun G i => Real.log (t i) + G i
  let Fc : (κ → ℝ) → κ → ℝ := fun W i => -(W i / t i)
  change lexMax Fs (fun i => -Real.log (E i)) = lexMax Fc E
  apply lexMax_eq_of_le_iff Fs Fc (fun i => -Real.log (E i)) E
  intro a b
  have hscore (i : κ) :
      Fs (fun j => -Real.log (E j)) i = -Real.log (E i / t i) := by
    dsimp only [Fs]
    rw [Real.log_div (hE i).ne' (ht i).ne']
    ring
  have hra (i : κ) : 0 < E i / t i := div_pos (hE i) (ht i)
  rw [hscore a, hscore b]
  change -Real.log (E a / t a) ≤ -Real.log (E b / t b) ↔
    -(E a / t a) ≤ -(E b / t b)
  rw [neg_le_neg_iff, neg_le_neg_iff]
  exact Real.strictMonoOn_log.le_iff_le (hra b) (hra a)

end SharedRace

namespace SharedRace

end SharedRace

/-! ### The fixed-seed cell-residual link -/

/-! ### Direct bridge from the all-label shared-race bound

The analytic theorem is stated for one finite source law and one posterior
vector at each source atom.  The duplicate quotient supplies exactly such a
problem in every `C₀ = g` context.  The lemmas below transport its shared
cluster race back to the original label race, without passing through the
scalar/cone KL decomposition.
-/

end stoch_to_det
