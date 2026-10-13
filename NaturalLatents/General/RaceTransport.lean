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
# Transport lemmas for the exponential race

Finite-map and arbitrary-latent transport for the race of the next two modules: the posterior
rows as probability laws, the calibration of the seed law, the transport of conditional mutual
information along the winner map, the Gibbs inequality against a reference law, and the reduction
(`race_of_single_law`) of the arbitrary-latent statement to a statement about one law with one
rate vector.

The statements are in nats.

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

/- Finite-map and arbitrary-latent transport for the race. -/
omit [DecidableEq X] [DecidableEq Y] in
lemma race_post_isPMF {p : Law X Y} (hp : stoch_to_det.IsPMF p)
    (L : FiniteLatent p) (z : X × Y) (hz : p z ≠ 0) :
    stoch_to_det.IsPMF (fun i => post L i z) := by
  constructor
  · intro i
    exact div_nonneg
      (mul_nonneg (L.prior_isPMF.nonneg i) ((L.comp_isPMF i).nonneg z)) (hp.nonneg z)
  · unfold stoch_to_det.mass post
    rw [← Finset.sum_div, L.mixture z, div_self hz]

lemma race_posteriorJoint {p : Law X Y} (_hp : stoch_to_det.IsPMF p)
    (L : FiniteLatent p) :
    stoch_to_det.SharedRace.posteriorJoint p (fun z i => post L i z) =
      stoch_to_det.push Prod.swap L.joint := by
  funext zi
  rcases zi with ⟨⟨x,y⟩,i⟩
  rw [stoch_to_det.SharedRace.posteriorJoint, p_mul_post L i (x,y)]
  unfold stoch_to_det.push
  symm
  apply Finset.sum_eq_single (i,(x,y))
  · intro b hb hne
    have hh := (Finset.mem_filter.mp hb).2
    have he : b = (i,(x,y)) := by
      have hs := congrArg Prod.swap hh
      simpa using hs
    exact (hne he).elim
  · intro hz
    simp at hz

lemma race_clock_probability {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (r : κ → ℝ) (hr : stoch_to_det.IsPMF r) (hpos : ∀ i, 0 < r i) (i : κ) :
    (∫ E : κ → ℝ, (if stoch_to_det.SharedRace.clockArgmin r E = i then (1 : ℝ) else 0)
      ∂stoch_to_det.clockLaw κ) = r i := by
  let : MeasurableSpace κ := ⊤
  have hm := stoch_to_det.SharedRace.measurable_clockArgmin r
  have hint : Integrable
      (fun E : κ → ℝ => if stoch_to_det.SharedRace.clockArgmin r E = i then (1 : ℝ) else 0)
      (stoch_to_det.clockLaw κ) := by
    apply Integrable.of_bound
      (Measurable.ite ((measurableSet_singleton i).preimage hm)
        measurable_const measurable_const).aestronglyMeasurable 1
    filter_upwards [] with E
    split <;> norm_num
  rw [stoch_to_det.integral_clock_eq_sum_strictClockWin r hpos
    (by simpa [stoch_to_det.mass] using hr.total) _ hint]
  have hcell (b : κ) :
      (∫ E : κ → ℝ, (if stoch_to_det.SharedRace.clockArgmin r E = i then (1 : ℝ) else 0)
        ∂(stoch_to_det.clockLaw κ).restrict {E | stoch_to_det.strictClockWin r b E}) =
      if b = i then r b else 0 := by
    calc
      _ = ∫ _E : κ → ℝ, (if b = i then (1 : ℝ) else 0)
          ∂(stoch_to_det.clockLaw κ).restrict {E | stoch_to_det.strictClockWin r b E} := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (stoch_to_det.strictClockWin_measurableSet r b)] with E hE
        rw [stoch_to_det.clockArgmin_eq_of_strictClockWin r E b hE]
      _ = _ := by
        by_cases hbi : b = i
        · simp only [hbi, if_true, integral_const, smul_eq_mul, mul_one, measureReal_def,
            Measure.restrict_apply_univ]
          rw [stoch_to_det.clockLaw,
            stoch_to_det.pi_exp_strictClockWin r hpos
              (by simpa [stoch_to_det.mass] using hr.total)]
          exact ENNReal.toReal_ofReal (hr.nonneg i)
        · simp [hbi]
  simp_rw [hcell]
  simp

lemma race_seed_probability {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (r : κ → ℝ) (hr : stoch_to_det.IsPMF r) (hpos : ∀ i, 0 < r i) (i : κ) :
    (∫ G : κ → ℝ, (if stoch_to_det.SharedRace.weightedLexWinner r G = i then (1 : ℝ) else 0)
      ∂stoch_to_det.seedLaw κ) = r i := by
  let : MeasurableSpace κ := ⊤
  have hm : Measurable (stoch_to_det.SharedRace.weightedLexWinner r) := by
    unfold stoch_to_det.SharedRace.weightedLexWinner
    apply stoch_to_det.measurable_lexMax
    intro b
    exact measurable_const.add (measurable_pi_apply b)
  have hg : Measurable (fun E : κ → ℝ => fun b => -Real.log (E b)) :=
    measurable_pi_lambda _ fun b => (Real.measurable_log.comp (measurable_pi_apply b)).neg
  unfold stoch_to_det.seedLaw
  have hf : AEStronglyMeasurable
      (fun G : κ → ℝ => if stoch_to_det.SharedRace.weightedLexWinner r G = i then (1 : ℝ) else 0)
      ((stoch_to_det.clockLaw κ).map (fun E b => -Real.log (E b))) := by
    have hmset : MeasurableSet {G : κ → ℝ | stoch_to_det.SharedRace.weightedLexWinner r G = i} := by
      exact (measurableSet_singleton i).preimage hm
    exact (Measurable.ite hmset measurable_const measurable_const).aestronglyMeasurable
  rw [integral_map hg.aemeasurable hf]
  calc
    _ = ∫ E : κ → ℝ, (if stoch_to_det.SharedRace.clockArgmin r E = i then (1 : ℝ) else 0)
        ∂stoch_to_det.clockLaw κ := by
      apply integral_congr_ae
      filter_upwards [stoch_to_det.SharedRace.ae_clockLaw_pos (κ := κ)] with E hE
      have heq : stoch_to_det.SharedRace.weightedLexWinner r (fun b => -Real.log (E b)) =
          stoch_to_det.SharedRace.clockArgmin r E :=
        stoch_to_det.SharedRace.weightedLexWinner_clock_eq_argmin r E hpos hE
      rw [heq]
    _ = r i := race_clock_probability r hr hpos i

lemma race_finite_expectation {Ω κ : Type} [Fintype Ω] [Fintype κ]
    [DecidableEq Ω] [DecidableEq κ] [Nonempty κ]
    (r : Ω → κ → ℝ) (f : (Ω → κ) → ℝ) :
    (∑ A : Ω → κ,
      (∫ G : κ → ℝ, (if stoch_to_det.SharedRace.sharedWinner r G = A then (1 : ℝ) else 0)
        ∂stoch_to_det.seedLaw κ) * f A) =
      ∫ G : κ → ℝ, f (stoch_to_det.SharedRace.sharedWinner r G) ∂stoch_to_det.seedLaw κ := by
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards [] with G
    simp
  · intro A _
    exact stoch_to_det.SharedRace.integrable_sharedWinner_code r
      (fun B => (if B = A then (1 : ℝ) else 0) * f A)

lemma race_map_calibrated {p : Law X Y} (hp : stoch_to_det.IsPMF p)
    (L : FiniteLatent p)
    (hrows : ∀ z ∈ stoch_to_det.support p, ∀ i, 0 < post L i z) :
    ∃ F : CalibratedSeededFamily L,
      F.seedLaw = fun A => ∫ G : L.ι → ℝ,
        (if stoch_to_det.SharedRace.sharedWinner (fun z i => post L i z) G = A then (1 : ℝ) else 0)
        ∂stoch_to_det.seedLaw L.ι := by
  let r : X × Y → L.ι → ℝ := fun z i => post L i z
  let w : (X × Y → L.ι) → ℝ := fun A => ∫ G : L.ι → ℝ,
    (if stoch_to_det.SharedRace.sharedWinner r G = A then (1 : ℝ) else 0)
      ∂stoch_to_det.seedLaw L.ι
  have hw : stoch_to_det.IsPMF w := by
    constructor
    · intro A
      apply integral_nonneg
      intro G
      change 0 ≤ if stoch_to_det.SharedRace.sharedWinner r G = A then (1 : ℝ) else 0
      split <;> norm_num
    · change ∑ A, w A = 1
      have he := race_finite_expectation r (fun _ => (1 : ℝ))
      simpa [w] using he
  have hc (z : X × Y) (hz : z ∈ stoch_to_det.support p) (i : L.ι) :
      (∑ A, if A z = i then w A else 0) = post L i z := by
    have he := race_finite_expectation r (fun A => if A z = i then (1 : ℝ) else 0)
    have hleft : (∑ A, w A * (if A z = i then (1 : ℝ) else 0)) =
        ∑ A, if A z = i then w A else 0 := by
      apply Finset.sum_congr rfl
      intro A _
      split <;> simp_all
    change (∑ A, w A * (if A z = i then (1 : ℝ) else 0)) = _ at he
    rw [hleft] at he
    rw [he]
    exact race_seed_probability (r z)
      (race_post_isPMF hp L z (by simpa [stoch_to_det.support] using hz)) (hrows z hz) i
  exact ⟨⟨w,hw,hc⟩,rfl⟩

lemma race_condMI_transport {p : Law X Y} (hp : stoch_to_det.IsPMF p)
    (L : FiniteLatent p) {Γ : Type} [Fintype Γ] [DecidableEq Γ] (g : X × Y → Γ) :
    stoch_to_det.condMI Prod.fst Prod.snd (fun zi : (X × Y) × L.ι => g zi.1)
        (stoch_to_det.SharedRace.posteriorJoint p (fun z i => post L i z)) =
      stoch_to_det.condMI Prod.fst Prod.snd (fun lz : L.ι × (X × Y) => g lz.2) L.joint := by
  rw [race_posteriorJoint hp L]
  have hswap :
      stoch_to_det.condMI Prod.fst Prod.snd (fun zi : (X × Y) × L.ι => g zi.1)
        (stoch_to_det.push Prod.swap L.joint) =
      stoch_to_det.condMI Prod.snd Prod.fst (fun lz : L.ι × (X × Y) => g lz.2) L.joint := by
    unfold stoch_to_det.condMI stoch_to_det.Hvar
    simp only [stoch_to_det.push_push, Function.comp_def, Prod.swap]
  rw [hswap, stoch_to_det.condMI_comm_local L.joint_isPMF Prod.snd Prod.fst]

private lemma condMI_pair_coordinate
    {A B C D E : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
    [DecidableEq B] [DecidableEq C] [DecidableEq D] [DecidableEq E]
    {m : A → ℝ} (hm : stoch_to_det.IsPMF m) (k : A → D) (f : A → B) (g : A → C)
    (pair : B → C → E) (getG : E → C) (hpair : ∀ b c, getG (pair b c) = c) :
    stoch_to_det.condMI k (fun a => pair (f a) (g a)) f m =
      stoch_to_det.condMI k g f m := by
  have hpairH := stoch_to_det.Hvar_eq_of_leftInverse hm (fun a => (g a, f a))
    (fun gf => (pair gf.2 gf.1, gf.2)) (fun ef => (getG ef.1, ef.2))
    (fun gf => by simp [hpair])
  have hprefixedH := stoch_to_det.Hvar_eq_of_leftInverse hm (fun a => (k a, g a, f a))
    (fun kgf => (kgf.1, pair kgf.2.2 kgf.2.1, kgf.2.2))
    (fun kef => (kef.1, getG kef.2.1, kef.2.2)) (fun kgf => by simp [hpair])
  have hpairH' : stoch_to_det.Hvar (fun a => (pair (f a) (g a), f a)) m =
      stoch_to_det.Hvar (fun a => (g a, f a)) m := by
    simpa only [Function.comp_def] using hpairH
  have hprefixedH' : stoch_to_det.Hvar (fun a => (k a, pair (f a) (g a), f a)) m =
      stoch_to_det.Hvar (fun a => (k a, g a, f a)) m := by
    simpa only [Function.comp_def] using hprefixedH
  unfold stoch_to_det.condMI
  rw [hpairH', hprefixedH']

lemma race_condMI_coordinate_sum {p : Law X Y} (L : FiniteLatent p) :
    Real.log 2 *
      (stoch_to_det.condMI Prod.fst Prod.snd (fun lz : L.ι × (X × Y) => lz.2.1) L.joint +
       stoch_to_det.condMI Prod.fst Prod.snd (fun lz : L.ι × (X × Y) => lz.2.2) L.joint) = B L := by
  rw [condMI_pair_coordinate L.joint_isPMF Prod.fst (fun lz => lz.2.1)
      (fun lz => lz.2.2) (fun x y => (x, y)) Prod.snd (fun _ _ => rfl),
    condMI_pair_coordinate L.joint_isPMF Prod.fst (fun lz => lz.2.2)
      (fun lz => lz.2.1) (fun y x => (x, y)) Prod.fst (fun _ _ => rfl)]
  unfold B
  ring

lemma race_h_eq {p : Law X Y} {L : FiniteLatent p} (F : CalibratedSeededFamily L)
    (hw : F.seedLaw = fun A => ∫ G : L.ι → ℝ,
      (if stoch_to_det.SharedRace.sharedWinner (fun z i => post L i z) G = A then (1 : ℝ) else 0)
      ∂stoch_to_det.seedLaw L.ι) :
    h F = Real.log 2 *
      ((∫ G : L.ι → ℝ,
          stoch_to_det.condH (stoch_to_det.SharedRace.sharedWinner (fun z i => post L i z) G)
            Prod.fst p ∂stoch_to_det.seedLaw L.ι) +
       (∫ G : L.ι → ℝ,
          stoch_to_det.condH (stoch_to_det.SharedRace.sharedWinner (fun z i => post L i z) G)
            Prod.snd p ∂stoch_to_det.seedLaw L.ι)) := by
  unfold h
  rw [hw, race_finite_expectation, integral_const_mul, integral_add]
  · exact stoch_to_det.SharedRace.integrable_sharedWinner_code _ (fun A => stoch_to_det.condH A Prod.fst p)
  · exact stoch_to_det.SharedRace.integrable_sharedWinner_code _ (fun A => stoch_to_det.condH A Prod.snd p)

/-- The complete-map and coordinate transport needs only the single-law analytic comparison. -/
lemma race_of_single_law {p : Law X Y} (hp : stoch_to_det.IsPMF p)
    (L : FiniteLatent p)
    (hrows : ∀ z ∈ stoch_to_det.support p, ∀ i, 0 < post L i z)
    (a b : ℝ)
    (hsingle : ∀ (μ : X × Y → ℝ) (r : X × Y → L.ι → ℝ),
      stoch_to_det.IsPMF μ → (∀ z, μ z ≠ 0 → stoch_to_det.IsPMF (r z)) →
      (∀ z, μ z ≠ 0 → ∀ i, 0 < r z i) →
      stoch_to_det.SharedRace.sharedRaceEntropy μ r ≤
        a * stoch_to_det.MI Prod.fst Prod.snd (stoch_to_det.SharedRace.posteriorJoint μ r) +
        b * stoch_to_det.SharedRace.categoricalMismatch μ r) :
    ∃ F : CalibratedSeededFamily L, h F ≤ a * B L + 2 * (Real.log 2 * b) * d L := by
  obtain ⟨F,hw⟩ := race_map_calibrated hp L hrows
  refine ⟨F, ?_⟩
  let r : X × Y → L.ι → ℝ := fun z i => post L i z
  have hr (z : X × Y) (hz : p z ≠ 0) : stoch_to_det.IsPMF (r z) :=
    race_post_isPMF hp L z hz
  have hrpos (z : X × Y) (hz : p z ≠ 0) (i : L.ι) : 0 < r z i :=
    hrows z (by simpa [stoch_to_det.support] using hz) i
  have hX := stoch_to_det.SharedRace.conditional_entropy_le_of_uniform_entropy_bound
    a b hsingle hp hr hrpos Prod.fst
  have hY := stoch_to_det.SharedRace.conditional_entropy_le_of_uniform_entropy_bound
    a b hsingle hp hr hrpos Prod.snd
  change (∫ G : L.ι → ℝ, stoch_to_det.condH
    (stoch_to_det.SharedRace.sharedWinner (fun z i => post L i z) G) Prod.fst p
      ∂stoch_to_det.seedLaw L.ι) ≤ _ at hX
  change (∫ G : L.ι → ℝ, stoch_to_det.condH
    (stoch_to_det.SharedRace.sharedWinner (fun z i => post L i z) G) Prod.snd p
      ∂stoch_to_det.seedLaw L.ι) ≤ _ at hY
  change _ ≤ a * stoch_to_det.condMI Prod.fst Prod.snd
    (fun zi : (X × Y) × L.ι => zi.1.1)
      (stoch_to_det.SharedRace.posteriorJoint p (fun z i => post L i z)) + b * d L at hX
  change _ ≤ a * stoch_to_det.condMI Prod.fst Prod.snd
    (fun zi : (X × Y) × L.ι => zi.1.2)
      (stoch_to_det.SharedRace.posteriorJoint p (fun z i => post L i z)) + b * d L at hY
  rw [race_condMI_transport hp L Prod.fst] at hX
  rw [race_condMI_transport hp L Prod.snd] at hY
  rw [race_h_eq F hw]
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hX hY) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hB := race_condMI_coordinate_sum L
  rw [← hB]
  convert hsum using 1 <;> first | rfl | ring

lemma race_gibbs_nats {Ω κ : Type} [Fintype Ω] [Fintype κ] [DecidableEq κ]
    {μ : Ω → ℝ} (hμ : stoch_to_det.IsPMF μ) (A : Ω → κ)
    {q : κ → ℝ} (hq : stoch_to_det.IsPMF q) (hqpos : ∀ i, 0 < q i) :
    Real.log 2 * stoch_to_det.H (stoch_to_det.push A μ) ≤
      ∑ z, μ z * Real.log (1 / q (A z)) := by
  have hg := stoch_to_det.SharedRace.H_push_le_expected_crossEntropy hμ A hq hqpos
  have hl := mul_le_mul_of_nonneg_left hg (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have heq : Real.log 2 * (∑ z, μ z * stoch_to_det.lg (1 / q (A z))) =
      ∑ z, μ z * Real.log (1 / q (A z)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [stoch_to_det.lg_eq_log_div]
    field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  rwa [heq] at hl

/-- Fixed-seed Gibbs and finite source averaging; the auxiliary seed changes only the reference. -/
lemma race_entropy_from_reference {Ω κ Ξ : Type} [Fintype Ω] [Fintype κ]
    [DecidableEq Ω] [DecidableEq κ] [Nonempty κ] [MeasurableSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (a c : ℝ) {μ : Ω → ℝ} {r : Ω → κ → ℝ}
    (hμ : stoch_to_det.IsPMF μ)
    (hr : ∀ z, μ z ≠ 0 → stoch_to_det.IsPMF (r z))
    (hrpos : ∀ z, μ z ≠ 0 → ∀ i, 0 < r z i)
    (Q : (κ → ℝ) × Ξ → κ → ℝ)
    (hQ : ∀ᵐ w ∂(stoch_to_det.seedLaw κ).prod ν,
      stoch_to_det.IsPMF (Q w) ∧ ∀ i, 0 < Q w i)
    (hInt : ∀ z, μ z ≠ 0 → Integrable
      (fun w : (κ → ℝ) × Ξ =>
        Real.log (1 / Q w (stoch_to_det.SharedRace.sharedWinner r w.1 z)))
      ((stoch_to_det.seedLaw κ).prod ν))
    (hLoss : ∀ z, μ z ≠ 0 →
      (∫ w : (κ → ℝ) × Ξ,
        Real.log (1 / Q w (stoch_to_det.SharedRace.sharedWinner r w.1 z))
          ∂(stoch_to_det.seedLaw κ).prod ν) ≤
      a * (∑ i, r z i * Real.log (r z i / stoch_to_det.SharedRace.posteriorMean μ r i)) +
      c * (1 - ∑ i, (r z i)^2)) :
    Real.log 2 * stoch_to_det.SharedRace.sharedRaceEntropy μ r ≤
      a * (Real.log 2 * stoch_to_det.MI Prod.fst Prod.snd
        (stoch_to_det.SharedRace.posteriorJoint μ r)) +
      c * stoch_to_det.SharedRace.categoricalMismatch μ r := by
  let ρ := (stoch_to_det.seedLaw κ).prod ν
  let loss : Ω → (κ → ℝ) × Ξ → ℝ := fun z w =>
    Real.log (1 / Q w (stoch_to_det.SharedRace.sharedWinner r w.1 z))
  have hzInt (z : Ω) : Integrable (fun w => μ z * loss z w) ρ := by
    by_cases hz : μ z = 0
    · simp only [hz, zero_mul]
      exact integrable_const 0
    · exact (hInt z hz).const_mul (μ z)
  have hsumInt : Integrable (fun w => ∑ z, μ z * loss z w) ρ :=
    integrable_finsetSum _ (fun z _ => hzInt z)
  have hHInt : Integrable (fun w : (κ → ℝ) × Ξ =>
      Real.log 2 * stoch_to_det.H (stoch_to_det.push
        (stoch_to_det.SharedRace.sharedWinner r w.1) μ)) ρ :=
    ((stoch_to_det.SharedRace.integrable_sharedWinner_code r
      (fun A => stoch_to_det.H (stoch_to_det.push A μ))).const_mul (Real.log 2)).comp_fst ν
  have hGibbs : (∫ w : (κ → ℝ) × Ξ,
      Real.log 2 * stoch_to_det.H (stoch_to_det.push
        (stoch_to_det.SharedRace.sharedWinner r w.1) μ) ∂ρ) ≤
      ∫ w, ∑ z, μ z * loss z w ∂ρ := by
    apply integral_mono_ae hHInt hsumInt
    filter_upwards [hQ] with w hw
    exact race_gibbs_nats hμ (stoch_to_det.SharedRace.sharedWinner r w.1) hw.1 hw.2
  have hleft : (∫ w : (κ → ℝ) × Ξ,
      Real.log 2 * stoch_to_det.H (stoch_to_det.push
        (stoch_to_det.SharedRace.sharedWinner r w.1) μ) ∂ρ) =
      Real.log 2 * stoch_to_det.SharedRace.sharedRaceEntropy μ r := by
    rw [integral_prod _ hHInt]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    rw [integral_const_mul]
    rfl
  rw [hleft, integral_finsetSum _ (fun z _ => hzInt z)] at hGibbs
  have hbound (z : Ω) : (∫ w, μ z * loss z w ∂ρ) ≤
      μ z * (a * (∑ i, r z i * Real.log
        (r z i / stoch_to_det.SharedRace.posteriorMean μ r i)) +
        c * (1 - ∑ i, (r z i)^2)) := by
    by_cases hz : μ z = 0
    · simp [hz]
    · rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hLoss z hz) (hμ.nonneg z)
  have hsum := Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset Ω)) => hbound z)
  have hright : (∑ z, μ z *
      (a * (∑ i, r z i * Real.log (r z i / stoch_to_det.SharedRace.posteriorMean μ r i)) +
      c * (1 - ∑ i, (r z i)^2))) =
      a * (Real.log 2 * stoch_to_det.MI Prod.fst Prod.snd
        (stoch_to_det.SharedRace.posteriorJoint μ r)) +
      c * stoch_to_det.SharedRace.categoricalMismatch μ r := by
    have hkl := stoch_to_det.SharedRace.posteriorMI_mul_logTwo_eq_expectedKL hμ hr hrpos
    change Real.log 2 * stoch_to_det.MI Prod.fst Prod.snd
      (stoch_to_det.SharedRace.posteriorJoint μ r) = _ at hkl
    rw [hkl]
    unfold stoch_to_det.SharedRace.categoricalMismatch
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    ring
  exact hGibbs.trans (hsum.trans_eq hright)

/-- The max only totalizes invalid appendage sequences; it is inactive a.s. for positive spacings. -/
lemma race_reference_isPMF {κ : Type} [Fintype κ] [Nonempty κ]
    (π : κ → ℝ) (hπpos : ∀ i, 0 < π i) (a : ℝ)
    (w : (κ → ℝ) × (κ → ℕ → ℝ)) :
    let S : κ → ℝ := fun i => (π i)^a * (Real.exp (-w.1 i))^(-a) *
      (1 + max 0 (Vtail a (Real.exp (-w.1 i)) (w.2 i)))
    let Q : κ → ℝ := fun i => S i / ∑ k, S k
    stoch_to_det.IsPMF Q ∧ ∀ i, 0 < Q i := by
  dsimp only
  let S : κ → ℝ := fun i => (π i)^a * (Real.exp (-w.1 i))^(-a) *
    (1 + max 0 (Vtail a (Real.exp (-w.1 i)) (w.2 i)))
  have hS (i : κ) : 0 < S i := by
    apply mul_pos
    · exact mul_pos (Real.rpow_pos_of_pos (hπpos i) a)
        (Real.rpow_pos_of_pos (Real.exp_pos _) (-a))
    · have hmax := le_max_left 0 (Vtail a (Real.exp (-w.1 i)) (w.2 i))
      linarith
  have hs : 0 < ∑ k, S k := by
    exact Finset.sum_pos' (fun k _ => (hS k).le)
      ⟨Classical.choice inferInstance, Finset.mem_univ _, hS _⟩
  constructor
  · constructor
    · intro i
      exact (div_pos (hS i) hs).le
    · change (∑ i, S i / ∑ k, S k) = 1
      rw [← Finset.sum_div, div_self hs.ne']
  · intro i
    exact div_pos (hS i) hs

end

end StochasticToDeterministicLatents.General
