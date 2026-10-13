-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/CoordinateRace.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed.
import NaturalLatents.Upstream.PoweredRaceWinner

/-! Conditioning the shared-race entropy bound on an observed coordinate. -/

namespace stoch_to_det

open Finset MeasureTheory

lemma coordinate_condMI_eq_sum
    {Ω Γ Δ Ξ : Type*} [Fintype Ω] [Fintype Γ] [Fintype Δ] [Fintype Ξ]
    [DecidableEq Γ] [DecidableEq Δ] [DecidableEq Ξ]
    {m : Ω → ℝ} (hm : IsPMF m) (f : Ω → Γ) (g : Ω → Δ) (h : Ω → Ξ) :
    condMI f g h m = ∑ k, MI f g (fun z => if h z = k then m z else 0) := by
  let mh : Ξ → Ω → ℝ := fun k z => if h z = k then m z else 0
  have hF := Hvar_pair_eq_sum_fibers hm f h
  have hG := Hvar_pair_eq_sum_fibers hm g h
  have hFG := Hvar_pair_eq_sum_fibers hm (fun z => (f z, g z)) h
  change Hvar (fun z => (f z, h z)) m = Hvar h m + ∑ k, H (push f (mh k)) at hF
  change Hvar (fun z => (g z, h z)) m = Hvar h m + ∑ k, H (push g (mh k)) at hG
  change Hvar (fun z => ((f z, g z), h z)) m = Hvar h m +
    ∑ k, H (push (fun z => (f z, g z)) (mh k)) at hFG
  have hAssoc : Hvar (fun z => (f z, g z, h z)) m =
      Hvar (fun z => ((f z, g z), h z)) m := by
    simpa using Hvar_equiv hm (fun z => ((f z, g z), h z))
      (Equiv.prodAssoc Γ Δ Ξ)
  unfold condMI
  rw [hF, hG, hAssoc, hFG]
  simp only [MI, Hvar, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

namespace SharedRace

universe u v
variable {Ω : Type u} {κ : Type} {Γ : Type v}
  [Fintype Ω] [Fintype κ] [Fintype Γ]
  [DecidableEq Ω] [DecidableEq κ] [DecidableEq Γ] [Nonempty κ]

lemma integrable_sharedWinner_code (r : Ω → κ → ℝ) (F : (Ω → κ) → ℝ) :
    Integrable (fun E : κ → ℝ => F (sharedWinner r E)) (seedLaw κ) := by
  let : MeasurableSpace κ := ⊤
  have hA : Measurable (fun E : κ → ℝ => sharedWinner r E) := by
    apply measurable_pi_lambda
    intro z
    unfold sharedWinner weightedLexWinner
    apply measurable_lexMax
    intro i
    exact measurable_const.add (measurable_pi_apply i)
  apply Integrable.of_bound
    ((measurable_of_finite F).comp hA).aestronglyMeasurable
    (∑ A : Ω → κ, ‖F A‖)
  filter_upwards [] with E
  exact Finset.single_le_sum (fun A _ => norm_nonneg (F A))
    (Finset.mem_univ (sharedWinner r E))

/-- A uniform shared-race entropy estimate over source laws and posterior rows. -/
def SharedRaceEntropyBound (a b : ℝ) : Prop :=
  ∀ (μ : Ω → ℝ) (r : Ω → κ → ℝ),
      IsPMF μ → (∀ z, μ z ≠ 0 → IsPMF (r z)) →
      (∀ z, μ z ≠ 0 → ∀ i, 0 < r z i) →
      sharedRaceEntropy μ r ≤ a * MI Prod.fst Prod.snd (posteriorJoint μ r) +
        b * categoricalMismatch μ r

/-- Homogeneous extension of any source-law entropy comparison. -/
theorem sharedRaceEntropy_le_of_finMeas
    (a b : ℝ) (h : SharedRaceEntropyBound (Ω := Ω) (κ := κ) a b)
    {μ : Ω → ℝ} {r : Ω → κ → ℝ} (hμ : IsFinMeas μ)
    (hr : ∀ z, μ z ≠ 0 → IsPMF (r z))
    (hrpos : ∀ z, μ z ≠ 0 → ∀ i, 0 < r z i) :
    sharedRaceEntropy μ r ≤ a * MI Prod.fst Prod.snd (posteriorJoint μ r) +
      b * categoricalMismatch μ r := by
  have hm0 : 0 ≤ mass μ := Finset.sum_nonneg fun z _ => hμ z
  by_cases hm : mass μ = 0
  · have hzero : μ = 0 := by
      funext z
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => hμ z)).mp hm z (mem_univ z)
    simp [hzero, sharedRaceEntropy, posteriorJoint, categoricalMismatch, MI, Hvar, H,
      push, mass]
  have hmp : 0 < mass μ := lt_of_le_of_ne hm0 (Ne.symm hm)
  let ν : Ω → ℝ := fun z => μ z / mass μ
  have hν : IsPMF ν := by
    refine ⟨fun z => div_nonneg (hμ z) hm0, ?_⟩
    change (∑ z, μ z / mass μ) = 1
    rw [← Finset.sum_div]
    exact div_self hm
  have hs := h ν r hν
    (fun z hz => hr z (fun hh => hz (by simp [ν, hh])))
    (fun z hz => hrpos z (fun hh => hz (by simp [ν, hh])))
  have hrec : (fun z => mass μ * ν z) = μ := by
    funext z
    dsimp [ν]
    field_simp
  have hH : mass μ * sharedRaceEntropy ν r = sharedRaceEntropy μ r := by
    unfold sharedRaceEntropy
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with E
    rw [← H_smul hm0, ← push_smul, hrec]
  have hMI : mass μ * MI Prod.fst Prod.snd (posteriorJoint ν r) =
      MI Prod.fst Prod.snd (posteriorJoint μ r) := by
    have hfin := (posteriorJoint_isPMF_of_support hν
      (fun z hz => hr z (fun hh => hz (by simp [ν, hh])))).nonneg
    rw [← MI_smul hfin Prod.fst Prod.snd hm0]
    congr 1
    funext zi
    change mass μ * (ν zi.1 * r zi.1 zi.2) = μ zi.1 * r zi.1 zi.2
    rw [← mul_assoc, congrFun hrec zi.1]
  have hd : mass μ * categoricalMismatch ν r = categoricalMismatch μ r := by
    unfold categoricalMismatch
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [← mul_assoc, congrFun hrec z]
  have hh := mul_le_mul_of_nonneg_left hs hm0
  rw [hH, mul_add] at hh
  have heq : mass μ * (a * MI Prod.fst Prod.snd (posteriorJoint ν r)) +
      mass μ * (b * categoricalMismatch ν r) =
      a * MI Prod.fst Prod.snd (posteriorJoint μ r) + b * categoricalMismatch μ r := by
    calc
      _ = a * (mass μ * MI Prod.fst Prod.snd (posteriorJoint ν r)) +
          b * (mass μ * categoricalMismatch ν r) := by ring
      _ = _ := by rw [hMI, hd]
  rwa [heq] at hh

/-- A universal shared-race entropy estimate can be conditioned on any finite
function of the source, without changing its mismatch term. -/
theorem conditional_entropy_le_of_uniform_entropy_bound
    (a b : ℝ) (h : SharedRaceEntropyBound (Ω := Ω) (κ := κ) a b)
    {μ : Ω → ℝ} {r : Ω → κ → ℝ} (hμ : IsPMF μ)
    (hr : ∀ z, μ z ≠ 0 → IsPMF (r z))
    (hrpos : ∀ z, μ z ≠ 0 → ∀ i, 0 < r z i) (g : Ω → Γ) :
    (∫ E : κ → ℝ, condH (sharedWinner r E) g μ ∂seedLaw κ) ≤
      a * condMI Prod.fst Prod.snd (fun zi : Ω × κ => g zi.1) (posteriorJoint μ r) +
        b * categoricalMismatch μ r := by
  let fiber : Γ → Ω → ℝ := fun c z => if g z = c then μ z else 0
  have hfin (c : Γ) : IsFinMeas (fiber c) := by
    intro z
    dsimp [fiber]
    split <;> simp_all [hμ.nonneg z]
  have hs (c : Γ) : sharedRaceEntropy (fiber c) r ≤
      a * MI Prod.fst Prod.snd (posteriorJoint (fiber c) r) +
        b * categoricalMismatch (fiber c) r := by
    apply sharedRaceEntropy_le_of_finMeas a b h (hfin c)
    · intro z hz
      have hsupp : μ z ≠ 0 := fun hh => hz (by simp [fiber, hh])
      exact hr z hsupp
    · intro z hz
      have hsupp : μ z ≠ 0 := fun hh => hz (by simp [fiber, hh])
      exact hrpos z hsupp
  have hpost (c : Γ) : posteriorJoint (fiber c) r =
      fun zi : Ω × κ => if g zi.1 = c then posteriorJoint μ r zi else 0 := by
    funext zi
    by_cases hh : g zi.1 = c <;> simp [posteriorJoint, fiber, hh]
  have hd : (∑ c, categoricalMismatch (fiber c) r) = categoricalMismatch μ r := by
    unfold categoricalMismatch
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    simp [fiber]
  calc
    _ = ∑ c, sharedRaceEntropy (fiber c) r := by
      simp_rw [condH_eq_sum_H_fibers hμ]
      rw [integral_finsetSum]
      · rfl
      · intro c _
        exact integrable_sharedWinner_code r (fun A => H (push A (fiber c)))
    _ ≤ ∑ c, (a * MI Prod.fst Prod.snd (posteriorJoint (fiber c) r) +
        b * categoricalMismatch (fiber c) r) := Finset.sum_le_sum fun c _ => hs c
    _ = _ := by
      simp_rw [hpost]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hd,
        ← coordinate_condMI_eq_sum (posteriorJoint_isPMF_of_support hμ hr)]

end SharedRace

section Grouped

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable {p : α × β → ℝ} (D : SeedSetup p) (K : Clustering D)

end Grouped

end stoch_to_det
