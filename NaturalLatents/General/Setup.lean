-- Adapted from the author's earlier repository (StochasticToDeterministicLatents);
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised; namespace renamed to NaturalLatents.General.
import NaturalLatents.General.Definitions

/-!
# Attaining latents for connected laws

For a law with connected support, `exists_setup_of_connected` constructs a `CommonSetup`:
an attaining latent whose components are distinct positive contacts of one feasible kernel.
The construction clusters the components of a `stoch_to_det.SeedSetup`; later estimates use
the resulting positive priors, common support, and posterior rows.

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

lemma setupConn_comp_eq_Q {p : Law X Y} {D : stoch_to_det.SeedSetup p}
    (K : stoch_to_det.Clustering D) (i : D.L.ι) : D.L.comp i = K.Q (K.cl i) := by
  unfold stoch_to_det.Clustering.Q
  apply (K.spec i (Classical.choose (K.surj (K.cl i)))).mp
  exact (Classical.choose_spec (K.surj (K.cl i))).symm

lemma setupConn_prior_pos {p : Law X Y} {D : stoch_to_det.SeedSetup p}
    (K : stoch_to_det.Clustering D) (c : K.κ) : 0 < K.s c := by
  classical
  obtain ⟨i, hi⟩ := K.surj c
  have hle : D.L.prior i ≤ K.s c := by
    unfold stoch_to_det.Clustering.s
    exact Finset.single_le_sum (fun j _ => D.L.prior_isPMF.nonneg j) (by simp [hi])
  exact (D.prior_pos i).trans_le hle

lemma setupConn_sum_weighted {p : Law X Y} {D : stoch_to_det.SeedSetup p}
    (K : stoch_to_det.Clustering D) (F : Law X Y → ℝ) :
    (∑ c, K.s c * F (K.Q c)) = ∑ i, D.L.prior i * F (D.L.comp i) := by
  classical
  calc
    (∑ c, K.s c * F (K.Q c)) =
        ∑ c, ∑ i ∈ Finset.univ.filter (fun i => K.cl i = c),
          D.L.prior i * F (D.L.comp i) := by
      apply Finset.sum_congr rfl
      intro c _
      unfold stoch_to_det.Clustering.s
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hic : K.cl i = c := (Finset.mem_filter.mp hi).2
      rw [setupConn_comp_eq_Q K i, hic]
    _ = ∑ i, D.L.prior i * F (D.L.comp i) :=
      Finset.sum_fiberwise Finset.univ K.cl (fun i => D.L.prior i * F (D.L.comp i))

/-- A law with connected support has an attaining latent with a feasible kernel whose components are distinct
positive contacts (`CommonSetup`). -/
theorem exists_setup_of_connected {p : Law X Y} (hp : stoch_to_det.IsPMF p)
    (hconn : stoch_to_det.IsConnected (stoch_to_det.support p)) : Nonempty (CommonSetup p) := by
  classical
  obtain ⟨D⟩ := stoch_to_det.exists_seedSetup hp hconn
  obtain ⟨K⟩ := stoch_to_det.exists_clustering D
  let L : FiniteLatent p := {
    ι := K.κ
    fin := inferInstance
    dec := inferInstance
    prior := K.s
    comp := K.Q
    prior_isPMF := by
      constructor
      · intro c
        exact (setupConn_prior_pos K c).le
      · unfold stoch_to_det.mass stoch_to_det.Clustering.s
        rw [Finset.sum_fiberwise Finset.univ K.cl D.L.prior]
        exact D.L.prior_isPMF.total
    comp_isPMF := fun c => (K.Q_isContact c).1
    mixture := fun z => (setupConn_sum_weighted K (fun q => q z)).trans (D.L.mixture z)
  }
  let w : Law X Y := fun z => if z ∈ stoch_to_det.support p then D.w z else 0
  have hw_eq : ∀ z ∈ stoch_to_det.support p, w z = D.w z := by
    intro z hz
    simp only [w, ite_eq_left hz]
  have hw : FeasibleKernel (stoch_to_det.support p) w := by
    constructor
    · intro z hz
      rw [hw_eq z hz]
      exact D.feasible.1 z hz
    · intro u v hu hv
      have hLambda : stoch_to_det.Lambda (stoch_to_det.support p) w u v =
          stoch_to_det.Lambda (stoch_to_det.support p) D.w u v := by
        unfold stoch_to_det.Lambda
        apply Finset.sum_congr rfl
        intro z hz
        rw [hw_eq z hz]
      rw [hLambda]
      exact D.feasible.2 u v hu hv
  have hpositive : ∀ i, PositiveOn (stoch_to_det.support p) (L.comp i) := by
    intro i z hz
    have hsupp := stoch_to_det.contact_support_eq D.feasible hconn (K.Q_isContact i)
    have hne : K.Q i z ≠ 0 := by
      have hzQ : z ∈ stoch_to_det.support (K.Q i) := by
        rw [hsupp]
        exact hz
      simpa only [stoch_to_det.support, Finset.mem_filter, Finset.mem_univ, true_and]
        using hzQ
    exact lt_of_le_of_ne ((K.Q_isContact i).1.nonneg z) (Ne.symm hne)
  refine ⟨{
    L := L
    w := w
    feasible := hw
    attained := ?_
    prior_pos := setupConn_prior_pos K
    distinct := K.Q_injective
    contact := ?_
    positive := hpositive
    rows_pos := ?_
  }⟩
  · calc
      M L + B L = c p + ∑ i, L.prior i * phi (L.comp i) := cost_identity p hp L
      _ = c p + ∑ i, D.L.prior i * phi (D.L.comp i) := by
        rw [show (∑ i, L.prior i * phi (L.comp i)) =
          ∑ i, D.L.prior i * phi (D.L.comp i) from setupConn_sum_weighted K phi]
      _ = M D.L + B D.L := (cost_identity p hp D.L).symm
      _ = tau p := by rw [budgets_eq_score, D.optimal]; rfl
  · intro i
    refine ⟨(K.Q_isContact i).1, (K.Q_isContact i).2.1, ?_⟩
    intro z hz
    rw [hw_eq z hz]
    exact (K.Q_isContact i).2.2 z hz
  · intro z hz i
    have hpz : 0 < p z := by
      have hne : p z ≠ 0 := by
        simpa only [stoch_to_det.support, Finset.mem_filter, Finset.mem_univ, true_and]
          using hz
      exact lt_of_le_of_ne (hp.nonneg z) (Ne.symm hne)
    exact div_pos (mul_pos (setupConn_prior_pos K i) (hpositive i z hz)) hpz

end

end NaturalLatents.General
