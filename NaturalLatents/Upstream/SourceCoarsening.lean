-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/SourceCoarsening.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised.
-- Source: pull request #6 by Jeremy Gillen (powered-reference race coding and the coordinate/table bridges).
import NaturalLatents.Upstream.Envelope

/-! Lifting a latent of a coordinatewise coarsening back to the original source. -/

namespace stoch_to_det.SourceCoarsening

open Finset

section Joint
variable {X Y : Type*} {K : Type} [Fintype X] [Fintype Y] [Fintype K]
  [DecidableEq X] [DecidableEq Y] [DecidableEq K]

private def priorOf (r : K × (X × Y) → ℝ) (k : K) : ℝ := ∑ z, r (k, z)

omit [Fintype K] [DecidableEq X] [DecidableEq Y] [DecidableEq K] in
private lemma joint_zero {r : K × (X × Y) → ℝ} (hr : IsFinMeas r)
    {k : K} (hk : priorOf r k = 0) (z : X × Y) : r (k, z) = 0 := by
  have h := Finset.single_le_sum (fun t (_ : t ∈ (univ : Finset (X × Y))) =>
    hr (k, t)) (Finset.mem_univ z)
  change r (k, z) ≤ priorOf r k at h
  exact le_antisymm (hk ▸ h) (hr _)

/-- A finite joint law with the specified source marginal defines a latent.
Zero-prior labels are filled with the source law. -/
noncomputable def ofJoint {p : X × Y → ℝ} (hp : IsPMF p)
    (r : K × (X × Y) → ℝ) (hr : IsPMF r) (hsource : push Prod.snd r = p) :
    Latent p where
  ι := K
  fin := inferInstance
  dec := inferInstance
  prior := priorOf r
  comp := fun k z => if priorOf r k = 0 then p z else r (k, z) / priorOf r k
  prior_isPMF := by
    constructor
    · intro k
      exact Finset.sum_nonneg fun z _ => hr.nonneg (k, z)
    · simpa [mass, priorOf, Fintype.sum_prod_type] using hr.total
  comp_isPMF := by
    intro k
    by_cases hk : priorOf r k = 0
    · simpa [hk] using hp
    · constructor
      · intro z
        simp only [hk, ite_false]
        exact div_nonneg (hr.nonneg _) (Finset.sum_nonneg fun z _ => hr.nonneg (k, z))
      · simp only [mass, hk, ite_false, ← Finset.sum_div]
        exact div_self hk
  mixture := by
    intro z
    have heq (k : K) : priorOf r k *
        (if priorOf r k = 0 then p z else r (k, z) / priorOf r k) = r (k, z) := by
      by_cases hk : priorOf r k = 0
      · simp [hk, joint_zero hr.nonneg hk z]
      · simp [hk, mul_div_cancel₀ _ hk]
    simp_rw [heq]
    have h := congrFun hsource z
    simpa [push, Finset.sum_filter, Fintype.sum_prod_type] using h

theorem ofJoint_joint {p : X × Y → ℝ} (hp : IsPMF p)
    (r : K × (X × Y) → ℝ) (hr : IsPMF r) (hsource : push Prod.snd r = p) :
    (ofJoint hp r hr hsource).joint = r := by
  funext ⟨k, z⟩
  change priorOf r k *
    (if priorOf r k = 0 then p z else r (k, z) / priorOf r k) = r (k, z)
  by_cases hk : priorOf r k = 0
  · simp [hk, joint_zero hr.nonneg hk z]
  · simp [hk, mul_div_cancel₀ _ hk]

theorem ofJoint_score {p : X × Y → ℝ} (hp : IsPMF p)
    (r : K × (X × Y) → ℝ) (hr : IsPMF r) (hsource : push Prod.snd r = p) :
    (ofJoint hp r hr hsource).score =
      condMI (fun v => v.2.1) (fun v => v.2.2) Prod.fst r +
      condMI Prod.fst (fun v => v.2.1) (fun v => v.2.2) r +
      condMI Prod.fst (fun v => v.2.2) (fun v => v.2.1) r := by
  change condMI (fun v : K × (X × Y) => v.2.1) (fun v => v.2.2) Prod.fst
      (ofJoint hp r hr hsource).joint +
      condMI Prod.fst (fun v => v.2.1) (fun v => v.2.2) (ofJoint hp r hr hsource).joint +
      condMI Prod.fst (fun v => v.2.2) (fun v => v.2.1) (ofJoint hp r hr hsource).joint = _
  rw [ofJoint_joint]
  rfl

end Joint

section Channel
variable {Z W : Type*} {K : Type} [Fintype Z] [Fintype W] [Fintype K]
  [DecidableEq Z] [DecidableEq W] [DecidableEq K]

end Channel

section Posterior
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
  {q : A × B → ℝ}

/-- A universe-polymorphic posterior, using the prior at null source atoms. -/
noncomputable def posterior (V : Latent q) (z : A × B) (k : V.ι) : ℝ :=
  if q z = 0 then V.prior k else V.joint (k, z) / q z

end Posterior

section Lift
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
  {p : X × Y → ℝ}

end Lift

end stoch_to_det.SourceCoarsening
