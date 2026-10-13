-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/Quotient.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised.
import NaturalLatents.Upstream.Seed
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic.NormNum
import NaturalLatents.Upstream.Prelude
import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# Duplicate clustering and the race interface

This file defines `Clustering`, which groups latent labels having identical
component laws, and develops the resulting cluster-level posterior identities.
It also defines `RaceQuantities`, the numerical interface through which the
race construction supplies entropy, scalar-channel, and residual bounds.
-/

namespace stoch_to_det

open Finset MeasureTheory ProbabilityTheory

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-! ### The duplicate clustering -/

/-- A duplicate clustering: a cluster map identifying labels
with equal component laws. -/
structure Clustering {p : α × β → ℝ} (D : SeedSetup p) : Type 1 where
  /-- Cluster index type. -/
  κ : Type
  /-- Finiteness. -/
  fin : Fintype κ
  /-- Decidable equality. -/
  dec : DecidableEq κ
  /-- The cluster map. -/
  cl : D.L.ι → κ
  /-- Clusters are exactly the fibres of "equal component law". -/
  spec : ∀ ℓ ℓ', cl ℓ = cl ℓ' ↔ D.L.comp ℓ = D.L.comp ℓ'
  /-- Every cluster is inhabited. -/
  surj : Function.Surjective cl

attribute [instance] Clustering.fin Clustering.dec

/-- Every setup has a duplicate quotient (`DecidableEq` on component laws is
classical). -/
theorem exists_clustering {p : α × β → ℝ} (D : SeedSetup p) : Nonempty (Clustering D) := by
  classical
  let r : Setoid D.L.ι := {
    r ℓ ℓ' := D.L.comp ℓ = D.L.comp ℓ'
    iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
  }
  let cl : D.L.ι → Quotient r := Quotient.mk r
  exact ⟨{
    κ := Quotient r
    fin := Fintype.ofSurjective cl Quotient.mk_surjective
    dec := Classical.decEq _
    cl := cl
    spec := by
      intro ℓ ℓ'
      exact Quotient.eq
    surj := Quotient.mk_surjective
  }⟩

namespace Clustering

variable {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)

/-- The common component law `Q_c` of a cluster. -/
noncomputable def Q (c : K.κ) : α × β → ℝ := D.L.comp (Classical.choose (K.surj c))

/-- The cluster mass `s_c := ∑_{ℓ ∈ c} λ_ℓ`. -/
noncomputable def s (c : K.κ) : ℝ := ∑ ℓ ∈ univ.filter (fun ℓ => K.cl ℓ = c), D.L.prior ℓ

/-- Distinct clusters are pairwise distinct contacts of `w` — the hypothesis
required by the later separation estimates. -/
theorem Q_isContact (c : K.κ) : IsContact (support p) D.w (K.Q c) := by
  let ℓ : D.L.ι := Classical.choose (K.surj c)
  have hℓ : D.L.prior ℓ ≠ 0 := (D.prior_pos ℓ).ne'
  simpa [Q, ℓ] using D.contact ℓ hℓ

theorem Q_injective : Function.Injective K.Q := by
  intro c c' hQ
  have hrep :
      K.cl (Classical.choose (K.surj c)) =
        K.cl (Classical.choose (K.surj c')) :=
    (K.spec _ _).mpr (by simpa [Q] using hQ)
  simpa only [Classical.choose_spec (K.surj c),
    Classical.choose_spec (K.surj c')] using hrep

private noncomputable def posteriorJoint (g : K.κ) : D.L.ι × (α × β) → ℝ :=
  fun v => K.Q g v.2 * D.post v.1 v.2

/-! ### The exact race law

At fixed `Z = z` the cluster clocks `T_c := X*_c/σ_c(z)` are
independent `Exp(σ_c(z))` (rate form), giving

* `P(Z=z, B=b, U ∈ du ∣ C₀=g) = q_g(z) e^{−u/σ_b(z)} du`  (7.1)
* losing clocks `X*_c ∼ u r_c(z) + Exp(1)`, independent          (7.2)
* `T := U/σ_B(Z) ∼ Exp(1)` independent of `(B,Z)`, and `P(B=b ∣ Z=z) = σ_b(z)`.

These identities feed the scalar and losing-vector channel bounds. -/

end Clustering

/-! ### The seed interface

The equation fields record the chain decomposition; the structure also records
nonnegativity, the channel bounds, and the fixed-seed residual link. -/

end stoch_to_det
