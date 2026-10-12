-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/Quotient.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed.
import NaturalLatents.Upstream.Seed
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic.NormNum
import NaturalLatents.Upstream.Prelude
import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# §7. The duplicate quotient, the exact race law, and the seed interface


The latent labels are grouped into **clusters** by exact equality of component
laws. The point is that the within-cluster posterior
`π_{u∣c}` does **not depend on `z`**, so the seed factorizes exactly: the label
race is the cluster race followed by an independent within-cluster race. That
is what lets §§8-10 analyse a race among *pairwise distinct* contacts, which is
exactly the hypothesis Theorem 6.2 needs.

## The quotient as a fibre map

Clusters are represented as the fibres of a map `cl : ι → κ` rather than as a
quotient type, so cluster-level quantities are `push cl`-images of label-level
ones, `stoch_to_det.Entropy` applies unchanged, and Lemma 7.2(d)'s
`I(L₁;Z ∣ L₀) = I(C₁;Z ∣ C₀)` is a `push_push` computation rather than a
transport.

## The seed-conditioned informations are not defined here

`D = I(ε; Z ∣ A, L₀)`, `scalar = I(U; Z ∣ B, C₀)` and
`cone = I(X*₋B; Z ∣ B, C₀, U)` pair a continuous variable against a finite `Z`,
and their status differs:

* `scalar` conditions on `B, C₀` only — both finite — so it is expressible by
  `condMIcts` (`stoch_to_det.Seed`), with the conditional law of `U` given `(Z=z, B=b)`
  an explicit exponential of mean `σ_b(z)` by Lemma 7.4.
* `cone` conditions additionally on `U`, which is continuous, and `condMIcts`
  does not cover that. The construction never uses `cone` as a standalone object:
  it bounds it in one step by integrating (10.2) against the exact joint
  density of (7.1).
* `D` conditions on the finite `A`, but its argument `ε` is the whole seed
  vector.

§§8-11 are therefore stated against the interface `RaceQuantities` below. The
structure carries the four scalars, the two structural identities, and the two
channel bounds plus the cell-residual link as obligations. Constructing an
instance (`stoch_to_det/Race.lean`, `exists_raceQuantities`) is Lemmas 7.2-7.5 +
Theorems 8.1 and 10.1, and is the only place the seed measure theory lives.
-/

namespace stoch_to_det

open Finset MeasureTheory ProbabilityTheory

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-! ### Definition 7.1 — the duplicate quotient -/

/-- The duplicate quotient of `Definition 7.1`: a cluster map identifying labels
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
Theorem 6.2 and Theorem 9.1 require. -/
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

/-! ### Lemma 7.4 — the exact race law

At fixed `Z = z` the cluster clocks `T_c := X*_c/σ_c(z)` are
independent `Exp(σ_c(z))` (rate form), giving

* `P(Z=z, B=b, U ∈ du ∣ C₀=g) = q_g(z) e^{−u/σ_b(z)} du`  (7.1)
* losing clocks `X*_c ∼ u r_c(z) + Exp(1)`, independent          (7.2)
* `T := U/σ_B(Z) ∼ Exp(1)` independent of `(B,Z)`, and `P(B=b ∣ Z=z) = σ_b(z)`.

These are the inputs to §§8 and 10. -/

end Clustering

/-! ### The seed interface

§§8-11 are theorems about any `RaceQuantities`. Its equation fields are
Lemmas 7.3 and 7.5; the construction also records nonnegativity, the §8/§10
channel bounds, and the §12 cell-residual link. -/

end stoch_to_det
