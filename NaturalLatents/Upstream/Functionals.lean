-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/Functionals.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised.
-- Source: the DLorell/stoch_to_det main branch, taken from the head of pull request #6 by Jeremy Gillen at the revision above.
import NaturalLatents.Upstream.Entropy

/-!
# Latents, the score, and the two functionals `τ` and `T`


## Support handling

We fix `𝒮 := supp p` without modelling it as a subtype: every object lives on
the ambient finite product
`α × β`, and membership in the support appears as a hypothesis (`p z ≠ 0`) or a
support condition (`Supported`). A connected component is then a law on the
same `α × β` that vanishes off the component, and `reduce_to_connected`
quantifies over the same `α`, `β`.

Statements consequently carry `Supported` / positivity hypotheses explicitly,
since `Real.log 0 = 0` gives junk values off the support.
-/

namespace stoch_to_det

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-! ### Supports and connectedness -/

/-- The support of a finite measure, as a `Finset`. -/
noncomputable def support (m : α × β → ℝ) : Finset (α × β) := univ.filter (fun z => m z ≠ 0)

/-- `m` vanishes outside `S`. -/
def Supported (S : Finset (α × β)) (m : α × β → ℝ) : Prop := ∀ z ∉ S, m z = 0

/-- Two cells are adjacent when they share a row or a column. The connected
components of this relation on `S` are exactly the connected components of the
bipartite support graph of the support decomposition (a component occupies a set of columns and a set
of rows disjoint from every other component's). -/
def Adj (z z' : α × β) : Prop := z.1 = z'.1 ∨ z.2 = z'.2

/-- `S` is connected: any two of its cells are joined by a chain of cells of `S`
each sharing a row or column with the next. -/
def IsConnected (S : Finset (α × β)) : Prop :=
  ∀ z ∈ S, ∀ z' ∈ S, Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ Adj a b) z z'

/-! ### Latents -/

/-- A **latent** for `p`: a finite mixture representation `p = ∑ᵥ λᵥ qᵥ`
The index type is bundled, so `Latent p` lives one universe up. -/
structure Latent (p : α × β → ℝ) where
  /-- The (finite) alphabet of the latent variable `V`. -/
  ι : Type
  /-- Finiteness of the latent alphabet. -/
  fin : Fintype ι
  /-- Decidable equality on the latent alphabet. -/
  dec : DecidableEq ι
  /-- The prior `λ`. -/
  prior : ι → ℝ
  /-- The components `qᵥ = P_{Z ∣ V = v}`. -/
  comp : ι → (α × β → ℝ)
  /-- `λ` is a probability law. -/
  prior_isPMF : IsPMF prior
  /-- Each component is a probability law. -/
  comp_isPMF : ∀ v, IsPMF (comp v)
  /-- The mixture reconstructs `p`. -/
  mixture : ∀ z, ∑ v, prior v * comp v z = p z

attribute [instance] Latent.fin Latent.dec

namespace Latent

variable {p : α × β → ℝ}

/-- A latent's index type is never empty: its prior is a probability law,
and an empty sum cannot be `1`. -/
instance nonempty_ι (V : Latent p) : Nonempty V.ι := by
  by_contra h
  let : IsEmpty V.ι := not_nonempty_iff.mp h
  have htotal := V.prior_isPMF.total
  simp [mass] at htotal

/-- The joint law of `(V, Z)` on `ι × (α × β)`. -/
noncomputable def joint (V : Latent p) : V.ι × (α × β) → ℝ :=
  fun w => V.prior w.1 * V.comp w.1 w.2

omit [DecidableEq α] [DecidableEq β] in
lemma joint_isPMF (V : Latent p) : IsPMF V.joint := by
  refine ⟨?_, ?_⟩
  · intro w
    exact mul_nonneg (V.prior_isPMF.nonneg w.1) ((V.comp_isPMF w.1).nonneg w.2)
  · rw [mass, Fintype.sum_prod_type]
    simp only [joint]
    simp_rw [← mul_sum]
    have hcomp : ∀ v, ∑ z, V.comp v z = 1 := fun v => by
      simpa [mass] using (V.comp_isPMF v).total
    simp_rw [hcomp, mul_one]
    simpa [mass] using V.prior_isPMF.total

/-- The **score** `S_p(V) := I(X;Y ∣ V) + I(V;X ∣ Y) + I(V;Y ∣ X)` -/
noncomputable def score (V : Latent p) : ℝ :=
  condMI (fun w => w.2.1) (fun w => w.2.2) (fun w => w.1) V.joint
    + condMI (fun w => w.1) (fun w => w.2.1) (fun w => w.2.2) V.joint
    + condMI (fun w => w.1) (fun w => w.2.2) (fun w => w.2.1) V.joint

lemma score_nonneg (V : Latent p) : 0 ≤ V.score := by
  unfold score
  exact add_nonneg
    (add_nonneg
      (condMI_nonneg V.joint_isPMF (fun w => w.2.1) (fun w => w.2.2) (fun w => w.1))
      (condMI_nonneg V.joint_isPMF (fun w => w.1) (fun w => w.2.1) (fun w => w.2.2)))
    (condMI_nonneg V.joint_isPMF (fun w => w.1) (fun w => w.2.2) (fun w => w.2.1))

/-- A latent is **deterministic** when its components have pairwise disjoint
supports, i.e. `V = f(Z)` for a function `f`. -/
def IsDet (V : Latent p) : Prop :=
  ∀ z, ∀ v v', V.prior v * V.comp v z ≠ 0 → V.prior v' * V.comp v' z ≠ 0 → v = v'

/-- The constant latent, witnessing `T p ≤ I(X;Y)` and, in particular,
nonemptiness of both index sets below. -/
noncomputable def const (hp : IsPMF p) : Latent p where
  ι := Unit
  fin := inferInstance
  dec := inferInstance
  prior := fun _ => 1
  comp := fun _ => p
  prior_isPMF := ⟨fun _ => zero_le_one, by simp [mass]⟩
  comp_isPMF := fun _ => hp
  mixture := by intro z; simp

omit [DecidableEq α] [DecidableEq β] in
lemma const_isDet (hp : IsPMF p) : (const hp).IsDet := by
  have : Subsingleton (const hp).ι := inferInstanceAs (Subsingleton Unit)
  intro z v v' _ _; exact Subsingleton.elim v v'

end Latent

/-! ### The two functionals

`τ` ranges over all finite latents; `T` over the deterministic ones. Both are
`⨅` over a bundled index; when `p` is not a law the index type may be empty
and the value is Lean's junk `sInf ∅ = 0`, so every substantive statement
carries `IsPMF p`. -/

/-- `τ(p) := inf over finite latents `V` of `S_p(V)`. -/
noncomputable def tau (p : α × β → ℝ) : ℝ := ⨅ V : Latent p, V.score

/-- `T(p) := inf over deterministic `A = f(X,Y)` of `S_p(A)`. -/
noncomputable def T (p : α × β → ℝ) : ℝ := ⨅ V : {V : Latent p // V.IsDet}, V.1.score

/-- The deterministic conditional-information expression
`I(X;Y | Γ) + H(Γ | X) + H(Γ | Y)`. -/
noncomputable def detScore {γ : Type*} [Fintype γ] [DecidableEq γ]
    (p : α × β → ℝ) (Γ : α × β → γ) : ℝ :=
  condMI (fun z : α × β => z.1) (fun z => z.2) Γ p +
    condH Γ (fun z : α × β => z.1) p +
    condH Γ (fun z : α × β => z.2) p

/-- Conditional mutual information as a difference of conditional
entropies. -/
theorem condMI_eq_condH_sub_pair
    {Ω γ δ ε : Type*} [Fintype Ω]
    [Fintype γ] [DecidableEq γ]
    [Fintype δ] [DecidableEq δ]
    [Fintype ε] [DecidableEq ε]
    {m : Ω → ℝ} (_hm : IsPMF m)
    (f : Ω → γ) (g : Ω → δ) (h : Ω → ε) :
    condMI f g h m =
      condH f h m - condH f (fun ω => (g ω, h ω)) m := by
  have hassoc :
      Hvar (fun ω : Ω => (f ω, (g ω, h ω))) m =
        Hvar (fun ω : Ω => (f ω, g ω, h ω)) m := by
    simp
  unfold condMI condH
  rw [hassoc]
  ring

/-- A deterministic function has zero conditional entropy given its input. -/
theorem condH_function_given_pair_zero
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    {p : α × β → ℝ} (hp : IsPMF p) (Γ : α × β → γ) :
    condH Γ (fun z : α × β => z) p = 0 := by
  let graph : α × β → γ × (α × β) := fun z => (Γ z, z)
  have hforward : Hvar graph p ≤ Hvar (fun z : α × β => z) p := by
    simpa [graph, Function.comp_def] using
      Hvar_comp_le hp (fun z : α × β => z) graph
  have hback : Hvar (fun z : α × β => z) p ≤ Hvar graph p := by
    simpa [graph, Function.comp_def] using
      Hvar_comp_le hp graph Prod.snd
  unfold condH
  change Hvar graph p - Hvar (fun z : α × β => z) p = 0
  linarith

theorem condMI_code_X_given_Y
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    {p : α × β → ℝ} (hp : IsPMF p) (Γ : α × β → γ) :
    condMI Γ (fun z : α × β => z.1) (fun z => z.2) p =
      condH Γ (fun z : α × β => z.2) p := by
  rw [condMI_eq_condH_sub_pair hp]
  have hz := condH_function_given_pair_zero hp Γ
  have hz' : condH Γ (fun z : α × β => (z.1, z.2)) p = 0 := by
    simpa using hz
  rw [hz', sub_zero]

theorem condMI_code_Y_given_X
    {γ : Type*} [Fintype γ] [DecidableEq γ]
    {p : α × β → ℝ} (hp : IsPMF p) (Γ : α × β → γ) :
    condMI Γ (fun z : α × β => z.2) (fun z => z.1) p =
      condH Γ (fun z : α × β => z.1) p := by
  rw [condMI_eq_condH_sub_pair hp]
  have hz := condH_function_given_pair_zero hp Γ
  have hz' : condH Γ (fun z : α × β => (z.2, z.1)) p = 0 := by
    unfold condH at hz ⊢
    have hswap :
        Hvar (fun z : α × β => (Γ z, (z.2, z.1))) p =
          Hvar (fun z : α × β => (Γ z, (z.1, z.2))) p := by
      let e : γ × (α × β) ≃ γ × (β × α) :=
        Equiv.prodCongr (Equiv.refl γ) (Equiv.prodComm α β)
      have he : (fun z : α × β => (Γ z, (z.2, z.1))) =
          fun z => e (Γ z, (z.1, z.2)) := by
        funext z
        rcases z with ⟨x, y⟩
        rfl
      rw [he]
      exact Hvar_equiv hp (fun z : α × β => (Γ z, (z.1, z.2))) e
    have hbase : Hvar (fun z : α × β => (z.2, z.1)) p =
        Hvar (fun z : α × β => (z.1, z.2)) p := by
      have he : (fun z : α × β => (z.2, z.1)) =
          fun z => (Equiv.prodComm α β) (z.1, z.2) := by
        funext z
        rcases z with ⟨x, y⟩
        rfl
      rw [he]
      exact Hvar_equiv hp (fun z : α × β => (z.1, z.2))
        (Equiv.prodComm α β)
    rw [hswap, hbase]
    exact hz
  rw [hz', sub_zero]

/-- The infimum `tau p` is below the score of every finite latent. -/
lemma tau_le_score {p : α × β → ℝ} (V : Latent p) : tau p ≤ V.score := by
  unfold tau
  have hb : BddBelow (Set.range fun W : Latent p => W.score) :=
    ⟨0, by
      rintro _ ⟨W, rfl⟩
      exact W.score_nonneg⟩
  exact ciInf_le hb V

/-- The score of any single deterministic latent bounds `T` from above. This is
the final bound uses `T`: `exists_good_seed` exhibits one suitable seed. -/
lemma T_le_score {p : α × β → ℝ} (V : Latent p) (hV : V.IsDet) : T p ≤ V.score := by
  unfold T
  have hb : BddBelow (Set.range fun W : {W : Latent p // W.IsDet} => W.1.score) :=
    ⟨0, by rintro _ ⟨W, rfl⟩; exact W.1.score_nonneg⟩
  exact ciInf_le_of_le hb ⟨V, hV⟩ le_rfl

end stoch_to_det
