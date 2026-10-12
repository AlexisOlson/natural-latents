import NaturalLatents.Statement
import NaturalLatents.General
import NaturalLatents.Upstream.TableBoundProof
import NaturalLatents.Upstream.SourceCoarsening

/-!
# The two headline theorems

`table : TableClaim` and `score : ScoreClaim`, for the propositions frozen in
`NaturalLatents/Statement.lean`. The constant is `2789/400 = 6.9725`.

The bound itself is `General.T_le_of_connected` extended to every law by
`General.extension_of_connected`. The passage from latents to probability
tables follows the bridge shape of `TableBoundProof` in DLorell/stoch_to_det
pull request #6 (Jeremy Gillen), with this repository's constant.
-/

open scoped BigOperators

namespace NaturalLatents

/-- The constant of both headline theorems. -/
noncomputable def c : ℝ := 2789 / 400

theorem c_nonneg : 0 ≤ c := by norm_num [c]

theorem c_lt_seven : c < 7 := by norm_num [c]

section Bridge

open stoch_to_det TableInformationProof TableBoundProof

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The optimum form in bits, over bundled latents. -/
theorem T_le_c_mul_tau {p : α × β → ℝ} (hp : IsPMF p) :
    stoch_to_det.T p ≤ c * stoch_to_det.tau p :=
  StochasticToDeterministicLatents.General.bits_of_nats_bound
    (StochasticToDeterministicLatents.General.extension_of_connected c c_nonneg
      (fun _ hq hqconn => StochasticToDeterministicLatents.General.T_le_of_connected hq hqconn) hp)

/-- One optimal deterministic code bounds every finite joint latent law. -/
theorem finite_bound {p : α × β → ℝ} (hp : IsPMF p) :
    ∃ Γ : α × β → Fin (Fintype.card (α × β)),
      ∀ {K : Type} [Fintype K] [DecidableEq K]
        (q : K × (α × β) → ℝ), IsPMF q →
        (∀ z, ∑ v, q (v, z) = p z) →
        condMI Prod.fst Prod.snd Γ p + condH Γ Prod.fst p + condH Γ Prod.snd p
          ≤ c * (condMI (fun w => w.2.1) (fun w => w.2.2) Prod.fst q
              + condMI Prod.fst (fun w => w.2.1) (fun w => w.2.2) q
              + condMI Prod.fst (fun w => w.2.2) (fun w => w.2.1) q) := by
  obtain ⟨Γ, hΓ⟩ := exists_T_optimal_code hp
  refine ⟨Γ, ?_⟩
  intro K _ _ q hq hmarginal
  have hsource : push Prod.snd q = p := by
    funext z
    simpa [push, Finset.sum_filter, Fintype.sum_prod_type] using hmarginal z
  let L := SourceCoarsening.ofJoint hp q hq hsource
  have hbound : detScore p Γ ≤ c * L.score := by
    calc
      detScore p Γ = stoch_to_det.T p := by
        rw [← Latent.ofFunction_score_eq_detScore hp Γ]
        exact hΓ
      _ ≤ c * stoch_to_det.tau p := T_le_c_mul_tau hp
      _ ≤ c * L.score := mul_le_mul_of_nonneg_left (tau_le_score L) c_nonneg
  simpa only [detScore, L, SourceCoarsening.ofJoint_score] using hbound

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

/-- The bound on probability tables, with the core-library error on both sides. -/
theorem table_bound {p : A × B → ℝ} (hp : probability p) :
    ∃ Γ : A × B → Fin (Fintype.card (A × B)),
      ∀ (k : ℕ) (q : A × B × Fin k → ℝ),
        probability q → (∀ a b, ∑ v, q (a, b, v) = p (a, b)) →
        latentError (TableBoundProof.deterministicTable p Γ) ≤ c * latentError q := by
  have hp' : IsPMF p := ⟨hp.1, hp.2⟩
  obtain ⟨Γ, hΓ⟩ := finite_bound hp'
  refine ⟨Γ, ?_⟩
  intro k q hq hmarginal
  have hq' : IsPMF q := ⟨hq.1, hq.2⟩
  let e : A × B × Fin k → Fin k × (A × B) :=
    fun abc => (abc.2.2, (abc.1, abc.2.1))
  have hr : IsPMF (push e q) := isPMF_push hq'
  have hm : ∀ ab, ∑ v, push e q (v, ab) = p ab := by
    intro ⟨a, b⟩
    change (∑ v, push (fun abc : A × B × Fin k =>
      (abc.2.2, (abc.1, abc.2.1))) q (v, (a, b))) = p (a, b)
    rw [← transpose_eq_push]
    exact hmarginal a b
  have h := hΓ (push e q) hr hm
  rw [deterministicTable_error hp', latentError_eq_core hq']
  simpa only [condMI_push_source, Function.comp_def, e, detScore] using h

/-- The bound on probability tables, with conditional entropies on the deterministic side. -/
theorem table_bound_entropy {p : A × B → ℝ} (hp : probability p) :
    ∃ Γ : A × B → Fin (Fintype.card (A × B)),
      ∀ (k : ℕ) (q : A × B × Fin k → ℝ),
        probability q → (∀ a b, ∑ v, q (a, b, v) = p (a, b)) →
        deterministicError (TableBoundProof.deterministicTable p Γ) ≤ c * latentError q := by
  obtain ⟨Γ, hΓ⟩ := table_bound hp
  refine ⟨Γ, ?_⟩
  rw [deterministicTable_errors_equal (show IsPMF p from ⟨hp.1, hp.2⟩)]
  exact hΓ

end Bridge

/-- **The finite natural-latent theorem, table form.** -/
theorem table : TableClaim :=
  ⟨c, c_nonneg, c_lt_seven, fun _ _ _ _ _ _ _ hp => table_bound_entropy hp⟩

/-- The table form implies the optimum form: `T p` is at most the error of any one code,
and the stochastic feasible set is nonempty (the constant latent). -/
theorem score_of_table (h : TableClaim) : ScoreClaim := by
  obtain ⟨c, hc0, hc7, hc⟩ := h
  refine ⟨c, hc0, hc7, ?_⟩
  intro A B _ _ _ _ p hp
  obtain ⟨g, hg⟩ := hc A B p hp
  have hT : T p ≤ DeterministicError (deterministicTable p g) :=
    ciInf_le (Set.finite_range _).bddBelow g
  have hne : {s : ℝ | ∃ (k : ℕ) (q : A × B × Fin k → ℝ), Probability q ∧
      (∀ x y, ∑ v, q (x, y, v) = p (x, y)) ∧ StochasticError q = s}.Nonempty := by
    refine ⟨_, 1, fun w => p (w.1, w.2.1), ⟨fun w => hp.1 _, ?_⟩, fun x y => by simp, rfl⟩
    simpa [Fintype.sum_prod_type] using hp.2
  refine hT.trans ?_
  rcases hc0.eq_or_lt with h0 | hpos
  · obtain ⟨s, k, q, hq, hm, rfl⟩ := hne
    have := hg k q hq hm
    rw [← h0, zero_mul] at this ⊢
    exact this
  · rw [← div_le_iff₀' hpos]
    unfold NaturalLatents.tau
    exact le_csInf hne (by
      rintro s ⟨k, q, hq, hm, rfl⟩
      rw [div_le_iff₀' hpos]
      exact hg k q hq hm)

/-- **The finite natural-latent theorem, optimum form.** -/
theorem score : ScoreClaim :=
  score_of_table table

end NaturalLatents
