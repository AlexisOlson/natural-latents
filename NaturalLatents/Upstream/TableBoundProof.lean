-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/TableBoundProof.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised.
import NaturalLatents.Upstream.TableInformationProof

/-! The final bound for probability tables, with conditional entropies on the deterministic side. -/

open scoped BigOperators
open stoch_to_det
open TableInformationProof

namespace TableBoundProof

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

def deterministicTable (p : A × B → ℝ) (Γ : A × B → C) : A × B × C → ℝ :=
  fun (a, b, c) => if Γ (a, b) = c then p (a, b) else 0

noncomputable def deterministicError (p : A × B × C → ℝ) : ℝ :=
  conditionalMutualInformation p
    + conditionalEntropy (fun gx : C × A => ∑ y, p (gx.2, y, gx.1))
    + conditionalEntropy (fun gy : C × B => ∑ x, p (x, gy.2, gy.1))

omit [DecidableEq B] in
theorem push_ca (p : A × B × C → ℝ) :
    push (fun w => (w.2.2, w.1)) p = fun ca => ∑ b, p (ca.2, b, ca.1) := by
  funext ⟨c, a⟩
  simp [push, Finset.sum_filter, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
  rw [Finset.sum_comm]
  simp

omit [DecidableEq A] in
theorem push_cb (p : A × B × C → ℝ) :
    push (fun w => (w.2.2, w.2.1)) p = fun cb => ∑ a, p (a, cb.2, cb.1) := by
  funext ⟨c, b⟩
  simp [push, Finset.sum_filter, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]

theorem deterministicError_push {Ω : Type*} [Fintype Ω]
    {p : Ω → ℝ} (hp : IsPMF p) (x : Ω → A) (y : Ω → B) (v : Ω → C) :
    deterministicError (push (fun w => (x w, y w, v w)) p) =
      condMI x y v p + condH v x p + condH v y p := by
  unfold deterministicError
  rw [conditionalMutualInformation_push hp, ← push_ca, ← push_cb,
    conditionalEntropy_eq_condH (isPMF_push (isPMF_push hp)),
    conditionalEntropy_eq_condH (isPMF_push (isPMF_push hp))]
  simp only [condH, Hvar, push_push, Function.comp_def]

omit [Fintype C] in
theorem deterministicTable_eq_push (p : A × B → ℝ) (Γ : A × B → C) :
    deterministicTable p Γ = push (fun ab => (ab.1, ab.2, Γ ab)) p := by
  funext ⟨a, b, c⟩
  simp [deterministicTable, push, Finset.sum_filter, Fintype.sum_prod_type,
    Prod.mk.injEq, ite_and]

theorem transpose_eq_push (q : A × B × C → ℝ) :
    (fun v : C × (A × B) => q (v.2.1, v.2.2, v.1)) =
      push (fun abc : A × B × C => (abc.2.2, (abc.1, abc.2.1))) q := by
  funext ⟨c, a, b⟩
  simp [push, Finset.sum_filter, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]

theorem deterministicTable_error {p : A × B → ℝ} (hp : IsPMF p)
    (Γ : A × B → C) : latentError (deterministicTable p Γ) = detScore p Γ := by
  rw [deterministicTable_eq_push, latentError_push hp,
    condMI_code_X_given_Y hp Γ, condMI_code_Y_given_X hp Γ]
  unfold detScore
  ring

theorem deterministicTable_entropy_error {p : A × B → ℝ} (hp : IsPMF p)
    (Γ : A × B → C) : deterministicError (deterministicTable p Γ) = detScore p Γ := by
  rw [deterministicTable_eq_push, deterministicError_push hp]
  rfl

theorem deterministicTable_errors_equal {p : A × B → ℝ} (hp : IsPMF p)
    (Γ : A × B → C) :
    deterministicError (deterministicTable p Γ) = latentError (deterministicTable p Γ) := by
  rw [deterministicTable_entropy_error hp, deterministicTable_error hp]

end TableBoundProof
