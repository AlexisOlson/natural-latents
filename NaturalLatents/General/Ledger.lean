-- Adapted from the author's earlier repository (StochasticToDeterministicLatents);
-- modified: module paths renamed; declarations unused by the main theorems removed.
import NaturalLatents.General.Definitions

/-!
# The ledger inequality for a seeded family

For a latent `L` of a probability law `p` and a calibrated seeded family `F`, the deterministic
optimum is controlled by the seed-averaged fixed-map scores:

    T p ≤ M L - B L / 2 + 3 h F / 2,

in nats (`T_le_ledger`). The proof averages the deterministic scores of the complete maps over
the seed law, writes each as a coordinate identity in the information budgets of the
fixed-map latent, and bounds the average mutual information below by the corresponding
arbitrary-latent budget.

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

lemma ledger_product_isPMF {S Z : Type*} [Fintype S] [Fintype Z]
    {r : S → ℝ} {p : Z → ℝ}
    (hr : stoch_to_det.IsPMF r) (hp : stoch_to_det.IsPMF p) :
    stoch_to_det.IsPMF (fun w : S × Z => r w.1 * p w.2) := by
  classical
  constructor
  · intro w
    exact mul_nonneg (hr.nonneg w.1) (hp.nonneg w.2)
  · change (∑ w : S × Z, r w.1 * p w.2) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    change stoch_to_det.mass r * stoch_to_det.mass p = 1
    rw [hr.total, hp.total, mul_one]

lemma ledger_push_source {S Z G : Type*}
    [Fintype S] [Fintype Z] [DecidableEq G]
    {r : S → ℝ} {p : Z → ℝ} (hr : ∑ s, r s = 1) (f : Z → G) :
    stoch_to_det.push (fun w : S × Z => f w.2) (fun w => r w.1 * p w.2) =
      stoch_to_det.push f p := by
  classical
  funext c
  simp only [stoch_to_det.push, Finset.sum_filter, Fintype.sum_prod_type]
  calc
    (∑ s, ∑ z, if f z = c then r s * p z else 0) =
        ∑ s, r s * (∑ z, if f z = c then p z else 0) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hf : f z = c <;> simp [hf]
    _ = (∑ s, r s) * (∑ z, if f z = c then p z else 0) := by
      rw [Finset.sum_mul]
    _ = ∑ z, if f z = c then p z else 0 := by
      rw [hr, one_mul]

lemma ledger_Hvar_source {S Z G : Type*}
    [Fintype S] [Fintype Z] [Fintype G] [DecidableEq G]
    {r : S → ℝ} {p : Z → ℝ} (hr : stoch_to_det.IsPMF r) (f : Z → G) :
    stoch_to_det.Hvar (fun w : S × Z => f w.2) (fun w => r w.1 * p w.2) =
      stoch_to_det.Hvar f p := by
  unfold stoch_to_det.Hvar
  rw [ledger_push_source hr.total f]

lemma ledger_push_seed_slice {S Z G : Type*}
    [Fintype S] [Fintype Z] [DecidableEq S] [DecidableEq G]
    (r : S → ℝ) (k : Z → ℝ) (q : S × Z → G) (s : S) :
    stoch_to_det.push q
        (fun w : S × Z => if w.1 = s then r w.1 * k w.2 else 0) =
      fun c => r s * stoch_to_det.push (fun z => q (s, z)) k c := by
  classical
  funext c
  simp only [stoch_to_det.push, Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single s]
  · simp only [ite_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hq : q (s, z) = c <;> simp [hq]
  · intro s' _ hs'
    simp [hs']
  · simp

lemma ledger_condH_seed {S Z G : Type*}
    [Fintype S] [Fintype Z] [Fintype G]
    [DecidableEq S] [DecidableEq G]
    {r : S → ℝ} {p : Z → ℝ}
    (hr : stoch_to_det.IsPMF r) (hp : stoch_to_det.IsPMF p) (q : S × Z → G) :
    stoch_to_det.condH q Prod.fst (fun w : S × Z => r w.1 * p w.2) =
      ∑ s, r s * stoch_to_det.Hvar (fun z => q (s, z)) p := by
  classical
  rw [stoch_to_det.condH_eq_sum_H_fibers (ledger_product_isPMF hr hp)]
  apply Finset.sum_congr rfl
  intro s _
  rw [ledger_push_seed_slice r p q s]
  exact stoch_to_det.H_smul (hr.nonneg s)

lemma ledger_condMI_seed {S Z G K : Type*}
    [Fintype S] [Fintype Z] [Fintype G] [Fintype K]
    [DecidableEq S] [DecidableEq G] [DecidableEq K]
    {r : S → ℝ} {p : Z → ℝ}
    (hr : stoch_to_det.IsPMF r) (hp : stoch_to_det.IsPMF p)
    (q : S × Z → G) (g : S × Z → K) :
    stoch_to_det.condMI q g Prod.fst (fun w : S × Z => r w.1 * p w.2) =
      ∑ s, r s * stoch_to_det.MI (fun z => q (s, z)) (fun z => g (s, z)) p := by
  classical
  have hAssoc : stoch_to_det.Hvar (fun w : S × Z => (q w, g w, w.1))
        (fun w : S × Z => r w.1 * p w.2) =
      stoch_to_det.Hvar (fun w : S × Z => ((q w, g w), w.1))
        (fun w : S × Z => r w.1 * p w.2) := by
    simpa using stoch_to_det.Hvar_equiv (ledger_product_isPMF hr hp)
      (fun w : S × Z => ((q w, g w), w.1)) (Equiv.prodAssoc G K S)
  have hForm : stoch_to_det.condMI q g Prod.fst
        (fun w : S × Z => r w.1 * p w.2) =
      stoch_to_det.condH q Prod.fst (fun w : S × Z => r w.1 * p w.2) +
        stoch_to_det.condH g Prod.fst (fun w : S × Z => r w.1 * p w.2) -
        stoch_to_det.condH (fun w : S × Z => (q w, g w)) Prod.fst
          (fun w : S × Z => r w.1 * p w.2) := by
    unfold stoch_to_det.condMI stoch_to_det.condH
    rw [hAssoc]
    ring
  rw [hForm, ledger_condH_seed hr hp q, ledger_condH_seed hr hp g,
    ledger_condH_seed hr hp (fun w : S × Z => (q w, g w))]
  simp only [stoch_to_det.MI, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]

lemma ledger_MI_seed_source_zero {S Z K : Type*}
    [Fintype S] [Fintype Z] [Fintype K]
    [DecidableEq S] [DecidableEq K]
    {r : S → ℝ} {p : Z → ℝ}
    (hr : stoch_to_det.IsPMF r) (hp : stoch_to_det.IsPMF p) (g : Z → K) :
    stoch_to_det.MI Prod.fst (fun w : S × Z => g w.2)
      (fun w : S × Z => r w.1 * p w.2) = 0 := by
  classical
  have hcond : stoch_to_det.condH (fun w : S × Z => g w.2) Prod.fst
        (fun w : S × Z => r w.1 * p w.2) = stoch_to_det.Hvar g p := by
    rw [ledger_condH_seed hr hp]
    change (∑ s, r s * stoch_to_det.Hvar g p) = stoch_to_det.Hvar g p
    rw [← Finset.sum_mul]
    change stoch_to_det.mass r * stoch_to_det.Hvar g p = stoch_to_det.Hvar g p
    rw [hr.total, one_mul]
  rw [stoch_to_det.MI_comm (ledger_product_isPMF hr hp) Prod.fst (fun w => g w.2)]
  unfold stoch_to_det.MI
  rw [ledger_Hvar_source hr g]
  unfold stoch_to_det.condH at hcond
  linarith

omit [DecidableEq X] [DecidableEq Y] in
lemma ledger_p_mul_post {p : Law X Y} (_hp : stoch_to_det.IsPMF p)
    (L : FiniteLatent p) (i : L.ι) (z : X × Y) :
    p z * post L i z = L.joint (i,z) := by
  unfold post stoch_to_det.Latent.joint
  by_cases hz : p z = 0
  · have hle : L.prior i * L.comp i z ≤ ∑ v, L.prior v * L.comp v z :=
      Finset.single_le_sum
        (fun v _ => mul_nonneg (L.prior_isPMF.nonneg v) ((L.comp_isPMF v).nonneg z))
        (Finset.mem_univ i)
    rw [L.mixture z, hz] at hle
    have hzero : L.prior i * L.comp i z = 0 :=
      le_antisymm hle
        (mul_nonneg (L.prior_isPMF.nonneg i) ((L.comp_isPMF i).nonneg z))
    simp [hz, hzero]
  · field_simp

lemma ledger_calibrated_graph {p : Law X Y} (hp : stoch_to_det.IsPMF p)
    (L : FiniteLatent p) (F : CalibratedSeededFamily L) :
    stoch_to_det.push (fun w : (X × Y → L.ι) × (X × Y) => (w.1 w.2,w.2))
      (seedSourceJoint F) = L.joint := by
  classical
  funext iz
  rcases iz with ⟨i,z⟩
  unfold stoch_to_det.push
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  have hfiber : ∀ A : X × Y → L.ι,
      (∑ t, if (A t,t) = (i,z) then seedSourceJoint F (A,t) else 0) =
      if A z = i then F.seedLaw A * p z else 0 := by
    intro A
    rw [Finset.sum_eq_single z]
    · simp [seedSourceJoint]
    · intro t _ ht
      have hh : (A t,t) ≠ (i,z) := fun h => ht (congrArg Prod.snd h)
      simp [hh]
    · simp
  simp_rw [hfiber]
  have hfactor : (∑ A, if A z = i then F.seedLaw A * p z else 0) =
      p z * ∑ A, if A z = i then F.seedLaw A else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A _
    split <;> simp_all [mul_comm]
  rw [hfactor]
  by_cases hz : p z = 0
  · rw [hz, zero_mul]
    simpa [hz] using ledger_p_mul_post hp L i z
  · rw [F.calibrated z (by simpa [stoch_to_det.support] using hz) i]
    exact ledger_p_mul_post hp L i z

lemma ledger_MI_push {Ω Ω' Γ Δ : Type} [Fintype Ω] [Fintype Ω']
    [DecidableEq Ω'] [Fintype Γ] [Fintype Δ] [DecidableEq Γ] [DecidableEq Δ]
    (m : Ω → ℝ) (e : Ω → Ω') (f : Ω' → Γ) (g : Ω' → Δ) :
    stoch_to_det.MI f g (stoch_to_det.push e m) =
      stoch_to_det.MI (f ∘ e) (g ∘ e) m := by
  unfold stoch_to_det.MI stoch_to_det.Hvar
  simp only [stoch_to_det.push_push, Function.comp_def]

/- Fixed-map scores and arbitrary-latent information balance. -/
lemma ledger_detScore_coordinate_identity {γ : Type*} [Fintype γ] [DecidableEq γ]
    {p : Law X Y} (hp : stoch_to_det.IsPMF p) (A : X × Y → γ) :
    stoch_to_det.detScore p A = stoch_to_det.Ixy p + (3 / 2 : ℝ) *
      (stoch_to_det.condH A Prod.fst p + stoch_to_det.condH A Prod.snd p) -
      (1 / 2 : ℝ) * (stoch_to_det.MI A Prod.fst p + stoch_to_det.MI A Prod.snd p) := by
  have hXA := stoch_to_det.Hvar_equiv hp (fun z : X × Y => (A z, z.1))
    (Equiv.prodComm γ X)
  change stoch_to_det.Hvar (fun z : X × Y => (z.1, A z)) p =
    stoch_to_det.Hvar (fun z : X × Y => (A z, z.1)) p at hXA
  have hYA := stoch_to_det.Hvar_equiv hp (fun z : X × Y => (A z, z.2))
    (Equiv.prodComm γ Y)
  change stoch_to_det.Hvar (fun z : X × Y => (z.2, A z)) p =
    stoch_to_det.Hvar (fun z : X × Y => (A z, z.2)) p at hYA
  have htrip := stoch_to_det.Hvar_eq_of_leftInverse hp (fun z : X × Y => z)
    (fun z : X × Y => (z.1, z.2, A z))
    (fun t : X × Y × γ => (t.1, t.2.1)) (by intro z; rfl)
  change stoch_to_det.Hvar (fun z : X × Y => (z.1, z.2, A z)) p =
    stoch_to_det.Hvar (fun z : X × Y => z) p at htrip
  have hid : stoch_to_det.Hvar (fun z : X × Y => z) p = stoch_to_det.H p := by
    unfold stoch_to_det.Hvar
    change stoch_to_det.H (stoch_to_det.push (Equiv.refl (X × Y)) p) = stoch_to_det.H p
    exact stoch_to_det.H_push_equiv (Equiv.refl (X × Y)) p hp
  unfold stoch_to_det.detScore stoch_to_det.condMI stoch_to_det.condH stoch_to_det.MI
  rw [hXA, hYA, htrip, hid]
  unfold stoch_to_det.Ixy
  simp only [stoch_to_det.Hvar, stoch_to_det.mX, stoch_to_det.mY]
  ring

lemma ledger_B_information {p : Law X Y} (L : FiniteLatent p) :
    stoch_to_det.condMI (fun v : L.ι × (X × Y) => v.1) (fun v => v.2.1)
        (fun v => v.2.2) L.joint +
      stoch_to_det.condMI (fun v : L.ι × (X × Y) => v.1) (fun v => v.2.2)
        (fun v => v.2.1) L.joint =
    2 * stoch_to_det.MI (fun v : L.ι × (X × Y) => v.1) (fun v => v.2) L.joint -
      stoch_to_det.MI (fun v : L.ι × (X × Y) => v.1) (fun v => v.2.1) L.joint -
      stoch_to_det.MI (fun v : L.ι × (X × Y) => v.1) (fun v => v.2.2) L.joint := by
  have hXY := stoch_to_det.MI_pair_left L.joint_isPMF
    (fun v : L.ι × (X × Y) => v.2.1) (fun v => v.2.2) (fun v => v.1)
  have hYX := stoch_to_det.MI_pair_left L.joint_isPMF
    (fun v : L.ι × (X × Y) => v.2.2) (fun v => v.2.1) (fun v => v.1)
  have hpairSwap :
      stoch_to_det.MI (fun v : L.ι × (X × Y) => (v.2.2, v.2.1)) (fun v => v.1) L.joint =
        stoch_to_det.MI (fun v : L.ι × (X × Y) => v.2) (fun v => v.1) L.joint := by
    simpa only [Equiv.prodComm_apply, Prod.swap] using stoch_to_det.MI_equiv_left_local L.joint_isPMF
      (fun v : L.ι × (X × Y) => v.2) (Equiv.prodComm X Y) (fun v => v.1)
  have hZcomm := stoch_to_det.MI_comm L.joint_isPMF
    (fun v : L.ι × (X × Y) => v.2) (fun v => v.1)
  have hXcomm := stoch_to_det.MI_comm L.joint_isPMF
    (fun v : L.ι × (X × Y) => v.2.1) (fun v => v.1)
  have hYcomm := stoch_to_det.MI_comm L.joint_isPMF
    (fun v : L.ι × (X × Y) => v.2.2) (fun v => v.1)
  have hcX := stoch_to_det.condMI_comm_local L.joint_isPMF
    (fun v : L.ι × (X × Y) => v.2.1) (fun v => v.1) (fun v => v.2.2)
  have hcY := stoch_to_det.condMI_comm_local L.joint_isPMF
    (fun v : L.ι × (X × Y) => v.2.2) (fun v => v.1) (fun v => v.2.1)
  rw [← hcX, ← hcY]
  rw [hpairSwap] at hYX
  rw [hZcomm, hXcomm] at hXY
  rw [hZcomm, hYcomm] at hYX
  linarith only [hXY, hYX]

lemma ledger_information_balance {p : Law X Y} (hp : stoch_to_det.IsPMF p)
    (L : FiniteLatent p) :
    M L - B L / 2 = Real.log 2 * (stoch_to_det.Ixy p -
      (stoch_to_det.MI (fun v : L.ι × (X × Y) => v.1) (fun v => v.2.1) L.joint +
       stoch_to_det.MI (fun v : L.ι × (X × Y) => v.1) (fun v => v.2.2) L.joint) / 2) := by
  have hs := stoch_to_det.Latent.score_sub_Ixy hp L
  have hb := ledger_B_information L
  unfold stoch_to_det.Latent.score at hs
  have hbits :
      stoch_to_det.condMI (fun v : L.ι × (X × Y) => v.2.1) (fun v => v.2.2)
          (fun v => v.1) L.joint -
        (stoch_to_det.condMI (fun v : L.ι × (X × Y) => v.1) (fun v => v.2.1)
          (fun v => v.2.2) L.joint +
         stoch_to_det.condMI (fun v : L.ι × (X × Y) => v.1) (fun v => v.2.2)
          (fun v => v.2.1) L.joint) / 2 =
      stoch_to_det.Ixy p -
        (stoch_to_det.MI (fun v : L.ι × (X × Y) => v.1) (fun v => v.2.1) L.joint +
         stoch_to_det.MI (fun v : L.ι × (X × Y) => v.1) (fun v => v.2.2) L.joint) / 2 := by
    linarith only [hs, hb]
  have hscaled := congrArg (fun t : ℝ => Real.log 2 * t) hbits
  unfold M B
  convert hscaled using 1
  all_goals ring

lemma ledger_average_MI_lower {p : Law X Y} (hp : stoch_to_det.IsPMF p)
    (L : FiniteLatent p) (F : CalibratedSeededFamily L)
    {Γ : Type} [Fintype Γ] [DecidableEq Γ] (g : X × Y → Γ) :
    stoch_to_det.MI Prod.fst (fun w : L.ι × (X × Y) => g w.2) L.joint ≤
      ∑ A, F.seedLaw A * stoch_to_det.MI A g p := by
  classical
  let J := seedSourceJoint F
  let Q : (X × Y → L.ι) × (X × Y) → L.ι := fun w => w.1 w.2
  let G : (X × Y → L.ι) × (X × Y) → Γ := fun w => g w.2
  have hJ : stoch_to_det.IsPMF J := ledger_product_isPMF F.seed_isPMF hp
  have hcal : stoch_to_det.MI Prod.fst (fun w : L.ι × (X × Y) => g w.2) L.joint =
      stoch_to_det.MI Q G J := by
    rw [← ledger_calibrated_graph hp L F, ledger_MI_push]
    rfl
  have hpair : stoch_to_det.MI (fun w => (Q w,w.1)) G J =
      stoch_to_det.MI (fun w => (w.1,Q w)) G J := by
    simpa using stoch_to_det.MI_equiv_left_local hJ
      (fun w => (w.1,Q w)) (Equiv.prodComm (X × Y → L.ι) L.ι) G
  have hzero : stoch_to_det.MI Prod.fst G J = 0 :=
    ledger_MI_seed_source_zero F.seed_isPMF hp g
  have hfirst := stoch_to_det.MI_pair_left hJ Q Prod.fst G
  have hsecond := stoch_to_det.MI_pair_left hJ Prod.fst Q G
  rw [hpair] at hfirst
  rw [hzero] at hsecond
  have hnonneg := stoch_to_det.condMI_nonneg hJ Prod.fst G Q
  have havg : stoch_to_det.condMI Q G Prod.fst J =
      ∑ A, F.seedLaw A * stoch_to_det.MI A g p := by
    exact ledger_condMI_seed F.seed_isPMF hp Q G
  rw [hcal]
  linarith only [hfirst, hsecond, hnonneg, havg]

/-- The ledger inequality, in nats: `T p ≤ M L - B L / 2 + 3 h F / 2` for a calibrated seeded family `F`
of a latent `L` of a probability law `p`. -/
theorem T_le_ledger {p : Law X Y} (hp : stoch_to_det.IsPMF p) (L : FiniteLatent p)
    (F : CalibratedSeededFamily L) : T p ≤ M L - B L/2 + 3*h F/2 := by
  classical
  have hlog : 0 ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num))
  have htotal : ∑ A, F.seedLaw A = 1 := F.seed_isPMF.total
  have hT : T p ≤ ∑ A, F.seedLaw A * (Real.log 2 * stoch_to_det.detScore p A) := by
    have hpoint : ∀ A : X × Y → L.ι, T p ≤ Real.log 2 * stoch_to_det.detScore p A := by
      intro A
      have hb := stoch_to_det.T_le_score (stoch_to_det.Latent.ofFunction hp A)
        (stoch_to_det.functionLatent_isDet hp A)
      rw [stoch_to_det.Latent.ofFunction_score_eq_detScore hp A] at hb
      exact mul_le_mul_of_nonneg_left hb hlog
    calc
      T p = ∑ A, F.seedLaw A * T p := by rw [← Finset.sum_mul, htotal, one_mul]
      _ ≤ ∑ A, F.seedLaw A * (Real.log 2 * stoch_to_det.detScore p A) :=
        Finset.sum_le_sum fun A _ => mul_le_mul_of_nonneg_left (hpoint A) (F.seed_isPMF.nonneg A)
  have havg : (∑ A, F.seedLaw A * (Real.log 2 * stoch_to_det.detScore p A)) =
      Real.log 2 * (stoch_to_det.Ixy p -
        ((∑ A, F.seedLaw A * stoch_to_det.MI A Prod.fst p) +
         (∑ A, F.seedLaw A * stoch_to_det.MI A Prod.snd p)) / 2) + 3 * h F / 2 := by
    simp_rw [ledger_detScore_coordinate_identity hp]
    unfold h
    simp only [mul_add, mul_sub, mul_left_comm, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, htotal, one_mul]
    ring
  have hx := ledger_average_MI_lower hp L F Prod.fst
  have hy := ledger_average_MI_lower hp L F Prod.snd
  have hxy := mul_le_mul_of_nonneg_left (add_le_add hx hy) hlog
  have hbalance := ledger_information_balance hp L
  rw [havg] at hT
  nlinarith only [hT, hxy, hbalance]

end

end StochasticToDeterministicLatents.General
