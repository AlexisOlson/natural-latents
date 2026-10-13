-- Original work by Alexis Olson, Apache-2.0 (see NOTICE), first developed in
-- github.com/AlexisOlson/stochastic-to-deterministic-latents; reorganised for this repository
-- (namespace NaturalLatents.General, declarations renamed, unused material removed).
-- This file builds on and cites the definitions of DLorell/stoch_to_det (Apache-2.0).
import NaturalLatents.General.Definitions

/-!
# The replica budget

For two independent posterior draws given the cell, the replica budget `replicaBudget L` of a latent satisfies

    replicaBudget L ≤ 2 * mediation L + redundancy L

in nats (`replica_budget`). The proof expands the conditional mutual information over the
fibers of the cell, uses that the two draws are conditionally independent and Markov given the
cell, and applies a chain rule coordinate by coordinate.

## Attribution

Original work by Alexis Olson, first developed in
github.com/AlexisOlson/stochastic-to-deterministic-latents.
This file builds on and cites the definitions of
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
-/

namespace NaturalLatents.General

noncomputable section

open scoped BigOperators
open MeasureTheory ProbabilityTheory

variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

open stoch_to_det in
omit [DecidableEq X] [DecidableEq Y] in
lemma replica_posterior_nonneg {p : Law X Y} (hp : IsPMF p) (L : stoch_to_det.Latent p)
    (i : L.ι) (z : X × Y) : 0 ≤ posterior L i z := by
  exact div_nonneg
    (mul_nonneg (L.prior_isPMF.nonneg i) ((L.comp_isPMF i).nonneg z))
    (hp.nonneg z)

omit [DecidableEq X] [DecidableEq Y] in
lemma replica_sum_posterior {p : Law X Y} (L : stoch_to_det.Latent p)
    (z : X × Y) (hz : p z ≠ 0) : ∑ i, posterior L i z = 1 := by
  unfold posterior
  rw [← Finset.sum_div, L.mixture z, div_self hz]

omit [DecidableEq X] [DecidableEq Y] in
lemma replica_sum_domain {p : Law X Y} (L : stoch_to_det.Latent p)
    (F : L.ι × L.ι × (X × Y) → ℝ) :
    (∑ u, F u) = ∑ i, ∑ j, ∑ z, F (i, j, z) := by
  simp only [Fintype.sum_prod_type]

omit [DecidableEq X] [DecidableEq Y] in
lemma replica_sum_replica_second {p : Law X Y} (L : stoch_to_det.Latent p)
    (i : L.ι) (z : X × Y) :
    (∑ j, replicaJoint L (i, j, z)) = L.joint (i, z) := by
  by_cases hpz : p z = 0
  · have hzero : L.joint (i, z) = 0 := by
      rw [← mul_posterior_eq_joint L i z, hpz, zero_mul]
    simp [replicaJoint, hpz, hzero]
  · change (∑ j, (p z * posterior L i z) * posterior L j z) = L.joint (i, z)
    rw [← Finset.mul_sum, replica_sum_posterior L z hpz, mul_one, mul_posterior_eq_joint]

omit [DecidableEq X] [DecidableEq Y] in
lemma replica_sum_replica_first {p : Law X Y} (L : stoch_to_det.Latent p)
    (j : L.ι) (z : X × Y) :
    (∑ i, replicaJoint L (i, j, z)) = L.joint (j, z) := by
  have hswap : ∀ i, replicaJoint L (i, j, z) = replicaJoint L (j, i, z) := by
    intro i
    unfold replicaJoint
    ring
  simp_rw [hswap]
  exact replica_sum_replica_second L j z

omit [DecidableEq X] [DecidableEq Y] in
open stoch_to_det in
lemma replica_replica_isPMF {p : Law X Y} (hp : IsPMF p) (L : stoch_to_det.Latent p) :
    IsPMF (replicaJoint L) := by
  refine ⟨?_, ?_⟩
  · intro u
    exact mul_nonneg
      (mul_nonneg (hp.nonneg u.2.2) (replica_posterior_nonneg hp L u.1 u.2.2))
      (replica_posterior_nonneg hp L u.2.1 u.2.2)
  · unfold mass
    rw [replica_sum_domain]
    calc
      (∑ i, ∑ j, ∑ z, replicaJoint L (i, j, z)) =
          ∑ i, ∑ z, ∑ j, replicaJoint L (i, j, z) := by
            apply Finset.sum_congr rfl
            intro i _
            exact Finset.sum_comm
      _ = ∑ i, ∑ z, L.joint (i, z) := by
            simp_rw [replica_sum_replica_second]
      _ = 1 := by
            rw [← Fintype.sum_prod_type]
            exact L.joint_isPMF.total

open stoch_to_det in
lemma replica_push_first {p : Law X Y} (L : stoch_to_det.Latent p) :
    push (fun u : L.ι × L.ι × (X × Y) => (u.1, u.2.2)) (replicaJoint L) = L.joint := by
  funext v
  rcases v with ⟨i, z⟩
  unfold push
  rw [Finset.sum_filter, replica_sum_domain]
  simp only [Prod.mk.injEq]
  simp_rw [ite_and]
  simp
  exact replica_sum_replica_second L i z

open stoch_to_det in
lemma replica_push_second {p : Law X Y} (L : stoch_to_det.Latent p) :
    push (Prod.snd : L.ι × L.ι × (X × Y) → L.ι × (X × Y)) (replicaJoint L) = L.joint := by
  funext v
  rcases v with ⟨j, z⟩
  unfold push
  rw [Finset.sum_filter, replica_sum_domain]
  simp only [Prod.mk.injEq]
  simp_rw [ite_and]
  simp
  exact replica_sum_replica_first L j z

open stoch_to_det in
lemma replica_push_id {A : Type*} [Fintype A] [DecidableEq A] (m : A → ℝ) :
    push (fun a => a) m = m := by
  funext a
  unfold push
  apply Finset.sum_eq_single a
  · intro b hb hba
    exact (hba (Finset.mem_filter.mp hb).2).elim
  · intro ha
    exact (ha (by simp)).elim

open stoch_to_det in
lemma replica_MI_eq_of_pair_push_eq
    {A A' Γ Δ : Type*} [Fintype A] [Fintype A'] [Fintype Γ] [Fintype Δ]
    [DecidableEq Γ] [DecidableEq Δ]
    (m : A → ℝ) (n : A' → ℝ) (f : A → Γ) (g : A → Δ)
    (f' : A' → Γ) (g' : A' → Δ)
    (hpair : push (fun a => (f a, g a)) m = push (fun a => (f' a, g' a)) n) :
    MI f g m = MI f' g' n := by
  have hf : push f m = push f' n := by
    calc
      push f m = push Prod.fst (push (fun a => (f a, g a)) m) := by
        symm
        simpa [Function.comp_def] using
          (push_push (fun a => (f a, g a)) Prod.fst m)
      _ = push Prod.fst (push (fun a => (f' a, g' a)) n) := by rw [hpair]
      _ = push f' n := by
        simpa [Function.comp_def] using
          (push_push (fun a => (f' a, g' a)) Prod.fst n)
  have hg : push g m = push g' n := by
    calc
      push g m = push Prod.snd (push (fun a => (f a, g a)) m) := by
        symm
        simpa [Function.comp_def] using
          (push_push (fun a => (f a, g a)) Prod.snd m)
      _ = push Prod.snd (push (fun a => (f' a, g' a)) n) := by rw [hpair]
      _ = push g' n := by
        simpa [Function.comp_def] using
          (push_push (fun a => (f' a, g' a)) Prod.snd n)
  unfold MI Hvar
  rw [hf, hg, hpair]

open stoch_to_det in
lemma replica_iidProduct_MI_zero
    {A : Type*} [Fintype A] [DecidableEq A] {t : A → ℝ} (ht : IsPMF t) :
    MI Prod.fst Prod.snd (fun u : A × A => t u.1 * t u.2) = 0 := by
  let q : A × A → ℝ := fun u => t u.1 * t u.2
  have ht_sum : ∑ a, t a = 1 := by simpa [mass] using ht.total
  have hq : IsPMF q := product_isPMF_dom ht ht
  have hfst : push Prod.fst q = t := by
    funext a
    unfold push
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    simp [q, ← Finset.mul_sum, ht_sum]
  have hsnd : push Prod.snd q = t := by
    funext b
    unfold push
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    simp [q, ← Finset.sum_mul, ht_sum]
  have hpair : push (fun u : A × A => (u.1, u.2)) q = q := by
    simpa only using replica_push_id q
  have hfiber (b : A) : H (fun a => q (a, b)) = t b * H t := by
    have heq : (fun a => q (a, b)) = fun a => t b * t a := by
      funext a
      dsimp only [q]
      ring
    rw [heq]
    exact H_smul (ht.nonneg b)
  have hqH := H_prod_eq_snd_add_fibers hq
  rw [hsnd] at hqH
  simp_rw [hfiber] at hqH
  rw [← Finset.sum_mul, ht_sum, one_mul] at hqH
  change MI Prod.fst Prod.snd q = 0
  unfold MI Hvar
  rw [hfst, hsnd, hpair, hqH]
  ring

open stoch_to_det in
lemma replica_push_Zfiber_pair {p : Law X Y} (L : stoch_to_det.Latent p) (z : X × Y) :
    push (fun u : L.ι × L.ι × (X × Y) => (u.1, u.2.1))
        (fun u => if u.2.2 = z then replicaJoint L u else 0) =
      fun v : L.ι × L.ι => p z * posterior L v.1 z * posterior L v.2 z := by
  funext v
  rcases v with ⟨i, j⟩
  unfold push
  rw [Finset.sum_filter, replica_sum_domain]
  simp only [Prod.mk.injEq]
  simp_rw [ite_and]
  simp [replicaJoint]

open stoch_to_det in
lemma replica_MI_Zfiber_zero {p : Law X Y} (hp : IsPMF p) (L : stoch_to_det.Latent p)
    (z : X × Y) :
    MI (fun u : L.ι × L.ι × (X × Y) => u.1) (fun u => u.2.1)
      (fun u => if u.2.2 = z then replicaJoint L u else 0) = 0 := by
  let n : L.ι × L.ι → ℝ := fun v => p z * posterior L v.1 z * posterior L v.2 z
  have hpair :
      push (fun u : L.ι × L.ι × (X × Y) => (u.1, u.2.1))
          (fun u => if u.2.2 = z then replicaJoint L u else 0) =
        push (fun v : L.ι × L.ι => (v.1, v.2)) n := by
    rw [replica_push_Zfiber_pair L z]
    symm
    simpa only using replica_push_id n
  have hMI := replica_MI_eq_of_pair_push_eq
    (fun u : L.ι × L.ι × (X × Y) => if u.2.2 = z then replicaJoint L u else 0) n
    (fun u => u.1) (fun u => u.2.1) (fun v => v.1) (fun v => v.2) hpair
  rw [hMI]
  by_cases hpz : p z = 0
  · simp [n, hpz, MI, Hvar, H, push, mass]
  · let t : L.ι → ℝ := fun i => posterior L i z
    have ht : IsPMF t := by
      constructor
      · intro i
        exact replica_posterior_nonneg hp L i z
      · simpa [mass, t] using replica_sum_posterior L z hpz
    let q : L.ι × L.ι → ℝ := fun v => t v.1 * t v.2
    have hq : IsPMF q := product_isPMF_dom ht ht
    have hzero : MI Prod.fst Prod.snd q = 0 := replica_iidProduct_MI_zero ht
    have hscale := MI_smul hq.nonneg Prod.fst Prod.snd (hp.nonneg z)
    have hn : n = fun v : L.ι × L.ι => p z * q v := by
      funext v
      simp [n, q, t]
      ring
    rw [hn, hscale, hzero, mul_zero]

open stoch_to_det in
lemma replica_replica_markov {p : Law X Y} (hp : IsPMF p) (L : stoch_to_det.Latent p) :
    condMI (fun u : L.ι × L.ι × (X × Y) => u.1) (fun u => u.2.1)
      (fun u => u.2.2) (replicaJoint L) = 0 := by
  rw [stoch_to_det.coordinate_condMI_eq_sum (replica_replica_isPMF hp L)]
  exact Finset.sum_eq_zero fun z _ => replica_MI_Zfiber_zero hp L z

/-- Two conditional chain rules bound one replica coordinate. -/
lemma replica_coordinate_chain_bound
    {Ω A B C D : Type*} [Fintype Ω] [Fintype A] [Fintype B]
    [Fintype C] [Fintype D] [DecidableEq A] [DecidableEq B]
    [DecidableEq C] [DecidableEq D]
    {q : Ω → ℝ} (hq : stoch_to_det.IsPMF q)
    (a : Ω → A) (b : Ω → B) (x : Ω → C) (y : Ω → D) :
    stoch_to_det.condMI b x a q ≤ stoch_to_det.condMI x y a q +
      stoch_to_det.condMI b x y q +
      stoch_to_det.condMI a b (fun w => (x w, y w)) q := by
  have h₁ := stoch_to_det.condMI_pair_left_local hq y b x a
  have h₂ := stoch_to_det.condMI_pair_left_local hq b y x a
  have hswap₁ := stoch_to_det.condMI_equiv_left_local hq
    (fun w => (b w, y w)) (Equiv.prodComm B D) x a
  change stoch_to_det.condMI (fun w => (y w, b w)) x a q =
    stoch_to_det.condMI (fun w => (b w, y w)) x a q at hswap₁
  have hcomm₁ := stoch_to_det.condMI_comm_local hq y x a
  have hn₁ := stoch_to_det.condMI_nonneg hq y x (fun w => (a w, b w))
  have h₃ := stoch_to_det.condMI_pair_left_local hq a x b y
  have h₄ := stoch_to_det.condMI_pair_left_local hq x a b y
  have hswap₂ := stoch_to_det.condMI_equiv_left_local hq
    (fun w => (x w, a w)) (Equiv.prodComm C A) b y
  change stoch_to_det.condMI (fun w => (a w, x w)) b y q =
    stoch_to_det.condMI (fun w => (x w, a w)) b y q at hswap₂
  have hswap₃ := stoch_to_det.condMI_equiv_cond_local hq a b
    (fun w => (x w, y w)) (Equiv.prodComm C D)
  change stoch_to_det.condMI a b (fun w => (y w, x w)) q =
    stoch_to_det.condMI a b (fun w => (x w, y w)) q at hswap₃
  have hswap₄ := stoch_to_det.condMI_equiv_cond_local hq b x
    (fun w => (a w, y w)) (Equiv.prodComm A D)
  change stoch_to_det.condMI b x (fun w => (y w, a w)) q =
    stoch_to_det.condMI b x (fun w => (a w, y w)) q at hswap₄
  have hcomm₂ := stoch_to_det.condMI_comm_local hq x b (fun w => (y w, a w))
  have hcomm₃ := stoch_to_det.condMI_comm_local hq x b y
  have hn₂ := stoch_to_det.condMI_nonneg hq a b y
  linarith

/-- The total two-coordinate budget, before applying the replica Markov law. -/
lemma replica_total_chain_bound
    {Ω A B C D : Type*} [Fintype Ω] [Fintype A] [Fintype B]
    [Fintype C] [Fintype D] [DecidableEq A] [DecidableEq B]
    [DecidableEq C] [DecidableEq D]
    {q : Ω → ℝ} (hq : stoch_to_det.IsPMF q)
    (a : Ω → A) (b : Ω → B) (x : Ω → C) (y : Ω → D) :
    stoch_to_det.condMI b x a q + stoch_to_det.condMI b y a q ≤
      2 * stoch_to_det.condMI x y a q +
      (stoch_to_det.condMI b x y q + stoch_to_det.condMI b y x q) +
      2 * stoch_to_det.condMI a b (fun w => (x w, y w)) q := by
  have hx := replica_coordinate_chain_bound hq a b x y
  have hy := replica_coordinate_chain_bound hq a b y x
  have hcomm := stoch_to_det.condMI_comm_local hq y x a
  have hswap := stoch_to_det.condMI_equiv_cond_local hq a b
    (fun w => (x w, y w)) (Equiv.prodComm C D)
  change stoch_to_det.condMI a b (fun w => (y w, x w)) q =
    stoch_to_det.condMI a b (fun w => (x w, y w)) q at hswap
  linarith

/-- The replica budget of a latent is at most `2 * mediation L + redundancy L`, in nats. -/
theorem replica_budget {p : Law X Y} (hp : stoch_to_det.IsPMF p) (L : stoch_to_det.Latent p) :
    replicaBudget L ≤ 2*mediation L + redundancy L := by
  have hq := replica_replica_isPMF hp L
  have hbits := replica_total_chain_bound hq
    (fun w => w.1) (fun w => w.2.1)
    (fun w => w.2.2.1) (fun w => w.2.2.2)
  have hmarkov := replica_replica_markov hp L
  have hM := stoch_to_det.condMI_push_source
    (fun w : L.ι × L.ι × (X × Y) => (w.1, w.2.2))
    (fun w => w.2.1) (fun w => w.2.2) (fun w => w.1) (replicaJoint L)
  have hBX := stoch_to_det.condMI_push_source
    (fun w : L.ι × L.ι × (X × Y) => w.2)
    (fun w => w.1) (fun w => w.2.1) (fun w => w.2.2) (replicaJoint L)
  have hBY := stoch_to_det.condMI_push_source
    (fun w : L.ι × L.ι × (X × Y) => w.2)
    (fun w => w.1) (fun w => w.2.2) (fun w => w.2.1) (replicaJoint L)
  rw [replica_push_first L] at hM
  rw [replica_push_second L] at hBX hBY
  simp only [Function.comp_def] at hM hBX hBY
  change stoch_to_det.condMI (fun w => w.1) (fun w => w.2.1)
    (fun w => (w.2.2.1, w.2.2.2)) (replicaJoint L) = 0 at hmarkov
  rw [hmarkov, mul_zero, add_zero, ← hM, ← hBX, ← hBY] at hbits
  have h := nats_le_nats_iff.mpr hbits
  simp only [nats] at h
  unfold replicaBudget mediation redundancy condMINat nats
  nlinarith only [h]

end

end NaturalLatents.General
