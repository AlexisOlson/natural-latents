-- Original work by Alexis Olson, Apache-2.0 (see NOTICE), first developed in
-- github.com/AlexisOlson/stochastic-to-deterministic-latents; reorganised for this repository
-- (namespace NaturalLatents.General, declarations renamed, unused material removed).
-- This file builds on and cites the definitions of DLorell/stoch_to_det (Apache-2.0).
import NaturalLatents.General.Replica

/-!
# Paying the mismatch

The categorical mismatch of a latent is paid by its budgets. Given the affinity bound for every
pair, the replica budget and the pair-charge statement `HasPairCharge beta gamma`,

    gamma * mismatch L ≤ (1 + 2 * beta) * mediation L + beta * redundancy L

(`mismatch_payment` for a `CommonSetup`). The proof averages the pair charge over component
pairs weighted by their overlap, then compares the sum with the information payment of the
replica budget.

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

omit [DecidableEq X] [DecidableEq Y] in
/-- Posterior overlap is symmetric. -/
lemma payment_pairMass_comm {p : Law X Y} (L : stoch_to_det.Latent p) (i j : L.ι) :
    pairMass L i j = pairMass L j i := by
  simp only [pairMass, mul_assoc, mul_left_comm, mul_comm]

omit [DecidableEq X] [DecidableEq Y] in
lemma payment_pairMass_nonneg {p : Law X Y} (hp : stoch_to_det.IsPMF p)
    (L : stoch_to_det.Latent p) (i j : L.ι) : 0 ≤ pairMass L i j := by
  exact Finset.sum_nonneg fun z _ =>
    mul_nonneg (mul_nonneg (hp.nonneg z) (replica_posterior_nonneg hp L i z))
      (replica_posterior_nonneg hp L j z)

omit [DecidableEq X] [DecidableEq Y] in
lemma payment_pairMass_rows {p : Law X Y} (L : stoch_to_det.Latent p) (i : L.ι) :
    ∑ j, pairMass L i j = L.prior i := by
  unfold pairMass
  rw [Finset.sum_comm]
  change (∑ z, ∑ j, replicaJoint L (i,j,z)) = L.prior i
  simp_rw [replica_sum_replica_second, stoch_to_det.Latent.joint]
  rw [← Finset.mul_sum]
  rw [(L.comp_isPMF i).sum_eq_one, mul_one]

lemma payment_pairMass_pos {p : Law X Y} (hp : stoch_to_det.IsPMF p)
    (D : CommonSetup p) (i j : D.L.ι) : 0 < pairMass D.L i j := by
  have ht : 0 < ∑ z, p z := by
    rw [hp.sum_eq_one]
    norm_num
  obtain ⟨z, _, hz⟩ := (Finset.sum_pos_iff_of_nonneg (fun z _ => hp.nonneg z)).mp ht
  have hzs : z ∈ stoch_to_det.support p := by
    simpa [stoch_to_det.support] using hz.ne'
  exact Finset.sum_pos' (fun z _ =>
    mul_nonneg (mul_nonneg (hp.nonneg z) (replica_posterior_nonneg hp D.L i z))
      (replica_posterior_nonneg hp D.L j z))
    ⟨z, Finset.mem_univ _, mul_pos (mul_pos hz (D.rows_pos z hzs i)) (D.rows_pos z hzs j)⟩

lemma payment_sum_ite {A : Type*} [Fintype A] (p : Prop) [Decidable p] (f : A → ℝ) :
    (∑ i, if p then f i else 0) = if p then ∑ i, f i else 0 := by
  by_cases hp : p <;> simp [hp]

lemma payment_push_triple {A C : Type*} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C] (q : A × A × C → ℝ) :
    stoch_to_det.push (fun u : A × A × C => (u.2.1,u.2.2,u.1)) q =
      fun v => q (v.2.2,v.1,v.2.1) := by
  funext ⟨j,c,i⟩
  simp only [stoch_to_det.push, Finset.sum_filter, Fintype.sum_prod_type,
    Prod.mk.injEq, ite_and]
  simp

lemma payment_push_pair {A C : Type*} [Fintype A] [Fintype C]
    [DecidableEq A] (q : A × A × C → ℝ) :
    stoch_to_det.push (fun u : A × A × C => (u.2.1,u.1)) q =
      fun v => ∑ c, q (v.2,v.1,c) := by
  funext ⟨j,i⟩
  unfold stoch_to_det.push
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [Prod.mk.injEq,ite_and]
  simp_rw [payment_sum_ite]
  simp

lemma payment_push_coord {A C : Type*} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C] (q : A × A × C → ℝ) :
    stoch_to_det.push (fun u : A × A × C => (u.2.2,u.1)) q =
      fun v => ∑ j, q (v.2,j,v.1) := by
  funext ⟨c,i⟩
  unfold stoch_to_det.push
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [Prod.mk.injEq,ite_and]
  simp

lemma payment_push_first {A C : Type*} [Fintype A] [Fintype C]
    [DecidableEq A] (q : A × A × C → ℝ) :
    stoch_to_det.push (fun u : A × A × C => u.1) q =
      fun i => ∑ j, ∑ c, q (i,j,c) := by
  funext i
  unfold stoch_to_det.push
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  have hh : ∀ a, (∑ j, ∑ c, if a = i then q (a,j,c) else 0) =
      if a = i then (∑ j, ∑ c, q (a,j,c)) else 0 := by
    intro a
    by_cases hi : a = i <;> simp [hi]
  simp_rw [hh]
  simp

lemma payment_entropy_push {Ω A : Type*} [Fintype Ω] [Fintype A] [DecidableEq A]
    {q : Ω → ℝ} (hq : stoch_to_det.IsPMF q) (f : Ω → A) :
    stoch_to_det.H (stoch_to_det.push f q) =
      ∑ u, q u * stoch_to_det.lg (1/stoch_to_det.push f q (f u)) := by
  unfold stoch_to_det.H
  rw [(stoch_to_det.isPMF_push hq).total]
  exact stoch_to_det.sum_push_mul _ _ _

lemma payment_zero_of_row_zero {A C : Type*} [Fintype A]
    (q : A × A × C → ℝ) (a : A → ℝ) (P : A → C → ℝ)
    (hq : stoch_to_det.IsFinMeas q)
    (hrow : ∀ i c, ∑ j, q (i,j,c) = a i * P i c) :
    ∀ i j c, P i c = 0 → q (i,j,c) = 0 := by
  intro i j c hc
  have hle : q (i,j,c) ≤ ∑ j, q (i,j,c) :=
    Finset.single_le_sum (fun j _ => hq (i,j,c)) (Finset.mem_univ j)
  rw [hrow, hc, mul_zero] at hle
  exact le_antisymm hle (hq _)

/-- Conditional MI of a finite replica law is a weighted conditional KL sum (bits). -/
lemma payment_condMI_KL {A C : Type*} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C]
    (q : A × A × C → ℝ) (a : A → ℝ) (P : A → C → ℝ)
    (hq : stoch_to_det.IsPMF q) (ha : ∀ i, 0 < a i)
    (hP : ∀ i, stoch_to_det.IsPMF (P i))
    (hrow : ∀ i c, ∑ j, q (i,j,c) = a i * P i c)
    (hm : ∀ i j, 0 < ∑ c, q (i,j,c)) :
    stoch_to_det.condMI (fun u => u.2.1) (fun u => u.2.2) (fun u => u.1) q =
      ∑ i, ∑ j, (∑ c, q (i,j,c)) *
        stoch_to_det.KL (fun c => q (i,j,c)/(∑ c, q (i,j,c))) (P i) := by
  classical
  let m := fun i j => ∑ c, q (i,j,c)
  have hfirst : ∀ i, (∑ j, ∑ c, q (i,j,c)) = a i := by
    intro i
    rw [Finset.sum_comm]
    simp_rw [hrow, ← Finset.mul_sum]
    rw [(hP i).sum_eq_one, mul_one]
  have hac := payment_zero_of_row_zero q a P hq.nonneg hrow
  have hterm : ∀ i j c,
      q (i,j,c) * stoch_to_det.lg (1/m i j) +
      q (i,j,c) * stoch_to_det.lg (1/(a i * P i c)) -
      q (i,j,c) * stoch_to_det.lg (1/q (i,j,c)) -
      q (i,j,c) * stoch_to_det.lg (1/a i) =
      m i j * ((q (i,j,c)/m i j) * stoch_to_det.lg ((q (i,j,c)/m i j)/P i c)) := by
    intro i j c
    by_cases hz : q (i,j,c) = 0
    · simp [hz]
    have hp : P i c ≠ 0 := fun h => hz (hac i j c h)
    have hmn : m i j ≠ 0 := (hm i j).ne'
    have han := (ha i).ne'
    simp only [stoch_to_det.lg_eq_log_div]
    rw [Real.log_div one_ne_zero hmn,
      Real.log_div one_ne_zero (mul_ne_zero han hp),
      Real.log_mul han hp, Real.log_div one_ne_zero hz,
      Real.log_div one_ne_zero han,
      Real.log_div (div_ne_zero hz hmn) hp,
      Real.log_div hz hmn, Real.log_one]
    field_simp
    ring
  unfold stoch_to_det.condMI stoch_to_det.Hvar
  rw [payment_entropy_push hq (fun u => (u.2.1,u.1)),
    payment_entropy_push hq (fun u => (u.2.2,u.1)),
    payment_entropy_push hq (fun u => (u.2.1,u.2.2,u.1)),
    payment_entropy_push hq (fun u => u.1)]
  rw [payment_push_pair, payment_push_coord, payment_push_triple, payment_push_first]
  simp_rw [hrow, hfirst]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    Fintype.sum_prod_type, stoch_to_det.KL, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro c _
  exact hterm i j c

/-- Midpoint KL and replica symmetry pay the entire marginal affinity profile. -/
lemma payment_midpoint_profile {A C : Type*} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C]
    (q : A × A × C → ℝ) (a : A → ℝ) (P : A → C → ℝ)
    (hq : stoch_to_det.IsPMF q) (ha : ∀ i, 0 < a i)
    (hP : ∀ i, stoch_to_det.IsPMF (P i))
    (hrow : ∀ i c, ∑ j, q (i,j,c) = a i * P i c)
    (hm : ∀ i j, 0 < ∑ c, q (i,j,c))
    (hsym : ∀ i j c, q (i,j,c) = q (j,i,c)) :
    (∑ i, ∑ j, (∑ c, q (i,j,c)) * (-Real.log (stoch_to_det.BC (P i) (P j)))) ≤
      condMINat
        (fun u => u.2.1) (fun u => u.2.2) (fun u => u.1) q := by
  classical
  let m := fun i j => ∑ c, q (i,j,c)
  let t := fun i j c => q (i,j,c)/m i j
  have hmc : ∀ i j, m i j = m j i := by
    intro i j
    exact Finset.sum_congr rfl (fun c _ => hsym i j c)
  have htc : ∀ i j, t i j = t j i := by
    intro i j
    funext c
    dsimp [t]
    rw [hsym, hmc]
  have ht : ∀ i j, stoch_to_det.IsPMF (t i j) := by
    intro i j
    constructor
    · intro c
      exact div_nonneg (hq.nonneg _) (hm i j).le
    · dsimp [stoch_to_det.mass,t]
      rw [← Finset.sum_div]
      exact div_self (hm i j).ne'
  have hac : ∀ i j, stoch_to_det.AbsCont (t i j) (P i) := by
    intro i j c hc
    simp [t, payment_zero_of_row_zero q a P hq.nonneg hrow i j c hc]
  have hright : (∑ i, ∑ j, m i j * stoch_to_det.KL (t i j) (P j)) =
      ∑ i, ∑ j, m i j * stoch_to_det.KL (t i j) (P i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hmc j i, htc j i]
  have hbound : ∀ i j,
      m i j * (-2*stoch_to_det.lg (stoch_to_det.BC (P i) (P j))) ≤
      m i j * (stoch_to_det.KL (t i j) (P i) + stoch_to_det.KL (t i j) (P j)) := by
    intro i j
    apply mul_le_mul_of_nonneg_left _ (hm i j).le
    exact stoch_to_det.bhattacharyya_le (hP i) (hP j) (ht i j) (hac i j)
      (by rw [htc i j]; exact hac j i)
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hbound i j))
  simp only [mul_add, Finset.sum_add_distrib] at hb
  rw [hright] at hb
  have hkl := payment_condMI_KL q a P hq ha hP hrow hm
  change stoch_to_det.condMI _ _ _ q = ∑ i, ∑ j, m i j * stoch_to_det.KL (t i j) (P i) at hkl
  rw [← hkl] at hb
  have hl : nats (∑ i, ∑ j, m i j * (-2*stoch_to_det.lg
      (stoch_to_det.BC (P i) (P j)))) =
      2 * (∑ i, ∑ j, m i j * (-Real.log (stoch_to_det.BC (P i) (P j)))) := by
    simp only [nats, Finset.mul_sum, stoch_to_det.lg_eq_log_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    field_simp [(Real.log_pos one_lt_two).ne']
  have hmul := nats_le_nats_iff.mpr hb
  rw [hl] at hmul
  simp only [nats_add] at hmul
  change _ ≤ nats (stoch_to_det.condMI _ _ _ _)
  dsimp [m] at hmul
  linarith only [hmul]

lemma payment_coordinate_payment {p : Law X Y} (hp : stoch_to_det.IsPMF p)
    (D : CommonSetup p) {C : Type*} [Fintype C] [DecidableEq C] (f : X × Y → C) :
    (∑ i, ∑ j, pairMass D.L i j * (-Real.log (stoch_to_det.BC
      (stoch_to_det.push f (D.L.comp i)) (stoch_to_det.push f (D.L.comp j))))) ≤
    condMINat (fun u => u.2.1)
      (fun u => f u.2.2) (fun u => u.1) (replicaJoint D.L) := by
  classical
  let F := fun u : D.L.ι × D.L.ι × (X × Y) => (u.1,u.2.1,f u.2.2)
  let q := stoch_to_det.push F (replicaJoint D.L)
  let P := fun i => stoch_to_det.push f (D.L.comp i)
  have hcell : ∀ i j c, q (i,j,c) = ∑ z, if f z = c then replicaJoint D.L (i,j,z) else 0 := by
    intro i j c
    simp [q, F, stoch_to_det.push, Finset.sum_filter, replica_sum_domain, ite_and]
  have hmass : ∀ i j, (∑ c, q (i,j,c)) = pairMass D.L i j := by
    intro i j
    simp_rw [hcell]
    rw [Finset.sum_comm]
    simp [pairMass, replicaJoint, eq_comm]
  have hrow : ∀ i c, (∑ j, q (i,j,c)) = D.L.prior i * P i c := by
    intro i c
    simp_rw [hcell]
    rw [Finset.sum_comm]
    simp_rw [payment_sum_ite, replica_sum_replica_second]
    dsimp [P]
    simp only [stoch_to_det.push, Finset.sum_filter, Finset.mul_sum, stoch_to_det.Latent.joint]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : f z = c <;> simp [hz]
  have hsym : ∀ i j c, q (i,j,c) = q (j,i,c) := by
    intro i j c
    rw [hcell,hcell]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : f z = c <;> simp [hz,replicaJoint]
    ring
  have hb := payment_midpoint_profile q D.L.prior P
    (stoch_to_det.isPMF_push (replica_replica_isPMF hp D.L)) D.prior_pos
    (fun i => stoch_to_det.isPMF_push (D.L.comp_isPMF i)) hrow
    (by intro i j; rw [hmass]; exact payment_pairMass_pos hp D i j) hsym
  simp_rw [hmass] at hb
  have htransport := stoch_to_det.condMI_push_source F
    (fun u => u.2.1) (fun u => u.2.2) (fun u => u.1) (replicaJoint D.L)
  change stoch_to_det.condMI _ _ _ q = _ at htransport
  rw [condMINat_eq, htransport] at hb
  exact hb

/-- The conditional information budget is the prior average of component information. -/
lemma payment_mediation_average {p : Law X Y} (L : stoch_to_det.Latent p) :
    mediation L = ∑ i, L.prior i * stoch_to_det.Knat (L.comp i) := by
  have hfiber : ∀ i,
      stoch_to_det.MI (fun w : L.ι × (X × Y) => w.2.1) (fun w => w.2.2)
        (fun w => if w.1 = i then L.joint w else 0) =
      L.prior i * stoch_to_det.Ixy (L.comp i) := by
    intro i
    let q := stoch_to_det.push (fun z : X × Y => (i,z)) (L.comp i)
    have hq : stoch_to_det.IsPMF q := stoch_to_det.isPMF_push (L.comp_isPMF i)
    have hcell : ∀ w : L.ι × (X × Y), q w = if w.1 = i then L.comp i w.2 else 0 := by
      intro ⟨j,z⟩
      simp [q,stoch_to_det.push,Finset.sum_filter,ite_and,eq_comm]
    have heq : (fun w : L.ι × (X × Y) => if w.1 = i then L.joint w else 0) =
        fun w => L.prior i * q w := by
      funext w
      rw [hcell]
      by_cases hi : w.1 = i <;> simp [hi,stoch_to_det.Latent.joint]
    rw [heq, stoch_to_det.MI_smul hq.nonneg _ _ (L.prior_isPMF.nonneg i)]
    congr 1
    dsimp [q]
    unfold stoch_to_det.MI stoch_to_det.Hvar stoch_to_det.Ixy
    simp only [stoch_to_det.push_push,Function.comp_def]
    rw [replica_push_id]
  unfold mediation condMINat nats
  rw [stoch_to_det.coordinate_condMI_eq_sum L.joint_isPMF]
  simp_rw [hfiber]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [stoch_to_det.Knat_eq_log_two_mul_Ixy (L.comp_isPMF i)]
  ring

omit [DecidableEq X] [DecidableEq Y] in
lemma payment_mismatch {p : Law X Y} (hp : stoch_to_det.IsPMF p) (L : stoch_to_det.Latent p) :
    mismatch L = ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i ≠ j), pairMass L i j := by
  have htotal : (∑ i, ∑ j, pairMass L i j) = 1 := by
    simp_rw [payment_pairMass_rows]
    exact L.prior_isPMF.total
  have hsplit : (∑ i, ∑ j, pairMass L i j) =
      (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i ≠ j), pairMass L i j) + ∑ i, pairMass L i i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.filter_ne Finset.univ i]
    exact (Finset.sum_erase_add Finset.univ (pairMass L i) (Finset.mem_univ i)).symm
  have hd : mismatch L = 1 - ∑ i, pairMass L i i := by
    unfold mismatch stoch_to_det.SharedRace.categoricalMismatch
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [hp.sum_eq_one,Finset.sum_comm]
    simp only [pairMass, pow_two, mul_assoc]
  rw [hd]
  linarith only [htotal,hsplit]

lemma payment_bhattacharyya_self {C : Type*} [Fintype C] (P : C → ℝ)
    (hP : stoch_to_det.IsPMF P) : stoch_to_det.BC P P = 1 := by
  unfold stoch_to_det.BC
  simp_rw [← pow_two, Real.sqrt_sq (hP.nonneg _)]
  exact hP.total

/-- The replica budget pays the off-diagonal separation prices. -/
lemma payment_profile_payment {p : Law X Y} (hp : stoch_to_det.IsPMF p)
    (D : CommonSetup p)
    (haffinity : ∀ i j, i ≠ j → AffinityBound (D.L.comp i) (D.L.comp j)) :
    (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i ≠ j),
      pairMass D.L i j * separationPrice (separation (D.L.comp i) (D.L.comp j))) ≤ replicaBudget D.L := by
  have hx := payment_coordinate_payment hp D Prod.fst
  have hy := payment_coordinate_payment hp D Prod.snd
  have hsum := add_le_add hx hy
  have hid :
      (∑ i, ∑ j, pairMass D.L i j * (-Real.log ((stoch_to_det.BC (stoch_to_det.mX (D.L.comp i)) (stoch_to_det.mX (D.L.comp j)))) -
        Real.log ((stoch_to_det.BC (stoch_to_det.mY (D.L.comp i)) (stoch_to_det.mY (D.L.comp j)))))) ≤ replicaBudget D.L := by
    unfold replicaBudget nats
    simp only [condMINat_eq, nats, mul_sub, Finset.sum_sub_distrib, mul_neg, Finset.sum_neg_distrib] at *
    linarith only [hsum]
  apply le_trans _ hid
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i ≠ j
  · simp only [ite_eq_left hij]
    exact mul_le_mul_of_nonneg_left (haffinity i j hij) (payment_pairMass_nonneg hp D.L i j)
  · have heq : i = j := not_ne_iff.mp hij
    subst j
    simp [payment_bhattacharyya_self _ (stoch_to_det.isPMF_push (D.L.comp_isPMF i)),hij]

lemma payment_information_payment {p : Law X Y} (hp : stoch_to_det.IsPMF p)
    (L : stoch_to_det.Latent p) :
    (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i ≠ j),
      pairMass L i j * ((stoch_to_det.Knat (L.comp i) + stoch_to_det.Knat (L.comp j))/2)) ≤ mediation L := by
  have hleft : (∑ i, ∑ j, pairMass L i j * stoch_to_det.Knat (L.comp i)) = mediation L := by
    rw [payment_mediation_average]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul,payment_pairMass_rows]
  have hright : (∑ i, ∑ j, pairMass L i j * stoch_to_det.Knat (L.comp j)) = mediation L := by
    rw [Finset.sum_comm]
    simp_rw [payment_pairMass_comm L]
    exact hleft
  have havg : (∑ i, ∑ j, pairMass L i j * ((stoch_to_det.Knat (L.comp i) + stoch_to_det.Knat (L.comp j))/2)) = mediation L := by
    simp only [← mul_div_assoc,mul_add]
    simp_rw [← Finset.sum_div]
    simp only [Finset.sum_add_distrib]
    rw [hleft,hright]
    ring
  rw [← havg]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro j _ _
  exact mul_nonneg (payment_pairMass_nonneg hp L i j)
    (div_nonneg (add_nonneg (stoch_to_det.Knat_nonneg (L.comp_isPMF i))
      (stoch_to_det.Knat_nonneg (L.comp_isPMF j))) (by norm_num))

/-- The mismatch of a `CommonSetup` is paid by its budgets: `gamma * mismatch L ≤ (1 + 2 * beta) * mediation L + beta * redundancy L`,
given the affinity bound for every pair, the replica budget and `HasPairCharge beta gamma`. -/
theorem mismatch_payment {p : Law X Y} (hp : stoch_to_det.IsPMF p) (D : CommonSetup p)
    (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (haffinity : ∀ i j, i ≠ j → AffinityBound (D.L.comp i) (D.L.comp j))
    (hreplica : replicaBudget D.L ≤ 2*mediation D.L + redundancy D.L)
    (hPC : HasPairCharge (X := X) (Y := Y) CommonSupportPair beta gamma) :
    gamma*mismatch D.L ≤ (1+2*beta)*mediation D.L + beta*redundancy D.L := by
  have hpair : ∀ i j : D.L.ι, i ≠ j →
      CommonSupportPair (stoch_to_det.support p) D.w (D.L.comp i) (D.L.comp j) := by
    intro i j hij
    exact ⟨D.feasible,D.contact i,D.contact j,D.positive i,D.positive j,
      fun h => hij (D.distinct h)⟩
  have hcharge : gamma*mismatch D.L ≤
      (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i ≠ j),
        pairMass D.L i j * ((stoch_to_det.Knat (D.L.comp i)+stoch_to_det.Knat (D.L.comp j))/2)) +
      beta*(∑ i, ∑ j ∈ Finset.univ.filter (fun j => i ≠ j),
        pairMass D.L i j * separationPrice (separation (D.L.comp i) (D.L.comp j))) := by
    have hscaled : gamma*mismatch D.L ≤ gamma*(∑ i, ∑ j ∈ Finset.univ.filter (fun j => i ≠ j), pairMass D.L i j) :=
      mul_le_mul_of_nonneg_left (le_of_eq (payment_mismatch hp D.L)) hgamma
    apply le_trans hscaled
    have hle : (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i ≠ j), pairMass D.L i j * gamma) ≤
        ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i ≠ j),
          pairMass D.L i j * (((stoch_to_det.Knat (D.L.comp i)+stoch_to_det.Knat (D.L.comp j))/2) +
            beta*separationPrice (separation (D.L.comp i) (D.L.comp j))) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (hPC _ _ _ _ (hpair i j (Finset.mem_filter.mp hj).2))
        (payment_pairMass_nonneg hp D.L i j)
    simpa only [Finset.mul_sum, mul_add, Finset.sum_add_distrib,
      mul_assoc, mul_left_comm, mul_comm] using hle
  calc
    gamma*mismatch D.L ≤ _ := hcharge
    _ ≤ mediation D.L + beta*replicaBudget D.L := add_le_add
      (payment_information_payment hp D.L)
      (mul_le_mul_of_nonneg_left (payment_profile_payment hp D haffinity) hbeta)
    _ ≤ mediation D.L + beta*(2*mediation D.L+redundancy D.L) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hreplica hbeta)
    _ = (1+2*beta)*mediation D.L + beta*redundancy D.L := by ring

end

end NaturalLatents.General
