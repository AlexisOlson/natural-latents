-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/Connected.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised; proofs shortened.
-- Source: the DLorell/stoch_to_det main branch, taken from the head of pull request #6 by Jeremy Gillen at the revision above.
-- Local changes: Added sum_components_tau_le and T_le_sum_components; re-proved reduce_to_connected from these two one-sided inequalities instead of upstream component equalities.
import NaturalLatents.Upstream.Duality

/-!
# Reduction to connected supports

This file constructs component decompositions of finite joint laws, proves
the component inequalities for `tau` and `T`, and derives
`reduce_to_connected`. `General.extension_of_connected` uses that reduction to pass from
connected supports to arbitrary finite laws.
-/

namespace stoch_to_det

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- A **component decomposition** of `p`: a finite family of laws `p i` with
weights `a i`, whose supports are the connected components of `support p`.

The two `hcol`/`hrow` fields encode the key observation: components occupy
disjoint columns and disjoint rows, so
the component index `K` is a function of `X` alone *and* of `Y` alone. That is
what makes the lower bound on `tau` work. -/
structure ComponentDecomp (p : α × β → ℝ) where
  /-- Index type of the components. -/
  κ : Type
  /-- Finiteness of the index type. -/
  fin : Fintype κ
  /-- Decidable equality on the index type. -/
  dec : DecidableEq κ
  /-- Component masses `αᵢ`. -/
  wt : κ → ℝ
  /-- Conditional laws `p⁽ⁱ⁾`. -/
  part : κ → (α × β → ℝ)
  /-- The masses form a law. -/
  wt_isPMF : IsPMF wt
  /-- Each part is a law. -/
  part_isPMF : ∀ i, IsPMF (part i)
  /-- The parts reconstruct `p`. -/
  mixture : ∀ z, ∑ i, wt i * part i z = p z
  /-- Each part has connected support. -/
  part_connected : ∀ i, IsConnected (support (part i))
  /-- Distinct components use disjoint columns. -/
  hcol : ∀ i j z z', z ∈ support (part i) → z' ∈ support (part j) → z.1 = z'.1 → i = j
  /-- Distinct components use disjoint rows. -/
  hrow : ∀ i j z z', z ∈ support (part i) → z' ∈ support (part j) → z.2 = z'.2 → i = j

attribute [instance] ComponentDecomp.fin ComponentDecomp.dec

private def componentRel (S : Finset (α × β))
    (z z' : {z // z ∈ S}) : Prop :=
  Relation.ReflTransGen (fun a b => Adj a.1 b.1) z z'

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
private lemma adj_symm {z z' : α × β} (h : Adj z z') : Adj z' z := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

private noncomputable def componentSetoid (S : Finset (α × β)) :
    Setoid {z // z ∈ S} where
  r := componentRel S
  iseqv := by
    refine ⟨fun _ => Relation.ReflTransGen.refl, ?_,
      fun hab hbc => Relation.ReflTransGen.trans hab hbc⟩
    intro a b hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih =>
        exact Relation.ReflTransGen.trans
          (r := fun a b : {z // z ∈ S} => Adj a.1 b.1)
          (Relation.ReflTransGen.single (adj_symm hbc)) ih

/-- Every finite law has a component decomposition. -/
theorem exists_componentDecomp {p : α × β → ℝ} (hp : IsPMF p) :
    Nonempty (ComponentDecomp p) := by
  classical
  let S := support p
  have hS : S.Nonempty := by
    by_contra h
    have hzero : ∀ z, p z = 0 := by
      intro z
      have hz : z ∉ S := by simp [Finset.not_nonempty_iff_eq_empty.mp h]
      simpa [S, support] using hz
    have hmass : mass p = 0 := by simp [mass, hzero]
    linarith [hp.total]
  let z0 : {z // z ∈ S} := ⟨hS.choose, hS.choose_spec⟩
  let s : Setoid {z // z ∈ S} := componentSetoid S
  let : DecidableRel ((· ≈ ·) : {z // z ∈ S} → {z // z ∈ S} → Prop) :=
    Classical.decRel _
  let Q := Quotient s
  let : Fintype Q := Quotient.fintype s
  let eQ : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  let κ := Fin (Fintype.card Q)
  let k : α × β → κ := fun z =>
    eQ (if hz : z ∈ S then (Quotient.mk'' ⟨z, hz⟩ : Q)
      else (Quotient.mk'' z0 : Q))
  let a : κ → ℝ := push k p
  have ha_pos : ∀ i, 0 < a i := by
    intro i
    obtain ⟨z, hz⟩ := Quotient.exists_rep (eQ.symm i)
    have hpz : 0 < p z.1 := by
      have hpz_ne : p z.1 ≠ 0 := by simpa [S, support] using z.2
      exact lt_of_le_of_ne (hp.nonneg z.1) (Ne.symm hpz_ne)
    have hle : p z.1 ≤ push k p (k z.1) := apply_le_push hp.nonneg k z.1
    have hk : k z.1 = eQ (Quotient.mk'' z : Q) := by
      simp [k, z.2]
    have hi : eQ (Quotient.mk'' z : Q) = i := by simpa using congrArg eQ hz
    simpa [a, hk, hi] using lt_of_lt_of_le hpz hle
  let q : κ → (α × β → ℝ) := fun i z =>
    if k z = i then (a i)⁻¹ * p z else 0
  have hq_pmf : ∀ i, IsPMF (q i) := by
    intro i
    constructor
    · intro z
      simp only [q]
      split
      · exact mul_nonneg (inv_nonneg.mpr (ha_pos i).le) (hp.nonneg z)
      · exact le_rfl
    · unfold mass
      have htotal : (∑ z, q i z) = (a i)⁻¹ * a i := by
        simp [q, a, push, Finset.sum_filter, Finset.mul_sum, mul_ite]
      exact htotal.trans (inv_mul_cancel₀ (ha_pos i).ne')
  have hsupp : ∀ i z, z ∈ support (q i) ↔ z ∈ S ∧ k z = i := by
    intro i z
    have hai : (a i)⁻¹ ≠ 0 := inv_ne_zero (ha_pos i).ne'
    simp [support, q, S, hai, and_comm]
  have hsame_of_adj {z z' : α × β} (hz : z ∈ S) (hz' : z' ∈ S)
      (hadj : Adj z z') : k z = k z' := by
    let zs : {z // z ∈ S} := ⟨z, hz⟩
    let zs' : {z // z ∈ S} := ⟨z', hz'⟩
    have hquot : (Quotient.mk'' zs : Q) = (Quotient.mk'' zs' : Q) := by
      apply Quotient.sound
      change componentRel S zs zs'
      exact Relation.ReflTransGen.single hadj
    simpa [k, zs, zs', hz, hz'] using congrArg eQ hquot
  have hq_conn : ∀ i, IsConnected (support (q i)) := by
    intro i z hz z' hz'
    obtain ⟨hzS, hkz⟩ := (hsupp i z).mp hz
    obtain ⟨hz'S, hkz'⟩ := (hsupp i z').mp hz'
    let zs : {z // z ∈ S} := ⟨z, hzS⟩
    let zs' : {z // z ∈ S} := ⟨z', hz'S⟩
    have hquot : (Quotient.mk'' zs : Q) = (Quotient.mk'' zs' : Q) := by
      apply eQ.injective
      simpa [k, zs, zs', hzS, hz'S] using hkz.trans hkz'.symm
    have hrel : componentRel S zs zs' := Quotient.exact hquot
    clear hquot hkz'
    have aux : ∀ t : {z // z ∈ S}, componentRel S zs t → k zs.1 = i →
        k t.1 = i ∧
          Relation.ReflTransGen
            (fun u v => u ∈ support (q i) ∧ v ∈ support (q i) ∧ Adj u v)
            zs.1 t.1 := by
      intro t ht hstart
      induction ht with
      | refl => exact ⟨hstart, Relation.ReflTransGen.refl⟩
      | @tail u v huv hadj ih =>
          have hkv : k v.1 = i := (hsame_of_adj u.2 v.2 hadj).symm.trans ih.1
          refine ⟨hkv, ih.2.tail ⟨?_, ?_, hadj⟩⟩
          · exact (hsupp i u.1).2 ⟨u.2, ih.1⟩
          · exact (hsupp i v.1).2 ⟨v.2, hkv⟩
    have hstart : k zs.1 = i := by simpa [zs] using hkz
    simpa [zs, zs'] using (aux zs' hrel hstart).2
  refine ⟨{
    κ := κ
    fin := inferInstance
    dec := inferInstance
    wt := a
    part := q
    wt_isPMF := isPMF_push hp
    part_isPMF := hq_pmf
    mixture := ?_
    part_connected := hq_conn
    hcol := ?_
    hrow := ?_ }⟩
  · intro z
    rw [Finset.sum_eq_single (k z)]
    · simp [q, (ha_pos (k z)).ne']
    · intro i _ hi
      simp [q, Ne.symm hi]
    · simp
  · intro i j z z' hz hz' hxy
    have hi : k z = i := (hsupp i z).mp hz |>.2
    have hj : k z' = j := (hsupp j z').mp hz' |>.2
    have hkk := hsame_of_adj ((hsupp i z).mp hz |>.1)
      ((hsupp j z').mp hz' |>.1) (Or.inl hxy)
    rw [hi, hj] at hkk
    exact hkk
  · intro i j z z' hz hz' hxy
    have hi : k z = i := (hsupp i z).mp hz |>.2
    have hj : k z' = j := (hsupp j z').mp hz' |>.2
    have hkk := hsame_of_adj ((hsupp i z).mp hz |>.1)
      ((hsupp j z').mp hz' |>.1) (Or.inr hxy)
    rw [hi, hj] at hkk
    exact hkk

private lemma push_equiv_apply {γ δ : Type*} [Fintype γ] [DecidableEq γ]
    [Fintype δ] [DecidableEq δ] (e : γ ≃ δ) (m : γ → ℝ) :
    push e m = fun d => m (e.symm d) := by
  funext d
  rw [push]
  apply Finset.sum_eq_single (e.symm d)
  · intro c hc hne
    have hec : e c = d := (Finset.mem_filter.mp hc).2
    exact (hne (e.eq_symm_apply.mpr hec)).elim
  · intro hnot
    exact (hnot (by simp)).elim

private lemma H_eq_zero_of_pairwise {γ : Type*} [Fintype γ] [DecidableEq γ]
    {m : γ → ℝ} (_hm : IsFinMeas m)
    (hsing : ∀ x y, m x ≠ 0 → m y ≠ 0 → x = y) : H m = 0 := by
  classical
  by_cases hne : ∃ x, m x ≠ 0
  · obtain ⟨x, hx⟩ := hne
    have hzero : ∀ y, y ≠ x → m y = 0 := by
      intro y hy
      by_contra hmy
      exact hy (hsing y x hmy hx)
    have hmass : mass m = m x := by
      unfold mass
      apply Finset.sum_eq_single x
      · intro y _ hy
        exact hzero y hy
      · simp
    unfold H
    rw [hmass]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : y = x
    · subst y
      simp [hx]
    · simp [hzero y hy]
  · push Not at hne
    have hm0 : m = fun _ => 0 := funext hne
    simp [hm0, H, mass]

private lemma exists_ne_zero_of_push_ne_zero {γ δ : Type*} [Fintype γ]
    [DecidableEq δ] {f : γ → δ} {m : γ → ℝ} {d : δ}
    (h : push f m d ≠ 0) : ∃ x, m x ≠ 0 ∧ f x = d := by
  classical
  by_contra hn
  apply h
  unfold push
  apply Finset.sum_eq_zero
  intro x hx
  by_contra hmx
  apply hn
  exact ⟨x, hmx, (Finset.mem_filter.mp hx).2⟩

private lemma H_mixture_disjoint {ι γ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype γ] [DecidableEq γ] (a : ι → ℝ) (q : ι → γ → ℝ)
    (ha : IsPMF a) (hq : ∀ i, IsPMF (q i))
    (hdisj : ∀ i j x, q i x ≠ 0 → q j x ≠ 0 → i = j)
    (m : γ → ℝ) (hmix : ∀ x, ∑ i, a i * q i x = m x) :
    H m = H a + ∑ i, a i * H (q i) := by
  classical
  let r : ι × γ → ℝ := fun w => a w.1 * q w.1 w.2
  have hr : IsPMF r := by
    constructor
    · intro w
      exact mul_nonneg (ha.nonneg w.1) ((hq w.1).nonneg w.2)
    · unfold mass r
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, (hq _).sum_eq_one, mul_one]
      exact ha.sum_eq_one
  have hsnd : push Prod.snd r = m := by
    funext x
    unfold push
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    simp only [r]
    simpa using hmix x
  have hfiber0 : ∀ x, H (fun i => r (i, x)) = 0 := by
    intro x
    apply H_eq_zero_of_pairwise
    · intro i
      exact mul_nonneg (ha.nonneg i) ((hq i).nonneg x)
    · intro i j hi hj
      exact hdisj i j x (fun hqi => hi (by simp [r, hqi]))
        (fun hqj => hj (by simp [r, hqj]))
  have hr_as_m : H r = H m := by
    rw [H_prod_eq_snd_add_fibers hr, hsnd]
    simp [hfiber0]
  let rs : γ × ι → ℝ := fun w => a w.2 * q w.2 w.1
  have hrs_push : push (Equiv.prodComm ι γ) r = rs := by
    rw [push_equiv_apply]
    rfl
  have hrs : IsPMF rs := by
    rw [← hrs_push]
    exact isPMF_push hr
  have hsnd_rs : push Prod.snd rs = a := by
    funext i
    unfold push
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    simp only [rs]
    simp [← Finset.mul_sum, (hq i).sum_eq_one]
  have hrs_decomp : H rs = H a + ∑ i, a i * H (q i) := by
    rw [H_prod_eq_snd_add_fibers hrs, hsnd_rs]
    apply congrArg (fun t => H a + t)
    apply Finset.sum_congr rfl
    intro i _
    simpa [rs] using H_smul (ha.nonneg i)
  have hrs_eq : H rs = H r := by
    rw [← hrs_push]
    exact H_push_equiv (Equiv.prodComm ι γ) r hr
  rw [← hr_as_m, ← hrs_eq, hrs_decomp]

omit [DecidableEq β] in
private lemma component_mixture_X {p : α × β → ℝ} (D : ComponentDecomp p) (x : α) :
    ∑ i, D.wt i * mX (D.part i) x = mX p x := by
  change ∑ i, D.wt i * push Prod.fst (D.part i) x = push Prod.fst p x
  unfold push
  simp_rw [← D.mixture, Finset.mul_sum]
  rw [Finset.sum_comm]

omit [DecidableEq α] in
private lemma component_mixture_Y {p : α × β → ℝ} (D : ComponentDecomp p) (y : β) :
    ∑ i, D.wt i * mY (D.part i) y = mY p y := by
  change ∑ i, D.wt i * push Prod.snd (D.part i) y = push Prod.snd p y
  unfold push
  simp_rw [← D.mixture, Finset.mul_sum]
  rw [Finset.sum_comm]

private lemma H_eq_components {p : α × β → ℝ} (D : ComponentDecomp p) :
    H p = H D.wt + ∑ i, D.wt i * H (D.part i) := by
  apply H_mixture_disjoint D.wt D.part D.wt_isPMF D.part_isPMF
  · intro i j z hi hj
    apply D.hcol i j z z
    · simpa [support] using hi
    · simpa [support] using hj
    · rfl
  · exact D.mixture

omit [DecidableEq β] in
private lemma HX_eq_components {p : α × β → ℝ} (D : ComponentDecomp p) :
    H (mX p) = H D.wt + ∑ i, D.wt i * H (mX (D.part i)) := by
  apply H_mixture_disjoint D.wt (fun i => mX (D.part i)) D.wt_isPMF
    (fun i => isPMF_push (D.part_isPMF i))
  · intro i j x hi hj
    obtain ⟨z, hzi, hzx⟩ := exists_ne_zero_of_push_ne_zero hi
    obtain ⟨z', hzj, hz'x⟩ := exists_ne_zero_of_push_ne_zero hj
    exact D.hcol i j z z' (by simpa [support] using hzi)
      (by simpa [support] using hzj) (hzx.trans hz'x.symm)
  · exact component_mixture_X D

omit [DecidableEq α] in
private lemma HY_eq_components {p : α × β → ℝ} (D : ComponentDecomp p) :
    H (mY p) = H D.wt + ∑ i, D.wt i * H (mY (D.part i)) := by
  apply H_mixture_disjoint D.wt (fun i => mY (D.part i)) D.wt_isPMF
    (fun i => isPMF_push (D.part_isPMF i))
  · intro i j y hi hj
    obtain ⟨z, hzi, hzy⟩ := exists_ne_zero_of_push_ne_zero hi
    obtain ⟨z', hzj, hz'y⟩ := exists_ne_zero_of_push_ne_zero hj
    exact D.hrow i j z z' (by simpa [support] using hzi)
      (by simpa [support] using hzj) (hzy.trans hz'y.symm)
  · exact component_mixture_Y D

private lemma Psi_eq_components {p : α × β → ℝ} (D : ComponentDecomp p) :
    Psi p = ∑ i, D.wt i * Psi (D.part i) := by
  rw [Psi, H_eq_components D, HX_eq_components D, HY_eq_components D]
  simp only [Psi, mul_sub, Finset.sum_sub_distrib]
  simp_rw [mul_left_comm (D.wt _) 2, ← Finset.mul_sum]
  ring

private noncomputable def glueLatent {p : α × β → ℝ} (D : ComponentDecomp p)
    (V : ∀ i, Latent (D.part i)) : Latent p where
  ι := Σ i, (V i).ι
  fin := inferInstance
  dec := inferInstance
  prior := fun w => D.wt w.1 * (V w.1).prior w.2
  comp := fun w => (V w.1).comp w.2
  prior_isPMF := by
    constructor
    · intro w
      exact mul_nonneg (D.wt_isPMF.nonneg w.1) ((V w.1).prior_isPMF.nonneg w.2)
    · unfold mass
      rw [Fintype.sum_sigma]
      simp_rw [← Finset.mul_sum, (V _).prior_isPMF.sum_eq_one, mul_one]
      exact D.wt_isPMF.sum_eq_one
  comp_isPMF := fun w => (V w.1).comp_isPMF w.2
  mixture := by
    intro z
    rw [Fintype.sum_sigma]
    simp_rw [mul_assoc, ← Finset.mul_sum, (V _).mixture]
    exact D.mixture z

private lemma glueLatent_score {p : α × β → ℝ} (hp : IsPMF p)
    (D : ComponentDecomp p) (V : ∀ i, Latent (D.part i)) :
    (glueLatent D V).score = ∑ i, D.wt i * (V i).score := by
  have hsigma :
      (∑ w : (glueLatent D V).ι,
          (glueLatent D V).prior w * Phi ((glueLatent D V).comp w)) =
        ∑ i, D.wt i * ∑ v, (V i).prior v * Phi ((V i).comp v) := by
    change (∑ w : Σ i, (V i).ι,
      (D.wt w.1 * (V w.1).prior w.2) * Phi ((V w.1).comp w.2)) = _
    rw [Fintype.sum_sigma]
    simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [Latent.score_eq hp, hsigma, Psi_eq_components D]
  simp_rw [Latent.score_eq (D.part_isPMF _)]
  simp only [mul_sub, Finset.sum_sub_distrib]

omit [DecidableEq α] [DecidableEq β] in
private lemma latent_base_ne_zero {p : α × β → ℝ} (V : Latent p)
    {v : V.ι} {z : α × β} (h : V.prior v * V.comp v z ≠ 0) : p z ≠ 0 := by
  have hpos : 0 < V.prior v * V.comp v z :=
    lt_of_le_of_ne
      (mul_nonneg (V.prior_isPMF.nonneg v) ((V.comp_isPMF v).nonneg z))
      (Ne.symm h)
  have hle : V.prior v * V.comp v z ≤ ∑ w, V.prior w * V.comp w z :=
    Finset.single_le_sum
      (fun w _ => mul_nonneg (V.prior_isPMF.nonneg w) ((V.comp_isPMF w).nonneg z))
      (by simp)
  rw [V.mixture z] at hle
  exact (lt_of_lt_of_le hpos hle).ne'

omit [DecidableEq α] [DecidableEq β] in
private lemma glueLatent_isDet {p : α × β → ℝ} (D : ComponentDecomp p)
    (V : ∀ i, Latent (D.part i)) (hV : ∀ i, (V i).IsDet) :
    (glueLatent D V).IsDet := by
  intro z w w' hw hw'
  rcases w with ⟨i, v⟩
  rcases w' with ⟨j, v'⟩
  simp only [glueLatent, mul_assoc] at hw hw'
  have hiv := (mul_ne_zero_iff.mp hw).2
  have hjv := (mul_ne_zero_iff.mp hw').2
  have hij : i = j := D.hcol i j z z
    (by simpa [support] using latent_base_ne_zero (V i) hiv)
    (by simpa [support] using latent_base_ne_zero (V j) hjv) rfl
  subst j
  have hv : v = v' := hV i z v v' hiv hjv
  subst v'
  rfl

omit [DecidableEq α] [DecidableEq β] in
private lemma componentDecomp_nonempty {p : α × β → ℝ} (D : ComponentDecomp p) :
    Nonempty D.κ := by
  by_contra h
  let : IsEmpty D.κ := not_nonempty_iff.mp h
  have ht := D.wt_isPMF.total
  simp [mass] at ht

private noncomputable def componentIndex {p : α × β → ℝ} (D : ComponentDecomp p)
    (z : α × β) : D.κ :=
  if h : ∃ i, z ∈ support (D.part i) then Classical.choose h
  else Classical.choice (componentDecomp_nonempty D)

private lemma componentIndex_eq {p : α × β → ℝ} (D : ComponentDecomp p)
    {i : D.κ} {z : α × β} (hz : z ∈ support (D.part i)) :
    componentIndex D z = i := by
  rw [componentIndex]
  split
  · rename_i h
    exact D.hcol (Classical.choose h) i z z (Classical.choose_spec h) hz rfl
  · rename_i h
    exact (h ⟨i, hz⟩).elim

private lemma part_eq_zero_of_index_ne {p : α × β → ℝ} (D : ComponentDecomp p)
    {i : D.κ} {z : α × β} (h : componentIndex D z ≠ i) : D.part i z = 0 := by
  by_contra hz
  exact h (componentIndex_eq D (by simpa [support] using hz))

private lemma component_slice {p : α × β → ℝ} (D : ComponentDecomp p)
    (i : D.κ) (z : α × β) :
    (if componentIndex D z = i then p z else 0) = D.wt i * D.part i z := by
  classical
  by_cases hk : componentIndex D z = i
  · rw [ite_eq_left hk, ← D.mixture z]
    apply Finset.sum_eq_single i
    · intro j _ hji
      have hkj : componentIndex D z ≠ j := by simpa [hk] using Ne.symm hji
      simp [part_eq_zero_of_index_ne D hkj]
    · simp
  · rw [ite_eq_right hk, part_eq_zero_of_index_ne D hk, mul_zero]

private lemma push_mixture {ι γ δ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype γ] [DecidableEq δ] (a : ι → ℝ) (q : ι → γ → ℝ) (m : γ → ℝ)
    (hmix : ∀ x, ∑ i, a i * q i x = m x) (f : γ → δ) (d : δ) :
    ∑ i, a i * push f (q i) d = push f m d := by
  unfold push
  simp_rw [← hmix, Finset.mul_sum]
  rw [Finset.sum_comm]

private lemma push_part_componentIndex {p : α × β → ℝ} (D : ComponentDecomp p)
    (i j : D.κ) :
    push (componentIndex D) (D.part i) j = if i = j then 1 else 0 := by
  classical
  rw [push, Finset.sum_filter]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    calc
      (∑ z, if componentIndex D z = i then D.part i z else 0) =
          ∑ z, D.part i z := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : componentIndex D z = i
        · simp [hz]
        · simp [hz, part_eq_zero_of_index_ne D hz]
      _ = 1 := by simpa [mass] using (D.part_isPMF i).total
  · rw [ite_eq_right hij]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hz : componentIndex D z = j
    · have hzi : componentIndex D z ≠ i := by simpa [hz] using Ne.symm hij
      simp [hz, part_eq_zero_of_index_ne D hzi]
    · simp [hz]

private lemma push_componentIndex {p : α × β → ℝ} (D : ComponentDecomp p) :
    push (componentIndex D) p = D.wt := by
  funext i
  calc
    push (componentIndex D) p i =
        ∑ j, D.wt j * push (componentIndex D) (D.part j) i :=
      (push_mixture D.wt D.part p D.mixture (componentIndex D) i).symm
    _ = D.wt i := by simp [push_part_componentIndex]

private noncomputable def fiberWeight {p : α × β → ℝ} (D : ComponentDecomp p)
    (V : Latent p) (v : V.ι) (i : D.κ) : ℝ :=
  push (componentIndex D) (V.comp v) i

private lemma fiberWeight_isPMF {p : α × β → ℝ} (D : ComponentDecomp p)
    (V : Latent p) (v : V.ι) : IsPMF (fiberWeight D V v) := by
  exact isPMF_push (V.comp_isPMF v)

private noncomputable def fiberLaw {p : α × β → ℝ} (D : ComponentDecomp p)
    (V : Latent p) (v : V.ι) (i : D.κ) : α × β → ℝ :=
  if _h : fiberWeight D V v i = 0 then D.part i
  else fun z => if componentIndex D z = i then (fiberWeight D V v i)⁻¹ * V.comp v z else 0

private lemma comp_eq_zero_of_fiberWeight_zero {p : α × β → ℝ}
    (D : ComponentDecomp p) (V : Latent p) (v : V.ι) (i : D.κ)
    {z : α × β} (hrho : fiberWeight D V v i = 0)
    (hz : componentIndex D z = i) : V.comp v z = 0 := by
  have hle : V.comp v z ≤ fiberWeight D V v i := by
    unfold fiberWeight push
    exact Finset.single_le_sum (fun w _ => (V.comp_isPMF v).nonneg w) (by simp [hz])
  rw [hrho] at hle
  exact le_antisymm hle ((V.comp_isPMF v).nonneg z)

private lemma fiberLaw_isPMF {p : α × β → ℝ} (D : ComponentDecomp p)
    (V : Latent p) (v : V.ι) (i : D.κ) : IsPMF (fiberLaw D V v i) := by
  classical
  by_cases hrho : fiberWeight D V v i = 0
  · simpa [fiberLaw, hrho] using D.part_isPMF i
  · constructor
    · intro z
      simp only [fiberLaw, dite_eq_right hrho]
      split
      · exact mul_nonneg (inv_nonneg.mpr ((fiberWeight_isPMF D V v).nonneg i))
          ((V.comp_isPMF v).nonneg z)
      · exact le_rfl
    · unfold mass
      simp only [fiberLaw, dite_eq_right hrho, ← Finset.sum_filter, ← Finset.mul_sum]
      exact inv_mul_cancel₀ hrho

private lemma fiberWeight_mul_fiberLaw {p : α × β → ℝ}
    (D : ComponentDecomp p) (V : Latent p) (v : V.ι) (i : D.κ) (z : α × β) :
    fiberWeight D V v i * fiberLaw D V v i z =
      if componentIndex D z = i then V.comp v z else 0 := by
  classical
  by_cases hrho : fiberWeight D V v i = 0
  · by_cases hz : componentIndex D z = i
    · simp [fiberLaw, hrho, hz, comp_eq_zero_of_fiberWeight_zero D V v i hrho hz]
    · simp [fiberLaw, hrho, hz]
  · by_cases hz : componentIndex D z = i <;> simp [fiberLaw, hrho, hz]

private lemma fiberLaw_mixture {p : α × β → ℝ} (D : ComponentDecomp p)
    (V : Latent p) (v : V.ι) (z : α × β) :
    ∑ i, fiberWeight D V v i * fiberLaw D V v i z = V.comp v z := by
  simp [fiberWeight_mul_fiberLaw]

private lemma fiberLaw_index {p : α × β → ℝ} (D : ComponentDecomp p)
    (V : Latent p) (v : V.ι) (i : D.κ) {z : α × β}
    (hz : z ∈ support (fiberLaw D V v i)) : componentIndex D z = i := by
  classical
  by_cases hrho : fiberWeight D V v i = 0
  · apply componentIndex_eq D
    simpa [fiberLaw, hrho] using hz
  · have h := hz
    simp [support, fiberLaw, hrho] at h
    exact h.1

private lemma fiberLaw_supported_component {p : α × β → ℝ}
    (D : ComponentDecomp p) (V : Latent p) {v : V.ι} (hv : V.prior v ≠ 0)
    (i : D.κ) {z : α × β} (hz : z ∈ support (fiberLaw D V v i)) :
    z ∈ support (D.part i) := by
  classical
  by_cases hrho : fiberWeight D V v i = 0
  · simpa [fiberLaw, hrho] using hz
  · have hk : componentIndex D z = i := fiberLaw_index D V v i hz
    have hcomp : V.comp v z ≠ 0 := by
      simpa [support, fiberLaw, hrho, hk] using hz
    have hpz : p z ≠ 0 := latent_base_ne_zero V (mul_ne_zero hv hcomp)
    have hs := component_slice D i z
    rw [ite_eq_left hk] at hs
    have hprod : D.wt i * D.part i z ≠ 0 := by rwa [← hs]
    simpa [support] using (mul_ne_zero_iff.mp hprod).2

private lemma Phi_mixture_disjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (q : ι → α × β → ℝ) (m : α × β → ℝ)
    (ha : IsPMF a) (hq : ∀ i, IsPMF (q i))
    (hmix : ∀ z, ∑ i, a i * q i z = m z)
    (hcol : ∀ i j z z', q i z ≠ 0 → q j z' ≠ 0 → z.1 = z'.1 → i = j)
    (hrow : ∀ i j z z', q i z ≠ 0 → q j z' ≠ 0 → z.2 = z'.2 → i = j) :
    Phi m = (∑ i, a i * Phi (q i)) - H a := by
  have hH : H m = H a + ∑ i, a i * H (q i) := by
    apply H_mixture_disjoint a q ha hq
    · intro i j z hi hj
      exact hcol i j z z hi hj rfl
    · exact hmix
  have hXmix : ∀ x, ∑ i, a i * mX (q i) x = mX m x := by
    exact fun x => push_mixture a q m hmix Prod.fst x
  have hYmix : ∀ y, ∑ i, a i * mY (q i) y = mY m y := by
    exact fun y => push_mixture a q m hmix Prod.snd y
  have hHX : H (mX m) = H a + ∑ i, a i * H (mX (q i)) := by
    apply H_mixture_disjoint a (fun i => mX (q i)) ha
      (fun i => isPMF_push (hq i))
    · intro i j x hi hj
      obtain ⟨z, hzi, hzx⟩ := exists_ne_zero_of_push_ne_zero hi
      obtain ⟨z', hzj, hz'x⟩ := exists_ne_zero_of_push_ne_zero hj
      exact hcol i j z z' hzi hzj (hzx.trans hz'x.symm)
    · exact hXmix
  have hHY : H (mY m) = H a + ∑ i, a i * H (mY (q i)) := by
    apply H_mixture_disjoint a (fun i => mY (q i)) ha
      (fun i => isPMF_push (hq i))
    · intro i j y hi hj
      obtain ⟨z, hzi, hzy⟩ := exists_ne_zero_of_push_ne_zero hi
      obtain ⟨z', hzj, hz'y⟩ := exists_ne_zero_of_push_ne_zero hj
      exact hrow i j z z' hzi hzj (hzy.trans hz'y.symm)
    · exact hYmix
  rw [Phi, hH, hHX, hHY]
  simp only [Phi, mul_sub, Finset.sum_sub_distrib]
  simp_rw [mul_left_comm (a _) 3, mul_left_comm (a _) 2, ← Finset.mul_sum]
  ring

private lemma Phi_fiber_decomp {p : α × β → ℝ} (D : ComponentDecomp p)
    (V : Latent p) {v : V.ι} (hv : V.prior v ≠ 0) :
    Phi (V.comp v) =
      (∑ i, fiberWeight D V v i * Phi (fiberLaw D V v i)) -
        H (fiberWeight D V v) := by
  apply Phi_mixture_disjoint (fiberWeight D V v) (fiberLaw D V v) (V.comp v)
    (fiberWeight_isPMF D V v) (fiberLaw_isPMF D V v)
    (fiberLaw_mixture D V v)
  · intro i j z z' hzi hzj hxy
    exact D.hcol i j z z'
      (fiberLaw_supported_component D V hv i (by simpa [support] using hzi))
      (fiberLaw_supported_component D V hv j (by simpa [support] using hzj)) hxy
  · intro i j z z' hzi hzj hxy
    exact D.hrow i j z z'
      (fiberLaw_supported_component D V hv i (by simpa [support] using hzi))
      (fiberLaw_supported_component D V hv j (by simpa [support] using hzj)) hxy

private lemma weighted_fiberWeight {p : α × β → ℝ} (D : ComponentDecomp p)
    (V : Latent p) (i : D.κ) :
    ∑ v, V.prior v * fiberWeight D V v i = D.wt i := by
  calc
    (∑ v, V.prior v * fiberWeight D V v i) =
        push (componentIndex D) p i :=
      push_mixture V.prior V.comp p V.mixture (componentIndex D) i
    _ = D.wt i := by rw [push_componentIndex D]

private noncomputable def conditionalLatent {p : α × β → ℝ}
    (D : ComponentDecomp p) (V : Latent p) (i : D.κ) (hwt : D.wt i ≠ 0) :
    Latent (D.part i) where
  ι := V.ι
  fin := inferInstance
  dec := inferInstance
  prior := fun v => (D.wt i)⁻¹ * V.prior v * fiberWeight D V v i
  comp := fun v => fiberLaw D V v i
  prior_isPMF := by
    constructor
    · intro v
      exact mul_nonneg
        (mul_nonneg (inv_nonneg.mpr (D.wt_isPMF.nonneg i)) (V.prior_isPMF.nonneg v))
        ((fiberWeight_isPMF D V v).nonneg i)
    · unfold mass
      simp_rw [mul_assoc, ← Finset.mul_sum]
      rw [weighted_fiberWeight D V i, inv_mul_cancel₀ hwt]
  comp_isPMF := fun v => fiberLaw_isPMF D V v i
  mixture := by
    intro z
    calc
      (∑ v, ((D.wt i)⁻¹ * V.prior v * fiberWeight D V v i) *
          fiberLaw D V v i z) =
          (D.wt i)⁻¹ * ∑ v, V.prior v *
            (fiberWeight D V v i * fiberLaw D V v i z) := by
        simp_rw [mul_assoc, ← Finset.mul_sum]
      _ = (D.wt i)⁻¹ * ∑ v, V.prior v *
            (if componentIndex D z = i then V.comp v z else 0) := by
        simp_rw [fiberWeight_mul_fiberLaw]
      _ = (D.wt i)⁻¹ * (if componentIndex D z = i then p z else 0) := by
        congr 1
        by_cases hz : componentIndex D z = i
        · simp [hz, V.mixture]
        · simp [hz]
      _ = (D.wt i)⁻¹ * (D.wt i * D.part i z) := by rw [component_slice D i z]
      _ = D.part i z := by
        rw [← mul_assoc, inv_mul_cancel₀ hwt, one_mul]

private noncomputable def restrictLatent {p : α × β → ℝ}
    (D : ComponentDecomp p) (V : Latent p) (i : D.κ) : Latent (D.part i) :=
  if hwt : D.wt i = 0 then Latent.const (D.part_isPMF i)
  else conditionalLatent D V i hwt

private lemma prior_mul_fiberWeight_eq_zero {p : α × β → ℝ}
    (D : ComponentDecomp p) (V : Latent p) (i : D.κ) (hwt : D.wt i = 0)
    (v : V.ι) : V.prior v * fiberWeight D V v i = 0 := by
  have hnonneg : ∀ w, 0 ≤ V.prior w * fiberWeight D V w i := fun w =>
    mul_nonneg (V.prior_isPMF.nonneg w) ((fiberWeight_isPMF D V w).nonneg i)
  have hle : V.prior v * fiberWeight D V v i ≤
      ∑ w, V.prior w * fiberWeight D V w i :=
    Finset.single_le_sum (fun w _ => hnonneg w) (by simp)
  rw [weighted_fiberWeight D V i, hwt] at hle
  exact le_antisymm hle (hnonneg v)

private lemma weighted_conditional_score {p : α × β → ℝ}
    (D : ComponentDecomp p) (V : Latent p) (i : D.κ) (hwt : D.wt i ≠ 0) :
    D.wt i * (conditionalLatent D V i hwt).score =
      D.wt i * Psi (D.part i) -
        ∑ v, V.prior v * fiberWeight D V v i * Phi (fiberLaw D V v i) := by
  rw [Latent.score_eq (D.part_isPMF i)]
  change D.wt i *
      (Psi (D.part i) -
        ∑ v, ((D.wt i)⁻¹ * V.prior v * fiberWeight D V v i) *
          Phi (fiberLaw D V v i)) = _
  rw [mul_sub]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  simp only [← mul_assoc, mul_inv_cancel₀ hwt, one_mul]

private lemma weighted_restrict_score {p : α × β → ℝ}
    (D : ComponentDecomp p) (V : Latent p) (i : D.κ) :
    D.wt i * (restrictLatent D V i).score =
      D.wt i * Psi (D.part i) -
        ∑ v, V.prior v * fiberWeight D V v i * Phi (fiberLaw D V v i) := by
  by_cases hwt : D.wt i = 0
  · have hsum :
        (∑ v, V.prior v * fiberWeight D V v i * Phi (fiberLaw D V v i)) = 0 := by
      apply Finset.sum_eq_zero
      intro v _
      rw [prior_mul_fiberWeight_eq_zero D V i hwt v, zero_mul]
    simp [restrictLatent, hwt, hsum]
  · simpa [restrictLatent, hwt] using weighted_conditional_score D V i hwt

private lemma restrict_score_gap {p : α × β → ℝ} (hp : IsPMF p)
    (D : ComponentDecomp p) (V : Latent p) :
    (∑ i, D.wt i * (restrictLatent D V i).score) =
      V.score - ∑ v, V.prior v * H (fiberWeight D V v) := by
  have hinner : ∀ v, (∑ i, V.prior v * fiberWeight D V v i *
      Phi (fiberLaw D V v i)) =
      V.prior v * (Phi (V.comp v) + H (fiberWeight D V v)) := by
    intro v
    by_cases hv : V.prior v = 0
    · simp [hv]
    · have hphi := Phi_fiber_decomp D V hv
      simp_rw [mul_assoc, ← Finset.mul_sum]
      congr 1
      linarith
  simp_rw [weighted_restrict_score]
  rw [Finset.sum_sub_distrib, Finset.sum_comm, ← Psi_eq_components D]
  simp_rw [hinner, mul_add, Finset.sum_add_distrib]
  rw [Latent.score_eq hp V]
  ring

private lemma restrict_score_le {p : α × β → ℝ} (hp : IsPMF p)
    (D : ComponentDecomp p) (V : Latent p) :
    (∑ i, D.wt i * (restrictLatent D V i).score) ≤ V.score := by
  rw [restrict_score_gap hp D V]
  exact sub_le_self _ (Finset.sum_nonneg fun v _ =>
    mul_nonneg (V.prior_isPMF.nonneg v) (H_nonneg_of_isPMF (fiberWeight_isPMF D V v)))

/-- The weighted component optima give a lower bound on `tau`. -/
theorem sum_components_tau_le {p : α × β → ℝ} (hp : IsPMF p) (D : ComponentDecomp p) :
    (∑ i, D.wt i * tau (D.part i)) ≤ tau p := by
  classical
  obtain ⟨V, hV⟩ := exists_tau_optimal_latent hp
  calc
    (∑ i, D.wt i * tau (D.part i)) ≤
        ∑ i, D.wt i * (restrictLatent D V i).score := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (tau_le_score (restrictLatent D V i))
        (D.wt_isPMF.nonneg i)
    _ ≤ V.score := restrict_score_le hp D V
    _ = tau p := hV

/-- Gluing deterministic component optima gives an upper bound on `T`. -/
theorem T_le_sum_components {p : α × β → ℝ} (hp : IsPMF p) (D : ComponentDecomp p) :
    T p ≤ ∑ i, D.wt i * T (D.part i) := by
  classical
  choose V hVdet hVscore using fun i => exists_T_optimal_latent (D.part_isPMF i)
  calc
    T p ≤ (glueLatent D V).score := T_le_score (glueLatent D V)
      (glueLatent_isDet D V hVdet)
    _ = ∑ i, D.wt i * (V i).score := glueLatent_score hp D V
    _ = ∑ i, D.wt i * T (D.part i) := by
      simp_rw [hVscore]

/-- Reduction consequence used by the table bound.

For `0 ≤ C`, if `T ≤ C τ` holds for every finite law with connected support,
it holds for every finite law. -/
theorem reduce_to_connected (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ q : α × β → ℝ, IsPMF q → IsConnected (support q) → T q ≤ C * tau q) :
    ∀ q : α × β → ℝ, IsPMF q → T q ≤ C * tau q := by
  intro q hq
  obtain ⟨D⟩ := exists_componentDecomp hq
  calc
    T q ≤ ∑ i, D.wt i * T (D.part i) := T_le_sum_components hq D
    _ ≤ ∑ i, D.wt i * (C * tau (D.part i)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (h (D.part i) (D.part_isPMF i) (D.part_connected i))
        (D.wt_isPMF.nonneg i)
    _ = C * ∑ i, D.wt i * tau (D.part i) := by
      simp_rw [mul_left_comm (D.wt _) C, ← Finset.mul_sum]
    _ ≤ C * tau q := mul_le_mul_of_nonneg_left (sum_components_tau_le hq D) hC

end stoch_to_det
