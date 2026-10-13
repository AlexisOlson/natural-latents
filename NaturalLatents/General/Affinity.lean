-- Adapted from the author's earlier repository (StochasticToDeterministicLatents);
-- modified: module paths renamed; declarations unused by the main theorems removed.
import NaturalLatents.General.Contact

/-!
# Marginal affinities bound the separation price

For two distinct positive contacts, `affinity_bound` shows `Psi (s P R) ≤ -log BC_X - log BC_Y`:
the separation price is paid by the Bhattacharyya affinities of the two pairs of marginals.
The proof bounds each affinity below by the Hellinger comparison of the cube-root secants,
using the contact moments of `Contact` and a polynomial remainder.

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

/-- The polynomial remainder in the marginal Hellinger comparison. -/
lemma affinity_scalar (a : ℝ) (ha : 0 ≤ a) :
    (9 / 8 : ℝ) * (a - 1)^2 * (a + 1) - (a * Real.sqrt a - 1)^2 ≤
      (3 / 16 : ℝ) * (a - 1)^2 * (Real.sqrt a - 1)^2 := by
  let y := Real.sqrt a
  have hy : y^2 = a := Real.sq_sqrt ha
  change (9 / 8 : ℝ) * (a - 1)^2 * (a + 1) - (a * y - 1)^2 ≤
    (3 / 16 : ℝ) * (a - 1)^2 * (y - 1)^2
  rw [← hy]
  have hrem : (3 / 16 : ℝ) * (y^2 - 1)^2 * (y - 1)^2 -
      ((9 / 8 : ℝ) * (y^2 - 1)^2 * (y^2 + 1) - (y^2 * y - 1)^2) =
        ((y - 1)^3)^2 / 16 := by ring
  apply sub_nonneg.mp
  rw [hrem]
  exact div_nonneg (sq_nonneg _) (by norm_num)

lemma affinity_weighted_square {ι : Type} [Fintype ι] (q G : ι → ℝ) (c : ℝ) :
    (∑ i, q i * (G i - c)^2) =
      (∑ i, q i * (G i)^2) - 2 * c * (∑ i, q i * G i) + c^2 * ∑ i, q i := by
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma affinity_conditional_square {ι : Type} [Fintype ι] (q G : ι → ℝ) (a : ℝ)
    (hq : ∀ i, 0 ≤ q i) (ha : 0 < a)
    (hsecond : ∑ i, q i * (G i)^2 = (∑ i, q i) * a) :
    (∑ i, q i) * (Real.sqrt a - 1)^2 ≤ ∑ i, q i * (G i - 1)^2 := by
  have hmass : 0 ≤ ∑ i, q i := Finset.sum_nonneg fun i _ => hq i
  have hvariance : 0 ≤ ∑ i, q i * (G i - Real.sqrt a)^2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hq i) (sq_nonneg _)
  have hraw : (∑ i, q i * G i) ≤ (∑ i, q i) * Real.sqrt a := by
    rw [affinity_weighted_square] at hvariance
    rw [hsecond] at hvariance
    have hs := Real.sq_sqrt ha.le
    have hsqrt := Real.sqrt_pos.2 ha
    have hproduct : 0 ≤ Real.sqrt a * ((∑ i, q i) * Real.sqrt a - ∑ i, q i * G i) := by
      nlinarith [hs]
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hsqrt).mp hproduct)
  have hexpand : (∑ i, q i * (G i - 1)^2) =
      (∑ i, q i * (G i)^2) - 2 * (∑ i, q i * G i) + (∑ i, q i) := by
    simpa using affinity_weighted_square q G 1
  rw [hexpand, hsecond]
  have hs := Real.sq_sqrt ha.le
  have hsweight := congrArg (fun t => (∑ i, q i) * t) hs
  nlinarith only [hraw, hsweight]

lemma affinity_sqrt_cube (p a r : ℝ) (hp : 0 ≤ p) (ha : 0 ≤ a)
    (hcube : p * a^3 = r) : Real.sqrt (p * r) = p * a * Real.sqrt a := by
  have hs : (p * a * Real.sqrt a)^2 = p * r := by
    calc
      (p * a * Real.sqrt a)^2 = p^2 * a^2 * (Real.sqrt a)^2 := by ring
      _ = p * (p * a^3) := by rw [Real.sq_sqrt ha]; ring
      _ = p * r := by rw [hcube]
  rw [← hs, Real.sqrt_sq (mul_nonneg (mul_nonneg hp ha) (Real.sqrt_nonneg a))]

/-- A finite marginal form of the Hellinger comparison; `D` is the unnormalized conditional energy. -/
lemma affinity_marginal_affinity {ι : Type} [Fintype ι]
    (p r F D : ι → ℝ) (t : ℝ)
    (hp : stoch_to_det.IsPMF p) (hF : ∀ i, 0 ≤ F i)
    (hcube : ∀ i, p i * (F i)^3 = r i)
    (hthird : ∑ i, p i * (F i)^3 = 1)
    (hmoment : ∑ i, p i * (F i - 1)^2 * (F i + 1) = t)
    (hD : ∀ i, p i * (Real.sqrt (F i) - 1)^2 ≤ D i)
    (hquartic : ∑ i, (F i - 1)^2 * D i ≤ t^2 / 2) :
    stoch_to_det.BC p r ≤ b t := by
  have hBC : stoch_to_det.BC p r = ∑ i, p i * F i * Real.sqrt (F i) := by
    unfold stoch_to_det.BC
    exact Finset.sum_congr rfl (fun i _ => affinity_sqrt_cube (p i) (F i) (r i) (hp.nonneg i) (hF i) (hcube i))
  have henergy : (∑ i, p i * (F i * Real.sqrt (F i) - 1)^2) =
      2 - 2 * stoch_to_det.BC p r := by
    have hexpand : (∑ i, p i * (F i * Real.sqrt (F i) - 1)^2) =
        (∑ i, p i * (F i)^3) - 2 * (∑ i, p i * F i * Real.sqrt (F i)) + (∑ i, p i) := by
      rw [affinity_weighted_square]
      congr 2
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow, Real.sq_sqrt (hF i)]
      ring
      all_goals ring_nf
    have htotal : ∑ i, p i = 1 := hp.total
    rw [hexpand, hthird, htotal, ← hBC]
    ring
  have hpoint : ∀ i, (9 / 8 : ℝ) * (p i * (F i - 1)^2 * (F i + 1)) -
      p i * (F i * Real.sqrt (F i) - 1)^2 ≤ (3 / 16 : ℝ) * ((F i - 1)^2 * D i) := by
    intro i
    calc
      (9 / 8 : ℝ) * (p i * (F i - 1)^2 * (F i + 1)) -
          p i * (F i * Real.sqrt (F i) - 1)^2 =
          p i * ((9 / 8 : ℝ) * (F i - 1)^2 * (F i + 1) -
            (F i * Real.sqrt (F i) - 1)^2) := by ring
      _ ≤ p i * ((3 / 16 : ℝ) * (F i - 1)^2 * (Real.sqrt (F i) - 1)^2) :=
        mul_le_mul_of_nonneg_left (affinity_scalar (F i) (hF i)) (hp.nonneg i)
      _ = ((3 / 16 : ℝ) * (F i - 1)^2) * (p i * (Real.sqrt (F i) - 1)^2) := by ring
      _ ≤ ((3 / 16 : ℝ) * (F i - 1)^2) * D i :=
        mul_le_mul_of_nonneg_left (hD i) (mul_nonneg (by norm_num) (sq_nonneg _))
      _ = (3 / 16 : ℝ) * ((F i - 1)^2 * D i) := by ring
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  rw [hmoment, henergy] at hsum
  unfold b
  nlinarith only [hsum, hquartic]

lemma affinity_cubic_moment {ι : Type} [Fintype ι] (p F : ι → ℝ)
    (hp : stoch_to_det.IsPMF p) (hthird : ∑ i, p i * (F i)^3 = 1) :
    (∑ i, p i * (F i - 1)^2 * (F i + 1)) =
      2 - (∑ i, p i * (F i)^2) - (∑ i, p i * F i) := by
  have hexpand : (∑ i, p i * (F i - 1)^2 * (F i + 1)) =
      (∑ i, p i * (F i)^3) - (∑ i, p i * (F i)^2) -
        (∑ i, p i * F i) + (∑ i, p i) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have htotal : ∑ i, p i = 1 := hp.total
  rw [hexpand, hthird, htotal]
  ring

lemma affinity_row {ι : Type} [Fintype ι] (q G : ι → ℝ) (a : ℝ) (H : Prop)
    (hq : ∀ i, 0 ≤ q i) (hsupport : 0 < ∑ i, q i → H) (ha : H → 0 < a)
    (hsecond : H → ∑ i, q i * (G i)^2 = (∑ i, q i) * a) :
    (∑ i, q i) * (Real.sqrt a - 1)^2 ≤ ∑ i, q i * (G i - 1)^2 := by
  by_cases hm : 0 < ∑ i, q i
  · exact affinity_conditional_square q G a hq (ha (hsupport hm)) (hsecond (hsupport hm))
  · have hm0 : ∑ i, q i = 0 := le_antisymm (le_of_not_gt hm) (Finset.sum_nonneg fun i _ => hq i)
    rw [hm0, zero_mul]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hq i) (sq_nonneg _)

lemma affinity_row_X {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (hmoments : ContactMoments S P R) (x : X) :
    stoch_to_det.mX P x * (Real.sqrt (f P R x) - 1)^2 ≤
      ∑ y, P (x,y) * (g P R y - 1)^2 := by
<<<<<<< HEAD
  rw [contact_mX_eq_sum]
  apply affinity_row (fun y => P (x, y)) (g P R) (f P R x) (x ∈ XSupport S)
    (fun y => hpair.2.1.1.nonneg (x, y))
  · simpa only [← contact_mX_eq_sum P x] using contact_mem_XSupport_of_mX_pos hpair.2.1
  · exact contact_f_pos hpair
  · intro hx
    rw [← contact_mX_eq_sum P x]
    simpa only [mul_comm] using
      (div_eq_iff (contact_mX_pos hpair.2.1 hpair.2.2.2.1 hx).ne').mp (hmoments.cond_g2 x hx)
||||||| merged common ancestors
  by_cases hx : x ∈ XSupport S
  · have hm := contact_mX_pos hpair.2.1 hpair.2.2.2.1 hx
    have hsecond : (∑ y, P (x,y) * (g P R y)^2) =
        (∑ y, P (x,y)) * f P R x := by
      rw [← contact_mX_eq_sum P x]
      have he := (div_eq_iff hm.ne').mp (hmoments.cond_g2 x hx)
      simpa only [mul_comm] using he
    simpa only [← contact_mX_eq_sum P x] using
      affinity_conditional_square (fun y => P (x,y)) (g P R) (f P R x)
        (fun y => hpair.2.1.1.nonneg (x,y))
        (by simpa only [← contact_mX_eq_sum P x] using hm) (contact_f_pos hpair hx) hsecond
  · have hm : stoch_to_det.mX P x = 0 := by
      rw [contact_mX_eq_sum]
      apply Finset.sum_eq_zero
      intro y _
      apply hpair.2.1.2.1
      intro hz
      exact hx (Finset.mem_image.mpr ⟨(x,y), hz, rfl⟩)
    rw [hm, zero_mul]
    exact Finset.sum_nonneg (fun y _ => mul_nonneg (hpair.2.1.1.nonneg (x,y)) (sq_nonneg _))
=======
  by_cases hx : x ∈ XSupport S
  · have hm := contact_mX_pos hpair.2.1 hpair.2.2.2.1 hx
    have hsecond : (∑ y, P (x,y) * (g P R y)^2) =
        (∑ y, P (x,y)) * f P R x := by
      rw [← stoch_to_det.mX_eq_sum P x]
      have he := (div_eq_iff hm.ne').mp (hmoments.cond_g2 x hx)
      simpa only [mul_comm] using he
    simpa only [← stoch_to_det.mX_eq_sum P x] using
      affinity_conditional_square (fun y => P (x,y)) (g P R) (f P R x)
        (fun y => hpair.2.1.1.nonneg (x,y))
        (by simpa only [← stoch_to_det.mX_eq_sum P x] using hm) (contact_f_pos hpair hx) hsecond
  · have hm : stoch_to_det.mX P x = 0 := by
      rw [stoch_to_det.mX_eq_sum]
      apply Finset.sum_eq_zero
      intro y _
      apply hpair.2.1.2.1
      intro hz
      exact hx (Finset.mem_image.mpr ⟨(x,y), hz, rfl⟩)
    rw [hm, zero_mul]
    exact Finset.sum_nonneg (fun y _ => mul_nonneg (hpair.2.1.1.nonneg (x,y)) (sq_nonneg _))
>>>>>>> lane/cleanup-low

lemma affinity_row_Y {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (hmoments : ContactMoments S P R) (y : Y) :
    stoch_to_det.mY P y * (Real.sqrt (g P R y) - 1)^2 ≤
      ∑ x, P (x,y) * (f P R x - 1)^2 := by
<<<<<<< HEAD
  rw [contact_mY_eq_sum]
  apply affinity_row (fun x => P (x, y)) (f P R) (g P R y) (y ∈ YSupport S)
    (fun x => hpair.2.1.1.nonneg (x, y))
  · simpa only [← contact_mY_eq_sum P y] using contact_mem_YSupport_of_mY_pos hpair.2.1
  · exact contact_g_pos hpair
  · intro hy
    rw [← contact_mY_eq_sum P y]
    simpa only [mul_comm] using
      (div_eq_iff (contact_mY_pos hpair.2.1 hpair.2.2.2.1 hy).ne').mp (hmoments.cond_f2 y hy)
||||||| merged common ancestors
  by_cases hy : y ∈ YSupport S
  · have hm := contact_mY_pos hpair.2.1 hpair.2.2.2.1 hy
    have hsecond : (∑ x, P (x,y) * (f P R x)^2) =
        (∑ x, P (x,y)) * g P R y := by
      rw [← contact_mY_eq_sum P y]
      have he := (div_eq_iff hm.ne').mp (hmoments.cond_f2 y hy)
      simpa only [mul_comm] using he
    simpa only [← contact_mY_eq_sum P y] using
      affinity_conditional_square (fun x => P (x,y)) (f P R) (g P R y)
        (fun x => hpair.2.1.1.nonneg (x,y))
        (by simpa only [← contact_mY_eq_sum P y] using hm) (contact_g_pos hpair hy) hsecond
  · have hm : stoch_to_det.mY P y = 0 := by
      rw [contact_mY_eq_sum]
      apply Finset.sum_eq_zero
      intro x _
      apply hpair.2.1.2.1
      intro hz
      exact hy (Finset.mem_image.mpr ⟨(x,y), hz, rfl⟩)
    rw [hm, zero_mul]
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (hpair.2.1.1.nonneg (x,y)) (sq_nonneg _))
=======
  by_cases hy : y ∈ YSupport S
  · have hm := contact_mY_pos hpair.2.1 hpair.2.2.2.1 hy
    have hsecond : (∑ x, P (x,y) * (f P R x)^2) =
        (∑ x, P (x,y)) * g P R y := by
      rw [← stoch_to_det.mY_eq_sum P y]
      have he := (div_eq_iff hm.ne').mp (hmoments.cond_f2 y hy)
      simpa only [mul_comm] using he
    simpa only [← stoch_to_det.mY_eq_sum P y] using
      affinity_conditional_square (fun x => P (x,y)) (f P R) (g P R y)
        (fun x => hpair.2.1.1.nonneg (x,y))
        (by simpa only [← stoch_to_det.mY_eq_sum P y] using hm) (contact_g_pos hpair hy) hsecond
  · have hm : stoch_to_det.mY P y = 0 := by
      rw [stoch_to_det.mY_eq_sum]
      apply Finset.sum_eq_zero
      intro x _
      apply hpair.2.1.2.1
      intro hz
      exact hy (Finset.mem_image.mpr ⟨(x,y), hz, rfl⟩)
    rw [hm, zero_mul]
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (hpair.2.1.1.nonneg (x,y)) (sq_nonneg _))
>>>>>>> lane/cleanup-low

lemma affinity_BC_X_le {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (hmoments : ContactMoments S P R) :
    BC_X P R ≤ b (s P R) := by
  have hpX := stoch_to_det.isPMF_push (f := Prod.fst) hpair.2.1.1
  have hthird : (∑ x, stoch_to_det.mX P x * (f P R x)^3) = 1 := by
    rw [← contact_E_fst]
    exact hmoments.f3
  apply affinity_marginal_affinity (stoch_to_det.mX P) (stoch_to_det.mX R) (f P R)
    (fun x => ∑ y, P (x,y) * (g P R y - 1)^2) (s P R) hpX (contact_f_nonneg hpair)
    (contact_f_cube hpair) hthird
  · rw [affinity_cubic_moment _ _ hpX hthird, ← contact_E_fst, ← contact_E_fst, hmoments.f2]
    unfold s
    ring
  · exact affinity_row_X hpair hmoments
  · have htower : (∑ x, (f P R x - 1)^2 * (∑ y, P (x,y) * (g P R y - 1)^2)) =
        J P R := by
      unfold J E
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      dsimp only [f, g]
      ring
    rw [htower]
    exact hmoments.J_bound.trans hmoments.scalar_bound

lemma affinity_BC_Y_le {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (hmoments : ContactMoments S P R) :
    BC_Y P R ≤ b (s P R) := by
  have hpY := stoch_to_det.isPMF_push (f := Prod.snd) hpair.2.1.1
  have hthird : (∑ y, stoch_to_det.mY P y * (g P R y)^3) = 1 := by
    rw [← contact_E_snd]
    exact hmoments.g3
  apply affinity_marginal_affinity (stoch_to_det.mY P) (stoch_to_det.mY R) (g P R)
    (fun y => ∑ x, P (x,y) * (f P R x - 1)^2) (s P R) hpY (contact_g_nonneg hpair)
    (contact_g_cube hpair) hthird
  · rw [affinity_cubic_moment _ _ hpY hthird, ← contact_E_snd, ← contact_E_snd, hmoments.g2]
    unfold s
    ring
  · exact affinity_row_Y hpair hmoments
  · have htower : (∑ y, (g P R y - 1)^2 * (∑ x, P (x,y) * (f P R x - 1)^2)) =
        J P R := by
      unfold J E
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      dsimp only [f, g]
      ring
    rw [htower]
    exact hmoments.J_bound.trans hmoments.scalar_bound

lemma affinity_affinities_pos {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) : 0 < BC_X P R ∧ 0 < BC_Y P R := by
  have hexists : ∃ z, 0 < P z := by
    by_contra! h
    have hzero : ∀ z, P z = 0 := fun z => le_antisymm (h z) (hpair.2.1.1.nonneg z)
    have hm : (∑ z, P z) = 0 := Finset.sum_eq_zero (fun z _ => hzero z)
    have ht : (∑ z, P z) = 1 := hpair.2.1.1.total
    linarith
  obtain ⟨z, hz⟩ := hexists
  have hx : z.1 ∈ XSupport S := contact_mem_XSupport_of_mX_pos hpair.2.1 <| hz.trans_le <| by
    rw [contact_mX_eq_sum]
    exact Finset.single_le_sum (fun y _ => hpair.2.1.1.nonneg (z.1, y)) (Finset.mem_univ z.2)
  have hy : z.2 ∈ YSupport S := contact_mem_YSupport_of_mY_pos hpair.2.1 <| hz.trans_le <| by
    rw [contact_mY_eq_sum]
    exact Finset.single_le_sum (fun x _ => hpair.2.1.1.nonneg (x, z.2)) (Finset.mem_univ z.1)
  constructor
  · have ht : 0 < Real.sqrt (stoch_to_det.mX P z.1 * stoch_to_det.mX R z.1) :=
      Real.sqrt_pos.2 (mul_pos (contact_mX_pos hpair.2.1 hpair.2.2.2.1 hx)
        (contact_mX_pos hpair.2.2.1 hpair.2.2.2.2.1 hx))
    exact ht.trans_le (Finset.single_le_sum (fun x _ => Real.sqrt_nonneg
      (stoch_to_det.mX P x * stoch_to_det.mX R x)) (Finset.mem_univ z.1))
  · have ht : 0 < Real.sqrt (stoch_to_det.mY P z.2 * stoch_to_det.mY R z.2) :=
      Real.sqrt_pos.2 (mul_pos (contact_mY_pos hpair.2.1 hpair.2.2.2.1 hy)
        (contact_mY_pos hpair.2.2.1 hpair.2.2.2.2.1 hy))
    exact ht.trans_le (Finset.single_le_sum (fun y _ => Real.sqrt_nonneg
      (stoch_to_det.mY P y * stoch_to_det.mY R y)) (Finset.mem_univ z.2))

lemma affinity_b_pos (t : ℝ) (ht : t < 2) : 0 < b t := by
  have hproduct : 0 < (2 - t) * (10 - t) :=
    mul_pos (sub_pos.mpr ht) (by linarith only [ht])
  have hrem : b t - (1 / 16 : ℝ) = 3 * ((2 - t) * (10 - t)) / 64 := by
    unfold b
    ring
  linarith only [hproduct, hrem]

/-- The separation price is paid by the marginal Bhattacharyya affinities of two contacts. -/
theorem affinity_bound {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (hmoments : ContactMoments S P R) : AffinityBound P R := by
  obtain ⟨hX, hY⟩ := affinity_affinities_pos hpair
  have hb := affinity_b_pos (s P R) hmoments.s_lt_two
  have hlogX := (Real.log_le_log_iff hX hb).mpr (affinity_BC_X_le hpair hmoments)
  have hlogY := (Real.log_le_log_iff hY hb).mpr (affinity_BC_Y_le hpair hmoments)
  unfold AffinityBound Psi
  linarith only [hlogX, hlogY]

end

end StochasticToDeterministicLatents.General
