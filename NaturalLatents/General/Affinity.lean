-- Original work by Alexis Olson, Apache-2.0 (see NOTICE), October 2026, first written on an unpublished branch of
-- github.com/AlexisOlson/stochastic-to-deterministic-latents; reorganised for this repository
-- (namespace NaturalLatents.General, declarations renamed, unused material removed).
-- This file builds on and cites the definitions of DLorell/stoch_to_det (Apache-2.0).
import NaturalLatents.General.Contact

/-!
# Marginal affinities bound the separation price

For two distinct positive contacts, `affinity_bound` shows `separationPrice (separation P R) ≤ -log X-marginal Bhattacharyya affinity - log Y-marginal Bhattacharyya affinity`:
the separation price is paid by the Bhattacharyya affinities of the two pairs of marginals.
The proof bounds each affinity below by the Hellinger comparison of the cube-root secants,
using the contact moments of `stoch_to_det.IsContact` and a polynomial remainder.

## Attribution

Original work by Alexis Olson, October 2026, first written on an unpublished branch of
github.com/AlexisOlson/stochastic-to-deterministic-latents.
This file builds on and cites the definitions of
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
-/

namespace NaturalLatents.General

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

/-- A finite marginal form of the Hellinger comparison; `D` is the unnormalized conditional energy. -/
lemma affinity_marginal_affinity {ι : Type} [Fintype ι]
    (p r F D : ι → ℝ) (t : ℝ)
    (hp : stoch_to_det.IsPMF p) (hF : ∀ i, 0 ≤ F i)
    (hcube : ∀ i, p i * (F i)^3 = r i)
    (hthird : ∑ i, p i * (F i)^3 = 1)
    (hmoment : ∑ i, p i * (F i - 1)^2 * (F i + 1) = t)
    (hD : ∀ i, p i * (Real.sqrt (F i) - 1)^2 ≤ D i)
    (hquartic : ∑ i, (F i - 1)^2 * D i ≤ t^2 / 2) :
    stoch_to_det.BC p r ≤ affinityPoly t := by
  have hBC : stoch_to_det.BC p r = ∑ i, p i * F i * Real.sqrt (F i) := by
    unfold stoch_to_det.BC
    apply Finset.sum_congr rfl
    intro i _
    have hs : (p i * F i * Real.sqrt (F i))^2 = p i * r i := by
      calc
        _ = (p i)^2 * (F i)^2 * (Real.sqrt (F i))^2 := by ring
        _ = p i * (p i * (F i)^3) := by rw [Real.sq_sqrt (hF i)]; ring
        _ = p i * r i := by rw [hcube i]
    rw [← hs, Real.sqrt_sq (mul_nonneg (mul_nonneg (hp.nonneg i) (hF i))
      (Real.sqrt_nonneg (F i)))]
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
  unfold affinityPoly
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
    (hpair : CommonSupportPair S w P R) (hmoments : ContactMoments S P R) (x : X) :
    stoch_to_det.mX P x * (Real.sqrt (rootRatioX P R x) - 1)^2 ≤
      ∑ y, P (x,y) * (rootRatioY P R y - 1)^2 := by
  rw [stoch_to_det.mX_eq_sum]
  apply affinity_row (fun y => P (x, y)) (rootRatioY P R) (rootRatioX P R x) (x ∈ xSupport S)
    (fun y => hpair.2.1.1.nonneg (x, y))
  · simpa only [← stoch_to_det.mX_eq_sum P x] using contact_mem_xSupport_of_mX_pos hpair.2.1
  · exact contact_rootRatioX_pos hpair
  · intro hx
    rw [← stoch_to_det.mX_eq_sum P x]
    simpa only [mul_comm] using
      (div_eq_iff (contact_mX_pos hpair.2.1 hpair.2.2.2.1 hx).ne').mp (hmoments.cond_rootRatioY_square x hx)

lemma affinity_row_Y {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (hmoments : ContactMoments S P R) (y : Y) :
    stoch_to_det.mY P y * (Real.sqrt (rootRatioY P R y) - 1)^2 ≤
      ∑ x, P (x,y) * (rootRatioX P R x - 1)^2 := by
  rw [stoch_to_det.mY_eq_sum]
  apply affinity_row (fun x => P (x, y)) (rootRatioX P R) (rootRatioY P R y) (y ∈ ySupport S)
    (fun x => hpair.2.1.1.nonneg (x, y))
  · simpa only [← stoch_to_det.mY_eq_sum P y] using contact_mem_ySupport_of_mY_pos hpair.2.1
  · exact contact_rootRatioY_pos hpair
  · intro hy
    rw [← stoch_to_det.mY_eq_sum P y]
    simpa only [mul_comm] using
      (div_eq_iff (contact_mY_pos hpair.2.1 hpair.2.2.2.1 hy).ne').mp (hmoments.cond_rootRatioX_square y hy)

lemma affinity_bhattacharyyaX_le {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (hmoments : ContactMoments S P R) :
    (stoch_to_det.BC (stoch_to_det.mX P) (stoch_to_det.mX R)) ≤ affinityPoly (separation P R) := by
  have hpX := stoch_to_det.isPMF_push (f := Prod.fst) hpair.2.1.1
  have hthird : (∑ x, stoch_to_det.mX P x * (rootRatioX P R x)^3) = 1 := by
    rw [← contact_expect_fst]
    exact hmoments.rootRatioX_cube
  apply affinity_marginal_affinity (stoch_to_det.mX P) (stoch_to_det.mX R) (rootRatioX P R)
    (fun x => ∑ y, P (x,y) * (rootRatioY P R y - 1)^2) (separation P R) hpX (contact_rootRatioX_nonneg hpair)
    (contact_rootRatioX_cube_mul_marginal hpair) hthird
  · rw [affinity_cubic_moment _ _ hpX hthird, ← contact_expect_fst, ← contact_expect_fst, hmoments.rootRatioX_square]
    unfold separation defectX defectY
    ring
  · exact affinity_row_X hpair hmoments
  · have htower : (∑ x, (rootRatioX P R x - 1)^2 * (∑ y, P (x,y) * (rootRatioY P R y - 1)^2)) =
        quarticMoment P R := by
      unfold quarticMoment expect
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      dsimp only [rootRatioX, rootRatioY]
      ring
    rw [htower]
    exact hmoments.quarticMoment_bound.trans hmoments.scalar_bound

lemma affinity_bhattacharyyaY_le {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (hmoments : ContactMoments S P R) :
    (stoch_to_det.BC (stoch_to_det.mY P) (stoch_to_det.mY R)) ≤ affinityPoly (separation P R) := by
  have hpY := stoch_to_det.isPMF_push (f := Prod.snd) hpair.2.1.1
  have hthird : (∑ y, stoch_to_det.mY P y * (rootRatioY P R y)^3) = 1 := by
    rw [← contact_expect_snd]
    exact hmoments.rootRatioY_cube
  apply affinity_marginal_affinity (stoch_to_det.mY P) (stoch_to_det.mY R) (rootRatioY P R)
    (fun y => ∑ x, P (x,y) * (rootRatioX P R x - 1)^2) (separation P R) hpY (contact_rootRatioY_nonneg hpair)
    (contact_rootRatioY_cube_mul_marginal hpair) hthird
  · rw [affinity_cubic_moment _ _ hpY hthird, ← contact_expect_snd, ← contact_expect_snd, hmoments.rootRatioY_square]
    unfold separation defectX defectY
    ring
  · exact affinity_row_Y hpair hmoments
  · have htower : (∑ y, (rootRatioY P R y - 1)^2 * (∑ x, P (x,y) * (rootRatioX P R x - 1)^2)) =
        quarticMoment P R := by
      unfold quarticMoment expect
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      dsimp only [rootRatioX, rootRatioY]
      ring
    rw [htower]
    exact hmoments.quarticMoment_bound.trans hmoments.scalar_bound

lemma affinity_affinities_pos {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) : 0 < (stoch_to_det.BC (stoch_to_det.mX P) (stoch_to_det.mX R)) ∧ 0 < (stoch_to_det.BC (stoch_to_det.mY P) (stoch_to_det.mY R)) := by
  have hexists : ∃ z, 0 < P z := by
    by_contra! h
    have hzero : ∀ z, P z = 0 := fun z => le_antisymm (h z) (hpair.2.1.1.nonneg z)
    have hm : (∑ z, P z) = 0 := Finset.sum_eq_zero (fun z _ => hzero z)
    have ht : (∑ z, P z) = 1 := hpair.2.1.1.total
    linarith
  obtain ⟨z, hz⟩ := hexists
  have hx : z.1 ∈ xSupport S := contact_mem_xSupport_of_mX_pos hpair.2.1 <| hz.trans_le <| by
    rw [stoch_to_det.mX_eq_sum]
    exact Finset.single_le_sum (fun y _ => hpair.2.1.1.nonneg (z.1, y)) (Finset.mem_univ z.2)
  have hy : z.2 ∈ ySupport S := contact_mem_ySupport_of_mY_pos hpair.2.1 <| hz.trans_le <| by
    rw [stoch_to_det.mY_eq_sum]
    exact Finset.single_le_sum (fun x _ => hpair.2.1.1.nonneg (x, z.2)) (Finset.mem_univ z.1)
  have affinity_pos {ι : Type} [Fintype ι] (p r : ι → ℝ) (i : ι)
      (hi : 0 < p i) (hir : 0 < r i) : 0 < ∑ j, Real.sqrt (p j * r j) := by
    have ht := Real.sqrt_pos.2 (mul_pos hi hir)
    exact ht.trans_le (Finset.single_le_sum
      (fun j _ => Real.sqrt_nonneg (p j * r j)) (Finset.mem_univ i))
  exact ⟨affinity_pos _ _ z.1 (contact_mX_pos hpair.2.1 hpair.2.2.2.1 hx)
      (contact_mX_pos hpair.2.2.1 hpair.2.2.2.2.1 hx),
    affinity_pos _ _ z.2 (contact_mY_pos hpair.2.1 hpair.2.2.2.1 hy)
      (contact_mY_pos hpair.2.2.1 hpair.2.2.2.2.1 hy)⟩

/-- The separation price is paid by the marginal Bhattacharyya affinities of two contacts. -/
theorem affinity_bound {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (hmoments : ContactMoments S P R) : AffinityBound P R := by
  obtain ⟨hX, hY⟩ := affinity_affinities_pos hpair
  have hb := affinityPoly_pos (separation P R) hmoments.separation_lt_two.le
  have hlogX := (Real.log_le_log_iff hX hb).mpr (affinity_bhattacharyyaX_le hpair hmoments)
  have hlogY := (Real.log_le_log_iff hY hb).mpr (affinity_bhattacharyyaY_le hpair hmoments)
  unfold AffinityBound separationPrice
  linarith only [hlogX, hlogY]

end

end NaturalLatents.General
