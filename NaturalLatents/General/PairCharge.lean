-- Adapted from the author's earlier repository (StochasticToDeterministicLatents);
-- modified: module paths renamed; declarations unused by the main theorems removed.
import NaturalLatents.General.PairCharge.Entropy
import NaturalLatents.General.PairCharge.Features

/-!
# The pair charge

On every pair of distinct positive contacts `P`, `R` of a common feasible kernel,

    (I P + I R) / 2 + (1/10) * Psi (s P R) ≥ 3/25,

that is, `PC CommonSupportPairs (1/10) (3/25)` (`pairCharge_A`). This module proves the
cubic conditional bounds, the covariance payment, the high-`j` charge in the small-`s` region and the
averaged charge in the remaining regions, and splits the rectangle of `(s, contactj)` into the five regions on which
one of the payments of the earlier parts closes.

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

lemma pairCharge_weighted_second_moment {ι : Type*} [Fintype ι]
    (p F : ι → ℝ) (d : ℝ) (hp : ∀ i, 0 ≤ p i) (hd : 0 ≤ d)
    (hsum : ∑ i, p i = d) :
    ((∑ i, p i * F i) / d)^2 ≤ (∑ i, p i * (F i)^2) / d := by
  by_cases hz : d = 0
  · have hpi : ∀ i, p i = 0 := by
      intro i
      apply le_antisymm
      · have := Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
        simpa [hsum, hz] using this
      · exact hp i
    simp [hz, hpi]
  · have hdp : 0 < d := lt_of_le_of_ne hd (Ne.symm hz)
    let q : ι → ℝ := fun i => p i / d
    have hqt : ∑ i, q i = 1 := by
      simp only [q, ← Finset.sum_div, hsum, div_self hz]
    have hv := pairCharge_variance_raw q F hqt
    have hn : 0 ≤ ∑ i, q i * (F i - ∑ j, q j * F j)^2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (div_nonneg (hp i) hdp.le) (sq_nonneg _)
    rw [hv] at hn
    dsimp [q] at hn
    simp only [div_mul_eq_mul_div, ← Finset.sum_div] at hn
    linarith

lemma pairCharge_cond_X_second_moment {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (G : Y → ℝ) (x : X) :
    ((∑ y, P (x,y)*G y)/stoch_to_det.mX P x)^2 ≤
      (∑ y, P (x,y)*(G y)^2)/stoch_to_det.mX P x := by
  apply pairCharge_weighted_second_moment (fun y => P (x, y)) G _
    (fun y => hP.nonneg (x, y)) ((stoch_to_det.isPMF_push hP).nonneg x)
  exact (stoch_to_det.mX_eq_sum P x).symm

lemma pairCharge_cubic_conditional_algebra {u a m D : ℝ} (hu : u = a - 1)
    (hD : D = a - 2 * m + 1) (hcs : m^2 ≤ a) :
    u^2 ≤ 2 * (2 + u) * D := by
  rw [hD, hu]
  nlinarith only [hcs, sq_nonneg (a + 1 - 2 * m)]

/-- The conditional root estimate; the proof is an exact square without square roots. -/
lemma pairCharge_cubic_conditional_X {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) {x : X} (hx : x ∈ XSupport S) :
    (U P R x)^2 ≤ 2*(2+U P R x)*
      ((∑ y, P (x,y)*(V P R y)^2)/stoch_to_det.mX P x) := by
  let m := (∑ y, P (x,y)*g P R y)/stoch_to_det.mX P x
  let DX := (∑ y, P (x,y)*(V P R y)^2)/stoch_to_det.mX P x
  have hcs : m^2 ≤ f P R x := by
    have h := pairCharge_cond_X_second_moment hpair.2.1.1 (g P R) x
    rw [(contact_moments hpair).cond_g2 x hx] at h
    exact h
  have hmx : stoch_to_det.mX P x ≠ 0 := (contact_mX_pos hpair.2.1 hpair.2.2.2.1 hx).ne'
  have hDX : DX = f P R x-2*m+1 := by
    have ht : (∑ y, P (x,y))/stoch_to_det.mX P x = 1 := by
      rw [← stoch_to_det.mX_eq_sum]
      exact div_self hmx
    have hgf := (contact_moments hpair).cond_g2 x hx
    have hid : (∑ y, P (x,y)*(V P R y)^2) =
        (∑ y, P (x,y)*(g P R y)^2)-2*(∑ y, P (x,y)*g P R y)+(∑ y, P (x,y)) := by
      rw [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y _
      unfold g
      ring
    dsimp [DX,m]
    rw [hid,add_div,sub_div,mul_div_assoc,hgf,ht]
  have hU : U P R x = f P R x-1 := by unfold f;ring
  exact pairCharge_cubic_conditional_algebra hU hDX hcs

-- Positive conditional `L^3` contraction.

lemma pairCharge_cubic_norm_scalar {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ≤ a^((2 : ℝ) / 3) * b^((2 : ℝ) / 3)) : a ≤ b^2 := by
  have hc := pow_le_pow_left₀ ha h 3
  have hp (c : ℝ) (hc0 : 0 ≤ c) : (c^((2 : ℝ) / 3))^3 = c^2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc0]
    norm_num [Real.rpow_two]
  rw [mul_pow, hp a ha, hp b hb] at hc
  by_cases hz : a = 0
  · rw [hz]
    exact sq_nonneg b
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
    apply (mul_le_mul_iff_of_pos_left (sq_pos_of_pos hap)).mp
    calc
      a^2 * a = a^3 := by ring
      _ ≤ a^2 * b^2 := hc

/-- Positive conditional `L^(3/2)` to `L^3` contraction. -/
lemma pairCharge_cond_X_cube_bound {S : Finset (X × Y)} {w P : Law X Y}
    (hw : FeasibleKernel S w) (hP : Contact S w P)
    (k : Y → ℝ) (hk : ∀ y, 0 ≤ k y) :
    E P (fun z => ((∑ y, P (z.1,y) * k y) / stoch_to_det.mX P z.1)^3) ≤
      (E P (fun z => (k z.2)^((3 : ℝ) / 2)))^2 := by
  let D : X → ℝ := fun x => (∑ y, P (x,y) * k y) / stoch_to_det.mX P x
  let a := E P (fun z => (D z.1)^3)
  let b := E P (fun z => (k z.2)^((3 : ℝ) / 2))
  have hD (x : X) : 0 ≤ D x := by
    exact div_nonneg (Finset.sum_nonneg fun y _ => mul_nonneg (hP.1.nonneg _) (hk y))
      ((stoch_to_det.isPMF_push hP.1).nonneg x)
  have ha : 0 ≤ a := contact_E_nonneg hP.1 _ (fun z => pow_nonneg (hD z.1) 3)
  have hb : 0 ≤ b := contact_E_nonneg hP.1 _ (fun z => Real.rpow_nonneg (hk z.2) _)
  have hpow (x : X) : ((D x)^2)^((3 : ℝ) / 2) = (D x)^3 := by
    rw [← Real.rpow_natCast_mul (hD x) 2 ((3 : ℝ) / 2)]
    norm_num
  have hhc := stoch_to_det.contact_hypercontractive hw hP
    (f := fun x => (D x)^2) (g := k) (fun _ => sq_nonneg _) hk
  simp only [hpow] at hhc
  have hleft : (∑ z ∈ S, P z * (D z.1)^2 * k z.2) =
      E P (fun z => (D z.1)^2 * k z.2) := by
    unfold E
    simp only [mul_assoc]
    apply Finset.sum_subset (Finset.subset_univ S)
    intro z _ hz
    simp [hP.2.1 z hz]
  have hsumD : (∑ x, stoch_to_det.mX P x * (D x)^3) = a :=
    stoch_to_det.sum_push_mul Prod.fst P (fun x => (D x)^3)
  have hsumk : (∑ y, stoch_to_det.mY P y * (k y)^((3 : ℝ) / 2)) = b :=
    stoch_to_det.sum_push_mul Prod.snd P (fun y => (k y)^((3 : ℝ) / 2))
  have ht := pairCharge_cond_X_inner hP.1 (fun x => (D x)^2) k
  have hinner : E P (fun z => (D z.1)^2 * k z.2) = a := by
    rw [← ht]
    change E P (fun z => (D z.1)^2 * D z.1) = E P (fun z => (D z.1)^3)
    congr 1
  rw [hleft, hsumD, hsumk, hinner] at hhc
  exact pairCharge_cubic_norm_scalar ha hb hhc

lemma pairCharge_cond_Y_cube_bound {S : Finset (X × Y)} {w P : Law X Y}
    (hw : FeasibleKernel S w) (hP : Contact S w P)
    (k : X → ℝ) (hk : ∀ x, 0 ≤ k x) :
    E P (fun z => ((∑ x, P (x,z.2) * k x) / stoch_to_det.mY P z.2)^3) ≤
      (E P (fun z => (k z.1)^((3 : ℝ) / 2)))^2 := by
  let D : Y → ℝ := fun y => (∑ x, P (x,y) * k x) / stoch_to_det.mY P y
  let a := E P (fun z => (D z.2)^3)
  let b := E P (fun z => (k z.1)^((3 : ℝ) / 2))
  have hD (y : Y) : 0 ≤ D y := by
    exact div_nonneg (Finset.sum_nonneg fun x _ => mul_nonneg (hP.1.nonneg _) (hk x))
      ((stoch_to_det.isPMF_push hP.1).nonneg y)
  have ha : 0 ≤ a := contact_E_nonneg hP.1 _ (fun z => pow_nonneg (hD z.2) 3)
  have hb : 0 ≤ b := contact_E_nonneg hP.1 _ (fun z => Real.rpow_nonneg (hk z.1) _)
  have hpow (y : Y) : ((D y)^2)^((3 : ℝ) / 2) = (D y)^3 := by
    rw [← Real.rpow_natCast_mul (hD y) 2 ((3 : ℝ) / 2)]
    norm_num
  have hhc := stoch_to_det.contact_hypercontractive hw hP
    (f := k) (g := fun y => (D y)^2) hk (fun _ => sq_nonneg _)
  simp only [hpow] at hhc
  have hleft : (∑ z ∈ S, P z * k z.1 * (D z.2)^2) =
      E P (fun z => k z.1 * (D z.2)^2) := by
    unfold E
    simp only [mul_assoc]
    apply Finset.sum_subset (Finset.subset_univ S)
    intro z _ hz
    simp [hP.2.1 z hz]
  have hsumD : (∑ y, stoch_to_det.mY P y * (D y)^3) = a :=
    stoch_to_det.sum_push_mul Prod.snd P (fun y => (D y)^3)
  have hsumk : (∑ x, stoch_to_det.mX P x * (k x)^((3 : ℝ) / 2)) = b :=
    stoch_to_det.sum_push_mul Prod.fst P (fun x => (k x)^((3 : ℝ) / 2))
  have ht := pairCharge_cond_Y_inner hP.1 k (fun y => (D y)^2)
  have hinner : E P (fun z => k z.1 * (D z.2)^2) = a := by
    rw [← ht]
    change E P (fun z => D z.2 * (D z.2)^2) = E P (fun z => (D z.2)^3)
    congr 1
    funext z
    ring
  rw [hleft, hsumD, hsumk, hinner] at hhc
  exact pairCharge_cubic_norm_scalar ha hb (hhc.trans_eq (mul_comm _ _))

lemma pairCharge_sq_rpow_three_halves (t : ℝ) :
    (t^2)^((3 : ℝ) / 2) = |t|^3 := by
  rw [← sq_abs, ← Real.rpow_natCast_mul (abs_nonneg t) 2 ((3 : ℝ) / 2)]
  norm_num

lemma pairCharge_contact_DX_cube {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    E P (fun z => ((∑ y, P (z.1,y) * (V P R y)^2) / stoch_to_det.mX P z.1)^3) ≤
      (E P (fun z => |V P R z.2|^3))^2 := by
  have h := pairCharge_cond_X_cube_bound hpair.1 hpair.2.1
    (fun y => (V P R y)^2) (fun _ => sq_nonneg _)
  simpa only [pairCharge_sq_rpow_three_halves] using h

lemma pairCharge_contact_DY_cube {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    E P (fun z => ((∑ x, P (x,z.2) * (U P R x)^2) / stoch_to_det.mY P z.2)^3) ≤
      (E P (fun z => |U P R z.1|^3))^2 := by
  have h := pairCharge_cond_Y_cube_bound hpair.1 hpair.2.1
    (fun x => (U P R x)^2) (fun _ => sq_nonneg _)
  simpa only [pairCharge_sq_rpow_three_halves] using h

lemma pairCharge_cond_Y_second_moment {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F : X → ℝ) (y : Y) :
    ((∑ x, P (x,y)*F x)/stoch_to_det.mY P y)^2 ≤
      (∑ x, P (x,y)*(F x)^2)/stoch_to_det.mY P y := by
  apply pairCharge_weighted_second_moment (fun x => P (x, y)) F _
    (fun x => hP.nonneg (x, y)) ((stoch_to_det.isPMF_push hP).nonneg y)
  exact (stoch_to_det.mY_eq_sum P y).symm

lemma pairCharge_cubic_conditional_Y {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) {y : Y} (hy : y ∈ YSupport S) :
    (V P R y)^2 ≤ 2*(2+V P R y)*
      ((∑ x, P (x,y)*(U P R x)^2)/stoch_to_det.mY P y) := by
  let m := (∑ x, P (x,y)*f P R x)/stoch_to_det.mY P y
  let DY := (∑ x, P (x,y)*(U P R x)^2)/stoch_to_det.mY P y
  have hcs : m^2 ≤ g P R y := by
    have h := pairCharge_cond_Y_second_moment hpair.2.1.1 (f P R) y
    rw [(contact_moments hpair).cond_f2 y hy] at h
    exact h
  have hmy : stoch_to_det.mY P y ≠ 0 := (contact_mY_pos hpair.2.1 hpair.2.2.2.1 hy).ne'
  have hDY : DY = g P R y-2*m+1 := by
    have ht : (∑ x, P (x,y))/stoch_to_det.mY P y = 1 := by
      rw [← stoch_to_det.mY_eq_sum]
      exact div_self hmy
    have hfg := (contact_moments hpair).cond_f2 y hy
    have hid : (∑ x, P (x,y)*(U P R x)^2) =
        (∑ x, P (x,y)*(f P R x)^2)-2*(∑ x, P (x,y)*f P R x)+(∑ x, P (x,y)) := by
      rw [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      unfold f
      ring
    dsimp [DY,m]
    rw [hid,add_div,sub_div,mul_div_assoc,hfg,ht]
  have hV : V P R y = g P R y-1 := by unfold g;ring
  exact pairCharge_cubic_conditional_algebra hV hDY hcs

lemma pairCharge_U_den_pos {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (x : X) : 0 < 2+U P R x := by
  have hf := contact_f_nonneg hpair x
  unfold f at hf
  linarith

lemma pairCharge_V_den_pos {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (y : Y) : 0 < 2+V P R y := by
  have hg := contact_g_nonneg hpair y
  unfold g at hg
  linarith

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_average_quartic_bound {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (L D : X × Y → ℝ) (J : ℝ)
    (hpoint : ∀ z, 0 < P z → L z ^ 4 / (2 + L z) ≤ 2 * (L z ^ 2 * D z))
    (hinner : E P (fun z => L z ^ 2 * D z) = J) :
    E P (fun z => L z ^ 4 / (2 + L z)) ≤ 2 * J := by
  calc
    _ ≤ E P (fun z => 2 * (L z ^ 2 * D z)) := by
      unfold E
      apply Finset.sum_le_sum
      intro z _
      by_cases hz : P z = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left
          (hpoint z (lt_of_le_of_ne (hP.nonneg z) (Ne.symm hz))) (hP.nonneg z)
    _ = 2 * E P (fun z => L z ^ 2 * D z) := contact_q_E_scale _ _ _
    _ = 2 * J := by rw [hinner]

lemma pairCharge_KX_bound {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    E P (fun z => (U P R z.1)^4/(2+U P R z.1)) ≤ 2*J P R := by
  let DX : X → ℝ := fun x => (∑ y, P (x,y)*(V P R y)^2)/stoch_to_det.mX P x
  have hpoint (z : X × Y) (hp : 0 < P z) :
      (U P R z.1)^4/(2+U P R z.1) ≤ 2*((U P R z.1)^2*DX z.1) := by
    have hz := pairCharge_mem_S_of_pos hpair.2.1 hp
    have hx : z.1 ∈ XSupport S := Finset.mem_image.mpr ⟨z,hz,rfl⟩
    have hc := pairCharge_cubic_conditional_X hpair hx
    change (U P R z.1)^2 ≤ 2*(2+U P R z.1)*DX z.1 at hc
    have hm := mul_le_mul_of_nonneg_left hc (sq_nonneg (U P R z.1))
    apply (div_le_iff₀ (pairCharge_U_den_pos hpair z.1)).2
    nlinarith only [hm]
  apply pairCharge_average_quartic_bound hpair.2.1.1
    (fun z => U P R z.1) (fun z => DX z.1) (J P R) hpoint
  exact pairCharge_cond_X_inner hpair.2.1.1
    (fun x => (U P R x)^2) (fun y => (V P R y)^2)

lemma pairCharge_KY_bound {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    E P (fun z => (V P R z.2)^4/(2+V P R z.2)) ≤ 2*J P R := by
  let DY : Y → ℝ := fun y => (∑ x, P (x,y)*(U P R x)^2)/stoch_to_det.mY P y
  have hpoint (z : X × Y) (hp : 0 < P z) :
      (V P R z.2)^4/(2+V P R z.2) ≤ 2*((V P R z.2)^2*DY z.2) := by
    have hz := pairCharge_mem_S_of_pos hpair.2.1 hp
    have hy : z.2 ∈ YSupport S := Finset.mem_image.mpr ⟨z,hz,rfl⟩
    have hc := pairCharge_cubic_conditional_Y hpair hy
    change (V P R z.2)^2 ≤ 2*(2+V P R z.2)*DY z.2 at hc
    have hm := mul_le_mul_of_nonneg_left hc (sq_nonneg (V P R z.2))
    apply (div_le_iff₀ (pairCharge_V_den_pos hpair z.2)).2
    nlinarith only [hm]
  apply pairCharge_average_quartic_bound hpair.2.1.1
    (fun z => V P R z.2) (fun z => DY z.2) (J P R) hpoint
  calc
    _ = E P (fun z => DY z.2 * (V P R z.2)^2) := by
      congr 1
      funext z
      ring
    _ = J P R := pairCharge_cond_Y_inner hpair.2.1.1
      (fun x => (U P R x)^2) (fun y => (V P R y)^2)

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_abs_cube_cauchy {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (L : X × Y → ℝ) (hden : ∀ z, 0 < 2+L z) :
    (E P (fun z => |L z|^3))^2 ≤
      E P (fun z => (L z)^4/(2+L z))*E P (fun z => (L z)^2*(2+L z)) := by
  let F : X × Y → ℝ := fun z => (L z)^2/Real.sqrt (2+L z)
  let G : X × Y → ℝ := fun z => |L z| * Real.sqrt (2+L z)
  have hprod : (fun z => F z*G z) = (fun z => |L z|^3) := by
    funext z
    have hn := (Real.sqrt_pos.2 (hden z)).ne'
    dsimp [F,G]
    calc
      _ = (L z)^2 * |L z| := by field_simp [hn]
      _ = |L z|^3 := by rw [← sq_abs];ring
  have hF : (fun z => (F z)^2) = (fun z => (L z)^4/(2+L z)) := by
    funext z
    dsimp [F]
    rw [div_pow,Real.sq_sqrt (hden z).le]
    ring
  have hG : (fun z => (G z)^2) = (fun z => (L z)^2*(2+L z)) := by
    funext z
    dsimp [G]
    rw [mul_pow,sq_abs,Real.sq_sqrt (hden z).le]
  have h := pairCharge_E_cauchy hP F G
  rw [hprod,hF,hG] at h
  exact h

lemma pairCharge_absolute_cubic_moments {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    (E P (fun z => |U P R z.1|^3))^2+(E P (fun z => |V P R z.2|^3))^2 ≤
      4*s P R*J P R := by
  have hs := (contact_moments hpair).s_pos
  have hu := pairCharge_abs_cube_cauchy hpair.2.1.1 (fun z => U P R z.1)
    (fun z => pairCharge_U_den_pos hpair z.1)
  have hv := pairCharge_abs_cube_cauchy hpair.2.1.1 (fun z => V P R z.2)
    (fun z => pairCharge_V_den_pos hpair z.2)
  rw [(pairCharge_UV_weighted_energy hpair).1] at hu
  rw [(pairCharge_UV_weighted_energy hpair).2] at hv
  have hku := mul_le_mul_of_nonneg_right (pairCharge_KX_bound hpair) hs.le
  have hkv := mul_le_mul_of_nonneg_right (pairCharge_KY_bound hpair) hs.le
  linarith

/-- The rational lower cubic-error payment for actual contacts. -/
lemma pairCharge_cubic_error_payment {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    let DX : X → ℝ := fun x => (∑ y, P (x,y)*(V P R y)^2)/stoch_to_det.mX P x
    let DY : Y → ℝ := fun y => (∑ x, P (x,y)*(U P R x)^2)/stoch_to_det.mY P y
    (-(71/100:ℝ))*contactj P R*s P R ≤
      E P (fun z => U P R z.1*V P R z.2*DX z.1*DY z.2)/(2*(s P R)^2) := by
  let DX : X → ℝ := fun x => (∑ y, P (x,y)*(V P R y)^2)/stoch_to_det.mX P x
  let DY : Y → ℝ := fun y => (∑ x, P (x,y)*(U P R x)^2)/stoch_to_det.mY P y
  let MU := E P (fun z => |U P R z.1|^3)
  let MV := E P (fun z => |V P R z.2|^3)
  let A := E P (fun z => (DX z.1)^3)
  let B := E P (fun z => (DY z.2)^3)
  let D := E P (fun z => (DX z.1)^2*(DY z.2)^2)
  let Z := E P (fun z => U P R z.1*V P R z.2*DX z.1*DY z.2)
  have hP := hpair.2.1.1
  have hDX (x : X) : 0 ≤ DX x := by
    exact div_nonneg (Finset.sum_nonneg fun y _ => mul_nonneg (hP.nonneg _) (sq_nonneg _))
      ((stoch_to_det.isPMF_push hP).nonneg x)
  have hDY (y : Y) : 0 ≤ DY y := by
    exact div_nonneg (Finset.sum_nonneg fun x _ => mul_nonneg (hP.nonneg _) (sq_nonneg _))
      ((stoch_to_det.isPMF_push hP).nonneg y)
  have hMU : 0 ≤ MU := contact_E_nonneg hP _ (fun _ => pow_nonneg (abs_nonneg _) _)
  have hMV : 0 ≤ MV := contact_E_nonneg hP _ (fun _ => pow_nonneg (abs_nonneg _) _)
  have hA : 0 ≤ A := contact_E_nonneg hP _ (fun z => pow_nonneg (hDX z.1) _)
  have hB : 0 ≤ B := contact_E_nonneg hP _ (fun z => pow_nonneg (hDY z.2) _)
  have hD : 0 ≤ D := contact_E_nonneg hP _ (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hhc := pairCharge_feasible_marginal_norm hpair.1 hpair.2.1 DX DY hDX hDY
  change D ≤ A^((2:ℝ)/3)*B^((2:ℝ)/3) at hhc
  have hcs : Z^2 ≤ J P R*D := by
    have h := pairCharge_E_cauchy hP (fun z => U P R z.1*V P R z.2)
      (fun z => DX z.1*DY z.2)
    simpa only [Z,D,mul_assoc,mul_pow,J] using h
  have herr := pairCharge_cubic_error_scalar (contact_moments hpair).s_pos (pairCharge_J_nonneg hpair)
    (le_trans (contact_moments hpair).J_bound (contact_moments hpair).scalar_bound)
    hMU hMV hA hB hD (pairCharge_contact_DX_cube hpair) (pairCharge_contact_DY_cube hpair)
    (pairCharge_absolute_cubic_moments hpair) hhc hcs
  exact herr

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_E_covariance_raw {M : Law X Y} (hM : stoch_to_det.IsPMF M)
    (F G : X × Y → ℝ) :
    E M (fun z => (F z-E M F)*(G z-E M G)) =
      E M (fun z => F z*G z)-E M F*E M G := by
  simpa only [E,mul_assoc] using pairCharge_covariance_raw M F G hM.total

/-- KL payment for `F - λ u C`, with both endpoint means of `C` zero. -/
lemma pairCharge_residual_information {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F C : X × Y → ℝ) (hCP : E P C = 0) (hCQ : E (productLaw P) C = 0)
    (hg : E P F-E (productLaw P) F ≠ 0) (lam : ℝ) :
    let gap := E P F-E (productLaw P) F
    let D := E (productLaw P) (fun z => (F z-E (productLaw P) F)^2)/3 +
      E P (fun z => (F z-E P F)^2)/6+gap^2/12
    let N := (E (productLaw P) (fun z => F z*C z)+E P (fun z => F z*C z))/12
    let W := E (productLaw P) (fun z => (C z)^2)/30+E P (fun z => (C z)^2)/20
    0 < D-2*lam*N+lam^2*W ∧ gap^2/(4*(D-2*lam*N+lam^2*W)) ≤ I P := by
  let Q := productLaw P
  let B : X × Y → ℝ := fun z => -lam*C z
  let gap := E P F-E Q F
  let D := E Q (fun z => (F z-E Q F)^2)/3 +
    E P (fun z => (F z-E P F)^2)/6+gap^2/12
  let N := (E Q (fun z => F z*C z)+E P (fun z => F z*C z))/12
  let W := E Q (fun z => (C z)^2)/30+E P (fun z => (C z)^2)/20
  let residual := D-2*lam*N+lam^2*W
  change 0 < residual ∧ gap^2/(4*residual) ≤ I P
  have hQ := pairCharge_product_isPMF hP
  have hBP : E P B = 0 := by
    dsimp [B]
    rw [contact_q_E_scale,hCP]
    ring
  have hBQ : E Q B = 0 := by
    dsimp [B]
    rw [contact_q_E_scale,hCQ]
    ring
  have he : (∑ z, (P z-Q z)*F z) = gap := by
    dsimp [gap,E]
    simp only [sub_mul,Finset.sum_sub_distrib]
  have hB : (∑ z, (P z-Q z)*B z) = 0 := by
    simp only [sub_mul,Finset.sum_sub_distrib]
    change E P B-E Q B = 0
    rw [hBP,hBQ]
    ring
  have hcov (M : Law X Y) (hM : stoch_to_det.IsPMF M)
      (hMB : E M B = 0) :
      E M (fun z => (F z-E M F)*(B z-E M B)) = -lam*E M (fun z => F z*C z) := by
    rw [pairCharge_E_covariance_raw hM,hMB,mul_zero,sub_zero]
    have hid (z : X × Y) : F z*B z = -lam*(F z*C z) := by dsimp [B];ring
    simp only [hid,contact_q_E_scale]
  have hvar (M : Law X Y) (hMB : E M B = 0) :
      E M (fun z => (B z-E M B)^2) = lam^2*E M (fun z => (C z)^2) := by
    rw [hMB]
    have hid (z : X × Y) : (B z-0)^2 = lam^2*(C z)^2 := by dsimp [B];ring
    simp only [hid,contact_q_E_scale]
  have hpay (τ : ℝ) : τ*gap ≤ I P+τ^2*residual := by
    have hp := pairCharge_entropy_linear_field_affine P Q F B hP.nonneg hQ.nonneg
      (stoch_to_det.joint_absCont_product hP) hP.total hQ.total hB τ
    rw [he] at hp
    simp only [mul_assoc] at hp
    change τ*gap ≤ I P+τ^2*(
      E Q (fun z => (F z-E Q F)^2)/3+
      E P (fun z => (F z-E P F)^2)/6+gap^2/12+
      E Q (fun z => (F z-E Q F)*(B z-E Q B))/6+
      E P (fun z => (F z-E P F)*(B z-E P B))/6+
      E Q (fun z => (B z-E Q B)^2)/30+
      E P (fun z => (B z-E P B)^2)/20) at hp
    rw [hcov Q hQ hBQ,hcov P hP hBP,hvar Q hBQ,hvar P hBP] at hp
    have hid :
        E Q (fun z => (F z-E Q F)^2)/3+
        E P (fun z => (F z-E P F)^2)/6+gap^2/12+
        (-lam*E Q (fun z => F z*C z))/6+(-lam*E P (fun z => F z*C z))/6+
        (lam^2*E Q (fun z => (C z)^2))/30+(lam^2*E P (fun z => (C z)^2))/20 = residual := by
      dsimp [residual,D,N,W]
      ring
    rw [hid] at hp
    exact hp
  have hr : 0 < residual := pairCharge_payment_positive (I P) gap residual hpay hg
  refine ⟨hr,?_⟩
  apply (div_le_iff₀ (show 0 < 4*residual by positivity)).2
  have hp := pairCharge_payment_bound (I P) gap residual hpay
  nlinarith only [hp]

-- Actual averaged contact covariance.

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_E_HC_split (P : Law X Y) (u DX PX : X → ℝ) (v DY PY : Y → ℝ) (c : ℝ) :
    E P (fun z => u z.1 * v z.2 / c *
      (((DX z.1 + DY z.2) / c - 1) + ((PX z.1 + PY z.2) / c - 1))) =
      E P (fun z => u z.1 * v z.2 / c * ((DX z.1 + DY z.2) / c - 1)) +
      E P (fun z => u z.1 * v z.2 / c * ((PX z.1 + PY z.2) / c - 1)) := by
  calc
    _ = E P (fun z =>
        u z.1 * v z.2 / c * ((DX z.1 + DY z.2) / c - 1) +
        u z.1 * v z.2 / c * ((PX z.1 + PY z.2) / c - 1)) := by
      congr 1
      funext z
      ring
    _ = _ := contact_E_add _ _ _

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_E_FC_split (P : Law X Y) (H L C : X × Y → ℝ) :
    E P (fun z => (H z + L z / 3) * C z) =
      E P (fun z => H z * C z) + E P (fun z => L z * C z) / 3 := by
  calc
    _ = E P (fun z => H z * C z + (L z * C z) / 3) := by
      congr 1
      funext z
      ring
    _ = _ := by rw [contact_E_add, pairCharge_E_div]

/-- The actual averaged HC covariance, with the four defect fields specified
by their conditional expectation equations. -/
lemma pairCharge_HC_average_identity {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R)
    (DX DXp PX PXp : X → ℝ) (DY DYp PY PYp : Y → ℝ)
    (hDX : ∀ x, DX x = (∑ y, P (x,y) * (V P R y)^2) / stoch_to_det.mX P x)
    (hDY : ∀ y, DY y = (∑ x, P (x,y) * (U P R x)^2) / stoch_to_det.mY P y)
    (hPX : ∀ x, PX x = (∑ y, P (x,y) * DY y) / stoch_to_det.mX P x)
    (hPY : ∀ y, PY y = (∑ x, P (x,y) * DX x) / stoch_to_det.mY P y)
    (hDXp : ∀ x, DXp x = (∑ y, R (x,y) * (V R P y)^2) / stoch_to_det.mX R x)
    (hDYp : ∀ y, DYp y = (∑ x, R (x,y) * (U R P x)^2) / stoch_to_det.mY R y)
    (hPXp : ∀ x, PXp x = (∑ y, R (x,y) * DYp y) / stoch_to_det.mX R x)
    (hPYp : ∀ y, PYp y = (∑ x, R (x,y) * DXp x) / stoch_to_det.mY R y) :
    let C : X × Y → ℝ := fun z =>
      ((DX z.1 + DY z.2) / s P R - 1) + ((PX z.1 + PY z.2) / s P R - 1)
    let Cp : X × Y → ℝ := fun z =>
      ((DXp z.1 + DYp z.2) / s R P - 1) + ((PXp z.1 + PYp z.2) / s R P - 1)
    let NH := ((E (productLaw P) (fun z => U P R z.1 * V P R z.2 / s P R * C z) +
      E P (fun z => U P R z.1 * V P R z.2 / s P R * C z)) / 12 +
      (E (productLaw R) (fun z => U R P z.1 * V R P z.2 / s R P * Cp z) +
        E R (fun z => U R P z.1 * V R P z.2 / s R P * Cp z)) / 12) / 2
    let x := ((E P (fun z => (DX z.1 - (2 * B0 P R - A0 P R))^2) +
      E P (fun z => (DY z.2 - (2 * A0 P R - B0 P R))^2)) / (s P R)^2 +
      (E R (fun z => (DXp z.1 - (2 * B0 R P - A0 R P))^2) +
        E R (fun z => (DYp z.2 - (2 * A0 R P - B0 R P))^2)) / (s R P)^2) / 2
    let M := (A0 P R * E P (fun z => (DX z.1)^2) +
      B0 P R * E P (fun z => (DY z.2)^2) +
      B0 P R * E R (fun z => (DXp z.1)^2) +
      A0 P R * E R (fun z => (DYp z.2)^2)) / (2 * (s P R)^2)
    let Z := E P (fun z => U P R z.1 * V P R z.2 * DX z.1 * DY z.2)
    12 * NH = contactj P R - (1/4 : ℝ) + x / 2 +
      12 * ((1/4 : ℝ) - A0 P R * B0 P R / (s P R)^2) +
      s P R * (contactj P R / 4 - 2 * (A0 P R * B0 P R / (s P R)^2)) +
      M / 2 + Z / (2 * (s P R)^2) := by
  let C : X × Y → ℝ := fun z =>
    ((DX z.1 + DY z.2) / s P R - 1) + ((PX z.1 + PY z.2) / s P R - 1)
  let Cp : X × Y → ℝ := fun z =>
    ((DXp z.1 + DYp z.2) / s R P - 1) + ((PXp z.1 + PYp z.2) / s R P - 1)
  let NH := ((E (productLaw P) (fun z => U P R z.1 * V P R z.2 / s P R * C z) +
    E P (fun z => U P R z.1 * V P R z.2 / s P R * C z)) / 12 +
    (E (productLaw R) (fun z => U R P z.1 * V R P z.2 / s R P * Cp z) +
      E R (fun z => U R P z.1 * V R P z.2 / s R P * Cp z)) / 12) / 2
  let x := ((E P (fun z => (DX z.1 - (2 * B0 P R - A0 P R))^2) +
    E P (fun z => (DY z.2 - (2 * A0 P R - B0 P R))^2)) / (s P R)^2 +
    (E R (fun z => (DXp z.1 - (2 * B0 R P - A0 R P))^2) +
      E R (fun z => (DYp z.2 - (2 * A0 R P - B0 R P))^2)) / (s R P)^2) / 2
  let HX := E P (fun z => (DX z.1)^2)
  let HY := E P (fun z => (DY z.2)^2)
  let HXp := E R (fun z => (DXp z.1)^2)
  let HYp := E R (fun z => (DYp z.2)^2)
  let M := (A0 P R * HX + B0 P R * HY + B0 P R * HXp + A0 P R * HYp) /
    (2 * (s P R)^2)
  let Z := E P (fun z => U P R z.1 * V P R z.2 * DX z.1 * DY z.2)
  let lam := E P (fun z => U P R z.1 * (DX z.1)^2) +
    E P (fun z => V P R z.2 * (DY z.2)^2)
  let lamp := E R (fun z => U R P z.1 * (DXp z.1)^2) +
    E R (fun z => V R P z.2 * (DYp z.2)^2)
  let om := E P (fun z => U P R z.1 * DX z.1 * PX z.1) +
    E P (fun z => V P R z.2 * DY z.2 * PY z.2)
  let omp := E R (fun z => U R P z.1 * DXp z.1 * PXp z.1) +
    E R (fun z => V R P z.2 * DYp z.2 * PYp z.2)
  change 12 * NH = contactj P R - (1/4 : ℝ) + x / 2 +
    12 * ((1/4 : ℝ) - A0 P R * B0 P R / (s P R)^2) +
    s P R * (contactj P R / 4 - 2 * (A0 P R * B0 P R / (s P R)^2)) +
    M / 2 + Z / (2 * (s P R)^2)
  have hrev := pairCharge_pair_reverse hpair
  have hsrev := pairCharge_s_reverse hpair
  have harev := (pairCharge_mean_losses_reverse hpair).1
  have hbrev := (pairCharge_mean_losses_reverse hpair).2
  have hJrev := pairCharge_J_reverse hpair
  have hDXscale : ∀ x ∈ XSupport S, f P R x * DXp x = DX x := by
    intro q hq
    rw [hDXp, hDX]
    exact pairCharge_cond_defect_X_reverse hpair hq
  have hDYscale : ∀ y ∈ YSupport S, g P R y * DYp y = DY y := by
    intro q hq
    rw [hDYp, hDY]
    exact pairCharge_cond_defect_Y_reverse hpair hq
  have hlam : lamp = -lam := by
    dsimp [lamp, lam]
    rw [pairCharge_lambda_X_reverse hpair DX DXp hDXscale,
      pairCharge_lambda_Y_reverse hpair DY DYp hDYscale]
    ring
  have hom : omp = -om - 2 * Z := by
    have hX := pairCharge_omega_X_reverse hpair DX DXp DY DYp hDXscale hDYscale
    have hY := pairCharge_omega_Y_reverse hpair DX DXp DY DYp hDXscale hDYscale
    simp_rw [← hPX, ← hPXp] at hX
    simp_rw [← hPY, ← hPYp] at hY
    dsimp [omp, om, Z]
    linarith only [hX, hY]
  have hnormP := pairCharge_defects_second_moment_identity hpair DX DY hDX hDY
  have hnormR := pairCharge_defects_second_moment_identity hrev DXp DYp hDXp hDYp
  rw [hsrev, harev, hbrev] at hnormR
  have hH : (HX + HY + HXp + HYp) / (2 * (s P R)^2) =
      5 - 18 * (A0 P R * B0 P R / (s P R)^2) + x := by
    dsimp [HX, HY, HXp, HYp, x]
    rw [hsrev, harev, hbrev]
    have hnR : (E R (fun z => (DXp z.1)^2) + E R (fun z => (DYp z.2)^2)) /
        (s P R)^2 = 5 - 18 * (A0 P R * B0 P R / (s P R)^2) +
        (E R (fun z => (DXp z.1 - (2 * A0 P R - B0 P R))^2) +
          E R (fun z => (DYp z.2 - (2 * B0 P R - A0 P R))^2)) / (s P R)^2 := by
      simpa only [mul_comm] using hnormR
    calc
      _ = ((E P (fun z => (DX z.1)^2) + E P (fun z => (DY z.2)^2)) / (s P R)^2 +
          (E R (fun z => (DXp z.1)^2) + E R (fun z => (DYp z.2)^2)) / (s P R)^2) / 2 := by ring
      _ = _ := by rw [hnormP, hnR]; ring
  have hHB0Q := pairCharge_HB0_product hpair DX DY hDX hDY
  have hHB0P := pairCharge_HB0_joint hpair DX DY hDX hDY
  have hHB1Q := pairCharge_HB1_product hpair DX DY PX PY hDX hDY hPX hPY
  have hHB1P := pairCharge_HB1_joint hpair DX DY PX PY hDX hDY hPX hPY
  have hHB0Qr := pairCharge_HB0_product hrev DXp DYp hDXp hDYp
  have hHB0R := pairCharge_HB0_joint hrev DXp DYp hDXp hDYp
  have hHB1Qr := pairCharge_HB1_product hrev DXp DYp PXp PYp hDXp hDYp hPXp hPYp
  have hHB1R := pairCharge_HB1_joint hrev DXp DYp PXp PYp hDXp hDYp hPXp hPYp
  have huvP : E P (fun z => U P R z.1 * V P R z.2) = (s P R + J P R) / 4 := by
    linarith only [(contact_moments hpair).quartic]
  have huvR : E R (fun z => U R P z.1 * V R P z.2) = (s P R + J P R) / 4 := by
    rw [← hsrev, ← hJrev]
    linarith only [(contact_moments hrev).quartic]
  rw [hsrev, hJrev, huvR] at hHB0R
  rw [hsrev, huvR] at hHB1R
  rw [hsrev, harev, hbrev, hJrev] at hHB0Qr hHB1Qr
  rw [huvP] at hHB0P hHB1P
  have hscalar := pairCharge_HC_endpoint_sum (s P R) (A0 P R) (B0 P R) (J P R)
    ((s P R + J P R) / 4) HX HY HXp HYp lam om lamp omp Z
    (contactj P R) (A0 P R * B0 P R / (s P R)^2) x M
    (contact_moments hpair).s_pos.ne' rfl rfl rfl rfl hlam hom hH rfl
  calc
    12 * NH =
        ((E (productLaw P) (fun z => U P R z.1 * V P R z.2 / s P R *
          ((DX z.1 + DY z.2) / s P R - 1)) +
        E P (fun z => U P R z.1 * V P R z.2 / s P R *
          ((DX z.1 + DY z.2) / s P R - 1)) +
        E (productLaw P) (fun z => U P R z.1 * V P R z.2 / s P R *
          ((PX z.1 + PY z.2) / s P R - 1)) +
        E P (fun z => U P R z.1 * V P R z.2 / s P R *
          ((PX z.1 + PY z.2) / s P R - 1))) +
        (E (productLaw R) (fun z => U R P z.1 * V R P z.2 / s R P *
          ((DXp z.1 + DYp z.2) / s R P - 1)) +
        E R (fun z => U R P z.1 * V R P z.2 / s R P *
          ((DXp z.1 + DYp z.2) / s R P - 1)) +
        E (productLaw R) (fun z => U R P z.1 * V R P z.2 / s R P *
          ((PXp z.1 + PYp z.2) / s R P - 1)) +
        E R (fun z => U R P z.1 * V R P z.2 / s R P *
          ((PXp z.1 + PYp z.2) / s R P - 1)))) / 2 := by
      dsimp [NH, C, Cp]
      rw [pairCharge_E_HC_split, pairCharge_E_HC_split, pairCharge_E_HC_split, pairCharge_E_HC_split]
      ring
    _ = _ := by
      rw [hsrev]
      rw [hHB0Q, hHB0P, hHB1Q, hHB1P, hHB0Qr, hHB0R, hHB1Qr, hHB1R]
      simpa only [add_assoc, mul_comm, HX, HY, HXp, HYp, lam, om, lamp, omp] using hscalar

/-- The covariance payment for the actual forward and reverse conditional features. -/
lemma pairCharge_actual_covariance_payment {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R)
    (hshi : s P R ≤ (1/3 : ℝ)) (hjlo : (5/16 : ℝ) ≤ contactj P R)
    (hjhi : contactj P R < (1/2 : ℝ)) :
    let DX : X → ℝ := fun x => (∑ y, P (x,y) * (V P R y)^2) / stoch_to_det.mX P x
    let DY : Y → ℝ := fun y => (∑ x, P (x,y) * (U P R x)^2) / stoch_to_det.mY P y
    let DXp : X → ℝ := fun x => (∑ y, R (x,y) * (V R P y)^2) / stoch_to_det.mX R x
    let DYp : Y → ℝ := fun y => (∑ x, R (x,y) * (U R P x)^2) / stoch_to_det.mY R y
    let PX : X → ℝ := fun x => (∑ y, P (x,y) * DY y) / stoch_to_det.mX P x
    let PY : Y → ℝ := fun y => (∑ x, P (x,y) * DX x) / stoch_to_det.mY P y
    let PXp : X → ℝ := fun x => (∑ y, R (x,y) * DYp y) / stoch_to_det.mX R x
    let PYp : Y → ℝ := fun y => (∑ x, R (x,y) * DXp x) / stoch_to_det.mY R y
    let C : X × Y → ℝ := fun z =>
      ((DX z.1 + DY z.2) / s P R - 1) + ((PX z.1 + PY z.2) / s P R - 1)
    let Cp : X × Y → ℝ := fun z =>
      ((DXp z.1 + DYp z.2) / s R P - 1) + ((PXp z.1 + PYp z.2) / s R P - 1)
    let F : X × Y → ℝ := fun z => U P R z.1 * V P R z.2 / s P R +
      (U P R z.1 + V P R z.2 + s P R) / 3
    let Fp : X × Y → ℝ := fun z => U R P z.1 * V R P z.2 / s R P +
      (U R P z.1 + V R P z.2 + s R P) / 3
    let N := ((E (productLaw P) (fun z => F z * C z) + E P (fun z => F z * C z)) / 12 +
      (E (productLaw R) (fun z => Fp z * Cp z) + E R (fun z => Fp z * Cp z)) / 12) / 2
    let x := ((E P (fun z => (DX z.1 - (2 * B0 P R - A0 P R))^2) +
      E P (fun z => (DY z.2 - (2 * A0 P R - B0 P R))^2)) / (s P R)^2 +
      (E R (fun z => (DXp z.1 - (2 * B0 R P - A0 R P))^2) +
        E R (fun z => (DYp z.2 - (2 * A0 R P - B0 R P))^2)) / (s R P)^2) / 2
    ((contactj P R - (1/4 : ℝ) +
      s P R * ((1/4 : ℝ) - 171 * contactj P R / 100) - (s P R)^2 / 160) +
      ((1/2 : ℝ) - 5 * s P R / 12) * x) / 12 ≤ N := by
  let DX : X → ℝ := fun x => (∑ y, P (x,y) * (V P R y)^2) / stoch_to_det.mX P x
  let DY : Y → ℝ := fun y => (∑ x, P (x,y) * (U P R x)^2) / stoch_to_det.mY P y
  let DXp : X → ℝ := fun x => (∑ y, R (x,y) * (V R P y)^2) / stoch_to_det.mX R x
  let DYp : Y → ℝ := fun y => (∑ x, R (x,y) * (U R P x)^2) / stoch_to_det.mY R y
  let PX : X → ℝ := fun x => (∑ y, P (x,y) * DY y) / stoch_to_det.mX P x
  let PY : Y → ℝ := fun y => (∑ x, P (x,y) * DX x) / stoch_to_det.mY P y
  let PXp : X → ℝ := fun x => (∑ y, R (x,y) * DYp y) / stoch_to_det.mX R x
  let PYp : Y → ℝ := fun y => (∑ x, R (x,y) * DXp x) / stoch_to_det.mY R y
  let C : X × Y → ℝ := fun z =>
    ((DX z.1 + DY z.2) / s P R - 1) + ((PX z.1 + PY z.2) / s P R - 1)
  let Cp : X × Y → ℝ := fun z =>
    ((DXp z.1 + DYp z.2) / s R P - 1) + ((PXp z.1 + PYp z.2) / s R P - 1)
  let H : X × Y → ℝ := fun z => U P R z.1 * V P R z.2 / s P R
  let Hp : X × Y → ℝ := fun z => U R P z.1 * V R P z.2 / s R P
  let L : X × Y → ℝ := fun z => U P R z.1 + V P R z.2 + s P R
  let Lp : X × Y → ℝ := fun z => U R P z.1 + V R P z.2 + s R P
  let F : X × Y → ℝ := fun z => H z + L z / 3
  let Fp : X × Y → ℝ := fun z => Hp z + Lp z / 3
  let N := ((E (productLaw P) (fun z => F z * C z) + E P (fun z => F z * C z)) / 12 +
    (E (productLaw R) (fun z => Fp z * Cp z) + E R (fun z => Fp z * Cp z)) / 12) / 2
  let NH := ((E (productLaw P) (fun z => H z * C z) + E P (fun z => H z * C z)) / 12 +
    (E (productLaw R) (fun z => Hp z * Cp z) + E R (fun z => Hp z * Cp z)) / 12) / 2
  let NL := ((E (productLaw P) (fun z => L z * C z) + E P (fun z => L z * C z)) / 12 +
    (E (productLaw R) (fun z => Lp z * Cp z) + E R (fun z => Lp z * Cp z)) / 12) / 2
  let x := ((E P (fun z => (DX z.1 - (2 * B0 P R - A0 P R))^2) +
    E P (fun z => (DY z.2 - (2 * A0 P R - B0 P R))^2)) / (s P R)^2 +
    (E R (fun z => (DXp z.1 - (2 * B0 R P - A0 R P))^2) +
      E R (fun z => (DYp z.2 - (2 * A0 R P - B0 R P))^2)) / (s R P)^2) / 2
  let z := (A0 P R - B0 P R) / s P R
  let v := A0 P R * B0 P R / (s P R)^2
  let t := (1/2 : ℝ) - contactj P R
  let t0 := 6 * v - 1 - contactj P R
  let HX := E P (fun z => (DX z.1)^2) / (s P R)^2
  let HY := E P (fun z => (DY z.2)^2) / (s P R)^2
  let HXp := E R (fun z => (DXp z.1)^2) / (s P R)^2
  let HYp := E R (fun z => (DYp z.2)^2) / (s P R)^2
  let hbar := (HX + HY + HXp + HYp) / 2
  let M := (A0 P R * HX + B0 P R * HY + B0 P R * HXp + A0 P R * HYp) / 2
  let Z := E P (fun z => U P R z.1 * V P R z.2 * DX z.1 * DY z.2)
  change ((contactj P R - (1/4 : ℝ) +
    s P R * ((1/4 : ℝ) - 171 * contactj P R / 100) - (s P R)^2 / 160) +
    ((1/2 : ℝ) - 5 * s P R / 12) * x) / 12 ≤ N
  have hs := (contact_moments hpair).s_pos
  have hsum : s P R = A0 P R + B0 P R := rfl
  have hv : v = (1 - z^2) / 4 := by
    dsimp [v, z]
    field_simp [hs.ne']
    rw [hsum]
    ring
  have ha : A0 P R = s P R * (1 + z) / 2 := by
    dsimp [z]
    field_simp [hs.ne']
    rw [hsum]
    ring
  have hb : B0 P R = s P R * (1 - z) / 2 := by
    dsimp [z]
    field_simp [hs.ne']
    rw [hsum]
    ring
  have ht0 : t0 = t - 3 * z^2 / 2 := by
    dsimp [t0, t]
    rw [hv]
    ring
  have hrev := pairCharge_pair_reverse hpair
  have hsrev := pairCharge_s_reverse hpair
  have harev := (pairCharge_mean_losses_reverse hpair).1
  have hbrev := (pairCharge_mean_losses_reverse hpair).2
  have hnormP := pairCharge_defects_second_moment_identity hpair DX DY (fun _ => rfl) (fun _ => rfl)
  have hnormR := pairCharge_defects_second_moment_identity hrev DXp DYp (fun _ => rfl) (fun _ => rfl)
  rw [hsrev, harev, hbrev] at hnormR
  have hbarScalar : hbar = (1/2 : ℝ) + x + 9 * z^2 / 2 := by
    have hnorm : hbar = 5 - 18 * v + x := by
      dsimp [hbar, HX, HY, HXp, HYp, v, x]
      rw [hsrev, harev, hbrev]
      have hnR : (E R (fun z => (DXp z.1)^2) + E R (fun z => (DYp z.2)^2)) /
          (s P R)^2 = 5 - 18 * (A0 P R * B0 P R / (s P R)^2) +
          (E R (fun z => (DXp z.1 - (2 * A0 P R - B0 P R))^2) +
            E R (fun z => (DYp z.2 - (2 * B0 P R - A0 P R))^2)) / (s P R)^2 := by
        simpa only [mul_comm] using hnormR
      calc
        _ = ((E P (fun z => (DX z.1)^2) + E P (fun z => (DY z.2)^2)) / (s P R)^2 +
            (E R (fun z => (DXp z.1)^2) + E R (fun z => (DYp z.2)^2)) / (s P R)^2) / 2 := by ring
        _ = _ := by rw [hnormP, hnR]; ring
    rw [hnorm, hv]
    ring
  have hHC := pairCharge_HC_average_identity hpair DX DXp PX PXp DY DYp PY PYp
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  change 12 * NH = contactj P R - (1/4 : ℝ) + x / 2 +
    12 * ((1/4 : ℝ) - v) + s P R * (contactj P R / 4 - 2 * v) +
    (A0 P R * E P (fun z => (DX z.1)^2) + B0 P R * E P (fun z => (DY z.2)^2) +
      B0 P R * E R (fun z => (DXp z.1)^2) + A0 P R * E R (fun z => (DYp z.2)^2)) /
      (2 * (s P R)^2) / 2 + Z / (2 * (s P R)^2) at hHC
  have hM : (A0 P R * E P (fun z => (DX z.1)^2) + B0 P R * E P (fun z => (DY z.2)^2) +
      B0 P R * E R (fun z => (DXp z.1)^2) + A0 P R * E R (fun z => (DYp z.2)^2)) /
      (2 * (s P R)^2) = M := by
    dsimp [M, HX, HY, HXp, HYp]
    ring
  rw [hM] at hHC
  have hrawLC := pairCharge_raw_LC_average_bound hpair
  change 0 < t0 ∧ 0 ≤ x ∧ x ≤ 2 * t0 ∧
    s P R / 48 * (15 * t0 - 8 * x + x^2 / t0) ≤ NL at hrawLC
  obtain ⟨ht0pos, hxlo, hxhi, hNL⟩ := hrawLC
  have hZ := pairCharge_cubic_error_payment hpair
  change -(71/100 : ℝ) * contactj P R * s P R ≤ Z / (2 * (s P R)^2) at hZ
  have hHX : 0 ≤ HX := div_nonneg
    (contact_E_nonneg hpair.2.1.1 _ (fun _ => sq_nonneg _)) (sq_nonneg _)
  have hHY : 0 ≤ HY := div_nonneg
    (contact_E_nonneg hpair.2.1.1 _ (fun _ => sq_nonneg _)) (sq_nonneg _)
  have hHXp : 0 ≤ HXp := div_nonneg
    (contact_E_nonneg hpair.2.2.1.1 _ (fun _ => sq_nonneg _)) (sq_nonneg _)
  have hHYp : 0 ≤ HYp := div_nonneg
    (contact_E_nonneg hpair.2.2.1.1 _ (fun _ => sq_nonneg _)) (sq_nonneg _)
  have hpaid := pairCharge_fixed_covariance (s P R) (contactj P R) z v t t0 x
    HX HY HXp HYp (A0 P R) (B0 P R) hbar M Z NH NL
    hs hshi hjlo hjhi hv rfl ht0 ht0pos hxlo hxhi hHX hHY hHXp hHYp
    ha hb rfl hbarScalar rfl hHC hNL hZ
  have hN : N = NH + NL / 3 := by
    dsimp [N, NH, NL, F, Fp]
    rw [pairCharge_E_FC_split, pairCharge_E_FC_split, pairCharge_E_FC_split, pairCharge_E_FC_split]
    ring
  rw [hN]
  linarith only [hpaid.2.2]

/-- The fixed-coefficient comparison instantiated at the correction `1/3`. -/
lemma pairCharge_high_fixed_data {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (hs : s P R ≤ (1/3:ℝ)) :
    let t := s P R
    let jj := contactj P R
    let F : X × Y → ℝ := fun z => U P R z.1*V P R z.2/t+
      (U P R z.1+V P R z.2+t)/3
    let gap := E P F-E (productLaw P) F
    let D := E (productLaw P) (fun z => (F z-E (productLaw P) F)^2)/3+
      E P (fun z => (F z-E P F)^2)/6+gap^2/12
    (1-t+t*jj)/4 ≤ gap ∧
      192*D ≤ 15+32*jj-((50/9:ℝ)+70*jj/3)*t+
        ((5/9:ℝ)+46*jj/9-jj^2)*t^2 := by
  let t := s P R
  let jj := contactj P R
  let vv := A0 P R*B0 P R/t^2
  let hh := (1+t*jj)/4
  let F : X × Y → ℝ := fun z => U P R z.1*V P R z.2/t+
    (U P R z.1+V P R z.2+t)/3
  let gap := E P F-E (productLaw P) F
  let D := E (productLaw P) (fun z => (F z-E (productLaw P) F)^2)/3+
    E P (fun z => (F z-E P F)^2)/6+gap^2/12
  let rawD := (9*vv-2)/3+jj/6-t^2*vv^2/4-t*vv*hh/6-hh^2/12
  let CL := t*((3/8:ℝ)-2*vv-jj/6+t*(vv/3+jj/24))
  let EL := t*((7/12:ℝ)-t/2+2*t*vv/3+t*jj/12)
  have hs0 : 0 < t := (contact_moments hpair).s_pos
  have hjs := pairCharge_contactj_bounds hpair
  have hvs := pairCharge_v_bounds hpair
  have hstats := pairCharge_fixed_coefficient_data hpair (1/3:ℝ)
  have hF : (fun z : X × Y => U P R z.1*V P R z.2/t+
      (1/3:ℝ)*(U P R z.1+V P R z.2+t)) = F := by
    funext z
    dsimp [F]
    ring
  change E P (fun z => U P R z.1*V P R z.2/t+
      (1/3:ℝ)*(U P R z.1+V P R z.2+t))-
    E (productLaw P) (fun z => U P R z.1*V P R z.2/t+
      (1/3:ℝ)*(U P R z.1+V P R z.2+t)) = hh-t*vv ∧ _ at hstats
  rw [hF] at hstats
  change gap = hh-t*vv ∧ _ at hstats
  have hD : D = rawD+2*CL/3+EL/9 := by
    convert hstats.2 using 1
    dsimp only [rawD,CL,EL,t,jj,vv,hh]
    ring
  change (1-t+t*jj)/4 ≤ gap ∧
    192*D ≤ 15+32*jj-((50/9:ℝ)+70*jj/3)*t+((5/9:ℝ)+46*jj/9-jj^2)*t^2
  constructor
  · rw [hstats.1]
    exact pairCharge_fixed_floor_gap t jj vv hh hs0.le hvs.2 rfl
  · rw [hD]
    exact pairCharge_fixed_third_variance t jj vv hh rawD CL EL hs hjs.2 hvs.2 rfl rfl rfl rfl

/-- The reciprocal mean step with separate positive mean gaps. -/
lemma pairCharge_average_KL_separate (Ip Im Vp Vm gp gm y : ℝ)
    (hVp : 0 < Vp) (hVm : 0 < Vm) (hy : 0 ≤ y)
    (hgp : y/4 ≤ gp) (hgm : y/4 ≤ gm)
    (hIp : gp^2/(4*Vp) ≤ Ip) (hIm : gm^2/(4*Vm) ≤ Im) :
    y^2/(64*((Vp+Vm)/2)) ≤ (Ip+Im)/2 := by
  have hpSq : (y/4)^2 ≤ gp^2 := by
    have h := mul_nonneg (show 0 ≤ gp-y/4 by linarith)
      (show 0 ≤ gp+y/4 by linarith)
    nlinarith only [h]
  have hmSq : (y/4)^2 ≤ gm^2 := by
    have h := mul_nonneg (show 0 ≤ gm-y/4 by linarith)
      (show 0 ≤ gm+y/4 by linarith)
    nlinarith only [h]
  have hip : (y/4)^2/(4*Vp) ≤ Ip :=
    le_trans (div_le_div_of_nonneg_right hpSq (by positivity)) hIp
  have him : (y/4)^2/(4*Vm) ≤ Im :=
    le_trans (div_le_div_of_nonneg_right hmSq (by positivity)) hIm
  exact pairCharge_average_KL Ip Im Vp Vm (y/4) y hVp hVm hy le_rfl hip him

/-- Scalar final assembly at the fixed common coefficient. -/
lemma pairCharge_high_charge_scalar
    (ss jj Ip Im Dp Dm Np Nm Wp Wm gp gm xx cost : ℝ)
    (hs : 0 < ss) (hshi : ss ≤ (1/3:ℝ))
    (hjlo : (5/16:ℝ) ≤ jj) (hjhi : jj ≤ (1/2:ℝ))
    (hDp : 192*Dp ≤ 15+32*jj-((50/9:ℝ)+70*jj/3)*ss+
      ((5/9:ℝ)+46*jj/9-jj^2)*ss^2)
    (hDm : 192*Dm ≤ 15+32*jj-((50/9:ℝ)+70*jj/3)*ss+
      ((5/9:ℝ)+46*jj/9-jj^2)*ss^2)
    (hN : ((jj-(1/4:ℝ)+ss*((1/4:ℝ)-171*jj/100)-ss^2/160)+
      ((1/2:ℝ)-5*ss/12)*xx)/12 ≤ (Np+Nm)/2)
    (hW : (Wp+Wm)/2 ≤ ((17/10:ℝ)*((1/2:ℝ)-jj)+(23/4:ℝ)*xx)/60)
    (hgp : (1-ss+ss*jj)/4 ≤ gp) (hgm : (1-ss+ss*jj)/4 ≤ gm)
    (hrp : 0 < Dp-2*(40*((1/2:ℝ)-5*ss/12)/23)*Np+
      (40*((1/2:ℝ)-5*ss/12)/23)^2*Wp)
    (hrm : 0 < Dm-2*(40*((1/2:ℝ)-5*ss/12)/23)*Nm+
      (40*((1/2:ℝ)-5*ss/12)/23)^2*Wm)
    (hIp : gp^2/(4*(Dp-2*(40*((1/2:ℝ)-5*ss/12)/23)*Np+
      (40*((1/2:ℝ)-5*ss/12)/23)^2*Wp)) ≤ Ip)
    (hIm : gm^2/(4*(Dm-2*(40*((1/2:ℝ)-5*ss/12)/23)*Nm+
      (40*((1/2:ℝ)-5*ss/12)/23)^2*Wm)) ≤ Im)
    (hcost : 9*ss/8+57*ss^2/256+ss^3/16 ≤ cost) :
    (3/25:ℝ) ≤ (Ip+Im)/2+(1/10:ℝ)*cost := by
  let y := 1-ss+ss*jj
  let U0 := 15+32*jj-((50/9:ℝ)+70*jj/3)*ss+
    ((5/9:ℝ)+46*jj/9-jj^2)*ss^2
  let A := jj-(1/4:ℝ)+ss*((1/4:ℝ)-171*jj/100)-ss^2/160
  let B := (1/2:ℝ)-5*ss/12
  let d := (17/10:ℝ)*((1/2:ℝ)-jj)
  let lam := 40*B/23
  let Vp := Dp-2*lam*Np+lam^2*Wp
  let Vm := Dm-2*lam*Nm+lam^2*Wm
  let residual := (Vp+Vm)/2
  let Dstar := U0/192-(5/3:ℝ)*B*((23/4:ℝ)*A-B*d)/(23/4:ℝ)^2
  let g0 := (3/25:ℝ)-9*ss/80-57*ss^2/2560-ss^3/160
  have hB : 0 ≤ B := by dsimp [B];linarith
  have hD : (Dp+Dm)/2 ≤ U0/192 := by
    change 192*Dp ≤ U0 at hDp
    change 192*Dm ≤ U0 at hDm
    linarith only [hDp,hDm]
  have hu := pairCharge_projection_residual_upper ((Dp+Dm)/2) ((Np+Nm)/2) ((Wp+Wm)/2)
    U0 A B d xx hB hD hN hW
  have hresD : residual ≤ Dstar := by
    have hid : residual = (Dp+Dm)/2-2*lam*((Np+Nm)/2)+lam^2*((Wp+Wm)/2) := by
      dsimp [residual,Vp,Vm]
      ring
    rw [hid]
    exact hu
  have hres : 0 < residual := by
    change 0 < Vp at hrp
    change 0 < Vm at hrm
    dsimp [residual]
    linarith only [hrp,hrm]
  have hy : 0 ≤ y := by
    dsimp [y]
    have hproduct : 0 ≤ ss*jj := mul_nonneg hs.le (by linarith)
    linarith only [hshi,hproduct]
  have hibar := pairCharge_average_KL_separate Ip Im Vp Vm gp gm y hrp hrm hy hgp hgm hIp hIm
  have hproj := pairCharge_projection_information ((Ip+Im)/2) y residual Dstar hres hresD hibar
  have hcert := pairCharge_scalar_high_payment ss jj hs.le hshi hjlo hjhi
  have hDstar : 0 < Dstar := hproj.1
  have hden : 0 < 192*Dstar := by positivity
  have hdenid : 192*Dstar = U0-(5120/529:ℝ)*B*((23/4:ℝ)*A-B*d) := by
    dsimp [Dstar]
    ring
  have hpoly : 0 < 3*y^2-g0*(192*Dstar) := by
    rw [hdenid]
    change (1/100:ℝ)+49*ss^2/12800 < 3*y^2-g0*(U0-(5120/529:ℝ)*B*((23/4:ℝ)*A-B*d)) at hcert
    have hsl : 0 ≤ (1/100:ℝ)+49*ss^2/12800 := by positivity
    linarith only [hcert,hsl]
  have hgf : g0 ≤ 3*y^2/(192*Dstar) := by
    apply (le_div_iff₀ hden).2
    linarith only [hpoly]
  have hinfo := le_trans hgf hproj.2
  dsimp [g0] at hinfo
  linarith only [hinfo,hcost]

/-- Region 1: the complete small-`s`, high-`j` contact assembly. -/
lemma pairCharge_region1_charge {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R)
    (hs : s P R ≤ (1/3:ℝ)) (hj : (5/16:ℝ) ≤ contactj P R) :
    (3/25:ℝ) ≤ (I P+I R)/2+(1/10:ℝ)*Psi (s P R) := by
  let DX (A B : Law X Y) : X → ℝ := fun x =>
    (∑ y, A (x,y)*(V A B y)^2)/stoch_to_det.mX A x
  let DY (A B : Law X Y) : Y → ℝ := fun y =>
    (∑ x, A (x,y)*(U A B x)^2)/stoch_to_det.mY A y
  let C (A B : Law X Y) : X × Y → ℝ := fun z =>
    ((DX A B z.1+DY A B z.2)/s A B-1)+
    (((∑ y, A (z.1,y)*DY A B y)/stoch_to_det.mX A z.1+
      (∑ x, A (x,z.2)*DX A B x)/stoch_to_det.mY A z.2)/s A B-1)
  let F (A B : Law X Y) : X × Y → ℝ := fun z =>
    U A B z.1*V A B z.2/s A B+(U A B z.1+V A B z.2+s A B)/3
  let gap (A B : Law X Y) := E A (F A B)-E (productLaw A) (F A B)
  let D (A B : Law X Y) := E (productLaw A) (fun z => (F A B z-E (productLaw A) (F A B))^2)/3+
    E A (fun z => (F A B z-E A (F A B))^2)/6+(gap A B)^2/12
  let N (A B : Law X Y) :=
    (E (productLaw A) (fun z => F A B z*C A B z)+E A (fun z => F A B z*C A B z))/12
  let W (A B : Law X Y) :=
    E (productLaw A) (fun z => (C A B z)^2)/30+E A (fun z => (C A B z)^2)/20
  let x (A B : Law X Y) :=
    (E A (fun z => (DX A B z.1-(2*B0 A B-A0 A B))^2)+
      E A (fun z => (DY A B z.2-(2*A0 A B-B0 A B))^2))/(s A B)^2
  let t := s P R
  let jj := contactj P R
  let y := 1-t+t*jj
  let U0 := 15+32*jj-((50/9:ℝ)+70*jj/3)*t+((5/9:ℝ)+46*jj/9-jj^2)*t^2
  let xx := (x P R+x R P)/2
  let lam := 40*((1/2:ℝ)-5*t/12)/23
  have hrev := pairCharge_pair_reverse hpair
  have hsr : s R P = t := pairCharge_s_reverse hpair
  have hjr : contactj R P = jj := pairCharge_contactj_reverse hpair
  have hjh : jj < (1/2:ℝ) := pairCharge_contactj_lt_half hpair
  have hs0 : 0 < t := (contact_moments hpair).s_pos
  have hsR : s R P ≤ (1/3:ℝ) := by rw [hsr];exact hs
  have hdataP := pairCharge_high_fixed_data hpair hs
  change y/4 ≤ gap P R ∧ 192*D P R ≤ U0 at hdataP
  have hdataR := pairCharge_high_fixed_data hrev hsR
  change (1-s R P+s R P*contactj R P)/4 ≤ gap R P ∧
    192*D R P ≤ 15+32*contactj R P-((50/9:ℝ)+70*contactj R P/3)*s R P+
      ((5/9:ℝ)+46*contactj R P/9-(contactj R P)^2)*(s R P)^2 at hdataR
  rw [hsr,hjr] at hdataR
  change y/4 ≤ gap R P ∧ 192*D R P ≤ U0 at hdataR
  have hn := pairCharge_actual_covariance_payment hpair hs hj hjh
  change ((jj-(1/4:ℝ)+t*((1/4:ℝ)-171*jj/100)-t^2/160)+
    ((1/2:ℝ)-5*t/12)*xx)/12 ≤ (N P R+N R P)/2 at hn
  have hw := pairCharge_raw_additive_variance_average_bound hpair
  change 0 < (1/2:ℝ)-jj ∧
    (W P R+W R P)/2 ≤ ((17/10:ℝ)*((1/2:ℝ)-jj)+(23/4:ℝ)*xx)/60 at hw
  have hmeanP := pairCharge_raw_C_means hpair
  change E P (C P R) = 0 ∧ E (productLaw P) (C P R) = 0 at hmeanP
  have hmeanR := pairCharge_raw_C_means hrev
  change E R (C R P) = 0 ∧ E (productLaw R) (C R P) = 0 at hmeanR
  have hy : 0 < y := by
    dsimp [y]
    have hprod : 0 ≤ t*jj := mul_nonneg hs0.le (by linarith)
    linarith only [hs,hprod]
  have hgapP : gap P R ≠ 0 := by linarith [hdataP.1]
  have hgapR : gap R P ≠ 0 := by linarith [hdataR.1]
  have hip := pairCharge_residual_information hpair.2.1.1 (F P R) (C P R) hmeanP.1 hmeanP.2 hgapP lam
  change 0 < D P R-2*lam*N P R+lam^2*W P R ∧
    (gap P R)^2/(4*(D P R-2*lam*N P R+lam^2*W P R)) ≤ I P at hip
  have him := pairCharge_residual_information hpair.2.2.1.1 (F R P) (C R P) hmeanR.1 hmeanR.2 hgapR lam
  change 0 < D R P-2*lam*N R P+lam^2*W R P ∧
    (gap R P)^2/(4*(D R P-2*lam*N R P+lam^2*W R P)) ≤ I R at him
  have hc := pairCharge_cubic_price hs0.le (by linarith : t ≤ 1)
  exact pairCharge_high_charge_scalar t jj (I P) (I R) (D P R) (D R P) (N P R) (N R P)
    (W P R) (W R P) (gap P R) (gap R P) xx (Psi t)
    hs0 hs hj hjh.le hdataP.2 hdataR.2 hn hw.2 hdataP.1 hdataR.1
    hip.1 him.1 hip.2 him.2 hc

/-- Regions 2 to 4, from the fixed-quarter floor and exact scalar payments. -/
lemma pairCharge_elementary_complement {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (hs1 : s P R ≤ 1)
    (hsmall : s P R ≤ (1/3:ℝ) → contactj P R ≤ (5/16:ℝ)) :
    (3:ℝ)/25 ≤ (I P+I R)/2+(1/10)*Psi (s P R) := by
  have hm := contact_moments hpair
  have hj := pairCharge_contactj_bounds hpair
  have hfloor := pairCharge_quarter_floor hpair hs1
  have hfloorR := pairCharge_quarter_floor (pairCharge_pair_reverse hpair)
    (by rw [pairCharge_s_reverse hpair];exact hs1)
  dsimp only at hfloor hfloorR
  rw [pairCharge_s_reverse hpair,pairCharge_contactj_reverse hpair] at hfloorR
  have hpay :
      ((3/25:ℝ)-9*s P R/80-57*(s P R)^2/2560-(s P R)^3/160)*
      (15-7*s P R+(s P R)^2+(32-18*s P R+3*(s P R)^2)*contactj P R-
        (s P R)^2*(contactj P R)^2) < 3*(1-s P R+s P R*contactj P R)^2 := by
    by_cases hfirst : s P R ≤ (1/3:ℝ)
    · exact pairCharge_region_small_low (s P R) (contactj P R) hm.s_pos hfirst hj.1 (hsmall hfirst)
    · by_cases hsecond : s P R ≤ (1/2:ℝ)
      · exact pairCharge_region_middle (s P R) (contactj P R) (by linarith) hsecond hj.1 hj.2
      · exact pairCharge_region_high (s P R) (contactj P R) (by linarith) hs1 hj.1 hj.2
  have hP := pairCharge_fixed_floor_information (s P R) (contactj P R) (I P) hfloor.1 hfloor.2 hpay
  have hR := pairCharge_fixed_floor_information (s P R) (contactj P R) (I R) hfloorR.1 hfloorR.2 hpay
  have hc := pairCharge_cubic_price hm.s_pos.le hs1
  linarith

/-- Region 1: the small-`s`, high-`j` averaged charge. The fixed-coefficient projection and exact scalar
payment close this region. -/
lemma pairCharge_region1_averaged {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R)
    (hsmall : s P R ≤ (1/3:ℝ)) (hhigh : (5/16:ℝ) ≤ contactj P R) :
    (3:ℝ)/25 ≤ (I P+I R)/2+(1/10)*Psi (s P R) := by
  exact pairCharge_region1_charge hpair hsmall hhigh

/-- The pair charge: on every pair of distinct positive contacts of a common feasible kernel,
`(I P + I R) / 2 + (1/10) * Psi (s P R) ≥ 3/25`, that is `PC CommonSupportPairs (1/10) (3/25)`. -/
theorem pairCharge_A : PC (X := X) (Y := Y) CommonSupportPairs (1/10) (3/25) := by
  intro S w P R hpair
  by_cases hs : s P R ≤ (1/3:ℝ)
  · by_cases hj : (5/16:ℝ) ≤ contactj P R
    · exact pairCharge_region1_averaged hpair hs hj
    · exact pairCharge_elementary_complement hpair (by linarith) (fun _ => le_of_lt (lt_of_not_ge hj))
  · by_cases hs1 : s P R ≤ 1
    · exact pairCharge_elementary_complement hpair hs1 (fun h => False.elim (hs h))
    · exact pairCharge_region5 hpair (le_of_lt (lt_of_not_ge hs1))

end

end StochasticToDeterministicLatents.General
