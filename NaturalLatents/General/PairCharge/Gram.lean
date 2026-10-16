-- Original work by Alexis Olson, Apache-2.0 (see NOTICE), October 2026, first written on an unpublished branch of
-- github.com/AlexisOlson/stochastic-to-deterministic-latents; reorganised for this repository
-- (namespace NaturalLatents.General, declarations renamed, unused material removed).
-- This file builds on and cites the definitions of DLorell/stoch_to_det (Apache-2.0).
import NaturalLatents.General.PairCharge.MomentBounds

/-!
# Pair charge: conditional expectations and the contact Gram form

This module supplies finite conditional-expectation identities and their affine
properties. It identifies the contact defects and Gram energy, proves the bilinear
identity for the contact form, and establishes the centering and support identities
used in the correction moments and Hessian bound.

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

lemma pairCharge_cond_X_mul {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (G : Y → ℝ) (x : X) :
    stoch_to_det.mX P x * ((∑ y, P (x,y) * G y) / stoch_to_det.mX P x) =
      ∑ y, P (x,y) * G y := by
  by_cases hx : stoch_to_det.mX P x = 0
  · have hzero (y : Y) : P (x,y) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hP.nonneg (x,y))).mp
        ((stoch_to_det.mX_eq_sum P x).symm.trans hx) y (Finset.mem_univ _)
    simp [hx, hzero]
  · exact mul_div_cancel₀ _ hx

lemma pairCharge_cond_Y_mul {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F : X → ℝ) (y : Y) :
    stoch_to_det.mY P y * ((∑ x, P (x,y) * F x) / stoch_to_det.mY P y) =
      ∑ x, P (x,y) * F x := by
  by_cases hy : stoch_to_det.mY P y = 0
  · have hzero (x : X) : P (x,y) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hP.nonneg (x,y))).mp
        ((stoch_to_det.mY_eq_sum P y).symm.trans hy) x (Finset.mem_univ _)
    simp [hy, hzero]
  · exact mul_div_cancel₀ _ hy

lemma pairCharge_cond_X_inner {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F : X → ℝ) (G : Y → ℝ) :
    expect P (fun z => F z.1 * ((∑ y, P (z.1,y) * G y) / stoch_to_det.mX P z.1)) =
      expect P (fun z => F z.1 * G z.2) := by
  rw [contact_expect_fst P (fun x => F x * ((∑ y, P (x,y) * G y) / stoch_to_det.mX P x))]
  simp_rw [mul_left_comm (stoch_to_det.mX P _) (F _), pairCharge_cond_X_mul hP,
    Finset.mul_sum]
  unfold expect
  rw [Fintype.sum_prod_type]
  congr 1
  funext x
  congr 1
  funext y
  ring

lemma pairCharge_cond_Y_inner {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F : X → ℝ) (G : Y → ℝ) :
    expect P (fun z => ((∑ x, P (x,z.2) * F x) / stoch_to_det.mY P z.2) * G z.2) =
      expect P (fun z => F z.1 * G z.2) := by
  rw [contact_expect_snd P (fun y => ((∑ x, P (x,y) * F x) / stoch_to_det.mY P y) * G y)]
  simp_rw [← mul_assoc, pairCharge_cond_Y_mul hP, Finset.sum_mul, mul_assoc]
  unfold expect
  rw [Fintype.sum_prod_type, Finset.sum_comm]

lemma pairCharge_cond_X_mean {P : Law X Y} (hP : stoch_to_det.IsPMF P) (G : Y → ℝ) :
    expect P (fun z => (∑ y, P (z.1,y) * G y) / stoch_to_det.mX P z.1) =
      expect P (fun z => G z.2) := by
  simpa only [one_mul] using pairCharge_cond_X_inner hP (fun _ => 1) G

lemma pairCharge_cond_Y_mean {P : Law X Y} (hP : stoch_to_det.IsPMF P) (F : X → ℝ) :
    expect P (fun z => (∑ x, P (x,z.2) * F x) / stoch_to_det.mY P z.2) =
      expect P (fun z => F z.1) := by
  simpa only [mul_one] using pairCharge_cond_Y_inner hP F (fun _ => 1)

omit [DecidableEq Y] in
lemma pairCharge_cond_X_linear (P : Law X Y) (G H : Y → ℝ) (a b : ℝ) (x : X) :
    (∑ y, P (x,y) * (a * G y + b * H y)) / stoch_to_det.mX P x =
      a * ((∑ y, P (x,y) * G y) / stoch_to_det.mX P x) +
      b * ((∑ y, P (x,y) * H y) / stoch_to_det.mX P x) := by
  simp only [mul_add, Finset.sum_add_distrib, mul_left_comm (P _) a,
    mul_left_comm (P _) b, ← Finset.mul_sum, add_div, mul_div_assoc]

omit [DecidableEq X] in
lemma pairCharge_cond_Y_linear (P : Law X Y) (F H : X → ℝ) (a b : ℝ) (y : Y) :
    (∑ x, P (x,y) * (a * F x + b * H x)) / stoch_to_det.mY P y =
      a * ((∑ x, P (x,y) * F x) / stoch_to_det.mY P y) +
      b * ((∑ x, P (x,y) * H x) / stoch_to_det.mY P y) := by
  simp only [mul_add, Finset.sum_add_distrib, mul_left_comm (P _) a,
    mul_left_comm (P _) b, ← Finset.mul_sum, add_div, mul_div_assoc]

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_expect_lincomb_prod (P : Law X Y) (F G H K : X × Y → ℝ) (a b : ℝ) :
    expect P (fun z => (a * F z + b * H z) * (a * G z + b * K z)) =
      a^2 * expect P (fun z => F z * G z) +
      a * b * (expect P (fun z => F z * K z) + expect P (fun z => H z * G z)) +
      b^2 * expect P (fun z => H z * K z) := by
  calc
    _ = expect P (fun z => (a^2 * (F z * G z) +
        (a * b) * (F z * K z + H z * G z)) + b^2 * (H z * K z)) := by
      congr 1
      funext z
      ring
    _ = _ := by
      simp only [contact_expect_add, contact_q_expect_scale]

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_expect_lincomb_sq (P : Law X Y) (F H : X × Y → ℝ) (a b : ℝ) :
    expect P (fun z => (a * F z + b * H z)^2) =
      a^2 * expect P (fun z => (F z)^2) +
      2 * a * b * expect P (fun z => F z * H z) +
      b^2 * expect P (fun z => (H z)^2) := by
  have h := pairCharge_expect_lincomb_prod P F F H H a b
  simp only [← pow_two, mul_comm (H _) (F _)] at h
  rw [h]
  ring

lemma pairCharge_cond_X_affine {P : Law X Y} (G : Y → ℝ) (a b : ℝ)
    {x : X} (hx : stoch_to_det.mX P x ≠ 0) :
    (∑ y, P (x,y) * (a * G y + b)) / stoch_to_det.mX P x =
      a * ((∑ y, P (x,y) * G y) / stoch_to_det.mX P x) + b := by
  simpa only [mul_one, ← stoch_to_det.mX_eq_sum, div_self hx, mul_one] using
    pairCharge_cond_X_linear P G (fun _ => 1) a b x

lemma pairCharge_cond_Y_affine {P : Law X Y} (F : X → ℝ) (a b : ℝ)
    {y : Y} (hy : stoch_to_det.mY P y ≠ 0) :
    (∑ x, P (x,y) * (a * F x + b)) / stoch_to_det.mY P y =
      a * ((∑ x, P (x,y) * F x) / stoch_to_det.mY P y) + b := by
  simpa only [mul_one, ← stoch_to_det.mY_eq_sum, div_self hy, mul_one] using
    pairCharge_cond_Y_linear P F (fun _ => 1) a b y

lemma pairCharge_cond_X_sq_add_one {P : Law X Y} (G : Y → ℝ)
    {x : X} (hx : stoch_to_det.mX P x ≠ 0) :
    (∑ y, P (x,y) * (G y + 1)^2) / stoch_to_det.mX P x =
      (∑ y, P (x,y) * (G y)^2) / stoch_to_det.mX P x +
        2 * ((∑ y, P (x,y) * G y) / stoch_to_det.mX P x) + 1 := by
  simp only [add_sq, mul_one, one_pow, mul_add, Finset.sum_add_distrib,
    mul_left_comm (P _) 2, ← Finset.mul_sum, add_div, mul_div_assoc,
    ← stoch_to_det.mX_eq_sum, div_self hx]

lemma pairCharge_cond_Y_sq_add_one {P : Law X Y} (F : X → ℝ)
    {y : Y} (hy : stoch_to_det.mY P y ≠ 0) :
    (∑ x, P (x,y) * (F x + 1)^2) / stoch_to_det.mY P y =
      (∑ x, P (x,y) * (F x)^2) / stoch_to_det.mY P y +
        2 * ((∑ x, P (x,y) * F x) / stoch_to_det.mY P y) + 1 := by
  simp only [add_sq, mul_one, one_pow, mul_add, Finset.sum_add_distrib,
    mul_left_comm (P _) 2, ← Finset.mul_sum, add_div, mul_div_assoc,
    ← stoch_to_det.mY_eq_sum, div_self hy]

lemma pairCharge_contact_defect_X {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) {x : X} (hx : x ∈ xSupport S) :
    (∑ y, P (x,y) * (stoch_to_det.contactSecantY P R y)^2) / stoch_to_det.mX P x - (2 * defectY P R - defectX P R) =
      stoch_to_det.contactSecantX P R x + defectX P R -
        2 * ((∑ y, P (x,y) * (stoch_to_det.contactSecantY P R y + defectY P R)) / stoch_to_det.mX P x) := by
  have hxne := (contact_mX_pos hpair.2.1 hpair.2.2.2.1 hx).ne'
  have hc := (contact_moments hpair).cond_rootRatioY_square x hx
  have hs := pairCharge_cond_X_sq_add_one (stoch_to_det.contactSecantY P R) hxne
  change (∑ y, P (x,y) * (stoch_to_det.contactSecantY P R y + 1)^2) / stoch_to_det.mX P x = stoch_to_det.contactSecantX P R x + 1 at hc
  have ha := pairCharge_cond_X_affine (stoch_to_det.contactSecantY P R) 1 (defectY P R) hxne
  simp only [one_mul] at ha
  rw [hs] at hc
  rw [ha]
  linarith

lemma pairCharge_contact_defect_Y {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) {y : Y} (hy : y ∈ ySupport S) :
    (∑ x, P (x,y) * (stoch_to_det.contactSecantX P R x)^2) / stoch_to_det.mY P y - (2 * defectX P R - defectY P R) =
      stoch_to_det.contactSecantY P R y + defectY P R -
        2 * ((∑ x, P (x,y) * (stoch_to_det.contactSecantX P R x + defectX P R)) / stoch_to_det.mY P y) := by
  have hyne := (contact_mY_pos hpair.2.1 hpair.2.2.2.1 hy).ne'
  have hc := (contact_moments hpair).cond_rootRatioX_square y hy
  have hs := pairCharge_cond_Y_sq_add_one (stoch_to_det.contactSecantX P R) hyne
  change (∑ x, P (x,y) * (stoch_to_det.contactSecantX P R x + 1)^2) / stoch_to_det.mY P y = stoch_to_det.contactSecantY P R y + 1 at hc
  have ha := pairCharge_cond_Y_affine (stoch_to_det.contactSecantX P R) 1 (defectX P R) hyne
  simp only [one_mul] at ha
  rw [hs] at hc
  rw [ha]
  linarith

lemma pairCharge_contact_gram_energy {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) :
    expect P (fun z => (stoch_to_det.contactSecantX P R z.1 + defectX P R)^2) +
      expect P (fun z => (stoch_to_det.contactSecantY P R z.2 + defectY P R)^2) -
      4 * expect P (fun z => (stoch_to_det.contactSecantX P R z.1 + defectX P R) * (stoch_to_det.contactSecantY P R z.2 + defectY P R)) =
        6 * defectX P R * defectY P R - (separation P R)^2 - quarticMoment P R := by
  have hm := contact_moments hpair
  have hu := contact_q_expect_shift_sq hpair.2.1.1 (fun z => stoch_to_det.contactSecantX P R z.1) (defectX P R)
  have hv := contact_q_expect_shift_sq hpair.2.1.1 (fun z => stoch_to_det.contactSecantY P R z.2) (defectY P R)
  have huv := contact_q_expect_shift_prod hpair.2.1.1 (fun z => stoch_to_det.contactSecantX P R z.1)
    (fun z => stoch_to_det.contactSecantY P R z.2) (defectX P R) (defectY P R)
  rw [hm.secantX_square, (pairCharge_secant_means hpair).1] at hu
  rw [hm.secantY_square, (pairCharge_secant_means hpair).2] at hv
  rw [(pairCharge_secant_means hpair).1, (pairCharge_secant_means hpair).2] at huv
  have hq := hm.quartic_identity
  have hs : separation P R = defectX P R + defectY P R := rfl
  rw [hu, hv, huv, hq, hs]
  ring

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_expect_congr_positive {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F G : X × Y → ℝ) (hFG : ∀ z, 0 < P z → F z = G z) :
    expect P F = expect P G := by
  unfold expect
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : P z = 0
  · simp [hz]
  · rw [hFG z (lt_of_le_of_ne (hP.nonneg z) (Ne.symm hz))]

lemma pairCharge_mem_S_of_pos {S : Finset (X × Y)} {w P : Law X Y}
    (hP : stoch_to_det.IsContact S w P) {z : X × Y} (hz : 0 < P z) : z ∈ S := by
  by_contra hn
  have hzero := hP.2.1 z hn
  linarith

lemma pairCharge_shifted_features_centered {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) :
    expect P (fun z => stoch_to_det.contactSecantX P R z.1 + defectX P R) = 0 ∧
      expect P (fun z => stoch_to_det.contactSecantY P R z.2 + defectY P R) = 0 := by
  rw [contact_expect_add, contact_expect_const hpair.2.1.1, (pairCharge_secant_means hpair).1,
    contact_expect_add, contact_expect_const hpair.2.1.1, (pairCharge_secant_means hpair).2]
  constructor <;> ring

lemma pairCharge_gram_bilinear {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F H : X → ℝ) (G K : Y → ℝ) :
    expect P (fun z => F z.1 * H z.1) + expect P (fun z => G z.2 * K z.2) -
      2 * expect P (fun z => F z.1 * K z.2) - 2 * expect P (fun z => H z.1 * G z.2) =
    expect P (fun z => (F z.1 -
      2 * ((∑ y, P (z.1,y) * G y) / stoch_to_det.mX P z.1)) * H z.1) +
    expect P (fun z => (G z.2 -
      2 * ((∑ x, P (x,z.2) * F x) / stoch_to_det.mY P z.2)) * K z.2) := by
  simp_rw [sub_mul, mul_assoc, contact_q_expect_sub, contact_q_expect_scale,
    mul_comm ((∑ y, P (_,y) * G y) / stoch_to_det.mX P _) (H _)]
  rw [pairCharge_cond_X_inner hP, pairCharge_cond_Y_inner hP]
  ring

lemma pairCharge_contact_defects_centered {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) :
    expect P (fun z => (∑ y, P (z.1,y) * (stoch_to_det.contactSecantY P R y)^2) / stoch_to_det.mX P z.1 -
      (2 * defectY P R - defectX P R)) = 0 ∧
    expect P (fun z => (∑ x, P (x,z.2) * (stoch_to_det.contactSecantX P R x)^2) / stoch_to_det.mY P z.2 -
      (2 * defectX P R - defectY P R)) = 0 := by
  constructor
  · rw [contact_q_expect_sub, contact_expect_const hpair.2.1.1, pairCharge_cond_X_mean hpair.2.1.1, (contact_moments hpair).secantY_square]
    ring
  · rw [contact_q_expect_sub, contact_expect_const hpair.2.1.1, pairCharge_cond_Y_mean hpair.2.1.1, (contact_moments hpair).secantX_square]
    ring

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_expect_mul_comm (P : Law X Y) (F G : X × Y → ℝ) :
    expect P (fun z => F z * G z) = expect P (fun z => G z * F z) := by
  simp only [mul_comm]

lemma pairCharge_cond_X_congr_support {S : Finset (X × Y)} {w P : Law X Y}
    (hP : stoch_to_det.IsContact S w P) (G H : Y → ℝ)
    (hGH : ∀ y ∈ ySupport S, G y = H y) (x : X) :
    (∑ y, P (x,y) * G y) / stoch_to_det.mX P x =
      (∑ y, P (x,y) * H y) / stoch_to_det.mX P x := by
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  by_cases hz : P (x,y) = 0
  · simp [hz]
  · have hzpos : 0 < P (x,y) := lt_of_le_of_ne (hP.1.nonneg _) (Ne.symm hz)
    rw [hGH y (Finset.mem_image.mpr ⟨(x,y), pairCharge_mem_S_of_pos hP hzpos, rfl⟩)]

lemma pairCharge_cond_Y_congr_support {S : Finset (X × Y)} {w P : Law X Y}
    (hP : stoch_to_det.IsContact S w P) (F H : X → ℝ)
    (hFH : ∀ x ∈ xSupport S, F x = H x) (y : Y) :
    (∑ x, P (x,y) * F x) / stoch_to_det.mY P y =
      (∑ x, P (x,y) * H x) / stoch_to_det.mY P y := by
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hz : P (x,y) = 0
  · simp [hz]
  · have hzpos : 0 < P (x,y) := lt_of_le_of_ne (hP.1.nonneg _) (Ne.symm hz)
    rw [hFH x (Finset.mem_image.mpr ⟨(x,y), pairCharge_mem_S_of_pos hP hzpos, rfl⟩)]

end

end NaturalLatents.General
