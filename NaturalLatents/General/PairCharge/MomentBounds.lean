-- Original work by Alexis Olson, Apache-2.0 (see NOTICE), first developed in
-- github.com/AlexisOlson/stochastic-to-deterministic-latents; reorganised for this repository
-- (namespace NaturalLatents.General, declarations renamed, unused material removed).
-- This file builds on and cites the definitions of DLorell/stoch_to_det (Apache-2.0).
import NaturalLatents.General.Contact

/-!
# Pair charge: scalar bounds, moments and reversal

This module bounds the contact moments `quarticRatio` and `defectX * defectY / s^2`, and supplies
the exchange of the two contacts. It also provides expectation identities, the fixed
endpoint table and coefficient data, and the averaging and projection inequalities
used in the information floor.

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

/-- The denominator comparison after the fixed coefficient. All analytic obligations are the supplied
positive residual variance and one KL lower bound at that coefficient. -/
lemma pairCharge_projection_information (ibar y residual Dstar : ℝ)
    (hr : 0 < residual) (hrD : residual ≤ Dstar)
    (hinfo : y ^ 2 / (64 * residual) ≤ ibar) :
    0 < Dstar ∧ 3 * y ^ 2 / (192 * Dstar) ≤ ibar := by
  have hD : 0 < Dstar := lt_of_lt_of_le hr hrD
  refine ⟨hD, le_trans ?_ hinfo⟩
  have hres : 0 < 64 * residual := by positivity
  have hstar : 0 < 192 * Dstar := by positivity
  apply (div_le_div_iff₀ hstar hres).2
  have hmul := mul_le_mul_of_nonneg_left hrD (sq_nonneg y)
  nlinarith only [hmul]

/-- Scalar reciprocal step from the entropy payment and the fixed-coefficient payment. No sign
assumption on the individual informations is needed: their positive variance KL floors imply it. -/
lemma pairCharge_average_KL (Ip Im Vp Vm Delta y : ℝ)
    (hVp : 0 < Vp) (hVm : 0 < Vm) (hy : 0 ≤ y)
    (hDelta : y / 4 ≤ Delta)
    (hIp : Delta ^ 2 / (4 * Vp) ≤ Ip)
    (hIm : Delta ^ 2 / (4 * Vm) ≤ Im) :
    y ^ 2 / (64 * ((Vp + Vm) / 2)) ≤ (Ip + Im) / 2 := by
  have hDel0 : 0 ≤ Delta := by linarith
  have hproduct : 0 ≤ (Delta - y / 4) * (Delta + y / 4) := by
    apply mul_nonneg
    · linarith
    · linarith
  have hsquare : y ^ 2 ≤ 16 * Delta ^ 2 := by
    nlinarith only [hproduct]
  have hipmul := (div_le_iff₀ (show 0 < 4 * Vp by positivity)).mp hIp
  have himmul := (div_le_iff₀ (show 0 < 4 * Vm by positivity)).mp hIm
  have hip0 : 0 ≤ Ip := le_trans (by positivity) hIp
  have him0 : 0 ≤ Im := le_trans (by positivity) hIm
  have hipy : y ^ 2 ≤ 64 * Vp * Ip := by nlinarith only [hsquare, hipmul]
  have himy : y ^ 2 ≤ 64 * Vm * Im := by nlinarith only [hsquare, himmul]
  have hipyM := mul_le_mul_of_nonneg_left hipy hVm.le
  have himyP := mul_le_mul_of_nonneg_left himy hVp.le
  have hcombined : y ^ 2 * (Vp + Vm) ≤ 64 * Vp * Vm * (Ip + Im) := by
    nlinarith only [hipyM, himyP]
  have hgram : 4 * Vp * Vm ≤ (Vp + Vm) ^ 2 := by
    nlinarith [sq_nonneg (Vp - Vm)]
  have hupper := mul_le_mul_of_nonneg_right hgram
    (show 0 ≤ 16 * (Ip + Im) by positivity)
  have hfinal : y ^ 2 ≤ 16 * (Vp + Vm) * (Ip + Im) := by
    by_contra h
    have hgap : 0 < y ^ 2 - 16 * (Vp + Vm) * (Ip + Im) := by linarith
    have hpositive := mul_pos (show 0 < Vp + Vm by positivity) hgap
    nlinarith only [hcombined, hupper, hpositive]
  apply (div_le_iff₀ (show 0 < 64 * ((Vp + Vm) / 2) by positivity)).2
  nlinarith only [hfinal]

/-- The mean-gap numerator is positive on its full scalar rectangle. -/
lemma pairCharge_fixed_floor_y_pos (s j : ℝ)
    (hsnonneg : 0 ≤ s) (hshi : s ≤ 1) (hjpos : 0 < j) :
    0 < 1 - s + s * j := by
  have hsj : 0 ≤ s * j := mul_nonneg hsnonneg hjpos.le
  by_cases hs : s = 1
  · subst s
    simpa using hjpos
  · have : 0 < 1 - s := lt_of_le_of_ne (by linarith) (sub_ne_zero.mpr (Ne.symm hs)).symm
    linarith

/-- The mean-gap comparison; the lower bound on `v` is unnecessary. -/
lemma pairCharge_fixed_floor_gap (s j v h : ℝ)
    (hslo : 0 ≤ s) (hvhi : v ≤ (1 / 4 : ℝ))
    (hh : h = (1 + s * j) / 4) :
    (1 - s + s * j) / 4 ≤ h - s * v := by
  have hsv := mul_le_mul_of_nonneg_left hvhi hslo
  rw [hh]
  nlinarith only [hsv]

lemma pairCharge_pair_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) : CommonSupportPair S w R P := by
  exact ⟨hpair.1, hpair.2.2.1, hpair.2.1, hpair.2.2.2.2.1,
    hpair.2.2.2.1, Ne.symm hpair.2.2.2.2.2⟩

lemma defect_bounds {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) :
    (2 : ℝ) / 9 ≤ defectX P R * defectY P R / (separation P R)^2 ∧
      defectX P R * defectY P R / (separation P R)^2 ≤ (1 : ℝ) / 4 := by
  have hm := contact_moments hpair
  have hU := contact_expect_nonneg hpair.2.1.1 (fun z => (stoch_to_det.contactSecantX P R z.1)^2)
    (fun _ => sq_nonneg _)
  have hV := contact_expect_nonneg hpair.2.1.1 (fun z => (stoch_to_det.contactSecantY P R z.2)^2)
    (fun _ => sq_nonneg _)
  rw [hm.secantX_square] at hU
  rw [hm.secantY_square] at hV
  have hs : 0 < (separation P R)^2 := sq_pos_of_pos hm.separation_pos
  have hsum : separation P R = defectX P R + defectY P R := rfl
  constructor
  · apply (le_div_iff₀ hs).2
    nlinarith [mul_nonneg hU hV]
  · apply (div_le_iff₀ hs).2
    nlinarith [sq_nonneg (defectX P R - defectY P R)]

lemma pairCharge_quarticMoment_nonneg {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) : 0 ≤ quarticMoment P R := by
  exact contact_expect_nonneg hpair.2.1.1 _ (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))

lemma pairCharge_quarticRatio_nonneg {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) : 0 ≤ quarticRatio P R := by
  exact div_nonneg (pairCharge_quarticMoment_nonneg hpair) (sq_nonneg _)

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_expect_centered_square {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F : X × Y → ℝ) :
    expect P (fun z => (F z - expect P F)^2) = expect P (fun z => (F z)^2) - (expect P F)^2 := by
  have h := contact_q_expect_shift_sq hP F (-expect P F)
  have heq : (fun z => (F z - expect P F)^2) = (fun z => (F z + -expect P F)^2) := by rfl
  rw [heq,h]
  ring

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_expect_sq_ge_sq_expect {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F : X × Y → ℝ) : (expect P F)^2 ≤ expect P (fun z => (F z)^2) := by
  rw [← sub_nonneg]
  rw [← pairCharge_expect_centered_square hP F]
  exact contact_expect_nonneg hP _ (fun z => sq_nonneg _)

lemma pairCharge_quarticMoment_ge_secantProduct_mean_sq {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) :
    (expect P (fun z => stoch_to_det.contactSecantX P R z.1 * stoch_to_det.contactSecantY P R z.2))^2 ≤ quarticMoment P R := by
  have h := pairCharge_expect_sq_ge_sq_expect hpair.2.1.1 (fun z => stoch_to_det.contactSecantX P R z.1 * stoch_to_det.contactSecantY P R z.2)
  convert h using 1
  unfold quarticMoment
  congr 1
  funext z
  ring

lemma pairCharge_quarticRatio_upper {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) :
    quarticRatio P R ≤ 6 * (defectX P R * defectY P R / (separation P R)^2) - 1 ∧
      quarticRatio P R ≤ (1 : ℝ) / 2 := by
  have hm := contact_moments hpair
  have hs : 0 < (separation P R)^2 := sq_pos_of_pos hm.separation_pos
  constructor
  · unfold quarticRatio
    apply (div_le_iff₀ hs).2
    calc
      _ ≤ 6 * defectX P R * defectY P R - (separation P R)^2 := hm.quarticMoment_bound
      _ = (6 * (defectX P R * defectY P R / (separation P R)^2) - 1) * (separation P R)^2 := by
        field_simp [hm.separation_pos.ne']
  · unfold quarticRatio
    apply (div_le_iff₀ hs).2
    nlinarith [hm.quarticMoment_bound, hm.scalar_bound]

lemma pairCharge_quarticRatio_lower {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) :
    (1 : ℝ) / 16 ≤ ((1 + separation P R * quarticRatio P R) / 4)^2 ∧
      ((1 + separation P R * quarticRatio P R) / 4)^2 ≤ quarticRatio P R := by
  have hm := contact_moments hpair
  have hj := pairCharge_quarticRatio_nonneg hpair
  have hs : 0 < (separation P R)^2 := sq_pos_of_pos hm.separation_pos
  have hcs := pairCharge_quarticMoment_ge_secantProduct_mean_sq hpair
  have hc := hm.quartic_identity
  have hden : separation P R ≠ 0 := ne_of_gt hm.separation_pos
  have hjs : quarticRatio P R * (separation P R)^2 = quarticMoment P R := by
    unfold quarticRatio
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hden)
  have hcov : separation P R * ((1 + separation P R * quarticRatio P R) / 4) =
      expect P (fun z => stoch_to_det.contactSecantX P R z.1 * stoch_to_det.contactSecantY P R z.2) := by
    nlinarith [hjs]
  constructor
  · have hh : (1 : ℝ) / 4 ≤ (1 + separation P R * quarticRatio P R) / 4 := by
      nlinarith [mul_nonneg hm.separation_pos.le hj]
    nlinarith [sq_nonneg ((1 + separation P R * quarticRatio P R) / 4 - 1/4)]
  · have hsq : (separation P R)^2 * ((1 + separation P R * quarticRatio P R) / 4)^2 =
        (expect P (fun z => stoch_to_det.contactSecantX P R z.1 * stoch_to_det.contactSecantY P R z.2))^2 := by
      rw [← hcov]
      ring
    apply (mul_le_mul_iff_of_pos_left hs).mp
    nlinarith [hsq, hjs]

lemma pairCharge_quarticRatio_bounds {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) :
    (1 : ℝ) / 16 ≤ quarticRatio P R ∧ quarticRatio P R ≤ (1 : ℝ) / 2 := by
  have hl := pairCharge_quarticRatio_lower hpair
  exact ⟨hl.1.trans hl.2, (pairCharge_quarticRatio_upper hpair).2⟩

lemma pairCharge_secant_means {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) :
    expect P (fun z => stoch_to_det.contactSecantX P R z.1) = -defectX P R ∧
      expect P (fun z => stoch_to_det.contactSecantY P R z.2) = -defectY P R := by
  have hEf : expect P (fun z => rootRatioX P R z.1) = expect P (fun z => stoch_to_det.contactSecantX P R z.1) + 1 := by
    change expect P (fun z => stoch_to_det.contactSecantX P R z.1 + 1) = _
    rw [contact_expect_add, contact_expect_const hpair.2.1.1]
  have hEg : expect P (fun z => rootRatioY P R z.2) = expect P (fun z => stoch_to_det.contactSecantY P R z.2) + 1 := by
    change expect P (fun z => stoch_to_det.contactSecantY P R z.2 + 1) = _
    rw [contact_expect_add, contact_expect_const hpair.2.1.1]
  unfold defectX defectY
  constructor <;> linarith

omit [DecidableEq X] [DecidableEq Y] in
/-- Expansion shared by the two orientations of the mixed shifted moment. -/
lemma pairCharge_expect_shift_mixed {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F G : X × Y → ℝ) :
    expect P (fun z => (F z + 1) * (G z + 1)^2) =
      expect P (fun z => F z * (G z)^2) + 2 * expect P (fun z => F z * G z) +
      expect P F + expect P (fun z => (G z)^2) + 2 * expect P G + 1 := by
  calc
    _ = expect P (fun z => (((((F z * (G z)^2) + 2 * (F z * G z)) + F z) +
        (G z)^2) + 2 * G z) + 1) := by
      congr 1
      funext z
      ring
    _ = _ := by
      simp only [contact_expect_add, contact_q_expect_scale, contact_expect_const hP]

lemma pairCharge_secant_mixed_moments {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) :
    expect P (fun z => stoch_to_det.contactSecantX P R z.1 * (stoch_to_det.contactSecantY P R z.2)^2) =
      (3 * (defectX P R - defectY P R) - quarticMoment P R) / 2 ∧
    expect P (fun z => (stoch_to_det.contactSecantX P R z.1)^2 * stoch_to_det.contactSecantY P R z.2) =
      (-3 * (defectX P R - defectY P R) - quarticMoment P R) / 2 := by
  have hm := contact_moments hpair
  have hmeans := pairCharge_secant_means hpair
  have hmix := contact_q_mixed_moments (contact_cond_rootRatioY_square_mul hpair) (contact_cond_rootRatioX_square_mul hpair)
  have hU := pairCharge_expect_shift_mixed hpair.2.1.1
    (fun z => stoch_to_det.contactSecantX P R z.1) (fun z => stoch_to_det.contactSecantY P R z.2)
  change expect P (fun z => rootRatioX P R z.1 * (rootRatioY P R z.2)^2) = _ at hU
  have hVraw := pairCharge_expect_shift_mixed hpair.2.1.1
    (fun z => stoch_to_det.contactSecantY P R z.2) (fun z => stoch_to_det.contactSecantX P R z.1)
  have hV : expect P (fun z => (rootRatioX P R z.1)^2 * rootRatioY P R z.2) =
      expect P (fun z => (stoch_to_det.contactSecantX P R z.1)^2 * stoch_to_det.contactSecantY P R z.2) +
      2 * expect P (fun z => stoch_to_det.contactSecantX P R z.1 * stoch_to_det.contactSecantY P R z.2) +
      expect P (fun z => stoch_to_det.contactSecantY P R z.2) + expect P (fun z => (stoch_to_det.contactSecantX P R z.1)^2) +
      2 * expect P (fun z => stoch_to_det.contactSecantX P R z.1) + 1 := by
    calc
      _ = expect P (fun z => (stoch_to_det.contactSecantY P R z.2 + 1) * (stoch_to_det.contactSecantX P R z.1 + 1)^2) := by
        congr 1
        funext z
        unfold rootRatioX rootRatioY
        ring
      _ = _ := by simpa only [mul_comm] using hVraw
  rw [hmix.2, hm.rootRatioX_square, hmeans.1, hmeans.2, hm.secantY_square] at hU
  rw [hmix.1, hm.rootRatioY_square, hmeans.1, hmeans.2, hm.secantX_square] at hV
  have hEf : expect P (fun z => rootRatioX P R z.1) = 1 - defectX P R := by unfold defectX; ring
  have hEg : expect P (fun z => rootRatioY P R z.2) = 1 - defectY P R := by unfold defectY; ring
  rw [hEg] at hU
  rw [hEf] at hV
  have hs : separation P R = defectX P R + defectY P R := rfl
  have hq := hm.quartic_identity
  constructor <;> linarith

lemma pairCharge_reciprocal_roots {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a / b)^((1 : ℝ) / 3) * (b / a)^((1 : ℝ) / 3) = 1 := by
  rw [← Real.mul_rpow (div_nonneg ha.le hb.le) (div_nonneg hb.le ha.le)]
  have hid : a / b * (b / a) = 1 := by field_simp
  rw [hid, Real.one_rpow]

lemma pairCharge_rootRatioX_reverse_mul {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) {x : X} (hx : x ∈ xSupport S) :
    rootRatioX P R x * rootRatioX R P x = 1 := by
  rw [rootRatioX_eq_cbrt, rootRatioX_eq_cbrt]
  exact pairCharge_reciprocal_roots
    (contact_mX_pos hpair.2.2.1 hpair.2.2.2.2.1 hx)
    (contact_mX_pos hpair.2.1 hpair.2.2.2.1 hx)

lemma pairCharge_rootRatioY_reverse_mul {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) {y : Y} (hy : y ∈ ySupport S) :
    rootRatioY P R y * rootRatioY R P y = 1 := by
  rw [rootRatioY_eq_cbrt, rootRatioY_eq_cbrt]
  exact pairCharge_reciprocal_roots
    (contact_mY_pos hpair.2.2.1 hpair.2.2.2.2.1 hy)
    (contact_mY_pos hpair.2.1 hpair.2.2.2.1 hy)

lemma pairCharge_mean_losses_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) :
    defectX R P = defectY P R ∧ defectY R P = defectX P R := by
  have hmix := contact_q_mixed_moments (contact_cond_rootRatioY_square_mul hpair) (contact_cond_rootRatioX_square_mul hpair)
  have hf : expect R (fun z => rootRatioX R P z.1) = expect P (fun z => rootRatioX P R z.1 * (rootRatioY P R z.2)^2) := by
    unfold expect
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : z ∈ S
    · have hroot := pairCharge_rootRatioX_reverse_mul hpair (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
      calc
        _ = (P z * (rootRatioY P R z.2)^2) * (rootRatioX P R z.1 * rootRatioX R P z.1) * rootRatioX P R z.1 := by
          rw [contact_ratio_mul hpair z]
          ring
        _ = _ := by rw [hroot]; ring
    · rw [hpair.2.1.2.1 z hz, hpair.2.2.1.2.1 z hz]
      ring
  have hg : expect R (fun z => rootRatioY R P z.2) = expect P (fun z => (rootRatioX P R z.1)^2 * rootRatioY P R z.2) := by
    unfold expect
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : z ∈ S
    · have hroot := pairCharge_rootRatioY_reverse_mul hpair (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
      calc
        _ = (P z * (rootRatioX P R z.1)^2) * (rootRatioY P R z.2 * rootRatioY R P z.2) * rootRatioY P R z.2 := by
          rw [contact_ratio_mul hpair z]
          ring
        _ = _ := by rw [hroot]; ring
    · rw [hpair.2.1.2.1 z hz, hpair.2.2.1.2.1 z hz]
      ring
  have hm := contact_moments hpair
  rw [hmix.2, hm.rootRatioX_square] at hf
  rw [hmix.1, hm.rootRatioY_square] at hg
  unfold defectX defectY
  constructor <;> linarith

lemma pairCharge_separation_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) : separation R P = separation P R := by
  rw [separation, separation,
    (pairCharge_mean_losses_reverse hpair).1, (pairCharge_mean_losses_reverse hpair).2]
  ring

lemma pairCharge_quarticMoment_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) : quarticMoment R P = quarticMoment P R := by
  unfold quarticMoment expect
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : z ∈ S
  · have hf := pairCharge_rootRatioX_reverse_mul hpair (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    have hg := pairCharge_rootRatioY_reverse_mul hpair (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    have hU : rootRatioX P R z.1 * stoch_to_det.contactSecantX R P z.1 = -stoch_to_det.contactSecantX P R z.1 := by
      unfold rootRatioX at hf ⊢
      nlinarith [hf]
    have hV : rootRatioY P R z.2 * stoch_to_det.contactSecantY R P z.2 = -stoch_to_det.contactSecantY P R z.2 := by
      unfold rootRatioY at hg ⊢
      nlinarith [hg]
    calc
      _ = P z * (rootRatioX P R z.1 * stoch_to_det.contactSecantX R P z.1)^2 *
          (rootRatioY P R z.2 * stoch_to_det.contactSecantY R P z.2)^2 := by
        rw [contact_ratio_mul hpair z]
        ring
      _ = _ := by rw [hU, hV]; ring
  · rw [hpair.2.1.2.1 z hz, hpair.2.2.1.2.1 z hz]
    ring

lemma pairCharge_quarticRatio_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) : quarticRatio R P = quarticRatio P R := by
  unfold quarticRatio
  rw [pairCharge_separation_reverse hpair, pairCharge_quarticMoment_reverse hpair]

lemma pairCharge_defectProductRatio_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) :
    defectX R P * defectY R P / (separation R P)^2 = defectX P R * defectY P R / (separation P R)^2 := by
  rw [pairCharge_separation_reverse hpair,
    (pairCharge_mean_losses_reverse hpair).1, (pairCharge_mean_losses_reverse hpair).2]
  ring

/-- Independence under the product of the two marginals, including its null cells. -/
lemma pairCharge_expect_product (P : Law X Y) (F : X → ℝ) (G : Y → ℝ) :
    expect (marginalProduct P) (fun z => F z.1 * G z.2) =
      expect P (fun z => F z.1) * expect P (fun z => G z.2) := by
  rw [contact_expect_fst, contact_expect_snd]
  unfold expect marginalProduct
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma pairCharge_expect_product_fst {P : Law X Y} (hP : stoch_to_det.IsPMF P) (F : X → ℝ) :
    expect (marginalProduct P) (fun z => F z.1) = expect P (fun z => F z.1) := by
  have h := pairCharge_expect_product P F (fun _ => 1)
  simpa only [mul_one, contact_expect_const hP] using h

lemma pairCharge_expect_product_snd {P : Law X Y} (hP : stoch_to_det.IsPMF P) (G : Y → ℝ) :
    expect (marginalProduct P) (fun z => G z.2) = expect P (fun z => G z.2) := by
  have h := pairCharge_expect_product P (fun _ => 1) G
  simpa only [one_mul, contact_expect_const hP] using h

lemma pairCharge_product_isPMF {P : Law X Y} (hP : stoch_to_det.IsPMF P) :
    stoch_to_det.IsPMF (marginalProduct P) :=
  stoch_to_det.product_isPMF_dom (stoch_to_det.isPMF_push hP) (stoch_to_det.isPMF_push hP)

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_expect_div (P : Law X Y) (F : X × Y → ℝ) (c : ℝ) :
    expect P (fun z => F z / c) = expect P F / c := by
  simp only [expect, ← mul_div_assoc, ← Finset.sum_div]

/-- The exact endpoint table for the fixed quarter correction. -/
lemma pairCharge_fixed_endpoint_table {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) :
    let H : X × Y → ℝ := fun z => stoch_to_det.contactSecantX P R z.1 * stoch_to_det.contactSecantY P R z.2
    let L : X × Y → ℝ := fun z => stoch_to_det.contactSecantX P R z.1 + stoch_to_det.contactSecantY P R z.2 + separation P R
    expect P H = (separation P R + quarticMoment P R)/4 ∧
    expect (marginalProduct P) H = defectX P R * defectY P R ∧
    expect P L = 0 ∧ expect (marginalProduct P) L = 0 ∧
    expect P (fun z => (H z)^2) = quarticMoment P R ∧
    expect (marginalProduct P) (fun z => (H z)^2) = 9*defectX P R*defectY P R-2*(separation P R)^2 ∧
    expect P (fun z => (L z)^2) = 3*separation P R/2-(separation P R)^2+quarticMoment P R/2 ∧
    expect (marginalProduct P) (fun z => (L z)^2) = separation P R-(separation P R)^2+2*defectX P R*defectY P R ∧
    expect P (fun z => H z*L z) = -quarticMoment P R+separation P R*(separation P R+quarticMoment P R)/4 ∧
    expect (marginalProduct P) (fun z => H z*L z) =
      (separation P R)^2-6*defectX P R*defectY P R+separation P R*defectX P R*defectY P R := by
  let H : X × Y → ℝ := fun z => stoch_to_det.contactSecantX P R z.1 * stoch_to_det.contactSecantY P R z.2
  let L : X × Y → ℝ := fun z => stoch_to_det.contactSecantX P R z.1 + stoch_to_det.contactSecantY P R z.2 + separation P R
  have hm := contact_moments hpair
  have hu := (pairCharge_secant_means hpair).1
  have hv := (pairCharge_secant_means hpair).2
  have hsum : separation P R = defectX P R + defectY P R := rfl
  have hH : expect P H = (separation P R+quarticMoment P R)/4 := by
    dsimp [H]
    linarith [hm.quartic_identity]
  have hHQ : expect (marginalProduct P) H = defectX P R*defectY P R := by
    dsimp [H]
    rw [pairCharge_expect_product,hu,hv]
    ring
  have hL : expect P L = 0 := by
    dsimp [L]
    rw [contact_expect_add,contact_expect_add,hu,hv,contact_expect_const hpair.2.1.1]
    linarith
  have hLQ : expect (marginalProduct P) L = 0 := by
    dsimp [L]
    rw [contact_expect_add,contact_expect_add,pairCharge_expect_product_fst hpair.2.1.1,
      pairCharge_expect_product_snd hpair.2.1.1,hu,hv,contact_expect_const (pairCharge_product_isPMF hpair.2.1.1)]
    linarith
  have hH2 : expect P (fun z => (H z)^2) = quarticMoment P R := by
    unfold H quarticMoment
    congr 1
    funext z
    ring
  have hH2Q : expect (marginalProduct P) (fun z => (H z)^2) =
      9*defectX P R*defectY P R-2*(separation P R)^2 := by
    simp only [H,mul_pow]
    rw [pairCharge_expect_product P (fun x => (stoch_to_det.contactSecantX P R x)^2) (fun y => (stoch_to_det.contactSecantY P R y)^2),hm.secantX_square,hm.secantY_square,hsum]
    ring
  have hL2 (Q : Law X Y) (hQ : stoch_to_det.IsPMF Q) :
      expect Q (fun z => (L z)^2) =
      expect Q (fun z => (stoch_to_det.contactSecantX P R z.1)^2)+expect Q (fun z => (stoch_to_det.contactSecantY P R z.2)^2)+
      2*expect Q H+2*separation P R*(expect Q (fun z => stoch_to_det.contactSecantX P R z.1)+expect Q (fun z => stoch_to_det.contactSecantY P R z.2))+(separation P R)^2 := by
    dsimp [L]
    rw [contact_q_expect_shift_sq hQ]
    have hid (z : X × Y) : (stoch_to_det.contactSecantX P R z.1+stoch_to_det.contactSecantY P R z.2)^2 =
        (stoch_to_det.contactSecantX P R z.1)^2+(stoch_to_det.contactSecantY P R z.2)^2+2*H z := by dsimp [H];ring
    simp only [hid,contact_expect_add,contact_q_expect_scale]
  have hHL (Q : Law X Y) : expect Q (fun z => H z*L z) =
      expect Q (fun z => (stoch_to_det.contactSecantX P R z.1)^2*stoch_to_det.contactSecantY P R z.2)+
      expect Q (fun z => stoch_to_det.contactSecantX P R z.1*(stoch_to_det.contactSecantY P R z.2)^2)+separation P R*expect Q H := by
    have hid (z : X × Y) : H z*L z =
        (stoch_to_det.contactSecantX P R z.1)^2*stoch_to_det.contactSecantY P R z.2+stoch_to_det.contactSecantX P R z.1*(stoch_to_det.contactSecantY P R z.2)^2+separation P R*H z := by dsimp [H,L];ring
    simp only [hid,contact_expect_add,contact_q_expect_scale]
  refine ⟨hH,hHQ,hL,hLQ,hH2,hH2Q,?_,?_,?_,?_⟩
  · rw [hL2 P hpair.2.1.1,hm.secantX_square,hm.secantY_square,hH,hu,hv,hsum]
    ring
  · rw [hL2 (marginalProduct P) (pairCharge_product_isPMF hpair.2.1.1),
      pairCharge_expect_product_fst hpair.2.1.1 (fun x => (stoch_to_det.contactSecantX P R x)^2),
      pairCharge_expect_product_snd hpair.2.1.1 (fun y => (stoch_to_det.contactSecantY P R y)^2),
      pairCharge_expect_product_fst hpair.2.1.1 (stoch_to_det.contactSecantX P R),
      pairCharge_expect_product_snd hpair.2.1.1 (stoch_to_det.contactSecantY P R),hm.secantX_square,hm.secantY_square,hHQ,hu,hv,hsum]
    ring
  · rw [hHL P,(pairCharge_secant_mixed_moments hpair).1,(pairCharge_secant_mixed_moments hpair).2,hH]
    ring
  · rw [hHL (marginalProduct P),
      pairCharge_expect_product P (fun x => (stoch_to_det.contactSecantX P R x)^2) (stoch_to_det.contactSecantY P R),
      pairCharge_expect_product P (stoch_to_det.contactSecantX P R) (fun y => (stoch_to_det.contactSecantY P R y)^2),
      hm.secantX_square,hm.secantY_square,hu,hv,hHQ,hsum]
    ring

/-- Exact variance for any fixed additive correction. -/
lemma pairCharge_fixed_coefficient_data {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (c : ℝ) :
    let t := separation P R
    let jj := quarticRatio P R
    let vv := defectX P R*defectY P R/t^2
    let hh := (1+t*jj)/4
    let F : X × Y → ℝ := fun z =>
      stoch_to_det.contactSecantX P R z.1*stoch_to_det.contactSecantY P R z.2/t+c*(stoch_to_det.contactSecantX P R z.1+stoch_to_det.contactSecantY P R z.2+t)
    expect P F-expect (marginalProduct P) F = hh-t*vv ∧
    expect (marginalProduct P) (fun z => (F z-expect (marginalProduct P) F)^2)/3 +
      expect P (fun z => (F z-expect P F)^2)/6 + (expect P F-expect (marginalProduct P) F)^2/12 =
    (9*vv-2)/3+jj/6-t^2*vv^2/4-t*vv*hh/6-hh^2/12 +
      2*c*t*((3/8:ℝ)-2*vv-jj/6+t*(vv/3+jj/24)) +
      c^2*t*((7/12:ℝ)-t/2+2*t*vv/3+t*jj/12) := by
  let t := separation P R
  let H : X × Y → ℝ := fun z => stoch_to_det.contactSecantX P R z.1*stoch_to_det.contactSecantY P R z.2
  let L : X × Y → ℝ := fun z => stoch_to_det.contactSecantX P R z.1+stoch_to_det.contactSecantY P R z.2+t
  let F : X × Y → ℝ := fun z => H z/t+c*L z
  change expect P F-expect (marginalProduct P) F = _ ∧ _ = _
  obtain ⟨hH,hHQ,hL,hLQ,hH2,hH2Q,hL2,hL2Q,hHL,hHLQ⟩ := pairCharge_fixed_endpoint_table hpair
  have hden : t ≠ 0 := (contact_moments hpair).separation_pos.ne'
  have hFP : expect P F = (t+quarticMoment P R)/(4*t) := by
    dsimp [F]
    rw [contact_expect_add,pairCharge_expect_div,contact_q_expect_scale,hH,hL]
    dsimp [t]
    ring
  have hFQ : expect (marginalProduct P) F = defectX P R*defectY P R/t := by
    dsimp [F]
    rw [contact_expect_add,pairCharge_expect_div,contact_q_expect_scale,hHQ,hLQ]
    ring
  have hsquare (Q : Law X Y) : expect Q (fun z => (F z)^2) =
      expect Q (fun z => (H z)^2)/t^2+(2*c/t)*expect Q (fun z => H z*L z)+
        c^2*expect Q (fun z => (L z)^2) := by
    have hid (z : X × Y) : (F z)^2 =
        (H z)^2/t^2+(2*c/t)*(H z*L z)+c^2*(L z)^2 := by
      dsimp [F]
      ring
    simp only [hid,contact_expect_add,contact_q_expect_scale,pairCharge_expect_div]
  have hFP2 : expect P (fun z => (F z)^2) =
      quarticMoment P R/t^2+(2*c/t)*(-quarticMoment P R+t*(t+quarticMoment P R)/4)+c^2*(3*t/2-t^2+quarticMoment P R/2) := by
    rw [hsquare P,hH2,hHL,hL2]
  have hFQ2 : expect (marginalProduct P) (fun z => (F z)^2) =
      (9*defectX P R*defectY P R-2*t^2)/t^2+
      (2*c/t)*(t^2-6*defectX P R*defectY P R+t*defectX P R*defectY P R)+
      c^2*(t-t^2+2*defectX P R*defectY P R) := by
    rw [hsquare (marginalProduct P),hH2Q,hHLQ,hL2Q]
  constructor
  · rw [hFP,hFQ]
    dsimp only [quarticRatio]
    change (t+quarticMoment P R)/(4*t)-defectX P R*defectY P R/t =
      (1+t*(quarticMoment P R/t^2))/4-t*(defectX P R*defectY P R/t^2)
    field_simp [hden]
  · rw [pairCharge_expect_centered_square (pairCharge_product_isPMF hpair.2.1.1),
      pairCharge_expect_centered_square hpair.2.1.1,hFP,hFQ,hFP2,hFQ2]
    dsimp only [quarticRatio]
    change _ = (9*(defectX P R*defectY P R/t^2)-2)/3+(quarticMoment P R/t^2)/6-
      t^2*(defectX P R*defectY P R/t^2)^2/4-
      t*(defectX P R*defectY P R/t^2)*((1+t*(quarticMoment P R/t^2))/4)/6-
      ((1+t*(quarticMoment P R/t^2))/4)^2/12+
      2*c*t*((3/8:ℝ)-2*(defectX P R*defectY P R/t^2)-(quarticMoment P R/t^2)/6+
        t*((defectX P R*defectY P R/t^2)/3+(quarticMoment P R/t^2)/24))+
      c^2*t*((7/12:ℝ)-t/2+2*t*(defectX P R*defectY P R/t^2)/3+t*(quarticMoment P R/t^2)/12)
    field_simp [hden]
    ring

end

end NaturalLatents.General
