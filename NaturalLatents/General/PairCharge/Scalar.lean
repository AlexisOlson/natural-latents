-- Adapted from the author's earlier repository (StochasticToDeterministicLatents);
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised; namespace renamed to NaturalLatents.General.
import NaturalLatents.General.Contact

/-!
# Pair charge: scalar bounds, moments and reversal

This module bounds the contact moments `contactj` and `A0 * B0 / s^2`, and supplies
the exchange of the two contacts. It also provides expectation identities, the fixed
endpoint table and coefficient data, and the averaging and projection inequalities
used in the information floor.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
This file retains that source's definitions and lemmas where cited, together with
material adapted from the author's earlier repository.
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
    (hpair : CommonSupportPairs S w P R) : CommonSupportPairs S w R P := by
  exact ⟨hpair.1, hpair.2.2.1, hpair.2.1, hpair.2.2.2.2.1,
    hpair.2.2.2.1, Ne.symm hpair.2.2.2.2.2⟩

lemma pairCharge_v_bounds {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    (2 : ℝ) / 9 ≤ A0 P R * B0 P R / (s P R)^2 ∧
      A0 P R * B0 P R / (s P R)^2 ≤ (1 : ℝ) / 4 := by
  have hm := contact_moments hpair
  have hU := contact_E_nonneg hpair.2.1.1 (fun z => (U P R z.1)^2)
    (fun _ => sq_nonneg _)
  have hV := contact_E_nonneg hpair.2.1.1 (fun z => (V P R z.2)^2)
    (fun _ => sq_nonneg _)
  rw [hm.U2] at hU
  rw [hm.V2] at hV
  have hs : 0 < (s P R)^2 := sq_pos_of_pos hm.s_pos
  have hsum : s P R = A0 P R + B0 P R := rfl
  constructor
  · apply (le_div_iff₀ hs).2
    nlinarith [mul_nonneg hU hV]
  · apply (div_le_iff₀ hs).2
    nlinarith [sq_nonneg (A0 P R - B0 P R)]

lemma pairCharge_J_nonneg {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) : 0 ≤ J P R := by
  exact contact_E_nonneg hpair.2.1.1 _ (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))

lemma pairCharge_contactj_nonneg {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) : 0 ≤ contactj P R := by
  exact div_nonneg (pairCharge_J_nonneg hpair) (sq_nonneg _)

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_E_centered_square {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F : X × Y → ℝ) :
    E P (fun z => (F z - E P F)^2) = E P (fun z => (F z)^2) - (E P F)^2 := by
  have h := contact_q_E_shift_sq hP F (-E P F)
  have heq : (fun z => (F z - E P F)^2) = (fun z => (F z + -E P F)^2) := by rfl
  rw [heq,h]
  ring

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_E_sq_ge_sq_E {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F : X × Y → ℝ) : (E P F)^2 ≤ E P (fun z => (F z)^2) := by
  rw [← sub_nonneg]
  rw [← pairCharge_E_centered_square hP F]
  exact contact_E_nonneg hP _ (fun z => sq_nonneg _)

lemma pairCharge_J_ge_uv_sq {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    (E P (fun z => U P R z.1 * V P R z.2))^2 ≤ J P R := by
  have h := pairCharge_E_sq_ge_sq_E hpair.2.1.1 (fun z => U P R z.1 * V P R z.2)
  convert h using 1
  unfold J
  congr 1
  funext z
  ring

lemma pairCharge_contactj_upper {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    contactj P R ≤ 6 * (A0 P R * B0 P R / (s P R)^2) - 1 ∧
      contactj P R ≤ (1 : ℝ) / 2 := by
  have hm := contact_moments hpair
  have hs : 0 < (s P R)^2 := sq_pos_of_pos hm.s_pos
  constructor
  · unfold contactj
    apply (div_le_iff₀ hs).2
    calc
      _ ≤ 6 * A0 P R * B0 P R - (s P R)^2 := hm.J_bound
      _ = (6 * (A0 P R * B0 P R / (s P R)^2) - 1) * (s P R)^2 := by
        field_simp [hm.s_pos.ne']
  · unfold contactj
    apply (div_le_iff₀ hs).2
    nlinarith [hm.J_bound, hm.scalar_bound]

lemma pairCharge_contactj_lower {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    (1 : ℝ) / 16 ≤ ((1 + s P R * contactj P R) / 4)^2 ∧
      ((1 + s P R * contactj P R) / 4)^2 ≤ contactj P R := by
  have hm := contact_moments hpair
  have hj := pairCharge_contactj_nonneg hpair
  have hs : 0 < (s P R)^2 := sq_pos_of_pos hm.s_pos
  have hcs := pairCharge_J_ge_uv_sq hpair
  have hc := hm.quartic
  have hden : s P R ≠ 0 := ne_of_gt hm.s_pos
  have hjs : contactj P R * (s P R)^2 = J P R := by
    unfold contactj
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hden)
  have hcov : s P R * ((1 + s P R * contactj P R) / 4) =
      E P (fun z => U P R z.1 * V P R z.2) := by
    nlinarith [hjs]
  constructor
  · have hh : (1 : ℝ) / 4 ≤ (1 + s P R * contactj P R) / 4 := by
      nlinarith [mul_nonneg hm.s_pos.le hj]
    nlinarith [sq_nonneg ((1 + s P R * contactj P R) / 4 - 1/4)]
  · have hsq : (s P R)^2 * ((1 + s P R * contactj P R) / 4)^2 =
        (E P (fun z => U P R z.1 * V P R z.2))^2 := by
      rw [← hcov]
      ring
    apply (mul_le_mul_iff_of_pos_left hs).mp
    nlinarith [hsq, hjs]

lemma pairCharge_contactj_bounds {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    (1 : ℝ) / 16 ≤ contactj P R ∧ contactj P R ≤ (1 : ℝ) / 2 := by
  have hl := pairCharge_contactj_lower hpair
  exact ⟨hl.1.trans hl.2, (pairCharge_contactj_upper hpair).2⟩

lemma pairCharge_mean_UV {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    E P (fun z => U P R z.1) = -A0 P R ∧
      E P (fun z => V P R z.2) = -B0 P R := by
  have hEf : E P (fun z => f P R z.1) = E P (fun z => U P R z.1) + 1 := by
    change E P (fun z => U P R z.1 + 1) = _
    rw [contact_E_add, contact_E_const hpair.2.1.1]
  have hEg : E P (fun z => g P R z.2) = E P (fun z => V P R z.2) + 1 := by
    change E P (fun z => V P R z.2 + 1) = _
    rw [contact_E_add, contact_E_const hpair.2.1.1]
  unfold A0 B0
  constructor <;> linarith

omit [DecidableEq X] [DecidableEq Y] in
/-- Expansion shared by the two orientations of the mixed shifted moment. -/
lemma pairCharge_E_shift_mixed {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F G : X × Y → ℝ) :
    E P (fun z => (F z + 1) * (G z + 1)^2) =
      E P (fun z => F z * (G z)^2) + 2 * E P (fun z => F z * G z) +
      E P F + E P (fun z => (G z)^2) + 2 * E P G + 1 := by
  calc
    _ = E P (fun z => (((((F z * (G z)^2) + 2 * (F z * G z)) + F z) +
        (G z)^2) + 2 * G z) + 1) := by
      congr 1
      funext z
      ring
    _ = _ := by
      simp only [contact_E_add, contact_q_E_scale, contact_E_const hP]

lemma pairCharge_mixed_UV {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    E P (fun z => U P R z.1 * (V P R z.2)^2) =
      (3 * (A0 P R - B0 P R) - J P R) / 2 ∧
    E P (fun z => (U P R z.1)^2 * V P R z.2) =
      (-3 * (A0 P R - B0 P R) - J P R) / 2 := by
  have hm := contact_moments hpair
  have hmeans := pairCharge_mean_UV hpair
  have hmix := contact_q_mixed_moments (contact_cond_g2_mul hpair) (contact_cond_f2_mul hpair)
  have hU := pairCharge_E_shift_mixed hpair.2.1.1
    (fun z => U P R z.1) (fun z => V P R z.2)
  change E P (fun z => f P R z.1 * (g P R z.2)^2) = _ at hU
  have hVraw := pairCharge_E_shift_mixed hpair.2.1.1
    (fun z => V P R z.2) (fun z => U P R z.1)
  have hV : E P (fun z => (f P R z.1)^2 * g P R z.2) =
      E P (fun z => (U P R z.1)^2 * V P R z.2) +
      2 * E P (fun z => U P R z.1 * V P R z.2) +
      E P (fun z => V P R z.2) + E P (fun z => (U P R z.1)^2) +
      2 * E P (fun z => U P R z.1) + 1 := by
    calc
      _ = E P (fun z => (V P R z.2 + 1) * (U P R z.1 + 1)^2) := by
        congr 1
        funext z
        unfold f g
        ring
      _ = _ := by simpa only [mul_comm] using hVraw
  rw [hmix.2, hm.f2, hmeans.1, hmeans.2, hm.V2] at hU
  rw [hmix.1, hm.g2, hmeans.1, hmeans.2, hm.U2] at hV
  have hEf : E P (fun z => f P R z.1) = 1 - A0 P R := by unfold A0; ring
  have hEg : E P (fun z => g P R z.2) = 1 - B0 P R := by unfold B0; ring
  rw [hEg] at hU
  rw [hEf] at hV
  have hs : s P R = A0 P R + B0 P R := rfl
  have hq := hm.quartic
  constructor <;> linarith

lemma pairCharge_reciprocal_roots {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a / b)^((1 : ℝ) / 3) * (b / a)^((1 : ℝ) / 3) = 1 := by
  rw [← Real.mul_rpow (div_nonneg ha.le hb.le) (div_nonneg hb.le ha.le)]
  have hid : a / b * (b / a) = 1 := by field_simp
  rw [hid, Real.one_rpow]

lemma pairCharge_f_reverse_mul {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) {x : X} (hx : x ∈ XSupport S) :
    f P R x * f R P x = 1 := by
  rw [f_eq_cubeRoot, f_eq_cubeRoot]
  exact pairCharge_reciprocal_roots
    (contact_mX_pos hpair.2.2.1 hpair.2.2.2.2.1 hx)
    (contact_mX_pos hpair.2.1 hpair.2.2.2.1 hx)

lemma pairCharge_g_reverse_mul {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) {y : Y} (hy : y ∈ YSupport S) :
    g P R y * g R P y = 1 := by
  rw [g_eq_cubeRoot, g_eq_cubeRoot]
  exact pairCharge_reciprocal_roots
    (contact_mY_pos hpair.2.2.1 hpair.2.2.2.2.1 hy)
    (contact_mY_pos hpair.2.1 hpair.2.2.2.1 hy)

lemma pairCharge_mean_losses_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    A0 R P = B0 P R ∧ B0 R P = A0 P R := by
  have hmix := contact_q_mixed_moments (contact_cond_g2_mul hpair) (contact_cond_f2_mul hpair)
  have hf : E R (fun z => f R P z.1) = E P (fun z => f P R z.1 * (g P R z.2)^2) := by
    unfold E
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : z ∈ S
    · have hroot := pairCharge_f_reverse_mul hpair (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
      calc
        _ = (P z * (g P R z.2)^2) * (f P R z.1 * f R P z.1) * f P R z.1 := by
          rw [contact_ratio_mul hpair z]
          ring
        _ = _ := by rw [hroot]; ring
    · rw [hpair.2.1.2.1 z hz, hpair.2.2.1.2.1 z hz]
      ring
  have hg : E R (fun z => g R P z.2) = E P (fun z => (f P R z.1)^2 * g P R z.2) := by
    unfold E
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : z ∈ S
    · have hroot := pairCharge_g_reverse_mul hpair (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
      calc
        _ = (P z * (f P R z.1)^2) * (g P R z.2 * g R P z.2) * g P R z.2 := by
          rw [contact_ratio_mul hpair z]
          ring
        _ = _ := by rw [hroot]; ring
    · rw [hpair.2.1.2.1 z hz, hpair.2.2.1.2.1 z hz]
      ring
  have hm := contact_moments hpair
  rw [hmix.2, hm.f2] at hf
  rw [hmix.1, hm.g2] at hg
  unfold A0 B0
  constructor <;> linarith

lemma pairCharge_s_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) : s R P = s P R := by
  rw [s, s,
    (pairCharge_mean_losses_reverse hpair).1, (pairCharge_mean_losses_reverse hpair).2]
  ring

lemma pairCharge_J_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) : J R P = J P R := by
  unfold J E
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : z ∈ S
  · have hf := pairCharge_f_reverse_mul hpair (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    have hg := pairCharge_g_reverse_mul hpair (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    have hU : f P R z.1 * U R P z.1 = -U P R z.1 := by
      unfold f at hf ⊢
      nlinarith [hf]
    have hV : g P R z.2 * V R P z.2 = -V P R z.2 := by
      unfold g at hg ⊢
      nlinarith [hg]
    calc
      _ = P z * (f P R z.1 * U R P z.1)^2 *
          (g P R z.2 * V R P z.2)^2 := by
        rw [contact_ratio_mul hpair z]
        ring
      _ = _ := by rw [hU, hV]; ring
  · rw [hpair.2.1.2.1 z hz, hpair.2.2.1.2.1 z hz]
    ring

lemma pairCharge_contactj_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) : contactj R P = contactj P R := by
  unfold contactj
  rw [pairCharge_s_reverse hpair, pairCharge_J_reverse hpair]

lemma pairCharge_v_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    A0 R P * B0 R P / (s R P)^2 = A0 P R * B0 P R / (s P R)^2 := by
  rw [pairCharge_s_reverse hpair,
    (pairCharge_mean_losses_reverse hpair).1, (pairCharge_mean_losses_reverse hpair).2]
  ring

/-- Independence under the product of the two marginals, including its null cells. -/
lemma pairCharge_E_product (P : Law X Y) (F : X → ℝ) (G : Y → ℝ) :
    E (productLaw P) (fun z => F z.1 * G z.2) =
      E P (fun z => F z.1) * E P (fun z => G z.2) := by
  rw [contact_E_fst, contact_E_snd]
  unfold E productLaw
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma pairCharge_E_product_fst {P : Law X Y} (hP : stoch_to_det.IsPMF P) (F : X → ℝ) :
    E (productLaw P) (fun z => F z.1) = E P (fun z => F z.1) := by
  have h := pairCharge_E_product P F (fun _ => 1)
  simpa only [mul_one, contact_E_const hP] using h

lemma pairCharge_E_product_snd {P : Law X Y} (hP : stoch_to_det.IsPMF P) (G : Y → ℝ) :
    E (productLaw P) (fun z => G z.2) = E P (fun z => G z.2) := by
  have h := pairCharge_E_product P (fun _ => 1) G
  simpa only [one_mul, contact_E_const hP] using h

lemma pairCharge_product_isPMF {P : Law X Y} (hP : stoch_to_det.IsPMF P) :
    stoch_to_det.IsPMF (productLaw P) :=
  stoch_to_det.product_isPMF_dom (stoch_to_det.isPMF_push hP) (stoch_to_det.isPMF_push hP)

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_E_div (P : Law X Y) (F : X × Y → ℝ) (c : ℝ) :
    E P (fun z => F z / c) = E P F / c := by
  simp only [E, ← mul_div_assoc, ← Finset.sum_div]

/-- The exact endpoint table for the fixed quarter correction. -/
lemma pairCharge_fixed_endpoint_table {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    let H : X × Y → ℝ := fun z => U P R z.1 * V P R z.2
    let L : X × Y → ℝ := fun z => U P R z.1 + V P R z.2 + s P R
    E P H = (s P R + J P R)/4 ∧
    E (productLaw P) H = A0 P R * B0 P R ∧
    E P L = 0 ∧ E (productLaw P) L = 0 ∧
    E P (fun z => (H z)^2) = J P R ∧
    E (productLaw P) (fun z => (H z)^2) = 9*A0 P R*B0 P R-2*(s P R)^2 ∧
    E P (fun z => (L z)^2) = 3*s P R/2-(s P R)^2+J P R/2 ∧
    E (productLaw P) (fun z => (L z)^2) = s P R-(s P R)^2+2*A0 P R*B0 P R ∧
    E P (fun z => H z*L z) = -J P R+s P R*(s P R+J P R)/4 ∧
    E (productLaw P) (fun z => H z*L z) =
      (s P R)^2-6*A0 P R*B0 P R+s P R*A0 P R*B0 P R := by
  let H : X × Y → ℝ := fun z => U P R z.1 * V P R z.2
  let L : X × Y → ℝ := fun z => U P R z.1 + V P R z.2 + s P R
  have hm := contact_moments hpair
  have hu := (pairCharge_mean_UV hpair).1
  have hv := (pairCharge_mean_UV hpair).2
  have hsum : s P R = A0 P R + B0 P R := rfl
  have hH : E P H = (s P R+J P R)/4 := by
    dsimp [H]
    linarith [hm.quartic]
  have hHQ : E (productLaw P) H = A0 P R*B0 P R := by
    dsimp [H]
    rw [pairCharge_E_product,hu,hv]
    ring
  have hL : E P L = 0 := by
    dsimp [L]
    rw [contact_E_add,contact_E_add,hu,hv,contact_E_const hpair.2.1.1]
    linarith
  have hLQ : E (productLaw P) L = 0 := by
    dsimp [L]
    rw [contact_E_add,contact_E_add,pairCharge_E_product_fst hpair.2.1.1,
      pairCharge_E_product_snd hpair.2.1.1,hu,hv,contact_E_const (pairCharge_product_isPMF hpair.2.1.1)]
    linarith
  have hH2 : E P (fun z => (H z)^2) = J P R := by
    unfold H J
    congr 1
    funext z
    ring
  have hH2Q : E (productLaw P) (fun z => (H z)^2) =
      9*A0 P R*B0 P R-2*(s P R)^2 := by
    simp only [H,mul_pow]
    rw [pairCharge_E_product P (fun x => (U P R x)^2) (fun y => (V P R y)^2),hm.U2,hm.V2,hsum]
    ring
  have hL2 (Q : Law X Y) (hQ : stoch_to_det.IsPMF Q) :
      E Q (fun z => (L z)^2) =
      E Q (fun z => (U P R z.1)^2)+E Q (fun z => (V P R z.2)^2)+
      2*E Q H+2*s P R*(E Q (fun z => U P R z.1)+E Q (fun z => V P R z.2))+(s P R)^2 := by
    dsimp [L]
    rw [contact_q_E_shift_sq hQ]
    have hid (z : X × Y) : (U P R z.1+V P R z.2)^2 =
        (U P R z.1)^2+(V P R z.2)^2+2*H z := by dsimp [H];ring
    simp only [hid,contact_E_add,contact_q_E_scale]
  have hHL (Q : Law X Y) : E Q (fun z => H z*L z) =
      E Q (fun z => (U P R z.1)^2*V P R z.2)+
      E Q (fun z => U P R z.1*(V P R z.2)^2)+s P R*E Q H := by
    have hid (z : X × Y) : H z*L z =
        (U P R z.1)^2*V P R z.2+U P R z.1*(V P R z.2)^2+s P R*H z := by dsimp [H,L];ring
    simp only [hid,contact_E_add,contact_q_E_scale]
  refine ⟨hH,hHQ,hL,hLQ,hH2,hH2Q,?_,?_,?_,?_⟩
  · rw [hL2 P hpair.2.1.1,hm.U2,hm.V2,hH,hu,hv,hsum]
    ring
  · rw [hL2 (productLaw P) (pairCharge_product_isPMF hpair.2.1.1),
      pairCharge_E_product_fst hpair.2.1.1 (fun x => (U P R x)^2),
      pairCharge_E_product_snd hpair.2.1.1 (fun y => (V P R y)^2),
      pairCharge_E_product_fst hpair.2.1.1 (U P R),
      pairCharge_E_product_snd hpair.2.1.1 (V P R),hm.U2,hm.V2,hHQ,hu,hv,hsum]
    ring
  · rw [hHL P,(pairCharge_mixed_UV hpair).1,(pairCharge_mixed_UV hpair).2,hH]
    ring
  · rw [hHL (productLaw P),
      pairCharge_E_product P (fun x => (U P R x)^2) (V P R),
      pairCharge_E_product P (U P R) (fun y => (V P R y)^2),
      hm.U2,hm.V2,hu,hv,hHQ,hsum]
    ring

/-- Exact variance for any fixed additive correction. -/
lemma pairCharge_fixed_coefficient_data {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (c : ℝ) :
    let t := s P R
    let jj := contactj P R
    let vv := A0 P R*B0 P R/t^2
    let hh := (1+t*jj)/4
    let F : X × Y → ℝ := fun z =>
      U P R z.1*V P R z.2/t+c*(U P R z.1+V P R z.2+t)
    E P F-E (productLaw P) F = hh-t*vv ∧
    E (productLaw P) (fun z => (F z-E (productLaw P) F)^2)/3 +
      E P (fun z => (F z-E P F)^2)/6 + (E P F-E (productLaw P) F)^2/12 =
    (9*vv-2)/3+jj/6-t^2*vv^2/4-t*vv*hh/6-hh^2/12 +
      2*c*t*((3/8:ℝ)-2*vv-jj/6+t*(vv/3+jj/24)) +
      c^2*t*((7/12:ℝ)-t/2+2*t*vv/3+t*jj/12) := by
  let t := s P R
  let H : X × Y → ℝ := fun z => U P R z.1*V P R z.2
  let L : X × Y → ℝ := fun z => U P R z.1+V P R z.2+t
  let F : X × Y → ℝ := fun z => H z/t+c*L z
  change E P F-E (productLaw P) F = _ ∧ _ = _
  obtain ⟨hH,hHQ,hL,hLQ,hH2,hH2Q,hL2,hL2Q,hHL,hHLQ⟩ := pairCharge_fixed_endpoint_table hpair
  have hden : t ≠ 0 := (contact_moments hpair).s_pos.ne'
  have hFP : E P F = (t+J P R)/(4*t) := by
    dsimp [F]
    rw [contact_E_add,pairCharge_E_div,contact_q_E_scale,hH,hL]
    dsimp [t]
    ring
  have hFQ : E (productLaw P) F = A0 P R*B0 P R/t := by
    dsimp [F]
    rw [contact_E_add,pairCharge_E_div,contact_q_E_scale,hHQ,hLQ]
    ring
  have hsquare (Q : Law X Y) : E Q (fun z => (F z)^2) =
      E Q (fun z => (H z)^2)/t^2+(2*c/t)*E Q (fun z => H z*L z)+
        c^2*E Q (fun z => (L z)^2) := by
    have hid (z : X × Y) : (F z)^2 =
        (H z)^2/t^2+(2*c/t)*(H z*L z)+c^2*(L z)^2 := by
      dsimp [F]
      ring
    simp only [hid,contact_E_add,contact_q_E_scale,pairCharge_E_div]
  have hFP2 : E P (fun z => (F z)^2) =
      J P R/t^2+(2*c/t)*(-J P R+t*(t+J P R)/4)+c^2*(3*t/2-t^2+J P R/2) := by
    rw [hsquare P,hH2,hHL,hL2]
  have hFQ2 : E (productLaw P) (fun z => (F z)^2) =
      (9*A0 P R*B0 P R-2*t^2)/t^2+
      (2*c/t)*(t^2-6*A0 P R*B0 P R+t*A0 P R*B0 P R)+
      c^2*(t-t^2+2*A0 P R*B0 P R) := by
    rw [hsquare (productLaw P),hH2Q,hHLQ,hL2Q]
  constructor
  · rw [hFP,hFQ]
    dsimp only [contactj]
    change (t+J P R)/(4*t)-A0 P R*B0 P R/t =
      (1+t*(J P R/t^2))/4-t*(A0 P R*B0 P R/t^2)
    field_simp [hden]
  · rw [pairCharge_E_centered_square (pairCharge_product_isPMF hpair.2.1.1),
      pairCharge_E_centered_square hpair.2.1.1,hFP,hFQ,hFP2,hFQ2]
    dsimp only [contactj]
    change _ = (9*(A0 P R*B0 P R/t^2)-2)/3+(J P R/t^2)/6-
      t^2*(A0 P R*B0 P R/t^2)^2/4-
      t*(A0 P R*B0 P R/t^2)*((1+t*(J P R/t^2))/4)/6-
      ((1+t*(J P R/t^2))/4)^2/12+
      2*c*t*((3/8:ℝ)-2*(A0 P R*B0 P R/t^2)-(J P R/t^2)/6+
        t*((A0 P R*B0 P R/t^2)/3+(J P R/t^2)/24))+
      c^2*t*((7/12:ℝ)-t/2+2*t*(A0 P R*B0 P R/t^2)/3+t*(J P R/t^2)/12)
    field_simp [hden]
    ring

end

end NaturalLatents.General
