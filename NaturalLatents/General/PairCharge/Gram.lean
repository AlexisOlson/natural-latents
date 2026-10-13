-- Adapted from the author's earlier repository (StochasticToDeterministicLatents);
-- modified: module paths renamed; declarations unused by the main theorems removed.
import NaturalLatents.General.PairCharge.Scalar

/-!
# Pair charge: conditional geometry and the Gram form

Third part of the pair charge. Finite conditional expectations of the two marginals, their
contraction and affine properties, the Gram form of the contact defects and its positive
semidefiniteness, the global sum-of-squares certificate for the operator, and the resulting
bounds on the contact defects.

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

lemma pairCharge_cond_X_mul {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (G : Y → ℝ) (x : X) :
    stoch_to_det.mX P x * ((∑ y, P (x,y) * G y) / stoch_to_det.mX P x) =
      ∑ y, P (x,y) * G y := by
  by_cases hx : stoch_to_det.mX P x = 0
  · have hrow : ∀ y, P (x,y) = 0 := by
      intro y
      apply le_antisymm
      · have hle : P (x,y) ≤ stoch_to_det.mX P x := by
          rw [stoch_to_det.mX_eq_sum]
          exact Finset.single_le_sum (fun y _ => hP.nonneg (x,y)) (Finset.mem_univ y)
        simpa [hx] using hle
      · exact hP.nonneg _
    simp [hx, hrow]
  · field_simp

lemma pairCharge_cond_Y_mul {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F : X → ℝ) (y : Y) :
    stoch_to_det.mY P y * ((∑ x, P (x,y) * F x) / stoch_to_det.mY P y) =
      ∑ x, P (x,y) * F x := by
  by_cases hy : stoch_to_det.mY P y = 0
  · have hcol : ∀ x, P (x,y) = 0 := by
      intro x
      apply le_antisymm
      · have hle : P (x,y) ≤ stoch_to_det.mY P y := by
          rw [stoch_to_det.mY_eq_sum]
          exact Finset.single_le_sum (fun x _ => hP.nonneg (x,y)) (Finset.mem_univ x)
        simpa [hy] using hle
      · exact hP.nonneg _
    simp [hy, hcol]
  · field_simp

lemma pairCharge_cond_X_inner {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F : X → ℝ) (G : Y → ℝ) :
    E P (fun z => F z.1 * ((∑ y, P (z.1,y) * G y) / stoch_to_det.mX P z.1)) =
      E P (fun z => F z.1 * G z.2) := by
  rw [contact_q_E_fst P (fun x => F x * ((∑ y, P (x,y) * G y) / stoch_to_det.mX P x))]
  calc
    _ = ∑ x, (stoch_to_det.mX P x *
        ((∑ y, P (x,y) * G y) / stoch_to_det.mX P x)) * F x := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ∑ x, (∑ y, P (x,y) * G y) * F x := by
      simp_rw [pairCharge_cond_X_mul hP]
    _ = ∑ x, ∑ y, P (x,y) * (F x * G y) := by
      simp_rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = _ := by unfold E; rw [Fintype.sum_prod_type]

lemma pairCharge_cond_Y_inner {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F : X → ℝ) (G : Y → ℝ) :
    E P (fun z => ((∑ x, P (x,z.2) * F x) / stoch_to_det.mY P z.2) * G z.2) =
      E P (fun z => F z.1 * G z.2) := by
  rw [contact_q_E_snd P (fun y => ((∑ x, P (x,y) * F x) / stoch_to_det.mY P y) * G y)]
  calc
    _ = ∑ y, (stoch_to_det.mY P y *
        ((∑ x, P (x,y) * F x) / stoch_to_det.mY P y)) * G y := by
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = ∑ y, (∑ x, P (x,y) * F x) * G y := by
      simp_rw [pairCharge_cond_Y_mul hP]
    _ = ∑ y, ∑ x, P (x,y) * (F x * G y) := by
      simp only [Finset.sum_mul, mul_assoc]
    _ = _ := by unfold E; rw [Fintype.sum_prod_type, Finset.sum_comm]

lemma pairCharge_cond_X_mean {P : Law X Y} (hP : stoch_to_det.IsPMF P) (G : Y → ℝ) :
    E P (fun z => (∑ y, P (z.1,y) * G y) / stoch_to_det.mX P z.1) =
      E P (fun z => G z.2) := by
  simpa only [one_mul] using pairCharge_cond_X_inner hP (fun _ => 1) G

lemma pairCharge_cond_Y_mean {P : Law X Y} (hP : stoch_to_det.IsPMF P) (F : X → ℝ) :
    E P (fun z => (∑ x, P (x,z.2) * F x) / stoch_to_det.mY P z.2) =
      E P (fun z => F z.1) := by
  simpa only [mul_one] using pairCharge_cond_Y_inner hP F (fun _ => 1)

lemma pairCharge_cond_X_contraction {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (G : Y → ℝ)
    (hG : E P (fun z => G z.2) = 0) :
    E P (fun z => ((∑ y, P (z.1,y) * G y) / stoch_to_det.mX P z.1)^2) ≤
      E P (fun z => (G z.2)^2) / 4 := by
  let F : X → ℝ := fun x => (∑ y, P (x,y) * G y) / stoch_to_det.mX P x
  have hF : E P (fun z => F z.1) = 0 := by
    dsimp [F]
    rw [pairCharge_cond_X_mean hpair.2.1.1, hG]
  have hinner : E P (fun z => F z.1 * G z.2) = E P (fun z => (F z.1)^2) := by
    have h := pairCharge_cond_X_inner hpair.2.1.1 F G
    simpa only [F, pow_two] using h.symm
  have hcs := pairCharge_maxcorr_sq hpair F G hF hG
  rw [hinner] at hcs
  have hA := contact_E_nonneg hpair.2.1.1 (fun z => (F z.1)^2) (fun _ => sq_nonneg _)
  have hB := contact_E_nonneg hpair.2.1.1 (fun z => (G z.2)^2) (fun _ => sq_nonneg _)
  change E P (fun z => (F z.1)^2) ≤ _
  by_cases hAz : E P (fun z => (F z.1)^2) = 0
  · rw [hAz]
    exact div_nonneg hB (by norm_num)
  · have hApos : 0 < E P (fun z => (F z.1)^2) := lt_of_le_of_ne hA (Ne.symm hAz)
    apply le_of_mul_le_mul_left (a := E P (fun z => (F z.1)^2)) _ hApos
    nlinarith [hcs]

lemma pairCharge_cond_Y_contraction {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (F : X → ℝ)
    (hF : E P (fun z => F z.1) = 0) :
    E P (fun z => ((∑ x, P (x,z.2) * F x) / stoch_to_det.mY P z.2)^2) ≤
      E P (fun z => (F z.1)^2) / 4 := by
  let G : Y → ℝ := fun y => (∑ x, P (x,y) * F x) / stoch_to_det.mY P y
  have hG : E P (fun z => G z.2) = 0 := by
    dsimp [G]
    rw [pairCharge_cond_Y_mean hpair.2.1.1, hF]
  have hinner : E P (fun z => F z.1 * G z.2) = E P (fun z => (G z.2)^2) := by
    have h := pairCharge_cond_Y_inner hpair.2.1.1 F G
    simpa only [G, pow_two] using h.symm
  have hcs := pairCharge_maxcorr_sq hpair F G hF hG
  rw [hinner] at hcs
  have hA := contact_E_nonneg hpair.2.1.1 (fun z => (G z.2)^2) (fun _ => sq_nonneg _)
  have hB := contact_E_nonneg hpair.2.1.1 (fun z => (F z.1)^2) (fun _ => sq_nonneg _)
  change E P (fun z => (G z.2)^2) ≤ _
  by_cases hAz : E P (fun z => (G z.2)^2) = 0
  · rw [hAz]
    exact div_nonneg hB (by norm_num)
  · have hApos : 0 < E P (fun z => (G z.2)^2) := lt_of_le_of_ne hA (Ne.symm hAz)
    apply le_of_mul_le_mul_left (a := E P (fun z => (G z.2)^2)) _ hApos
    nlinarith [hcs]

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_E_sub_scale_sq (P : Law X Y) (F H : X × Y → ℝ) (a : ℝ) :
    E P (fun z => (F z - a * H z)^2) =
      E P (fun z => (F z)^2) - 2 * a * E P (fun z => F z * H z) +
        a^2 * E P (fun z => (H z)^2) := by
  calc
    _ = E P (fun z => ((F z)^2 - (2 * a) * (F z * H z)) + a^2 * (H z)^2) := by
      congr 1
      funext z
      ring
    _ = _ := by
      simp only [contact_q_E_add, contact_q_E_sub, contact_q_E_scale]

lemma pairCharge_S0_norm_le_twice_form {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (F : X → ℝ) (G : Y → ℝ)
    (hF : E P (fun z => F z.1) = 0) (hG : E P (fun z => G z.2) = 0) :
    E P (fun z => (F z.1 -
        2 * ((∑ y, P (z.1,y) * G y) / stoch_to_det.mX P z.1))^2) +
    E P (fun z => (G z.2 -
        2 * ((∑ x, P (x,z.2) * F x) / stoch_to_det.mY P z.2))^2) ≤
    2 * (E P (fun z => (F z.1)^2) + E P (fun z => (G z.2)^2) -
      4 * E P (fun z => F z.1 * G z.2)) := by
  have hX := pairCharge_cond_X_contraction hpair G hG
  have hY := pairCharge_cond_Y_contraction hpair F hF
  have hIX := pairCharge_cond_X_inner hpair.2.1.1 F G
  have hIY := pairCharge_cond_Y_inner hpair.2.1.1 F G
  have hIXsq := pairCharge_E_sub_scale_sq P (fun z => F z.1)
    (fun z => (∑ y, P (z.1,y) * G y) / stoch_to_det.mX P z.1) 2
  have hIYsq := pairCharge_E_sub_scale_sq P (fun z => G z.2)
    (fun z => (∑ x, P (x,z.2) * F x) / stoch_to_det.mY P z.2) 2
  have hIY' : E P (fun z => G z.2 *
      ((∑ x, P (x,z.2) * F x) / stoch_to_det.mY P z.2)) =
      E P (fun z => F z.1 * G z.2) := by
    calc
      _ = E P (fun z => ((∑ x, P (x,z.2) * F x) / stoch_to_det.mY P z.2) * G z.2) := by
        congr 1
        funext z
        ring
      _ = _ := hIY
  rw [hIX] at hIXsq
  rw [hIY'] at hIYsq
  nlinarith [hX, hY, hIXsq, hIYsq]

lemma pairCharge_cond_X_affine {P : Law X Y} (G : Y → ℝ) (a b : ℝ)
    {x : X} (hx : stoch_to_det.mX P x ≠ 0) :
    (∑ y, P (x,y) * (a * G y + b)) / stoch_to_det.mX P x =
      a * ((∑ y, P (x,y) * G y) / stoch_to_det.mX P x) + b := by
  have hsum : (∑ y, P (x,y) * (a * G y + b)) =
      a * (∑ y, P (x,y) * G y) + b * stoch_to_det.mX P x := by
    rw [stoch_to_det.mX_eq_sum]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro y _ <;> ring
  rw [hsum]
  field_simp

lemma pairCharge_cond_Y_affine {P : Law X Y} (F : X → ℝ) (a b : ℝ)
    {y : Y} (hy : stoch_to_det.mY P y ≠ 0) :
    (∑ x, P (x,y) * (a * F x + b)) / stoch_to_det.mY P y =
      a * ((∑ x, P (x,y) * F x) / stoch_to_det.mY P y) + b := by
  have hsum : (∑ x, P (x,y) * (a * F x + b)) =
      a * (∑ x, P (x,y) * F x) + b * stoch_to_det.mY P y := by
    rw [stoch_to_det.mY_eq_sum]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro x _ <;> ring
  rw [hsum]
  field_simp

lemma pairCharge_cond_X_sq_add_one {P : Law X Y} (G : Y → ℝ)
    {x : X} (hx : stoch_to_det.mX P x ≠ 0) :
    (∑ y, P (x,y) * (G y + 1)^2) / stoch_to_det.mX P x =
      (∑ y, P (x,y) * (G y)^2) / stoch_to_det.mX P x +
        2 * ((∑ y, P (x,y) * G y) / stoch_to_det.mX P x) + 1 := by
  have hsum : (∑ y, P (x,y) * (G y + 1)^2) =
      (∑ y, P (x,y) * (G y)^2) + 2 * (∑ y, P (x,y) * G y) +
        stoch_to_det.mX P x := by
    rw [stoch_to_det.mX_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hsum]
  field_simp

lemma pairCharge_cond_Y_sq_add_one {P : Law X Y} (F : X → ℝ)
    {y : Y} (hy : stoch_to_det.mY P y ≠ 0) :
    (∑ x, P (x,y) * (F x + 1)^2) / stoch_to_det.mY P y =
      (∑ x, P (x,y) * (F x)^2) / stoch_to_det.mY P y +
        2 * ((∑ x, P (x,y) * F x) / stoch_to_det.mY P y) + 1 := by
  have hsum : (∑ x, P (x,y) * (F x + 1)^2) =
      (∑ x, P (x,y) * (F x)^2) + 2 * (∑ x, P (x,y) * F x) +
        stoch_to_det.mY P y := by
    rw [stoch_to_det.mY_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum]
  field_simp

lemma pairCharge_contact_defect_X {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) {x : X} (hx : x ∈ XSupport S) :
    (∑ y, P (x,y) * (V P R y)^2) / stoch_to_det.mX P x - (2 * B0 P R - A0 P R) =
      U P R x + A0 P R -
        2 * ((∑ y, P (x,y) * (V P R y + B0 P R)) / stoch_to_det.mX P x) := by
  have hxne := (contact_mX_pos hpair.2.1 hpair.2.2.2.1 hx).ne'
  have hc := (contact_moments hpair).cond_g2 x hx
  have hs := pairCharge_cond_X_sq_add_one (V P R) hxne
  change (∑ y, P (x,y) * (V P R y + 1)^2) / stoch_to_det.mX P x = U P R x + 1 at hc
  have ha := pairCharge_cond_X_affine (V P R) 1 (B0 P R) hxne
  simp only [one_mul] at ha
  rw [hs] at hc
  rw [ha]
  linarith

lemma pairCharge_contact_defect_Y {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) {y : Y} (hy : y ∈ YSupport S) :
    (∑ x, P (x,y) * (U P R x)^2) / stoch_to_det.mY P y - (2 * A0 P R - B0 P R) =
      V P R y + B0 P R -
        2 * ((∑ x, P (x,y) * (U P R x + A0 P R)) / stoch_to_det.mY P y) := by
  have hyne := (contact_mY_pos hpair.2.1 hpair.2.2.2.1 hy).ne'
  have hc := (contact_moments hpair).cond_f2 y hy
  have hs := pairCharge_cond_Y_sq_add_one (U P R) hyne
  change (∑ x, P (x,y) * (U P R x + 1)^2) / stoch_to_det.mY P y = V P R y + 1 at hc
  have ha := pairCharge_cond_Y_affine (U P R) 1 (A0 P R) hyne
  simp only [one_mul] at ha
  rw [hs] at hc
  rw [ha]
  linarith

lemma pairCharge_contact_gram_energy {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    E P (fun z => (U P R z.1 + A0 P R)^2) +
      E P (fun z => (V P R z.2 + B0 P R)^2) -
      4 * E P (fun z => (U P R z.1 + A0 P R) * (V P R z.2 + B0 P R)) =
        6 * A0 P R * B0 P R - (s P R)^2 - J P R := by
  have hm := contact_moments hpair
  have hu := contact_q_E_shift_sq hpair.2.1.1 (fun z => U P R z.1) (A0 P R)
  have hv := contact_q_E_shift_sq hpair.2.1.1 (fun z => V P R z.2) (B0 P R)
  have huv := contact_q_E_shift_prod hpair.2.1.1 (fun z => U P R z.1)
    (fun z => V P R z.2) (A0 P R) (B0 P R)
  rw [hm.U2, (pairCharge_mean_UV hpair).1] at hu
  rw [hm.V2, (pairCharge_mean_UV hpair).2] at hv
  rw [(pairCharge_mean_UV hpair).1, (pairCharge_mean_UV hpair).2] at huv
  have hq := hm.quartic
  have hs := pairCharge_s_eq_A0_add_B0 P R
  rw [hu, hv, huv, hq, hs]
  ring

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_E_congr_positive {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F G : X × Y → ℝ) (hFG : ∀ z, 0 < P z → F z = G z) :
    E P F = E P G := by
  unfold E
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : P z = 0
  · simp [hz]
  · rw [hFG z (lt_of_le_of_ne (hP.nonneg z) (Ne.symm hz))]

lemma pairCharge_mem_S_of_pos {S : Finset (X × Y)} {w P : Law X Y}
    (hP : Contact S w P) {z : X × Y} (hz : 0 < P z) : z ∈ S := by
  by_contra hn
  have hzero := hP.2.1 z hn
  linarith

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_E_mul_zero_of_sq_zero {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F H : X × Y → ℝ) (hF : E P (fun z => (F z)^2) = 0) :
    E P (fun z => H z * F z) = 0 := by
  unfold E
  apply Finset.sum_eq_zero
  intro z _
  by_cases hz : P z = 0
  · simp [hz]
  · have hFz := contact_weighted_sq_zero hP F hF
      (lt_of_le_of_ne (hP.nonneg z) (Ne.symm hz))
    simp [hFz]

lemma pairCharge_contact_defects_norm_le {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    E P (fun z => ((∑ y, P (z.1,y) * (V P R y)^2) / stoch_to_det.mX P z.1 -
        (2 * B0 P R - A0 P R))^2) +
    E P (fun z => ((∑ x, P (x,z.2) * (U P R x)^2) / stoch_to_det.mY P z.2 -
        (2 * A0 P R - B0 P R))^2) ≤
      2 * (6 * A0 P R * B0 P R - (s P R)^2 - J P R) := by
  let F : X → ℝ := fun x => U P R x + A0 P R
  let G : Y → ℝ := fun y => V P R y + B0 P R
  have hF : E P (fun z => F z.1) = 0 := by
    dsimp [F]
    rw [contact_q_E_add, contact_q_E_const hpair.2.1.1, (pairCharge_mean_UV hpair).1]
    ring
  have hG : E P (fun z => G z.2) = 0 := by
    dsimp [G]
    rw [contact_q_E_add, contact_q_E_const hpair.2.1.1, (pairCharge_mean_UV hpair).2]
    ring
  have hnorm := pairCharge_S0_norm_le_twice_form hpair F G hF hG
  have hX : E P (fun z => (F z.1 -
      2 * ((∑ y, P (z.1,y) * G y) / stoch_to_det.mX P z.1))^2) =
      E P (fun z => ((∑ y, P (z.1,y) * (V P R y)^2) / stoch_to_det.mX P z.1 -
        (2 * B0 P R - A0 P R))^2) := by
    apply pairCharge_E_congr_positive hpair.2.1.1
    intro z hz
    dsimp [F, G]
    rw [← pairCharge_contact_defect_X hpair
      (Finset.mem_image.mpr ⟨z, pairCharge_mem_S_of_pos hpair.2.1 hz, rfl⟩)]
  have hY : E P (fun z => (G z.2 -
      2 * ((∑ x, P (x,z.2) * F x) / stoch_to_det.mY P z.2))^2) =
      E P (fun z => ((∑ x, P (x,z.2) * (U P R x)^2) / stoch_to_det.mY P z.2 -
        (2 * A0 P R - B0 P R))^2) := by
    apply pairCharge_E_congr_positive hpair.2.1.1
    intro z hz
    dsimp [F, G]
    rw [← pairCharge_contact_defect_Y hpair
      (Finset.mem_image.mpr ⟨z, pairCharge_mem_S_of_pos hpair.2.1 hz, rfl⟩)]
  rw [hX, hY] at hnorm
  change _ ≤ 2 * (E P (fun z => (U P R z.1 + A0 P R)^2) +
      E P (fun z => (V P R z.2 + B0 P R)^2) -
      4 * E P (fun z => (U P R z.1 + A0 P R) * (V P R z.2 + B0 P R))) at hnorm
  rw [pairCharge_contact_gram_energy hpair] at hnorm
  exact hnorm

lemma pairCharge_J_bound_strict {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    J P R < 6 * A0 P R * B0 P R - (s P R)^2 := by
  have hm := contact_moments hpair
  let DX : X → ℝ := fun x => (∑ y, P (x,y) * (V P R y)^2) / stoch_to_det.mX P x
  let mX : ℝ := 2 * B0 P R - A0 P R
  let DY : Y → ℝ := fun y => (∑ x, P (x,y) * (U P R x)^2) / stoch_to_det.mY P y
  let mY : ℝ := 2 * A0 P R - B0 P R
  have hnorm := pairCharge_contact_defects_norm_le hpair
  change E P (fun z => (DX z.1 - mX)^2) +
    E P (fun z => (DY z.2 - mY)^2) ≤
      2 * (6 * A0 P R * B0 P R - (s P R)^2 - J P R) at hnorm
  have hDXnon := contact_E_nonneg hpair.2.1.1 (fun z => (DX z.1 - mX)^2) (fun _ => sq_nonneg _)
  have hDYnon := contact_E_nonneg hpair.2.1.1 (fun z => (DY z.2 - mY)^2) (fun _ => sq_nonneg _)
  by_contra hn
  have henergy : 6 * A0 P R * B0 P R - (s P R)^2 - J P R = 0 := by
    linarith [hm.J_bound]
  have hDXzero : E P (fun z => (DX z.1 - mX)^2) = 0 := by linarith
  have hzero := pairCharge_E_mul_zero_of_sq_zero hpair.2.1.1
    (fun z => DX z.1 - mX) (fun z => (U P R z.1)^2) hDXzero
  have hinner := pairCharge_cond_X_inner hpair.2.1.1
    (fun x => (U P R x)^2) (fun y => (V P R y)^2)
  change E P (fun z => (U P R z.1)^2 * DX z.1) = J P R at hinner
  have hprod : E P (fun z => (U P R z.1)^2 * (DX z.1 - mX)) =
      J P R - mX * E P (fun z => (U P R z.1)^2) := by
    calc
      _ = E P (fun z => (U P R z.1)^2 * DX z.1 -
          mX * (U P R z.1)^2) := by
        congr 1
        funext z
        ring
      _ = _ := by rw [contact_q_E_sub, contact_q_E_scale, hinner]
  rw [hprod, hm.U2] at hzero
  have hs := pairCharge_s_eq_A0_add_B0 P R
  dsimp [mX] at hzero
  have hspos : 0 < (s P R)^2 := sq_pos_of_pos hm.s_pos
  have hb := hm.scalar_bound
  rw [hs] at henergy hspos hb
  nlinarith [hzero, henergy, hb]

lemma pairCharge_gram_t0_pos {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    0 < 6 * (A0 P R * B0 P R / (s P R)^2) - 1 - contactj P R := by
  have hm := contact_moments hpair
  have hstrict := pairCharge_J_bound_strict hpair
  have hspos : 0 < (s P R)^2 := sq_pos_of_pos hm.s_pos
  apply (mul_pos_iff_of_pos_right hspos).mp
  unfold contactj
  have hid : (6 * (A0 P R * B0 P R / (s P R)^2) - 1 - J P R / (s P R)^2) *
      (s P R)^2 = 6 * A0 P R * B0 P R - (s P R)^2 - J P R := by
    field_simp [hm.s_pos.ne']
  rw [hid]
  linarith

lemma pairCharge_contactj_lt_half {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) : contactj P R < (1 : ℝ) / 2 := by
  have ht := pairCharge_gram_t0_pos hpair
  have hv := (pairCharge_v_bounds hpair).2
  linarith

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_E_lincomb_sq (P : Law X Y) (F H : X × Y → ℝ) (a b : ℝ) :
    E P (fun z => (a * F z + b * H z)^2) =
      a^2 * E P (fun z => (F z)^2) +
      2 * a * b * E P (fun z => F z * H z) +
      b^2 * E P (fun z => (H z)^2) := by
  calc
    _ = E P (fun z => (a^2 * (F z)^2 + (2 * a * b) * (F z * H z)) +
        b^2 * (H z)^2) := by
      congr 1
      funext z
      ring
    _ = _ := by simp only [contact_q_E_add, contact_q_E_scale]

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_E_lincomb_prod (P : Law X Y) (F G H K : X × Y → ℝ) (a b : ℝ) :
    E P (fun z => (a * F z + b * H z) * (a * G z + b * K z)) =
      a^2 * E P (fun z => F z * G z) +
      a * b * (E P (fun z => F z * K z) + E P (fun z => H z * G z)) +
      b^2 * E P (fun z => H z * K z) := by
  calc
    _ = E P (fun z => (a^2 * (F z * G z) +
        (a * b) * (F z * K z + H z * G z)) + b^2 * (H z * K z)) := by
      congr 1
      funext z
      ring
    _ = _ := by
      simp only [contact_q_E_add, contact_q_E_scale]

lemma pairCharge_psd_gram {a b c : ℝ} (ha : 0 < a)
    (h : ∀ u v : ℝ, 0 ≤ a * u^2 + 2 * b * u * v + c * v^2) :
    b^2 ≤ a * c := by
  apply (mul_le_mul_iff_of_pos_left ha).mp
  have hh := h b (-a)
  nlinarith [hh]

lemma pairCharge_hessian_gram {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R)
    (F H : X → ℝ) (G K : Y → ℝ)
    (hF : E P (fun z => F z.1) = 0) (hG : E P (fun z => G z.2) = 0)
    (hH : E P (fun z => H z.1) = 0) (hK : E P (fun z => K z.2) = 0)
    (ha : 0 < E P (fun z => (F z.1)^2) + E P (fun z => (G z.2)^2) -
      4 * E P (fun z => F z.1 * G z.2)) :
    (E P (fun z => F z.1 * H z.1) + E P (fun z => G z.2 * K z.2) -
      2 * E P (fun z => F z.1 * K z.2) - 2 * E P (fun z => H z.1 * G z.2))^2 ≤
      (E P (fun z => (F z.1)^2) + E P (fun z => (G z.2)^2) -
        4 * E P (fun z => F z.1 * G z.2)) *
      (E P (fun z => (H z.1)^2) + E P (fun z => (K z.2)^2) -
        4 * E P (fun z => H z.1 * K z.2)) := by
  apply pairCharge_psd_gram ha
  intro a b
  have hcenterX : E P (fun z => a * F z.1 + b * H z.1) = 0 := by
    rw [contact_q_E_add, contact_q_E_scale, contact_q_E_scale, hF, hH]
    ring
  have hcenterY : E P (fun z => a * G z.2 + b * K z.2) = 0 := by
    rw [contact_q_E_add, contact_q_E_scale, contact_q_E_scale, hG, hK]
    ring
  have hh := (contact_moments hpair).hessian (fun x => a * F x + b * H x)
    (fun y => a * G y + b * K y) hcenterX hcenterY
  rw [pairCharge_E_lincomb_sq, pairCharge_E_lincomb_sq, pairCharge_E_lincomb_prod] at hh
  nlinarith [hh]

lemma pairCharge_S0_bilinear {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F H : X → ℝ) (G K : Y → ℝ) :
    E P (fun z => F z.1 * H z.1) + E P (fun z => G z.2 * K z.2) -
      2 * E P (fun z => F z.1 * K z.2) - 2 * E P (fun z => H z.1 * G z.2) =
    E P (fun z => (F z.1 -
      2 * ((∑ y, P (z.1,y) * G y) / stoch_to_det.mX P z.1)) * H z.1) +
    E P (fun z => (G z.2 -
      2 * ((∑ x, P (x,z.2) * F x) / stoch_to_det.mY P z.2)) * K z.2) := by
  have hX : E P (fun z => (F z.1 -
      2 * ((∑ y, P (z.1,y) * G y) / stoch_to_det.mX P z.1)) * H z.1) =
      E P (fun z => F z.1 * H z.1) - 2 * E P (fun z => H z.1 * G z.2) := by
    calc
      _ = E P (fun z => F z.1 * H z.1 -
          2 * (H z.1 * ((∑ y, P (z.1,y) * G y) / stoch_to_det.mX P z.1))) := by
        congr 1
        funext z
        ring
      _ = _ := by rw [contact_q_E_sub, contact_q_E_scale, pairCharge_cond_X_inner hP]
  have hY : E P (fun z => (G z.2 -
      2 * ((∑ x, P (x,z.2) * F x) / stoch_to_det.mY P z.2)) * K z.2) =
      E P (fun z => G z.2 * K z.2) - 2 * E P (fun z => F z.1 * K z.2) := by
    calc
      _ = E P (fun z => G z.2 * K z.2 -
          2 * (((∑ x, P (x,z.2) * F x) / stoch_to_det.mY P z.2) * K z.2)) := by
        congr 1
        funext z
        ring
      _ = _ := by rw [contact_q_E_sub, contact_q_E_scale, pairCharge_cond_Y_inner hP]
  rw [hX, hY]
  ring

lemma pairCharge_contact_defects_centered {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    E P (fun z => (∑ y, P (z.1,y) * (V P R y)^2) / stoch_to_det.mX P z.1 -
      (2 * B0 P R - A0 P R)) = 0 ∧
    E P (fun z => (∑ x, P (x,z.2) * (U P R x)^2) / stoch_to_det.mY P z.2 -
      (2 * A0 P R - B0 P R)) = 0 := by
  constructor
  · rw [contact_q_E_sub, contact_q_E_const hpair.2.1.1, pairCharge_cond_X_mean hpair.2.1.1, (contact_moments hpair).V2]
    ring
  · rw [contact_q_E_sub, contact_q_E_const hpair.2.1.1, pairCharge_cond_Y_mean hpair.2.1.1, (contact_moments hpair).U2]
    ring

lemma pairCharge_contact_defects_gram {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    let H : X → ℝ := fun x =>
      (∑ y, P (x,y) * (V P R y)^2) / stoch_to_det.mX P x - (2 * B0 P R - A0 P R)
    let K : Y → ℝ := fun y =>
      (∑ x, P (x,y) * (U P R x)^2) / stoch_to_det.mY P y - (2 * A0 P R - B0 P R)
    (E P (fun z => (H z.1)^2) + E P (fun z => (K z.2)^2))^2 ≤
      (6 * A0 P R * B0 P R - (s P R)^2 - J P R) *
      (E P (fun z => (H z.1)^2) + E P (fun z => (K z.2)^2) -
        4 * E P (fun z => H z.1 * K z.2)) := by
  let H : X → ℝ := fun x =>
    (∑ y, P (x,y) * (V P R y)^2) / stoch_to_det.mX P x - (2 * B0 P R - A0 P R)
  let K : Y → ℝ := fun y =>
    (∑ x, P (x,y) * (U P R x)^2) / stoch_to_det.mY P y - (2 * A0 P R - B0 P R)
  let F : X → ℝ := fun x => U P R x + A0 P R
  let G : Y → ℝ := fun y => V P R y + B0 P R
  change (E P (fun z => (H z.1)^2) + E P (fun z => (K z.2)^2))^2 ≤ _
  have hF : E P (fun z => F z.1) = 0 := by
    dsimp [F]
    rw [contact_q_E_add, contact_q_E_const hpair.2.1.1, (pairCharge_mean_UV hpair).1]
    ring
  have hG : E P (fun z => G z.2) = 0 := by
    dsimp [G]
    rw [contact_q_E_add, contact_q_E_const hpair.2.1.1, (pairCharge_mean_UV hpair).2]
    ring
  have hH : E P (fun z => H z.1) = 0 := (pairCharge_contact_defects_centered hpair).1
  have hK : E P (fun z => K z.2) = 0 := (pairCharge_contact_defects_centered hpair).2
  have henergy : E P (fun z => (F z.1)^2) + E P (fun z => (G z.2)^2) -
      4 * E P (fun z => F z.1 * G z.2) =
      6 * A0 P R * B0 P R - (s P R)^2 - J P R := pairCharge_contact_gram_energy hpair
  have henergypos : 0 < E P (fun z => (F z.1)^2) + E P (fun z => (G z.2)^2) -
      4 * E P (fun z => F z.1 * G z.2) := by
    rw [henergy]
    linarith [pairCharge_J_bound_strict hpair]
  have hgram := pairCharge_hessian_gram hpair F H G K hF hG hH hK henergypos
  have hbilinear := pairCharge_S0_bilinear hpair.2.1.1 F H G K
  have hX : E P (fun z => (F z.1 -
      2 * ((∑ y, P (z.1,y) * G y) / stoch_to_det.mX P z.1)) * H z.1) =
      E P (fun z => (H z.1)^2) := by
    apply pairCharge_E_congr_positive hpair.2.1.1
    intro z hz
    dsimp [F, G]
    rw [← pairCharge_contact_defect_X hpair
      (Finset.mem_image.mpr ⟨z, pairCharge_mem_S_of_pos hpair.2.1 hz, rfl⟩)]
    change H z.1 * H z.1 = (H z.1)^2
    ring
  have hY : E P (fun z => (G z.2 -
      2 * ((∑ x, P (x,z.2) * F x) / stoch_to_det.mY P z.2)) * K z.2) =
      E P (fun z => (K z.2)^2) := by
    apply pairCharge_E_congr_positive hpair.2.1.1
    intro z hz
    dsimp [F, G]
    rw [← pairCharge_contact_defect_Y hpair
      (Finset.mem_image.mpr ⟨z, pairCharge_mem_S_of_pos hpair.2.1 hz, rfl⟩)]
    change K z.2 * K z.2 = (K z.2)^2
    ring
  rw [hX, hY] at hbilinear
  rw [hbilinear, henergy] at hgram
  exact hgram

omit [DecidableEq Y] in
lemma pairCharge_cond_X_linear (P : Law X Y) (G H : Y → ℝ) (a b : ℝ) (x : X) :
    (∑ y, P (x,y) * (a * G y + b * H y)) / stoch_to_det.mX P x =
      a * ((∑ y, P (x,y) * G y) / stoch_to_det.mX P x) +
      b * ((∑ y, P (x,y) * H y) / stoch_to_det.mX P x) := by
  have hi (y : Y) : P (x,y) * (a * G y + b * H y) =
      a * (P (x,y) * G y) + b * (P (x,y) * H y) := by ring
  simp_rw [hi]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

omit [DecidableEq X] in
lemma pairCharge_cond_Y_linear (P : Law X Y) (F H : X → ℝ) (a b : ℝ) (y : Y) :
    (∑ x, P (x,y) * (a * F x + b * H x)) / stoch_to_det.mY P y =
      a * ((∑ x, P (x,y) * F x) / stoch_to_det.mY P y) +
      b * ((∑ x, P (x,y) * H x) / stoch_to_det.mY P y) := by
  have hi (x : X) : P (x,y) * (a * F x + b * H x) =
      a * (P (x,y) * F x) + b * (P (x,y) * H x) := by ring
  simp_rw [hi]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_E_mul_comm (P : Law X Y) (F G : X × Y → ℝ) :
    E P (fun z => F z * G z) = E P (fun z => G z * F z) := by
  congr 1
  funext z
  ring

lemma pairCharge_raw_gram_bounds {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    let H : X → ℝ := fun x =>
      (∑ y, P (x,y) * (V P R y)^2) / stoch_to_det.mX P x - (2 * B0 P R - A0 P R)
    let K : Y → ℝ := fun y =>
      (∑ x, P (x,y) * (U P R x)^2) / stoch_to_det.mY P y - (2 * A0 P R - B0 P R)
    let t0 := 6 * (A0 P R * B0 P R / (s P R)^2) - 1 - contactj P R
    let xP := (E P (fun z => (H z.1)^2) + E P (fun z => (K z.2)^2)) / (s P R)^2
    let cP := 2 * E P (fun z => H z.1 * K z.2) / (s P R)^2
    0 < t0 ∧ 0 ≤ xP ∧ xP ≤ 2 * t0 ∧ cP ≤ xP / 2 - xP^2 / (2 * t0) := by
  let H : X → ℝ := fun x =>
    (∑ y, P (x,y) * (V P R y)^2) / stoch_to_det.mX P x - (2 * B0 P R - A0 P R)
  let K : Y → ℝ := fun y =>
    (∑ x, P (x,y) * (U P R x)^2) / stoch_to_det.mY P y - (2 * A0 P R - B0 P R)
  let T := 6 * A0 P R * B0 P R - (s P R)^2 - J P R
  let t0 := 6 * (A0 P R * B0 P R / (s P R)^2) - 1 - contactj P R
  let n := E P (fun z => (H z.1)^2) + E P (fun z => (K z.2)^2)
  let e := E P (fun z => H z.1 * K z.2)
  let xP := n / (s P R)^2
  let cP := 2 * e / (s P R)^2
  change 0 < t0 ∧ 0 ≤ xP ∧ xP ≤ 2 * t0 ∧ cP ≤ xP / 2 - xP^2 / (2 * t0)
  have ht : 0 < t0 := pairCharge_gram_t0_pos hpair
  have hn : 0 ≤ n := add_nonneg
    (contact_E_nonneg hpair.2.1.1 (fun z => (H z.1)^2) (fun _ => sq_nonneg _))
    (contact_E_nonneg hpair.2.1.1 (fun z => (K z.2)^2) (fun _ => sq_nonneg _))
  have hnorm : n ≤ 2 * T := pairCharge_contact_defects_norm_le hpair
  have hgram : n^2 ≤ T * (n - 4 * e) := pairCharge_contact_defects_gram hpair
  have hs := (contact_moments hpair).s_pos
  have hs2 : 0 < (s P R)^2 := sq_pos_of_pos hs
  have hs4 : 0 < (s P R)^4 := pow_pos hs 4
  have hT : T = t0 * (s P R)^2 := by
    dsimp [T, t0, contactj]
    field_simp [hs.ne']
  have hx : 0 ≤ xP := div_nonneg hn hs2.le
  have hxhi : xP ≤ 2 * t0 := by
    apply (div_le_iff₀ hs2).2
    rw [hT] at hnorm
    nlinarith [hnorm]
  have hxgram : xP^2 ≤ t0 * (xP - 2 * cP) := by
    apply (mul_le_mul_iff_of_pos_right hs4).mp
    have hid : (xP^2 - t0 * (xP - 2 * cP)) * (s P R)^4 =
        n^2 - T * (n - 4 * e) := by
      rw [hT]
      dsimp [xP, cP]
      field_simp [hs.ne']
      ring
    nlinarith [hid, hgram]
  refine ⟨ht, hx, hxhi, ?_⟩
  have hden : 0 < 2 * t0 := by positivity
  have hquot : xP^2 / (2 * t0) * (2 * t0) = xP^2 := div_mul_cancel₀ _ hden.ne'
  apply (mul_le_mul_iff_of_pos_right hden).mp
  nlinarith [hxgram, hquot]

lemma pairCharge_cond_X_congr_support {S : Finset (X × Y)} {w P : Law X Y}
    (hP : Contact S w P) (G H : Y → ℝ)
    (hGH : ∀ y ∈ YSupport S, G y = H y) (x : X) :
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
    (hP : Contact S w P) (F H : X → ℝ)
    (hFH : ∀ x ∈ XSupport S, F x = H x) (y : Y) :
    (∑ x, P (x,y) * F x) / stoch_to_det.mY P y =
      (∑ x, P (x,y) * H x) / stoch_to_det.mY P y := by
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hz : P (x,y) = 0
  · simp [hz]
  · have hzpos : 0 < P (x,y) := lt_of_le_of_ne (hP.1.nonneg _) (Ne.symm hz)
    rw [hFH x (Finset.mem_image.mpr ⟨(x,y), pairCharge_mem_S_of_pos hP hzpos, rfl⟩)]

-- Finite algebra for the global sum-of-squares certificate. No eigenvalue or Hilbert-space
-- infrastructure is used.

lemma pairCharge_operator_sos_identity {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (hK : ∀ x y, B (K x) y = B x (K y)) (w : V) :
    let d := w - (2 : ℝ) • K w
    let p := K (K w) + (19/12 : ℝ) • K w - (11/20 : ℝ) • w
    let q := K w - (243/787 : ℝ) • w
    let y := d + (2 : ℝ) • K d + K (K d)
    (17/10 : ℝ) * B w (w - (2 : ℝ) • K w) + (23/4 : ℝ) * B d d -
        B d ((5 : ℝ) • y + (3 : ℝ) • K y) =
      6 * B p (p - (2 : ℝ) • K p) +
      (787/120 : ℝ) * B q (q - (2 : ℝ) • K q) +
      (767/78700 : ℝ) * B w (w - (2 : ℝ) • K w) := by
  dsimp only
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, hK]
  ring

lemma pairCharge_operator_sos_bound {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (hK : ∀ x y, B (K x) y = B x (K y)) (w : V)
    (h0 : 0 ≤ B w (w - (2 : ℝ) • K w))
    (hp : let p := K (K w) + (19/12 : ℝ) • K w - (11/20 : ℝ) • w
      0 ≤ B p (p - (2 : ℝ) • K p))
    (hq : let q := K w - (243/787 : ℝ) • w
      0 ≤ B q (q - (2 : ℝ) • K q)) :
    let d := w - (2 : ℝ) • K w
    let y := d + (2 : ℝ) • K d + K (K d)
    B d ((5 : ℝ) • y + (3 : ℝ) • K y) ≤
      (17/10 : ℝ) * B w (w - (2 : ℝ) • K w) + (23/4 : ℝ) * B d d := by
  have hid := pairCharge_operator_sos_identity B K hK w
  dsimp only at hp hq hid ⊢
  linarith [hp, hq, h0]

lemma pairCharge_finite_conditional_geometry {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    ∃ (B : ((X → ℝ) × (Y → ℝ)) →ₗ[ℝ] ((X → ℝ) × (Y → ℝ)) →ₗ[ℝ] ℝ)
      (K : ((X → ℝ) × (Y → ℝ)) →ₗ[ℝ] ((X → ℝ) × (Y → ℝ))),
    (∀ p q, B p q = E P (fun z => p.1 z.1 * q.1 z.1) +
      E P (fun z => p.2 z.2 * q.2 z.2)) ∧
    (∀ p, (K p).1 = fun x => (∑ y, P (x,y) * p.2 y) / stoch_to_det.mX P x) ∧
    (∀ p, (K p).2 = fun y => (∑ x, P (x,y) * p.1 x) / stoch_to_det.mY P y) ∧
    (∀ p q, B (K p) q = B p (K q)) ∧
    (∀ p, E P (fun z => p.1 z.1) = 0 → E P (fun z => p.2 z.2) = 0 →
      0 ≤ B p (p - (2 : ℝ) • K p)) ∧
    (∀ p, E P (fun z => p.1 z.1) = 0 → E P (fun z => p.2 z.2) = 0 →
      E P (fun z => (K p).1 z.1) = 0 ∧ E P (fun z => (K p).2 z.2) = 0) := by
  let B : ((X → ℝ) × (Y → ℝ)) →ₗ[ℝ] ((X → ℝ) × (Y → ℝ)) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ
      (fun p q => E P (fun z => p.1 z.1 * q.1 z.1) + E P (fun z => p.2 z.2 * q.2 z.2))
      (by
        intro p q r
        change E P (fun z => (p.1 z.1 + q.1 z.1) * r.1 z.1) +
          E P (fun z => (p.2 z.2 + q.2 z.2) * r.2 z.2) = _
        simp only [add_mul, contact_q_E_add]
        ring)
      (by
        intro a p q
        change E P (fun z => (a * p.1 z.1) * q.1 z.1) +
          E P (fun z => (a * p.2 z.2) * q.2 z.2) = a * _
        simp only [mul_assoc, contact_q_E_scale]
        ring)
      (by
        intro p q r
        change E P (fun z => p.1 z.1 * (q.1 z.1 + r.1 z.1)) +
          E P (fun z => p.2 z.2 * (q.2 z.2 + r.2 z.2)) = _
        simp only [mul_add, contact_q_E_add]
        ring)
      (by
        intro a p q
        change E P (fun z => p.1 z.1 * (a * q.1 z.1)) +
          E P (fun z => p.2 z.2 * (a * q.2 z.2)) = a * _
        simp_rw [show ∀ z : X × Y, p.1 z.1 * (a * q.1 z.1) = a * (p.1 z.1 * q.1 z.1) by intro z; ring,
          show ∀ z : X × Y, p.2 z.2 * (a * q.2 z.2) = a * (p.2 z.2 * q.2 z.2) by intro z; ring]
        rw [contact_q_E_scale, contact_q_E_scale]
        ring)
  let K : ((X → ℝ) × (Y → ℝ)) →ₗ[ℝ] ((X → ℝ) × (Y → ℝ)) :=
    { toFun := fun p =>
        (fun x => (∑ y, P (x,y) * p.2 y) / stoch_to_det.mX P x,
         fun y => (∑ x, P (x,y) * p.1 x) / stoch_to_det.mY P y)
      map_add' := by
        intro p q
        apply Prod.ext
        · funext x
          change (∑ y, P (x,y) * (p.2 y + q.2 y)) / stoch_to_det.mX P x =
            (∑ y, P (x,y) * p.2 y) / stoch_to_det.mX P x +
            (∑ y, P (x,y) * q.2 y) / stoch_to_det.mX P x
          simpa only [one_mul] using pairCharge_cond_X_linear P p.2 q.2 1 1 x
        · funext y
          change (∑ x, P (x,y) * (p.1 x + q.1 x)) / stoch_to_det.mY P y =
            (∑ x, P (x,y) * p.1 x) / stoch_to_det.mY P y +
            (∑ x, P (x,y) * q.1 x) / stoch_to_det.mY P y
          simpa only [one_mul] using pairCharge_cond_Y_linear P p.1 q.1 1 1 y
      map_smul' := by
        intro a p
        apply Prod.ext
        · funext x
          change (∑ y, P (x,y) * (a * p.2 y)) / stoch_to_det.mX P x =
            a * ((∑ y, P (x,y) * p.2 y) / stoch_to_det.mX P x)
          simpa only [zero_mul, add_zero, Finset.sum_const_zero, zero_div] using
            pairCharge_cond_X_linear P p.2 (fun _ => 0) a 0 x
        · funext y
          change (∑ x, P (x,y) * (a * p.1 x)) / stoch_to_det.mY P y =
            a * ((∑ x, P (x,y) * p.1 x) / stoch_to_det.mY P y)
          simpa only [zero_mul, add_zero, Finset.sum_const_zero, zero_div] using
            pairCharge_cond_Y_linear P p.1 (fun _ => 0) a 0 y }
  have hB (p q : (X → ℝ) × (Y → ℝ)) :
      B p q = E P (fun z => p.1 z.1 * q.1 z.1) +
        E P (fun z => p.2 z.2 * q.2 z.2) := rfl
  have hKX (p : (X → ℝ) × (Y → ℝ)) :
      (K p).1 = fun x => (∑ y, P (x,y) * p.2 y) / stoch_to_det.mX P x := rfl
  have hKY (p : (X → ℝ) × (Y → ℝ)) :
      (K p).2 = fun y => (∑ x, P (x,y) * p.1 x) / stoch_to_det.mY P y := rfl
  have hcross (p q : (X → ℝ) × (Y → ℝ)) :
      B p (K q) = E P (fun z => p.1 z.1 * q.2 z.2) +
        E P (fun z => q.1 z.1 * p.2 z.2) := by
    rw [hB, hKX, hKY]
    rw [pairCharge_cond_X_inner hpair.2.1.1]
    rw [pairCharge_E_mul_comm P (fun z => p.2 z.2)
      (fun z => (∑ x, P (x,z.2) * q.1 x) / stoch_to_det.mY P z.2)]
    rw [pairCharge_cond_Y_inner hpair.2.1.1]
  refine ⟨B, K, hB, hKX, hKY, ?_, ?_, ?_⟩
  · intro p q
    rw [hB, hKX, hKY]
    rw [pairCharge_E_mul_comm P
      (fun z => (∑ y, P (z.1,y) * p.2 y) / stoch_to_det.mX P z.1) (fun z => q.1 z.1)]
    rw [pairCharge_cond_X_inner hpair.2.1.1, pairCharge_cond_Y_inner hpair.2.1.1, hcross]
    ring
  · intro p hpX hpY
    rw [map_sub, map_smul, smul_eq_mul, hB, hcross]
    have hh := (contact_moments hpair).hessian p.1 p.2 hpX hpY
    simp only [← pow_two]
    linarith
  · intro p hpX hpY
    rw [hKX, hKY, pairCharge_cond_X_mean hpair.2.1.1, pairCharge_cond_Y_mean hpair.2.1.1, hpX, hpY]
    exact ⟨rfl, rfl⟩

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_operator_sos_centered_pair {P : Law X Y}
    (B : ((X → ℝ) × (Y → ℝ)) →ₗ[ℝ] ((X → ℝ) × (Y → ℝ)) →ₗ[ℝ] ℝ)
    (K : ((X → ℝ) × (Y → ℝ)) →ₗ[ℝ] ((X → ℝ) × (Y → ℝ)))
    (hK : ∀ p q, B (K p) q = B p (K q))
    (hpos : ∀ p, E P (fun z => p.1 z.1) = 0 → E P (fun z => p.2 z.2) = 0 →
      0 ≤ B p (p - (2 : ℝ) • K p))
    (hmean : ∀ p, E P (fun z => p.1 z.1) = 0 → E P (fun z => p.2 z.2) = 0 →
      E P (fun z => (K p).1 z.1) = 0 ∧ E P (fun z => (K p).2 z.2) = 0)
    (F : X → ℝ) (G : Y → ℝ)
    (hF : E P (fun z => F z.1) = 0) (hG : E P (fun z => G z.2) = 0) :
    let u : (X → ℝ) × (Y → ℝ) := (F,G)
    let d := u - (2 : ℝ) • K u
    let y := d + (2 : ℝ) • K d + K (K d)
    B d ((5 : ℝ) • y + (3 : ℝ) • K y) ≤
      (17/10 : ℝ) * B u (u - (2 : ℝ) • K u) + (23/4 : ℝ) * B d d := by
  let u : (X → ℝ) × (Y → ℝ) := (F,G)
  have huX : E P (fun z => u.1 z.1) = 0 := hF
  have huY : E P (fun z => u.2 z.2) = 0 := hG
  have h1 := hmean u huX huY
  have h2 := hmean (K u) h1.1 h1.2
  have hpX : E P (fun z =>
      (K (K u) + (19/12 : ℝ) • K u - (11/20 : ℝ) • u).1 z.1) = 0 := by
    change E P (fun z => ((K (K u)).1 z.1 + (19/12 : ℝ) * (K u).1 z.1) -
      (11/20 : ℝ) * u.1 z.1) = 0
    rw [contact_q_E_sub, contact_q_E_add, contact_q_E_scale, contact_q_E_scale, h2.1, h1.1, huX]
    ring
  have hpY : E P (fun z =>
      (K (K u) + (19/12 : ℝ) • K u - (11/20 : ℝ) • u).2 z.2) = 0 := by
    change E P (fun z => ((K (K u)).2 z.2 + (19/12 : ℝ) * (K u).2 z.2) -
      (11/20 : ℝ) * u.2 z.2) = 0
    rw [contact_q_E_sub, contact_q_E_add, contact_q_E_scale, contact_q_E_scale, h2.2, h1.2, huY]
    ring
  have hqX : E P (fun z => (K u - (243/787 : ℝ) • u).1 z.1) = 0 := by
    change E P (fun z => (K u).1 z.1 - (243/787 : ℝ) * u.1 z.1) = 0
    rw [contact_q_E_sub, contact_q_E_scale, h1.1, huX]
    ring
  have hqY : E P (fun z => (K u - (243/787 : ℝ) • u).2 z.2) = 0 := by
    change E P (fun z => (K u).2 z.2 - (243/787 : ℝ) * u.2 z.2) = 0
    rw [contact_q_E_sub, contact_q_E_scale, h1.2, huY]
    ring
  exact pairCharge_operator_sos_bound B K hK u
    (hpos u huX huY)
    (hpos _ hpX hpY)
    (hpos _ hqX hqY)

lemma pairCharge_additive_variance_geometry {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (B : ((X → ℝ) × (Y → ℝ)) →ₗ[ℝ] ((X → ℝ) × (Y → ℝ)) →ₗ[ℝ] ℝ)
    (K : ((X → ℝ) × (Y → ℝ)) →ₗ[ℝ] ((X → ℝ) × (Y → ℝ)))
    (hB : ∀ p q, B p q = E P (fun z => p.1 z.1 * q.1 z.1) +
      E P (fun z => p.2 z.2 * q.2 z.2))
    (hKX : ∀ p, (K p).1 = fun x => (∑ y, P (x,y) * p.2 y) / stoch_to_det.mX P x)
    (hKY : ∀ p, (K p).2 = fun y => (∑ x, P (x,y) * p.1 x) / stoch_to_det.mY P y)
    (p : (X → ℝ) × (Y → ℝ))
    (hpX : E P (fun z => p.1 z.1) = 0) (hpY : E P (fun z => p.2 z.2) = 0) :
    E (productLaw P) (fun z => (p.1 z.1 + p.2 z.2)^2) = B p p ∧
      E P (fun z => (p.1 z.1 + p.2 z.2)^2) = B p p + B p (K p) := by
  have hcross : B p (K p) = 2 * E P (fun z => p.1 z.1 * p.2 z.2) := by
    rw [hB, hKX, hKY, pairCharge_cond_X_inner hP]
    rw [pairCharge_E_mul_comm P (fun z => p.2 z.2)
      (fun z => (∑ x, P (x,z.2) * p.1 x) / stoch_to_det.mY P z.2)]
    rw [pairCharge_cond_Y_inner hP]
    ring
  have hQ := pairCharge_E_lincomb_sq (productLaw P) (fun z => p.1 z.1) (fun z => p.2 z.2) 1 1
  have hJ := pairCharge_E_lincomb_sq P (fun z => p.1 z.1) (fun z => p.2 z.2) 1 1
  norm_num at hQ hJ
  rw [pairCharge_E_product_fst hP (fun x => (p.1 x)^2),
    pairCharge_E_product_snd hP (fun y => (p.2 y)^2),
    pairCharge_E_product P p.1 p.2, hpX, hpY] at hQ
  have hdiag : B p p = E P (fun z => (p.1 z.1)^2) + E P (fun z => (p.2 z.2)^2) := by
    rw [hB]
    simp only [pow_two]
  constructor <;> linarith [hQ, hJ, hdiag, hcross]

lemma pairCharge_operator_additive_variance_identity {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (hK : ∀ x y, B (K x) y = B x (K y)) (d : V) :
    let p := d + K d
    let y := d + (2 : ℝ) • K d + K (K d)
    B p ((5 : ℝ) • p + (3 : ℝ) • K p) =
      B d ((5 : ℝ) • y + (3 : ℝ) • K y) := by
  dsimp only
  simp only [map_add, map_smul, LinearMap.add_apply, smul_eq_mul, hK]
  ring

lemma pairCharge_contact_additive_variance_bound {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R)
    (B : ((X → ℝ) × (Y → ℝ)) →ₗ[ℝ] ((X → ℝ) × (Y → ℝ)) →ₗ[ℝ] ℝ)
    (K : ((X → ℝ) × (Y → ℝ)) →ₗ[ℝ] ((X → ℝ) × (Y → ℝ)))
    (hB : ∀ p q, B p q = E P (fun z => p.1 z.1 * q.1 z.1) +
      E P (fun z => p.2 z.2 * q.2 z.2))
    (hKX : ∀ p, (K p).1 = fun x => (∑ y, P (x,y) * p.2 y) / stoch_to_det.mX P x)
    (hKY : ∀ p, (K p).2 = fun y => (∑ x, P (x,y) * p.1 x) / stoch_to_det.mY P y)
    (hself : ∀ p q, B (K p) q = B p (K q))
    (hpos : ∀ p, E P (fun z => p.1 z.1) = 0 → E P (fun z => p.2 z.2) = 0 →
      0 ≤ B p (p - (2 : ℝ) • K p))
    (hmean : ∀ p, E P (fun z => p.1 z.1) = 0 → E P (fun z => p.2 z.2) = 0 →
      E P (fun z => (K p).1 z.1) = 0 ∧ E P (fun z => (K p).2 z.2) = 0) :
    let u : (X → ℝ) × (Y → ℝ) := (fun x => U P R x + A0 P R, fun y => V P R y + B0 P R)
    let d := u - (2 : ℝ) • K u
    let p := d + K d
    let C : X × Y → ℝ := fun z => (p.1 z.1 + p.2 z.2) / s P R
    60 * (s P R)^2 *
      (E (productLaw P) (fun z => (C z)^2) / 30 + E P (fun z => (C z)^2) / 20) ≤
      (17/10 : ℝ) * (6 * A0 P R * B0 P R - (s P R)^2 - J P R) +
        (23/4 : ℝ) * B d d := by
  let u : (X → ℝ) × (Y → ℝ) := (fun x => U P R x + A0 P R, fun y => V P R y + B0 P R)
  let d := u - (2 : ℝ) • K u
  let p := d + K d
  let C : X × Y → ℝ := fun z => (p.1 z.1 + p.2 z.2) / s P R
  change 60 * (s P R)^2 *
    (E (productLaw P) (fun z => (C z)^2) / 30 + E P (fun z => (C z)^2) / 20) ≤ _
  have huX : E P (fun z => u.1 z.1) = 0 := by
    dsimp [u]
    rw [contact_q_E_add, contact_q_E_const hpair.2.1.1, (pairCharge_mean_UV hpair).1]
    ring
  have huY : E P (fun z => u.2 z.2) = 0 := by
    dsimp [u]
    rw [contact_q_E_add, contact_q_E_const hpair.2.1.1, (pairCharge_mean_UV hpair).2]
    ring
  have hKu := hmean u huX huY
  have hdX : E P (fun z => d.1 z.1) = 0 := by
    change E P (fun z => u.1 z.1 - 2 * (K u).1 z.1) = 0
    rw [contact_q_E_sub, contact_q_E_scale, huX, hKu.1]
    ring
  have hdY : E P (fun z => d.2 z.2) = 0 := by
    change E P (fun z => u.2 z.2 - 2 * (K u).2 z.2) = 0
    rw [contact_q_E_sub, contact_q_E_scale, huY, hKu.2]
    ring
  have hKd := hmean d hdX hdY
  have hpX : E P (fun z => p.1 z.1) = 0 := by
    change E P (fun z => d.1 z.1 + (K d).1 z.1) = 0
    rw [contact_q_E_add, hdX, hKd.1]
    ring
  have hpY : E P (fun z => p.2 z.2) = 0 := by
    change E P (fun z => d.2 z.2 + (K d).2 z.2) = 0
    rw [contact_q_E_add, hdY, hKd.2]
    ring
  have hvar := pairCharge_additive_variance_geometry hpair.2.1.1 B K hB hKX hKY p hpX hpY
  have hCQ : E (productLaw P) (fun z => (C z)^2) = B p p / (s P R)^2 := by
    simp only [C, div_pow, pairCharge_E_div, hvar.1]
  have hCP : E P (fun z => (C z)^2) = (B p p + B p (K p)) / (s P R)^2 := by
    simp only [C, div_pow, pairCharge_E_div, hvar.2]
  have hspec := pairCharge_operator_sos_centered_pair B K hself hpos hmean u.1 u.2 huX huY
  have hid := pairCharge_operator_additive_variance_identity B K hself d
  change B d ((5 : ℝ) • (d + (2 : ℝ) • K d + K (K d)) +
      (3 : ℝ) • K (d + (2 : ℝ) • K d + K (K d))) ≤
      (17/10 : ℝ) * B u (u - (2 : ℝ) • K u) + (23/4 : ℝ) * B d d at hspec
  change B p ((5 : ℝ) • p + (3 : ℝ) • K p) =
      B d ((5 : ℝ) • (d + (2 : ℝ) • K d + K (K d)) +
      (3 : ℝ) • K (d + (2 : ℝ) • K d + K (K d))) at hid
  rw [← hid, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hspec
  have hcross : B u (K u) = 2 * E P (fun z => u.1 z.1 * u.2 z.2) := by
    rw [hB, hKX, hKY, pairCharge_cond_X_inner hpair.2.1.1]
    rw [pairCharge_E_mul_comm P (fun z => u.2 z.2)
      (fun z => (∑ x, P (x,z.2) * u.1 x) / stoch_to_det.mY P z.2)]
    rw [pairCharge_cond_Y_inner hpair.2.1.1]
    ring
  have henergy : B u (u - (2 : ℝ) • K u) =
      6 * A0 P R * B0 P R - (s P R)^2 - J P R := by
    rw [map_sub, map_smul, smul_eq_mul, hB, hcross]
    change E P (fun z => (U P R z.1 + A0 P R) * (U P R z.1 + A0 P R)) +
      E P (fun z => (V P R z.2 + B0 P R) * (V P R z.2 + B0 P R)) -
      2 * (2 * E P (fun z => (U P R z.1 + A0 P R) * (V P R z.2 + B0 P R))) = _
    have he := pairCharge_contact_gram_energy hpair
    simp only [pow_two] at he
    linarith
  rw [henergy] at hspec
  have hvariance : 60 * (s P R)^2 *
      (E (productLaw P) (fun z => (C z)^2) / 30 + E P (fun z => (C z)^2) / 20) =
      5 * B p p + 3 * B p (K p) := by
    rw [hCQ, hCP]
    field_simp [(contact_moments hpair).s_pos.ne']
    ring
  rw [hvariance]
  exact hspec

lemma pairCharge_operator_LC_identity {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V)
    (hK : ∀ x y, B (K x) y = B x (K y)) (u : V) :
    let d := u - (2 : ℝ) • K u
    let p := d + K d
    4 * (2 * B u p + B u (K p)) =
      15 * B u d - 7 * B d d - 2 * B d (K d) := by
  dsimp only
  simp only [map_add, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, hK]
  ring

lemma pairCharge_additive_covariance_geometry {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (B : ((X → ℝ) × (Y → ℝ)) →ₗ[ℝ] ((X → ℝ) × (Y → ℝ)) →ₗ[ℝ] ℝ)
    (K : ((X → ℝ) × (Y → ℝ)) →ₗ[ℝ] ((X → ℝ) × (Y → ℝ)))
    (hB : ∀ p q, B p q = E P (fun z => p.1 z.1 * q.1 z.1) +
      E P (fun z => p.2 z.2 * q.2 z.2))
    (hKX : ∀ p, (K p).1 = fun x => (∑ y, P (x,y) * p.2 y) / stoch_to_det.mX P x)
    (hKY : ∀ p, (K p).2 = fun y => (∑ x, P (x,y) * p.1 x) / stoch_to_det.mY P y)
    (p q : (X → ℝ) × (Y → ℝ))
    (hpX : E P (fun z => p.1 z.1) = 0) (hpY : E P (fun z => p.2 z.2) = 0)
    (hqX : E P (fun z => q.1 z.1) = 0) (hqY : E P (fun z => q.2 z.2) = 0) :
    E (productLaw P) (fun z => (p.1 z.1 + p.2 z.2) * (q.1 z.1 + q.2 z.2)) = B p q ∧
    E P (fun z => (p.1 z.1 + p.2 z.2) * (q.1 z.1 + q.2 z.2)) = B p q + B p (K q) := by
  have hexpand (Q : Law X Y) :
      E Q (fun z => (p.1 z.1 + p.2 z.2) * (q.1 z.1 + q.2 z.2)) =
      E Q (fun z => p.1 z.1 * q.1 z.1) + E Q (fun z => p.2 z.2 * q.2 z.2) +
        E Q (fun z => p.1 z.1 * q.2 z.2) + E Q (fun z => q.1 z.1 * p.2 z.2) := by
    calc
      _ = E Q (fun z => ((p.1 z.1 * q.1 z.1 + p.2 z.2 * q.2 z.2) +
          p.1 z.1 * q.2 z.2) + q.1 z.1 * p.2 z.2) := by
        congr 1
        funext z
        ring
      _ = _ := by rw [contact_q_E_add, contact_q_E_add, contact_q_E_add]
  have hcross : B p (K q) = E P (fun z => p.1 z.1 * q.2 z.2) +
      E P (fun z => q.1 z.1 * p.2 z.2) := by
    rw [hB, hKX, hKY, pairCharge_cond_X_inner hP]
    rw [pairCharge_E_mul_comm P (fun z => p.2 z.2)
      (fun z => (∑ x, P (x,z.2) * q.1 x) / stoch_to_det.mY P z.2), pairCharge_cond_Y_inner hP]
  constructor
  · rw [hexpand, pairCharge_E_product_fst hP (fun x => p.1 x * q.1 x),
      pairCharge_E_product_snd hP (fun y => p.2 y * q.2 y), pairCharge_E_product P p.1 q.2,
      pairCharge_E_product P q.1 p.2, hpX, hpY, hqX, hqY, hB]
    ring
  · rw [hexpand, hB, hcross]
    ring

-- Raw conditional-feature bridges on the marginal rectangle, including its holes.

lemma pairCharge_E_congr_rectangle {S : Finset (X × Y)} {w P : Law X Y}
    (hP : Contact S w P) (F G : X × Y → ℝ)
    (hFG : ∀ z ∈ MarginalRectangle S, F z = G z) :
    E P F = E P G ∧ E (productLaw P) F = E (productLaw P) G := by
  constructor
  · apply pairCharge_E_congr_positive hP.1
    intro z hz
    apply hFG
    have hzS := pairCharge_mem_S_of_pos hP hz
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨z, hzS, rfl⟩, Finset.mem_image.mpr ⟨z, hzS, rfl⟩⟩
  · apply pairCharge_E_congr_positive (pairCharge_product_isPMF hP.1)
    intro z hz
    have hmX : 0 ≤ stoch_to_det.mX P z.1 := (stoch_to_det.isPMF_push hP.1).nonneg _
    have hmY : 0 ≤ stoch_to_det.mY P z.2 := (stoch_to_det.isPMF_push hP.1).nonneg _
    change 0 < stoch_to_det.mX P z.1 * stoch_to_det.mY P z.2 at hz
    have hpos := mul_pos_iff.mp hz
    have hmXpos : 0 < stoch_to_det.mX P z.1 := by
      rcases hpos with h | h
      · exact h.1
      · linarith [h.1]
    have hmYpos : 0 < stoch_to_det.mY P z.2 := by
      rcases hpos with h | h
      · exact h.2
      · linarith [h.2]
    apply hFG
    exact Finset.mem_product.mpr
      ⟨contact_mem_XSupport_of_mX_pos hP hmXpos, contact_mem_YSupport_of_mY_pos hP hmYpos⟩

end

end StochasticToDeterministicLatents.General
