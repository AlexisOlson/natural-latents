-- Original work by Alexis Olson, Apache-2.0 (see NOTICE), first developed in
-- github.com/AlexisOlson/stochastic-to-deterministic-latents; reorganised for this repository
-- (namespace NaturalLatents.General, declarations renamed, unused material removed).
-- This file builds on and cites the definitions of DLorell/stoch_to_det (Apache-2.0).
import NaturalLatents.General.PairCharge.Features

/-! # Contact correction fields and their moments

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

/-- The centered row defect. -/
abbrev pairCharge_defectX (P R : Law X Y) : X → ℝ := fun x =>
  pairCharge_rawDefectX P R x - (2 * defectY P R - defectX P R)

/-- The centered column defect. -/
abbrev pairCharge_defectY (P R : Law X Y) : Y → ℝ := fun y =>
  pairCharge_rawDefectY P R y - (2 * defectX P R - defectY P R)

/-- The sum of the two centered defect second moments. -/
abbrev pairCharge_defectNorm (P R : Law X Y) : ℝ :=
  expect P (fun z => (pairCharge_defectX P R z.1)^2) + expect P (fun z => (pairCharge_defectY P R z.2)^2)

/-- The centered defect cross moment. -/
abbrev pairCharge_defectCross (P R : Law X Y) : ℝ :=
  expect P (fun z => pairCharge_defectX P R z.1 * pairCharge_defectY P R z.2)

/-- The additive correction field, centered under both endpoint laws. -/
abbrev pairCharge_correction (P R : Law X Y) : X × Y → ℝ := fun z =>
  (pairCharge_rawDefectX P R z.1 + pairCharge_rawDefectY P R z.2) / separation P R - 1

/-- The fixed-coefficient statistic at coefficient `1/5`. -/
abbrev pairCharge_statistic (P R : Law X Y) : X × Y → ℝ := fun z =>
  stoch_to_det.contactSecantX P R z.1 * stoch_to_det.contactSecantY P R z.2 / separation P R + (1/5 : ℝ) * (stoch_to_det.contactSecantX P R z.1 + stoch_to_det.contactSecantY P R z.2 + separation P R)

/-- The correction is the sum of the centered defects divided by separation. -/
lemma pairCharge_correction_eq (P R : Law X Y) (hs : separation P R ≠ 0) (z : X × Y) :
    pairCharge_correction P R z =
      (pairCharge_defectX P R z.1 + pairCharge_defectY P R z.2) / separation P R := by
  unfold pairCharge_correction pairCharge_defectX pairCharge_defectY
  field_simp [hs]
  unfold separation
  ring

/-- The correction has zero mean under the contact and its product law. -/
lemma pairCharge_correction_means {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) :
    expect P (pairCharge_correction P R) = 0 ∧ expect (marginalProduct P) (pairCharge_correction P R) = 0 := by
  have hDX := (pairCharge_defect_X_moments hpair (pairCharge_rawDefectX P R) (fun _ => rfl)).1
  have hDY := (pairCharge_defect_Y_moments hpair (pairCharge_rawDefectY P R) (fun _ => rfl)).1
  have hs : separation P R = defectX P R + defectY P R := rfl
  constructor
  · simp only [contact_q_expect_sub, pairCharge_expect_div, contact_expect_add,
      contact_expect_const hpair.2.1.1, hDX, hDY]
    field_simp [(contact_moments hpair).separation_pos.ne']
    linarith [hs]
  · simp only [contact_q_expect_sub, pairCharge_expect_div, contact_expect_add,
      contact_expect_const (pairCharge_product_isPMF hpair.2.1.1),
      pairCharge_expect_product_fst hpair.2.1.1, pairCharge_expect_product_snd hpair.2.1.1, hDX, hDY]
    field_simp [(contact_moments hpair).separation_pos.ne']
    linarith [hs]

private lemma pairCharge_defect_bilinear {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (H : X → ℝ) (K : Y → ℝ) :
    expect P (fun z => (stoch_to_det.contactSecantX P R z.1 + defectX P R) * H z.1) +
      expect P (fun z => (stoch_to_det.contactSecantY P R z.2 + defectY P R) * K z.2) -
      2 * expect P (fun z => (stoch_to_det.contactSecantX P R z.1 + defectX P R) * K z.2) -
      2 * expect P (fun z => H z.1 * (stoch_to_det.contactSecantY P R z.2 + defectY P R)) =
      expect P (fun z => pairCharge_defectX P R z.1 * H z.1) +
      expect P (fun z => pairCharge_defectY P R z.2 * K z.2) := by
  have hb := pairCharge_gram_bilinear hpair.2.1.1
    (fun x => stoch_to_det.contactSecantX P R x + defectX P R) H (fun y => stoch_to_det.contactSecantY P R y + defectY P R) K
  rw [hb]
  congr 1
  · apply pairCharge_expect_congr_positive hpair.2.1.1
    intro z hz
    rw [← pairCharge_contact_defect_X hpair
      (Finset.mem_image.mpr ⟨z, pairCharge_mem_S_of_pos hpair.2.1 hz, rfl⟩)]
  · apply pairCharge_expect_congr_positive hpair.2.1.1
    intro z hz
    rw [← pairCharge_contact_defect_Y hpair
      (Finset.mem_image.mpr ⟨z, pairCharge_mem_S_of_pos hpair.2.1 hz, rfl⟩)]

/-- The diagonal and off-diagonal products of shifted features with defects. -/
lemma pairCharge_defect_products {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) :
    expect P (fun z => (stoch_to_det.contactSecantX P R z.1 + defectX P R) * pairCharge_defectX P R z.1) +
        expect P (fun z => (stoch_to_det.contactSecantY P R z.2 + defectY P R) * pairCharge_defectY P R z.2) =
      6 * defectX P R * defectY P R - (separation P R)^2 - quarticMoment P R ∧
    expect P (fun z => (stoch_to_det.contactSecantX P R z.1 + defectX P R) * pairCharge_defectY P R z.2) +
        expect P (fun z => (stoch_to_det.contactSecantY P R z.2 + defectY P R) * pairCharge_defectX P R z.1) =
      ((6 * defectX P R * defectY P R - (separation P R)^2 - quarticMoment P R) - pairCharge_defectNorm P R) / 2 := by
  have hself := pairCharge_defect_bilinear hpair
    (fun x => stoch_to_det.contactSecantX P R x + defectX P R) (fun y => stoch_to_det.contactSecantY P R y + defectY P R)
  have hcross := pairCharge_defect_bilinear hpair
    (pairCharge_defectX P R) (pairCharge_defectY P R)
  have henergy := pairCharge_contact_gram_energy hpair
  simp only [← pow_two] at hself hcross
  rw [pairCharge_expect_mul_comm P (fun z => pairCharge_defectX P R z.1)
      (fun z => stoch_to_det.contactSecantX P R z.1 + defectX P R),
    pairCharge_expect_mul_comm P (fun z => pairCharge_defectY P R z.2)
      (fun z => stoch_to_det.contactSecantY P R z.2 + defectY P R)] at hself
  rw [pairCharge_expect_mul_comm P (fun z => pairCharge_defectX P R z.1)
      (fun z => stoch_to_det.contactSecantY P R z.2 + defectY P R)] at hcross
  constructor
  · linarith [hself, henergy]
  · unfold pairCharge_defectNorm
    linarith [hself, hcross, henergy]

private lemma pairCharge_correction_square (P R Q : Law X Y) (hs : separation P R ≠ 0) :
    expect Q (fun z => (pairCharge_correction P R z)^2) =
      (expect Q (fun z => (pairCharge_defectX P R z.1)^2) +
        expect Q (fun z => (pairCharge_defectY P R z.2)^2) +
        2 * expect Q (fun z => pairCharge_defectX P R z.1 * pairCharge_defectY P R z.2)) /
        (separation P R)^2 := by
  have hp (z : X × Y) : (pairCharge_correction P R z)^2 =
      ((pairCharge_defectX P R z.1)^2 + (pairCharge_defectY P R z.2)^2 +
        2 * (pairCharge_defectX P R z.1 * pairCharge_defectY P R z.2)) / (separation P R)^2 := by
    rw [pairCharge_correction_eq P R hs]
    ring
  simp only [hp, pairCharge_expect_div, contact_expect_add, contact_q_expect_scale]

/-- The exact correction second moments under the two endpoint laws. -/
lemma pairCharge_correction_second_moments {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) :
    expect (marginalProduct P) (fun z => (pairCharge_correction P R z)^2) =
        pairCharge_defectNorm P R / (separation P R)^2 ∧
    expect P (fun z => (pairCharge_correction P R z)^2) =
        (pairCharge_defectNorm P R + 2 * pairCharge_defectCross P R) / (separation P R)^2 := by
  have hc := pairCharge_contact_defects_centered hpair
  change expect P (fun z => pairCharge_defectX P R z.1) = 0 ∧
    expect P (fun z => pairCharge_defectY P R z.2) = 0 at hc
  constructor
  · rw [pairCharge_correction_square P R (marginalProduct P) (contact_moments hpair).separation_pos.ne',
      pairCharge_expect_product_fst hpair.2.1.1 (fun x => (pairCharge_defectX P R x)^2),
      pairCharge_expect_product_snd hpair.2.1.1 (fun y => (pairCharge_defectY P R y)^2),
      pairCharge_expect_product, hc.1, hc.2]
    simp only [mul_zero, add_zero]
  · exact pairCharge_correction_square P R P (contact_moments hpair).separation_pos.ne'

private lemma pairCharge_correction_additive_product (P R Q : Law X Y)
    (hs : separation P R ≠ 0) :
    expect Q (fun z => (stoch_to_det.contactSecantX P R z.1 + stoch_to_det.contactSecantY P R z.2 + separation P R) * pairCharge_correction P R z) =
      (expect Q (fun z => (stoch_to_det.contactSecantX P R z.1 + defectX P R) * pairCharge_defectX P R z.1) +
        expect Q (fun z => (stoch_to_det.contactSecantY P R z.2 + defectY P R) * pairCharge_defectY P R z.2) +
        (expect Q (fun z => (stoch_to_det.contactSecantX P R z.1 + defectX P R) * pairCharge_defectY P R z.2) +
          expect Q (fun z => (stoch_to_det.contactSecantY P R z.2 + defectY P R) * pairCharge_defectX P R z.1))) / separation P R := by
  have hp (z : X × Y) :
      (stoch_to_det.contactSecantX P R z.1 + stoch_to_det.contactSecantY P R z.2 + separation P R) * pairCharge_correction P R z =
      ((stoch_to_det.contactSecantX P R z.1 + defectX P R) * pairCharge_defectX P R z.1 +
        (stoch_to_det.contactSecantY P R z.2 + defectY P R) * pairCharge_defectY P R z.2 +
        ((stoch_to_det.contactSecantX P R z.1 + defectX P R) * pairCharge_defectY P R z.2 +
          (stoch_to_det.contactSecantY P R z.2 + defectY P R) * pairCharge_defectX P R z.1)) / separation P R := by
    rw [pairCharge_correction_eq P R hs]
    unfold separation
    ring
  simp only [hp, pairCharge_expect_div, contact_expect_add]

/-- The sum of the two endpoint products of the additive statistic and correction. -/
lemma pairCharge_linear_correction {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) :
    expect (marginalProduct P) (fun z => (stoch_to_det.contactSecantX P R z.1 + stoch_to_det.contactSecantY P R z.2 + separation P R) * pairCharge_correction P R z) +
        expect P (fun z => (stoch_to_det.contactSecantX P R z.1 + stoch_to_det.contactSecantY P R z.2 + separation P R) * pairCharge_correction P R z) =
      (5 * (6 * defectX P R * defectY P R - (separation P R)^2 - quarticMoment P R) - pairCharge_defectNorm P R) /
        (2 * separation P R) := by
  have hs := (contact_moments hpair).separation_pos.ne'
  have hd := pairCharge_defect_products hpair
  have hw := pairCharge_shifted_features_centered hpair
  rw [pairCharge_correction_additive_product P R (marginalProduct P) hs,
    pairCharge_correction_additive_product P R P hs,
    pairCharge_expect_product_fst hpair.2.1.1
      (fun x => (stoch_to_det.contactSecantX P R x + defectX P R) * pairCharge_defectX P R x),
    pairCharge_expect_product_snd hpair.2.1.1
      (fun y => (stoch_to_det.contactSecantY P R y + defectY P R) * pairCharge_defectY P R y),
    pairCharge_expect_product P (fun x => stoch_to_det.contactSecantX P R x + defectX P R) (pairCharge_defectY P R)]
  have he := pairCharge_expect_product P (pairCharge_defectX P R) (fun y => stoch_to_det.contactSecantY P R y + defectY P R)
  rw [pairCharge_expect_mul_comm (marginalProduct P) (fun z => stoch_to_det.contactSecantY P R z.2 + defectY P R)
    (fun z => pairCharge_defectX P R z.1), he, hw.1, hw.2, hd.1, hd.2]
  ring

/-- The feasibility Hessian evaluated on `6 * lam * defect - k * shifted feature`. -/
lemma pairCharge_correction_hessian {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (lam k : ℝ) :
    0 ≤ 36 * lam^2 * (pairCharge_defectNorm P R - 4 * pairCharge_defectCross P R)
      - 12 * lam * k * pairCharge_defectNorm P R
      + k^2 * (6 * defectX P R * defectY P R - (separation P R)^2 - quarticMoment P R) := by
  let F : X → ℝ := pairCharge_defectX P R
  let G : Y → ℝ := pairCharge_defectY P R
  let H : X → ℝ := fun x => stoch_to_det.contactSecantX P R x + defectX P R
  let K : Y → ℝ := fun y => stoch_to_det.contactSecantY P R y + defectY P R
  have hc := pairCharge_contact_defects_centered hpair
  change expect P (fun z => F z.1) = 0 ∧ expect P (fun z => G z.2) = 0 at hc
  have hw := pairCharge_shifted_features_centered hpair
  have hx : expect P (fun z => 6 * lam * F z.1 + (-k) * H z.1) = 0 := by
    rw [contact_expect_add, contact_q_expect_scale, contact_q_expect_scale, hc.1, hw.1]
    ring
  have hy : expect P (fun z => 6 * lam * G z.2 + (-k) * K z.2) = 0 := by
    rw [contact_expect_add, contact_q_expect_scale, contact_q_expect_scale, hc.2, hw.2]
    ring
  have hh := (contact_moments hpair).hessian
    (fun x => 6 * lam * F x + (-k) * H x)
    (fun y => 6 * lam * G y + (-k) * K y) hx hy
  have hb := pairCharge_defect_bilinear hpair F G
  have he := pairCharge_contact_gram_energy hpair
  have hi :
      expect P (fun z => (6 * lam * F z.1 + (-k) * H z.1)^2) +
        expect P (fun z => (6 * lam * G z.2 + (-k) * K z.2)^2) -
        4 * expect P (fun z => (6 * lam * F z.1 + (-k) * H z.1) *
          (6 * lam * G z.2 + (-k) * K z.2)) =
      36 * lam^2 * (pairCharge_defectNorm P R - 4 * pairCharge_defectCross P R) -
        12 * lam * k * pairCharge_defectNorm P R +
        k^2 * (6 * defectX P R * defectY P R - (separation P R)^2 - quarticMoment P R) := by
    rw [pairCharge_expect_lincomb_sq, pairCharge_expect_lincomb_sq, pairCharge_expect_lincomb_prod]
    dsimp only [F, G, H, K] at *
    simp only [← pow_two] at hb
    rw [pairCharge_expect_mul_comm P (fun z => pairCharge_defectX P R z.1)
      (fun z => stoch_to_det.contactSecantX P R z.1 + defectX P R),
      pairCharge_expect_mul_comm P (fun z => pairCharge_defectY P R z.2)
      (fun z => stoch_to_det.contactSecantY P R z.2 + defectY P R)]
    unfold pairCharge_defectNorm pairCharge_defectCross
    linear_combination (-12 * lam * k) * hb + k^2 * he
  linarith only [hh, hi]

end

end NaturalLatents.General
