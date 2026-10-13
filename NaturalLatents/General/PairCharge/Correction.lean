import NaturalLatents.General.PairCharge.Features

/-! # Contact correction fields and their moments -/

namespace NaturalLatents.General

noncomputable section

open scoped BigOperators
open MeasureTheory ProbabilityTheory

variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- The centered row defect. -/
abbrev pairCharge_defectX (P R : Law X Y) : X → ℝ := fun x =>
  pairCharge_rawDX P R x - (2 * B0 P R - A0 P R)

/-- The centered column defect. -/
abbrev pairCharge_defectY (P R : Law X Y) : Y → ℝ := fun y =>
  pairCharge_rawDY P R y - (2 * A0 P R - B0 P R)

/-- The sum of the two centered defect second moments. -/
abbrev pairCharge_defectNorm (P R : Law X Y) : ℝ :=
  E P (fun z => (pairCharge_defectX P R z.1)^2) + E P (fun z => (pairCharge_defectY P R z.2)^2)

/-- The centered defect cross moment. -/
abbrev pairCharge_defectCross (P R : Law X Y) : ℝ :=
  E P (fun z => pairCharge_defectX P R z.1 * pairCharge_defectY P R z.2)

/-- The additive correction field, centered under both endpoint laws. -/
abbrev pairCharge_correction (P R : Law X Y) : X × Y → ℝ := fun z =>
  (pairCharge_rawDX P R z.1 + pairCharge_rawDY P R z.2) / s P R - 1

/-- The fixed-coefficient statistic at coefficient `1/5`. -/
abbrev pairCharge_statistic (P R : Law X Y) : X × Y → ℝ := fun z =>
  U P R z.1 * V P R z.2 / s P R + (1/5 : ℝ) * (U P R z.1 + V P R z.2 + s P R)

/-- The correction is the sum of the centered defects divided by separation. -/
lemma pairCharge_correction_eq (P R : Law X Y) (hs : s P R ≠ 0) (z : X × Y) :
    pairCharge_correction P R z =
      (pairCharge_defectX P R z.1 + pairCharge_defectY P R z.2) / s P R := by
  unfold pairCharge_correction pairCharge_defectX pairCharge_defectY
  field_simp [hs]
  unfold s
  ring

/-- The correction has zero mean under the contact and its product law. -/
lemma pairCharge_correction_means {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    E P (pairCharge_correction P R) = 0 ∧ E (productLaw P) (pairCharge_correction P R) = 0 := by
  have hDX := (pairCharge_defect_X_moments hpair (pairCharge_rawDX P R) (fun _ => rfl)).1
  have hDY := (pairCharge_defect_Y_moments hpair (pairCharge_rawDY P R) (fun _ => rfl)).1
  have hs : s P R = A0 P R + B0 P R := rfl
  constructor
  · simp only [contact_q_E_sub, pairCharge_E_div, contact_E_add,
      contact_E_const hpair.2.1.1, hDX, hDY]
    field_simp [(contact_moments hpair).s_pos.ne']
    linarith [hs]
  · simp only [contact_q_E_sub, pairCharge_E_div, contact_E_add,
      contact_E_const (pairCharge_product_isPMF hpair.2.1.1),
      pairCharge_E_product_fst hpair.2.1.1, pairCharge_E_product_snd hpair.2.1.1, hDX, hDY]
    field_simp [(contact_moments hpair).s_pos.ne']
    linarith [hs]

private lemma pairCharge_defect_bilinear {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (H : X → ℝ) (K : Y → ℝ) :
    E P (fun z => (U P R z.1 + A0 P R) * H z.1) +
      E P (fun z => (V P R z.2 + B0 P R) * K z.2) -
      2 * E P (fun z => (U P R z.1 + A0 P R) * K z.2) -
      2 * E P (fun z => H z.1 * (V P R z.2 + B0 P R)) =
      E P (fun z => pairCharge_defectX P R z.1 * H z.1) +
      E P (fun z => pairCharge_defectY P R z.2 * K z.2) := by
  have hb := pairCharge_S0_bilinear hpair.2.1.1
    (fun x => U P R x + A0 P R) H (fun y => V P R y + B0 P R) K
  rw [hb]
  congr 1
  · apply pairCharge_E_congr_positive hpair.2.1.1
    intro z hz
    rw [← pairCharge_contact_defect_X hpair
      (Finset.mem_image.mpr ⟨z, pairCharge_mem_S_of_pos hpair.2.1 hz, rfl⟩)]
  · apply pairCharge_E_congr_positive hpair.2.1.1
    intro z hz
    rw [← pairCharge_contact_defect_Y hpair
      (Finset.mem_image.mpr ⟨z, pairCharge_mem_S_of_pos hpair.2.1 hz, rfl⟩)]

/-- The diagonal and off-diagonal products of shifted features with defects. -/
lemma pairCharge_defect_products {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    E P (fun z => (U P R z.1 + A0 P R) * pairCharge_defectX P R z.1) +
        E P (fun z => (V P R z.2 + B0 P R) * pairCharge_defectY P R z.2) =
      6 * A0 P R * B0 P R - (s P R)^2 - J P R ∧
    E P (fun z => (U P R z.1 + A0 P R) * pairCharge_defectY P R z.2) +
        E P (fun z => (V P R z.2 + B0 P R) * pairCharge_defectX P R z.1) =
      ((6 * A0 P R * B0 P R - (s P R)^2 - J P R) - pairCharge_defectNorm P R) / 2 := by
  have hself := pairCharge_defect_bilinear hpair
    (fun x => U P R x + A0 P R) (fun y => V P R y + B0 P R)
  have hcross := pairCharge_defect_bilinear hpair
    (pairCharge_defectX P R) (pairCharge_defectY P R)
  have henergy := pairCharge_contact_gram_energy hpair
  simp only [← pow_two] at hself hcross
  rw [pairCharge_E_mul_comm P (fun z => pairCharge_defectX P R z.1)
      (fun z => U P R z.1 + A0 P R),
    pairCharge_E_mul_comm P (fun z => pairCharge_defectY P R z.2)
      (fun z => V P R z.2 + B0 P R)] at hself
  rw [pairCharge_E_mul_comm P (fun z => pairCharge_defectX P R z.1)
      (fun z => V P R z.2 + B0 P R)] at hcross
  constructor
  · linarith [hself, henergy]
  · unfold pairCharge_defectNorm
    linarith [hself, hcross, henergy]

private lemma pairCharge_correction_square (P R Q : Law X Y) (hs : s P R ≠ 0) :
    E Q (fun z => (pairCharge_correction P R z)^2) =
      (E Q (fun z => (pairCharge_defectX P R z.1)^2) +
        E Q (fun z => (pairCharge_defectY P R z.2)^2) +
        2 * E Q (fun z => pairCharge_defectX P R z.1 * pairCharge_defectY P R z.2)) /
        (s P R)^2 := by
  have hp (z : X × Y) : (pairCharge_correction P R z)^2 =
      ((pairCharge_defectX P R z.1)^2 + (pairCharge_defectY P R z.2)^2 +
        2 * (pairCharge_defectX P R z.1 * pairCharge_defectY P R z.2)) / (s P R)^2 := by
    rw [pairCharge_correction_eq P R hs]
    ring
  simp only [hp, pairCharge_E_div, contact_E_add, contact_q_E_scale]

/-- The exact correction second moments under the two endpoint laws. -/
lemma pairCharge_correction_second_moments {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    E (productLaw P) (fun z => (pairCharge_correction P R z)^2) =
        pairCharge_defectNorm P R / (s P R)^2 ∧
    E P (fun z => (pairCharge_correction P R z)^2) =
        (pairCharge_defectNorm P R + 2 * pairCharge_defectCross P R) / (s P R)^2 := by
  have hc := pairCharge_contact_defects_centered hpair
  change E P (fun z => pairCharge_defectX P R z.1) = 0 ∧
    E P (fun z => pairCharge_defectY P R z.2) = 0 at hc
  constructor
  · rw [pairCharge_correction_square P R (productLaw P) (contact_moments hpair).s_pos.ne',
      pairCharge_E_product_fst hpair.2.1.1 (fun x => (pairCharge_defectX P R x)^2),
      pairCharge_E_product_snd hpair.2.1.1 (fun y => (pairCharge_defectY P R y)^2),
      pairCharge_E_product, hc.1, hc.2]
    simp only [mul_zero, add_zero]
  · exact pairCharge_correction_square P R P (contact_moments hpair).s_pos.ne'

private lemma pairCharge_correction_additive_product (P R Q : Law X Y)
    (hs : s P R ≠ 0) :
    E Q (fun z => (U P R z.1 + V P R z.2 + s P R) * pairCharge_correction P R z) =
      (E Q (fun z => (U P R z.1 + A0 P R) * pairCharge_defectX P R z.1) +
        E Q (fun z => (V P R z.2 + B0 P R) * pairCharge_defectY P R z.2) +
        (E Q (fun z => (U P R z.1 + A0 P R) * pairCharge_defectY P R z.2) +
          E Q (fun z => (V P R z.2 + B0 P R) * pairCharge_defectX P R z.1))) / s P R := by
  have hp (z : X × Y) :
      (U P R z.1 + V P R z.2 + s P R) * pairCharge_correction P R z =
      ((U P R z.1 + A0 P R) * pairCharge_defectX P R z.1 +
        (V P R z.2 + B0 P R) * pairCharge_defectY P R z.2 +
        ((U P R z.1 + A0 P R) * pairCharge_defectY P R z.2 +
          (V P R z.2 + B0 P R) * pairCharge_defectX P R z.1)) / s P R := by
    rw [pairCharge_correction_eq P R hs]
    unfold s
    ring
  simp only [hp, pairCharge_E_div, contact_E_add]

/-- The sum of the two endpoint products of the additive statistic and correction. -/
lemma pairCharge_linear_correction {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    E (productLaw P) (fun z => (U P R z.1 + V P R z.2 + s P R) * pairCharge_correction P R z) +
        E P (fun z => (U P R z.1 + V P R z.2 + s P R) * pairCharge_correction P R z) =
      (5 * (6 * A0 P R * B0 P R - (s P R)^2 - J P R) - pairCharge_defectNorm P R) /
        (2 * s P R) := by
  have hs := (contact_moments hpair).s_pos.ne'
  have hd := pairCharge_defect_products hpair
  have hw := pairCharge_shifted_features_centered hpair
  rw [pairCharge_correction_additive_product P R (productLaw P) hs,
    pairCharge_correction_additive_product P R P hs,
    pairCharge_E_product_fst hpair.2.1.1
      (fun x => (U P R x + A0 P R) * pairCharge_defectX P R x),
    pairCharge_E_product_snd hpair.2.1.1
      (fun y => (V P R y + B0 P R) * pairCharge_defectY P R y),
    pairCharge_E_product P (fun x => U P R x + A0 P R) (pairCharge_defectY P R)]
  have he := pairCharge_E_product P (pairCharge_defectX P R) (fun y => V P R y + B0 P R)
  rw [pairCharge_E_mul_comm (productLaw P) (fun z => V P R z.2 + B0 P R)
    (fun z => pairCharge_defectX P R z.1), he, hw.1, hw.2, hd.1, hd.2]
  ring

/-- The feasibility Hessian evaluated on `6 * lam * defect - k * shifted feature`. -/
lemma pairCharge_correction_hessian {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (lam k : ℝ) :
    0 ≤ 36 * lam^2 * (pairCharge_defectNorm P R - 4 * pairCharge_defectCross P R)
      - 12 * lam * k * pairCharge_defectNorm P R
      + k^2 * (6 * A0 P R * B0 P R - (s P R)^2 - J P R) := by
  let F : X → ℝ := pairCharge_defectX P R
  let G : Y → ℝ := pairCharge_defectY P R
  let H : X → ℝ := fun x => U P R x + A0 P R
  let K : Y → ℝ := fun y => V P R y + B0 P R
  have hc := pairCharge_contact_defects_centered hpair
  change E P (fun z => F z.1) = 0 ∧ E P (fun z => G z.2) = 0 at hc
  have hw := pairCharge_shifted_features_centered hpair
  have hx : E P (fun z => 6 * lam * F z.1 + (-k) * H z.1) = 0 := by
    rw [contact_E_add, contact_q_E_scale, contact_q_E_scale, hc.1, hw.1]
    ring
  have hy : E P (fun z => 6 * lam * G z.2 + (-k) * K z.2) = 0 := by
    rw [contact_E_add, contact_q_E_scale, contact_q_E_scale, hc.2, hw.2]
    ring
  have hh := (contact_moments hpair).hessian
    (fun x => 6 * lam * F x + (-k) * H x)
    (fun y => 6 * lam * G y + (-k) * K y) hx hy
  have hb := pairCharge_defect_bilinear hpair F G
  have he := pairCharge_contact_gram_energy hpair
  have hi :
      E P (fun z => (6 * lam * F z.1 + (-k) * H z.1)^2) +
        E P (fun z => (6 * lam * G z.2 + (-k) * K z.2)^2) -
        4 * E P (fun z => (6 * lam * F z.1 + (-k) * H z.1) *
          (6 * lam * G z.2 + (-k) * K z.2)) =
      36 * lam^2 * (pairCharge_defectNorm P R - 4 * pairCharge_defectCross P R) -
        12 * lam * k * pairCharge_defectNorm P R +
        k^2 * (6 * A0 P R * B0 P R - (s P R)^2 - J P R) := by
    rw [pairCharge_E_lincomb_sq, pairCharge_E_lincomb_sq, pairCharge_E_lincomb_prod]
    dsimp only [F, G, H, K] at *
    simp only [← pow_two] at hb
    rw [pairCharge_E_mul_comm P (fun z => pairCharge_defectX P R z.1)
      (fun z => U P R z.1 + A0 P R),
      pairCharge_E_mul_comm P (fun z => pairCharge_defectY P R z.2)
      (fun z => V P R z.2 + B0 P R)]
    unfold pairCharge_defectNorm pairCharge_defectCross
    linear_combination (-12 * lam * k) * hb + k^2 * he
  linarith only [hh, hi]

end

end NaturalLatents.General
