-- Original work by Alexis Olson, Apache-2.0 (see NOTICE), first developed in
-- github.com/AlexisOlson/stochastic-to-deterministic-latents; reorganised for this repository
-- (namespace NaturalLatents.General, declarations renamed, unused material removed).
-- This file builds on and cites the definitions of DLorell/stoch_to_det (Apache-2.0).
import NaturalLatents.General.PairCharge.Gram

/-!
# Pair charge: defect fields and reversal identities

This module defines the raw row and column defect fields and proves their moments.
It supplies reversal identities for the features, conditional defects and weighted
second moments, together with the endpoint products of `UV/s` and the correction
`(DX + DY)/s - 1` under the joint and product laws.

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

/-- The row defect field used throughout the raw pair-charge estimates. -/
abbrev pairCharge_rawDefectX (P R : Law X Y) : X → ℝ := fun x =>
  (∑ y, P (x,y) * (stoch_to_det.contactSecantY P R y)^2) / stoch_to_det.mX P x

/-- The column defect field used throughout the raw pair-charge estimates. -/
abbrev pairCharge_rawDefectY (P R : Law X Y) : Y → ℝ := fun y =>
  (∑ x, P (x,y) * (stoch_to_det.contactSecantX P R x)^2) / stoch_to_det.mY P y

lemma pairCharge_secantX_reverse_scaled {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) {x : X} (hx : x ∈ xSupport S) :
    rootRatioX P R x * stoch_to_det.contactSecantX R P x = -stoch_to_det.contactSecantX P R x := by
  have hf := pairCharge_rootRatioX_reverse_mul hpair hx
  unfold rootRatioX at hf ⊢
  nlinarith only [hf]

lemma pairCharge_secantY_reverse_scaled {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) {y : Y} (hy : y ∈ ySupport S) :
    rootRatioY P R y * stoch_to_det.contactSecantY R P y = -stoch_to_det.contactSecantY P R y := by
  have hg := pairCharge_rootRatioY_reverse_mul hpair hy
  unfold rootRatioY at hg ⊢
  nlinarith only [hg]

lemma pairCharge_expect_reverse_fst {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (F : X → ℝ) :
    expect R (fun z => F z.1) = expect P (fun z => (rootRatioX P R z.1)^3 * F z.1) := by
  rw [contact_expect_fst R F, contact_expect_fst P (fun x => (rootRatioX P R x)^3 * F x)]
  apply Finset.sum_congr rfl
  intro x _
  rw [← contact_rootRatioX_cube_mul_marginal hpair x]
  ring

lemma pairCharge_expect_reverse_snd {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (G : Y → ℝ) :
    expect R (fun z => G z.2) = expect P (fun z => (rootRatioY P R z.2)^3 * G z.2) := by
  rw [contact_expect_snd R G, contact_expect_snd P (fun y => (rootRatioY P R y)^3 * G y)]
  apply Finset.sum_congr rfl
  intro y _
  rw [← contact_rootRatioY_cube_mul_marginal hpair y]
  ring

lemma pairCharge_cond_X_reverse_weight {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (G : Y → ℝ)
    {x : X} (hx : x ∈ xSupport S) :
    rootRatioX P R x * ((∑ y, R (x,y) * G y) / stoch_to_det.mX R x) =
      (∑ y, P (x,y) * ((rootRatioY P R y)^2 * G y)) / stoch_to_det.mX P x := by
  have hnum : (∑ y, R (x,y) * G y) =
      (rootRatioX P R x)^2 * (∑ y, P (x,y) * ((rootRatioY P R y)^2 * G y)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [contact_ratio_mul hpair (x,y)]
    ring
  rw [hnum, ← contact_rootRatioX_cube_mul_marginal hpair x]
  field_simp [(contact_mX_pos hpair.2.1 hpair.2.2.2.1 hx).ne',
    (contact_rootRatioX_pos hpair hx).ne']

lemma pairCharge_cond_Y_reverse_weight {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (F : X → ℝ)
    {y : Y} (hy : y ∈ ySupport S) :
    rootRatioY P R y * ((∑ x, R (x,y) * F x) / stoch_to_det.mY R y) =
      (∑ x, P (x,y) * ((rootRatioX P R x)^2 * F x)) / stoch_to_det.mY P y := by
  have hnum : (∑ x, R (x,y) * F x) =
      (rootRatioY P R y)^2 * (∑ x, P (x,y) * ((rootRatioX P R x)^2 * F x)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [contact_ratio_mul hpair (x,y)]
    ring
  rw [hnum, ← contact_rootRatioY_cube_mul_marginal hpair y]
  field_simp [(contact_mY_pos hpair.2.1 hpair.2.2.2.1 hy).ne',
    (contact_rootRatioY_pos hpair hy).ne']

lemma pairCharge_cond_defect_X_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R)
    {x : X} (hx : x ∈ xSupport S) :
    rootRatioX P R x * ((∑ y, R (x,y) * (stoch_to_det.contactSecantY R P y)^2) / stoch_to_det.mX R x) =
      (∑ y, P (x,y) * (stoch_to_det.contactSecantY P R y)^2) / stoch_to_det.mX P x := by
  rw [pairCharge_cond_X_reverse_weight hpair (fun y => (stoch_to_det.contactSecantY R P y)^2) hx]
  apply pairCharge_cond_X_congr_support hpair.2.1
  intro y hy
  rw [show (rootRatioY P R y)^2 * (stoch_to_det.contactSecantY R P y)^2 = (rootRatioY P R y * stoch_to_det.contactSecantY R P y)^2 by ring,
    pairCharge_secantY_reverse_scaled hpair hy]
  ring

lemma pairCharge_cond_defect_Y_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R)
    {y : Y} (hy : y ∈ ySupport S) :
    rootRatioY P R y * ((∑ x, R (x,y) * (stoch_to_det.contactSecantX R P x)^2) / stoch_to_det.mY R y) =
      (∑ x, P (x,y) * (stoch_to_det.contactSecantX P R x)^2) / stoch_to_det.mY P y := by
  rw [pairCharge_cond_Y_reverse_weight hpair (fun x => (stoch_to_det.contactSecantX R P x)^2) hy]
  apply pairCharge_cond_Y_congr_support hpair.2.1
  intro x hx
  rw [show (rootRatioX P R x)^2 * (stoch_to_det.contactSecantX R P x)^2 = (rootRatioX P R x * stoch_to_det.contactSecantX R P x)^2 by ring,
    pairCharge_secantX_reverse_scaled hpair hx]
  ring

lemma pairCharge_secantX_defect_square_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (DX DXp : X → ℝ)
    (hDX : ∀ x ∈ xSupport S, rootRatioX P R x * DXp x = DX x) :
    expect R (fun z => stoch_to_det.contactSecantX R P z.1 * (DXp z.1)^2) =
      -expect P (fun z => stoch_to_det.contactSecantX P R z.1 * (DX z.1)^2) := by
  rw [pairCharge_expect_reverse_fst hpair (fun x => stoch_to_det.contactSecantX R P x * (DXp x)^2)]
  calc
    _ = expect P (fun z => -1 * (stoch_to_det.contactSecantX P R z.1 * (DX z.1)^2)) := by
      apply pairCharge_expect_congr_positive hpair.2.1.1
      intro z hz
      have hzS := pairCharge_mem_S_of_pos hpair.2.1 hz
      have hx : z.1 ∈ xSupport S := Finset.mem_image.mpr ⟨z, hzS, rfl⟩
      calc
        (rootRatioX P R z.1)^3 * (stoch_to_det.contactSecantX R P z.1 * (DXp z.1)^2) =
          (rootRatioX P R z.1 * stoch_to_det.contactSecantX R P z.1) * (rootRatioX P R z.1 * DXp z.1)^2 := by ring
        _ = _ := by rw [pairCharge_secantX_reverse_scaled hpair hx, hDX _ hx]; ring
    _ = _ := by rw [contact_q_expect_scale]; ring

lemma pairCharge_secantY_defect_square_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (DY DYp : Y → ℝ)
    (hDY : ∀ y ∈ ySupport S, rootRatioY P R y * DYp y = DY y) :
    expect R (fun z => stoch_to_det.contactSecantY R P z.2 * (DYp z.2)^2) =
      -expect P (fun z => stoch_to_det.contactSecantY P R z.2 * (DY z.2)^2) := by
  rw [pairCharge_expect_reverse_snd hpair (fun y => stoch_to_det.contactSecantY R P y * (DYp y)^2)]
  calc
    _ = expect P (fun z => -1 * (stoch_to_det.contactSecantY P R z.2 * (DY z.2)^2)) := by
      apply pairCharge_expect_congr_positive hpair.2.1.1
      intro z hz
      have hzS := pairCharge_mem_S_of_pos hpair.2.1 hz
      have hy : z.2 ∈ ySupport S := Finset.mem_image.mpr ⟨z, hzS, rfl⟩
      calc
        (rootRatioY P R z.2)^3 * (stoch_to_det.contactSecantY R P z.2 * (DYp z.2)^2) =
          (rootRatioY P R z.2 * stoch_to_det.contactSecantY R P z.2) * (rootRatioY P R z.2 * DYp z.2)^2 := by ring
        _ = _ := by rw [pairCharge_secantY_reverse_scaled hpair hy, hDY _ hy]; ring
    _ = _ := by rw [contact_q_expect_scale]; ring

lemma pairCharge_secantX_conditional_identity {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) {x : X} (hx : x ∈ xSupport S) :
    stoch_to_det.contactSecantX P R x = 2 * ((∑ y, P (x,y) * stoch_to_det.contactSecantY P R y) / stoch_to_det.mX P x) +
      (∑ y, P (x,y) * (stoch_to_det.contactSecantY P R y)^2) / stoch_to_det.mX P x := by
  have hc := (contact_moments hpair).cond_rootRatioY_square x hx
  have hs := pairCharge_cond_X_sq_add_one (stoch_to_det.contactSecantY P R) (contact_mX_pos hpair.2.1 hpair.2.2.2.1 hx).ne'
  change (∑ y, P (x,y) * (stoch_to_det.contactSecantY P R y + 1)^2) / stoch_to_det.mX P x = stoch_to_det.contactSecantX P R x + 1 at hc
  rw [hs] at hc
  linarith

lemma pairCharge_secantY_conditional_identity {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) {y : Y} (hy : y ∈ ySupport S) :
    stoch_to_det.contactSecantY P R y = 2 * ((∑ x, P (x,y) * stoch_to_det.contactSecantX P R x) / stoch_to_det.mY P y) +
      (∑ x, P (x,y) * (stoch_to_det.contactSecantX P R x)^2) / stoch_to_det.mY P y := by
  have hc := (contact_moments hpair).cond_rootRatioX_square y hy
  have hs := pairCharge_cond_Y_sq_add_one (stoch_to_det.contactSecantX P R) (contact_mY_pos hpair.2.1 hpair.2.2.2.1 hy).ne'
  change (∑ x, P (x,y) * (stoch_to_det.contactSecantX P R x + 1)^2) / stoch_to_det.mY P y = stoch_to_det.contactSecantY P R y + 1 at hc
  rw [hs] at hc
  linarith

/-- A row-field conditioning identity, shared by the raw UV and defect specializations. -/
lemma pairCharge_row_field {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (DX F : X → ℝ)
    (hDX : ∀ x, DX x = pairCharge_rawDefectX P R x) :
    expect P (fun z => F z.1 * stoch_to_det.contactSecantY P R z.2) =
      (expect P (fun z => F z.1 * stoch_to_det.contactSecantX P R z.1) - expect P (fun z => F z.1 * DX z.1)) / 2 := by
  have htower := pairCharge_cond_X_inner hpair.2.1.1 F (stoch_to_det.contactSecantY P R)
  have hpoint : ∀ z, 0 < P z →
      (∑ y, P (z.1,y) * stoch_to_det.contactSecantY P R y) / stoch_to_det.mX P z.1 =
        (stoch_to_det.contactSecantX P R z.1 - DX z.1) / 2 := by
    intro z hz
    have hx : z.1 ∈ xSupport S :=
      Finset.mem_image.mpr ⟨z, pairCharge_mem_S_of_pos hpair.2.1 hz, rfl⟩
    have hu := pairCharge_secantX_conditional_identity hpair hx
    have hd := hDX z.1
    dsimp [pairCharge_rawDefectX] at hd
    rw [← hd] at hu
    linarith only [hu]
  have hcongr : expect P (fun z => F z.1 *
      ((∑ y, P (z.1,y) * stoch_to_det.contactSecantY P R y) / stoch_to_det.mX P z.1)) =
      expect P (fun z => (F z.1 * stoch_to_det.contactSecantX P R z.1 - F z.1 * DX z.1) / 2) := by
    apply pairCharge_expect_congr_positive hpair.2.1.1
    intro z hz
    rw [hpoint z hz]
    ring
  rw [hcongr, pairCharge_expect_div, contact_q_expect_sub] at htower
  exact htower.symm

/-- A column-field conditioning identity, shared by the raw UV and defect specializations. -/
lemma pairCharge_column_field {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (DY G : Y → ℝ)
    (hDY : ∀ y, DY y = pairCharge_rawDefectY P R y) :
    expect P (fun z => stoch_to_det.contactSecantX P R z.1 * G z.2) =
      (expect P (fun z => stoch_to_det.contactSecantY P R z.2 * G z.2) - expect P (fun z => DY z.2 * G z.2)) / 2 := by
  have htower := pairCharge_cond_Y_inner hpair.2.1.1 (stoch_to_det.contactSecantX P R) G
  have hpoint : ∀ z, 0 < P z →
      (∑ x, P (x,z.2) * stoch_to_det.contactSecantX P R x) / stoch_to_det.mY P z.2 =
        (stoch_to_det.contactSecantY P R z.2 - DY z.2) / 2 := by
    intro z hz
    have hy : z.2 ∈ ySupport S :=
      Finset.mem_image.mpr ⟨z, pairCharge_mem_S_of_pos hpair.2.1 hz, rfl⟩
    have hv := pairCharge_secantY_conditional_identity hpair hy
    have hd := hDY z.2
    dsimp [pairCharge_rawDefectY] at hd
    rw [← hd] at hv
    linarith only [hv]
  have hcongr : expect P (fun z =>
      ((∑ x, P (x,z.2) * stoch_to_det.contactSecantX P R x) / stoch_to_det.mY P z.2) * G z.2) =
      expect P (fun z => (stoch_to_det.contactSecantY P R z.2 * G z.2 - DY z.2 * G z.2) / 2) := by
    apply pairCharge_expect_congr_positive hpair.2.1.1
    intro z hz
    rw [hpoint z hz]
    ring
  rw [hcongr, pairCharge_expect_div, contact_q_expect_sub] at htower
  exact htower.symm

/-- Conditioning UV against an arbitrary row field. -/
lemma pairCharge_secantProduct_row_field {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (DX F : X → ℝ)
    (hDX : ∀ x, DX x = pairCharge_rawDefectX P R x) :
    expect P (fun z => stoch_to_det.contactSecantX P R z.1 * stoch_to_det.contactSecantY P R z.2 * F z.1) =
      (expect P (fun z => (stoch_to_det.contactSecantX P R z.1)^2 * F z.1) -
        expect P (fun z => stoch_to_det.contactSecantX P R z.1 * DX z.1 * F z.1)) / 2 := by
  simpa only [mul_assoc, mul_left_comm, mul_comm, pow_two] using
    pairCharge_row_field hpair DX (fun x => stoch_to_det.contactSecantX P R x * F x) hDX

/-- Conditioning UV against an arbitrary column field. -/
lemma pairCharge_secantProduct_column_field {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (DY G : Y → ℝ)
    (hDY : ∀ y, DY y = pairCharge_rawDefectY P R y) :
    expect P (fun z => stoch_to_det.contactSecantX P R z.1 * stoch_to_det.contactSecantY P R z.2 * G z.2) =
      (expect P (fun z => (stoch_to_det.contactSecantY P R z.2)^2 * G z.2) -
        expect P (fun z => stoch_to_det.contactSecantY P R z.2 * DY z.2 * G z.2)) / 2 := by
  simpa only [mul_assoc, mul_left_comm, mul_comm, pow_two] using
    pairCharge_column_field hpair DY (fun y => stoch_to_det.contactSecantY P R y * G y) hDY

lemma pairCharge_defect_X_moments {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (DX : X → ℝ)
    (hDX : ∀ x, DX x = (∑ y, P (x,y) * (stoch_to_det.contactSecantY P R y)^2) / stoch_to_det.mX P x) :
    expect P (fun z => DX z.1) = 2 * defectY P R - defectX P R ∧
    expect P (fun z => stoch_to_det.contactSecantX P R z.1 * DX z.1) = (3 * (defectX P R - defectY P R) - quarticMoment P R) / 2 ∧
    expect P (fun z => (stoch_to_det.contactSecantX P R z.1)^2 * DX z.1) = quarticMoment P R := by
  have hm := contact_moments hpair
  constructor
  · simp_rw [hDX]
    rw [pairCharge_cond_X_mean hpair.2.1.1, hm.secantY_square]
  · constructor
    · calc
        _ = expect P (fun z => stoch_to_det.contactSecantX P R z.1 * (stoch_to_det.contactSecantY P R z.2)^2) := by
          simp_rw [hDX]
          exact pairCharge_cond_X_inner hpair.2.1.1 (stoch_to_det.contactSecantX P R) (fun y => (stoch_to_det.contactSecantY P R y)^2)
        _ = _ := (pairCharge_secant_mixed_moments hpair).1
    · simp_rw [hDX]
      exact pairCharge_cond_X_inner hpair.2.1.1 (fun x => (stoch_to_det.contactSecantX P R x)^2) (fun y => (stoch_to_det.contactSecantY P R y)^2)

lemma pairCharge_defect_Y_moments {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (DY : Y → ℝ)
    (hDY : ∀ y, DY y = (∑ x, P (x,y) * (stoch_to_det.contactSecantX P R x)^2) / stoch_to_det.mY P y) :
    expect P (fun z => DY z.2) = 2 * defectX P R - defectY P R ∧
    expect P (fun z => stoch_to_det.contactSecantY P R z.2 * DY z.2) = (-3 * (defectX P R - defectY P R) - quarticMoment P R) / 2 ∧
    expect P (fun z => (stoch_to_det.contactSecantY P R z.2)^2 * DY z.2) = quarticMoment P R := by
  have hm := contact_moments hpair
  constructor
  · simp_rw [hDY]
    rw [pairCharge_cond_Y_mean hpair.2.1.1, hm.secantX_square]
  · constructor
    · calc
        _ = expect P (fun z => stoch_to_det.contactSecantX P R z.1 ^ 2 * stoch_to_det.contactSecantY P R z.2) := by
          have htower := pairCharge_cond_Y_inner hpair.2.1.1 (fun x => (stoch_to_det.contactSecantX P R x)^2) (stoch_to_det.contactSecantY P R)
          simp_rw [← hDY] at htower
          calc
            _ = expect P (fun z => DY z.2 * stoch_to_det.contactSecantY P R z.2) := by congr 1; funext z; ring
            _ = _ := htower
        _ = _ := (pairCharge_secant_mixed_moments hpair).2
    · have htower := pairCharge_cond_Y_inner hpair.2.1.1 (fun x => (stoch_to_det.contactSecantX P R x)^2) (fun y => (stoch_to_det.contactSecantY P R y)^2)
      simp_rw [← hDY] at htower
      calc
        _ = expect P (fun z => DY z.2 * (stoch_to_det.contactSecantY P R z.2)^2) := by congr 1; funext z; ring
        _ = _ := htower

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_secantStatistic_additive_expectation (P : Law X Y) (u F : X → ℝ) (v G : Y → ℝ)
    (c : ℝ) (hc : c ≠ 0) :
    expect P (fun z => u z.1 * v z.2 / c * ((F z.1 + G z.2) / c - 1)) =
      (expect P (fun z => u z.1 * v z.2 * F z.1) +
        expect P (fun z => u z.1 * v z.2 * G z.2)) / c ^ 2 -
          expect P (fun z => u z.1 * v z.2) / c := by
  have hpoint (z : X × Y) :
      u z.1 * v z.2 / c * ((F z.1 + G z.2) / c - 1) =
      (u z.1 * v z.2 * F z.1 + u z.1 * v z.2 * G z.2) / c ^ 2 -
        u z.1 * v z.2 / c := by
    field_simp [hc]
  simp only [hpoint, contact_q_expect_sub, pairCharge_expect_div, contact_expect_add]

lemma pairCharge_secantStatistic_additive_product (P : Law X Y) (u F : X → ℝ) (v G : Y → ℝ)
    (c : ℝ) (hc : c ≠ 0) :
    expect (marginalProduct P) (fun z => u z.1 * v z.2 / c * ((F z.1 + G z.2) / c - 1)) =
      (expect P (fun z => u z.1 * F z.1) * expect P (fun z => v z.2) +
        expect P (fun z => u z.1) * expect P (fun z => v z.2 * G z.2)) / c ^ 2 -
          expect P (fun z => u z.1) * expect P (fun z => v z.2) / c := by
  have hf : (fun z : X × Y => u z.1 * v z.2 * F z.1) =
      (fun z => (u z.1 * F z.1) * v z.2) := by funext z; ring
  have hg : (fun z : X × Y => u z.1 * v z.2 * G z.2) =
      (fun z => u z.1 * (v z.2 * G z.2)) := by funext z; ring
  rw [pairCharge_secantStatistic_additive_expectation _ _ _ _ _ _ hc, hf, hg,
    pairCharge_expect_product P (fun x => u x * F x) v,
    pairCharge_expect_product P u (fun y => v y * G y), pairCharge_expect_product]


/-- The unaveraged contact endpoint for `H` and `defectY`. -/
lemma pairCharge_secantStatistic_correction_joint {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (DX : X → ℝ) (DY : Y → ℝ)
    (hDX : ∀ x, DX x = (∑ y, P (x,y) * (stoch_to_det.contactSecantY P R y)^2) / stoch_to_det.mX P x)
    (hDY : ∀ y, DY y = (∑ x, P (x,y) * (stoch_to_det.contactSecantX P R x)^2) / stoch_to_det.mY P y) :
    expect P (fun z => stoch_to_det.contactSecantX P R z.1 * stoch_to_det.contactSecantY P R z.2 / separation P R *
      ((DX z.1 + DY z.2) / separation P R - 1)) =
      quarticMoment P R / (separation P R)^2 - expect P (fun z => stoch_to_det.contactSecantX P R z.1 * stoch_to_det.contactSecantY P R z.2) / separation P R -
        (expect P (fun z => stoch_to_det.contactSecantX P R z.1 * (DX z.1)^2) +
          expect P (fun z => stoch_to_det.contactSecantY P R z.2 * (DY z.2)^2)) / (2 * (separation P R)^2) := by
  have hsne := (contact_moments hpair).separation_pos.ne'
  have hX := pairCharge_secantProduct_row_field hpair DX DX hDX
  have hY := pairCharge_secantProduct_column_field hpair DY DY hDY
  have hXsquare : expect P (fun z => stoch_to_det.contactSecantX P R z.1 * DX z.1 * DX z.1) =
      expect P (fun z => stoch_to_det.contactSecantX P R z.1 * (DX z.1)^2) := by congr 1; funext z; ring
  have hYsquare : expect P (fun z => stoch_to_det.contactSecantY P R z.2 * DY z.2 * DY z.2) =
      expect P (fun z => stoch_to_det.contactSecantY P R z.2 * (DY z.2)^2) := by congr 1; funext z; ring
  rw [(pairCharge_defect_X_moments hpair DX hDX).2.2, hXsquare] at hX
  rw [(pairCharge_defect_Y_moments hpair DY hDY).2.2, hYsquare] at hY
  rw [pairCharge_secantStatistic_additive_expectation _ _ _ _ _ _ hsne, hX, hY]
  field_simp [hsne]
  ring

/-- The product endpoint for `H` and `defectY`. -/
lemma pairCharge_secantStatistic_correction_product {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (DX : X → ℝ) (DY : Y → ℝ)
    (hDX : ∀ x, DX x = (∑ y, P (x,y) * (stoch_to_det.contactSecantY P R y)^2) / stoch_to_det.mX P x)
    (hDY : ∀ y, DY y = (∑ x, P (x,y) * (stoch_to_det.contactSecantX P R x)^2) / stoch_to_det.mY P y) :
    expect (marginalProduct P) (fun z => stoch_to_det.contactSecantX P R z.1 * stoch_to_det.contactSecantY P R z.2 / separation P R *
      ((DX z.1 + DY z.2) / separation P R - 1)) =
      (3 / 2 : ℝ) * ((defectX P R - defectY P R) / separation P R)^2 +
        quarticMoment P R / (2 * separation P R) - defectX P R * defectY P R / separation P R := by
  have hsne := (contact_moments hpair).separation_pos.ne'
  rw [pairCharge_secantStatistic_additive_product _ _ _ _ _ _ hsne,
    (pairCharge_defect_X_moments hpair DX hDX).2.1,
    (pairCharge_defect_Y_moments hpair DY hDY).2.1,
    (pairCharge_secant_means hpair).1, (pairCharge_secant_means hpair).2]
  have hs : separation P R = defectX P R + defectY P R := rfl
  field_simp [hsne]
  rw [hs]
  ring

end

end NaturalLatents.General
