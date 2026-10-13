-- Adapted from the author's earlier repository (StochasticToDeterministicLatents);
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised; namespace renamed to NaturalLatents.General.
import NaturalLatents.General.PairCharge.Gram

/-!
# Pair charge: defect fields and reversal identities

This module defines the raw row and column defect fields and proves their moments.
It supplies reversal identities for the features, conditional defects and weighted
second moments, together with the endpoint products of `UV/s` and the correction
`(DX + DY)/s - 1` under the joint and product laws.

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

/-- The row defect field used throughout the raw pair-charge estimates. -/
abbrev pairCharge_rawDX (P R : Law X Y) : X → ℝ := fun x =>
  (∑ y, P (x,y) * (V P R y)^2) / stoch_to_det.mX P x

/-- The column defect field used throughout the raw pair-charge estimates. -/
abbrev pairCharge_rawDY (P R : Law X Y) : Y → ℝ := fun y =>
  (∑ x, P (x,y) * (U P R x)^2) / stoch_to_det.mY P y

lemma pairCharge_U_reverse_scaled {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) {x : X} (hx : x ∈ XSupport S) :
    f P R x * U R P x = -U P R x := by
  have hf := pairCharge_f_reverse_mul hpair hx
  unfold f at hf ⊢
  nlinarith only [hf]

lemma pairCharge_V_reverse_scaled {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) {y : Y} (hy : y ∈ YSupport S) :
    g P R y * V R P y = -V P R y := by
  have hg := pairCharge_g_reverse_mul hpair hy
  unfold g at hg ⊢
  nlinarith only [hg]

lemma pairCharge_E_reverse_fst {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (F : X → ℝ) :
    E R (fun z => F z.1) = E P (fun z => (f P R z.1)^3 * F z.1) := by
  rw [contact_E_fst R F, contact_E_fst P (fun x => (f P R x)^3 * F x)]
  apply Finset.sum_congr rfl
  intro x _
  rw [← contact_f_cube hpair x]
  ring

lemma pairCharge_E_reverse_snd {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (G : Y → ℝ) :
    E R (fun z => G z.2) = E P (fun z => (g P R z.2)^3 * G z.2) := by
  rw [contact_E_snd R G, contact_E_snd P (fun y => (g P R y)^3 * G y)]
  apply Finset.sum_congr rfl
  intro y _
  rw [← contact_g_cube hpair y]
  ring

lemma pairCharge_cond_X_reverse_weight {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (G : Y → ℝ)
    {x : X} (hx : x ∈ XSupport S) :
    f P R x * ((∑ y, R (x,y) * G y) / stoch_to_det.mX R x) =
      (∑ y, P (x,y) * ((g P R y)^2 * G y)) / stoch_to_det.mX P x := by
  have hnum : (∑ y, R (x,y) * G y) =
      (f P R x)^2 * (∑ y, P (x,y) * ((g P R y)^2 * G y)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [contact_ratio_mul hpair (x,y)]
    ring
  rw [hnum, ← contact_f_cube hpair x]
  field_simp [(contact_mX_pos hpair.2.1 hpair.2.2.2.1 hx).ne',
    (contact_f_pos hpair hx).ne']

lemma pairCharge_cond_Y_reverse_weight {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (F : X → ℝ)
    {y : Y} (hy : y ∈ YSupport S) :
    g P R y * ((∑ x, R (x,y) * F x) / stoch_to_det.mY R y) =
      (∑ x, P (x,y) * ((f P R x)^2 * F x)) / stoch_to_det.mY P y := by
  have hnum : (∑ x, R (x,y) * F x) =
      (g P R y)^2 * (∑ x, P (x,y) * ((f P R x)^2 * F x)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [contact_ratio_mul hpair (x,y)]
    ring
  rw [hnum, ← contact_g_cube hpair y]
  field_simp [(contact_mY_pos hpair.2.1 hpair.2.2.2.1 hy).ne',
    (contact_g_pos hpair hy).ne']

lemma pairCharge_cond_defect_X_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R)
    {x : X} (hx : x ∈ XSupport S) :
    f P R x * ((∑ y, R (x,y) * (V R P y)^2) / stoch_to_det.mX R x) =
      (∑ y, P (x,y) * (V P R y)^2) / stoch_to_det.mX P x := by
  rw [pairCharge_cond_X_reverse_weight hpair (fun y => (V R P y)^2) hx]
  apply pairCharge_cond_X_congr_support hpair.2.1
  intro y hy
  rw [show (g P R y)^2 * (V R P y)^2 = (g P R y * V R P y)^2 by ring,
    pairCharge_V_reverse_scaled hpair hy]
  ring

lemma pairCharge_cond_defect_Y_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R)
    {y : Y} (hy : y ∈ YSupport S) :
    g P R y * ((∑ x, R (x,y) * (U R P x)^2) / stoch_to_det.mY R y) =
      (∑ x, P (x,y) * (U P R x)^2) / stoch_to_det.mY P y := by
  rw [pairCharge_cond_Y_reverse_weight hpair (fun x => (U R P x)^2) hy]
  apply pairCharge_cond_Y_congr_support hpair.2.1
  intro x hx
  rw [show (f P R x)^2 * (U R P x)^2 = (f P R x * U R P x)^2 by ring,
    pairCharge_U_reverse_scaled hpair hx]
  ring

lemma pairCharge_lambda_X_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (DX DXp : X → ℝ)
    (hDX : ∀ x ∈ XSupport S, f P R x * DXp x = DX x) :
    E R (fun z => U R P z.1 * (DXp z.1)^2) =
      -E P (fun z => U P R z.1 * (DX z.1)^2) := by
  rw [pairCharge_E_reverse_fst hpair (fun x => U R P x * (DXp x)^2)]
  calc
    _ = E P (fun z => -1 * (U P R z.1 * (DX z.1)^2)) := by
      apply pairCharge_E_congr_positive hpair.2.1.1
      intro z hz
      have hzS := pairCharge_mem_S_of_pos hpair.2.1 hz
      have hx : z.1 ∈ XSupport S := Finset.mem_image.mpr ⟨z, hzS, rfl⟩
      calc
        (f P R z.1)^3 * (U R P z.1 * (DXp z.1)^2) =
          (f P R z.1 * U R P z.1) * (f P R z.1 * DXp z.1)^2 := by ring
        _ = _ := by rw [pairCharge_U_reverse_scaled hpair hx, hDX _ hx]; ring
    _ = _ := by rw [contact_q_E_scale]; ring

lemma pairCharge_lambda_Y_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (DY DYp : Y → ℝ)
    (hDY : ∀ y ∈ YSupport S, g P R y * DYp y = DY y) :
    E R (fun z => V R P z.2 * (DYp z.2)^2) =
      -E P (fun z => V P R z.2 * (DY z.2)^2) := by
  rw [pairCharge_E_reverse_snd hpair (fun y => V R P y * (DYp y)^2)]
  calc
    _ = E P (fun z => -1 * (V P R z.2 * (DY z.2)^2)) := by
      apply pairCharge_E_congr_positive hpair.2.1.1
      intro z hz
      have hzS := pairCharge_mem_S_of_pos hpair.2.1 hz
      have hy : z.2 ∈ YSupport S := Finset.mem_image.mpr ⟨z, hzS, rfl⟩
      calc
        (g P R z.2)^3 * (V R P z.2 * (DYp z.2)^2) =
          (g P R z.2 * V R P z.2) * (g P R z.2 * DYp z.2)^2 := by ring
        _ = _ := by rw [pairCharge_V_reverse_scaled hpair hy, hDY _ hy]; ring
    _ = _ := by rw [contact_q_E_scale]; ring

lemma pairCharge_U_conditional_identity {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) {x : X} (hx : x ∈ XSupport S) :
    U P R x = 2 * ((∑ y, P (x,y) * V P R y) / stoch_to_det.mX P x) +
      (∑ y, P (x,y) * (V P R y)^2) / stoch_to_det.mX P x := by
  have hc := (contact_moments hpair).cond_g2 x hx
  have hs := pairCharge_cond_X_sq_add_one (V P R) (contact_mX_pos hpair.2.1 hpair.2.2.2.1 hx).ne'
  change (∑ y, P (x,y) * (V P R y + 1)^2) / stoch_to_det.mX P x = U P R x + 1 at hc
  rw [hs] at hc
  linarith

lemma pairCharge_V_conditional_identity {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) {y : Y} (hy : y ∈ YSupport S) :
    V P R y = 2 * ((∑ x, P (x,y) * U P R x) / stoch_to_det.mY P y) +
      (∑ x, P (x,y) * (U P R x)^2) / stoch_to_det.mY P y := by
  have hc := (contact_moments hpair).cond_f2 y hy
  have hs := pairCharge_cond_Y_sq_add_one (U P R) (contact_mY_pos hpair.2.1 hpair.2.2.2.1 hy).ne'
  change (∑ x, P (x,y) * (U P R x + 1)^2) / stoch_to_det.mY P y = V P R y + 1 at hc
  rw [hs] at hc
  linarith

/-- A row-field conditioning identity, shared by the raw UV and defect specializations. -/
lemma pairCharge_row_field {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (DX F : X → ℝ)
    (hDX : ∀ x, DX x = pairCharge_rawDX P R x) :
    E P (fun z => F z.1 * V P R z.2) =
      (E P (fun z => F z.1 * U P R z.1) - E P (fun z => F z.1 * DX z.1)) / 2 := by
  have htower := pairCharge_cond_X_inner hpair.2.1.1 F (V P R)
  have hpoint : ∀ z, 0 < P z →
      (∑ y, P (z.1,y) * V P R y) / stoch_to_det.mX P z.1 =
        (U P R z.1 - DX z.1) / 2 := by
    intro z hz
    have hx : z.1 ∈ XSupport S :=
      Finset.mem_image.mpr ⟨z, pairCharge_mem_S_of_pos hpair.2.1 hz, rfl⟩
    have hu := pairCharge_U_conditional_identity hpair hx
    have hd := hDX z.1
    dsimp [pairCharge_rawDX] at hd
    rw [← hd] at hu
    linarith only [hu]
  have hcongr : E P (fun z => F z.1 *
      ((∑ y, P (z.1,y) * V P R y) / stoch_to_det.mX P z.1)) =
      E P (fun z => (F z.1 * U P R z.1 - F z.1 * DX z.1) / 2) := by
    apply pairCharge_E_congr_positive hpair.2.1.1
    intro z hz
    rw [hpoint z hz]
    ring
  rw [hcongr, pairCharge_E_div, contact_q_E_sub] at htower
  exact htower.symm

/-- A column-field conditioning identity, shared by the raw UV and defect specializations. -/
lemma pairCharge_column_field {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (DY G : Y → ℝ)
    (hDY : ∀ y, DY y = pairCharge_rawDY P R y) :
    E P (fun z => U P R z.1 * G z.2) =
      (E P (fun z => V P R z.2 * G z.2) - E P (fun z => DY z.2 * G z.2)) / 2 := by
  have htower := pairCharge_cond_Y_inner hpair.2.1.1 (U P R) G
  have hpoint : ∀ z, 0 < P z →
      (∑ x, P (x,z.2) * U P R x) / stoch_to_det.mY P z.2 =
        (V P R z.2 - DY z.2) / 2 := by
    intro z hz
    have hy : z.2 ∈ YSupport S :=
      Finset.mem_image.mpr ⟨z, pairCharge_mem_S_of_pos hpair.2.1 hz, rfl⟩
    have hv := pairCharge_V_conditional_identity hpair hy
    have hd := hDY z.2
    dsimp [pairCharge_rawDY] at hd
    rw [← hd] at hv
    linarith only [hv]
  have hcongr : E P (fun z =>
      ((∑ x, P (x,z.2) * U P R x) / stoch_to_det.mY P z.2) * G z.2) =
      E P (fun z => (V P R z.2 * G z.2 - DY z.2 * G z.2) / 2) := by
    apply pairCharge_E_congr_positive hpair.2.1.1
    intro z hz
    rw [hpoint z hz]
    ring
  rw [hcongr, pairCharge_E_div, contact_q_E_sub] at htower
  exact htower.symm

/-- Conditioning UV against an arbitrary row field. -/
lemma pairCharge_UV_row_field {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (DX F : X → ℝ)
    (hDX : ∀ x, DX x = pairCharge_rawDX P R x) :
    E P (fun z => U P R z.1 * V P R z.2 * F z.1) =
      (E P (fun z => (U P R z.1)^2 * F z.1) -
        E P (fun z => U P R z.1 * DX z.1 * F z.1)) / 2 := by
  simpa only [mul_assoc, mul_left_comm, mul_comm, pow_two] using
    pairCharge_row_field hpair DX (fun x => U P R x * F x) hDX

/-- Conditioning UV against an arbitrary column field. -/
lemma pairCharge_UV_column_field {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (DY G : Y → ℝ)
    (hDY : ∀ y, DY y = pairCharge_rawDY P R y) :
    E P (fun z => U P R z.1 * V P R z.2 * G z.2) =
      (E P (fun z => (V P R z.2)^2 * G z.2) -
        E P (fun z => V P R z.2 * DY z.2 * G z.2)) / 2 := by
  simpa only [mul_assoc, mul_left_comm, mul_comm, pow_two] using
    pairCharge_column_field hpair DY (fun y => V P R y * G y) hDY

lemma pairCharge_defect_X_moments {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (DX : X → ℝ)
    (hDX : ∀ x, DX x = (∑ y, P (x,y) * (V P R y)^2) / stoch_to_det.mX P x) :
    E P (fun z => DX z.1) = 2 * B0 P R - A0 P R ∧
    E P (fun z => U P R z.1 * DX z.1) = (3 * (A0 P R - B0 P R) - J P R) / 2 ∧
    E P (fun z => (U P R z.1)^2 * DX z.1) = J P R := by
  have hm := contact_moments hpair
  constructor
  · simp_rw [hDX]
    rw [pairCharge_cond_X_mean hpair.2.1.1, hm.V2]
  · constructor
    · calc
        _ = E P (fun z => U P R z.1 * (V P R z.2)^2) := by
          simp_rw [hDX]
          exact pairCharge_cond_X_inner hpair.2.1.1 (U P R) (fun y => (V P R y)^2)
        _ = _ := (pairCharge_mixed_UV hpair).1
    · simp_rw [hDX]
      exact pairCharge_cond_X_inner hpair.2.1.1 (fun x => (U P R x)^2) (fun y => (V P R y)^2)

lemma pairCharge_defect_Y_moments {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (DY : Y → ℝ)
    (hDY : ∀ y, DY y = (∑ x, P (x,y) * (U P R x)^2) / stoch_to_det.mY P y) :
    E P (fun z => DY z.2) = 2 * A0 P R - B0 P R ∧
    E P (fun z => V P R z.2 * DY z.2) = (-3 * (A0 P R - B0 P R) - J P R) / 2 ∧
    E P (fun z => (V P R z.2)^2 * DY z.2) = J P R := by
  have hm := contact_moments hpair
  constructor
  · simp_rw [hDY]
    rw [pairCharge_cond_Y_mean hpair.2.1.1, hm.U2]
  · constructor
    · calc
        _ = E P (fun z => U P R z.1 ^ 2 * V P R z.2) := by
          have htower := pairCharge_cond_Y_inner hpair.2.1.1 (fun x => (U P R x)^2) (V P R)
          simp_rw [← hDY] at htower
          calc
            _ = E P (fun z => DY z.2 * V P R z.2) := by congr 1; funext z; ring
            _ = _ := htower
        _ = _ := (pairCharge_mixed_UV hpair).2
    · have htower := pairCharge_cond_Y_inner hpair.2.1.1 (fun x => (U P R x)^2) (fun y => (V P R y)^2)
      simp_rw [← hDY] at htower
      calc
        _ = E P (fun z => DY z.2 * (V P R z.2)^2) := by congr 1; funext z; ring
        _ = _ := htower

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_H_additive_expectation (P : Law X Y) (u F : X → ℝ) (v G : Y → ℝ)
    (c : ℝ) (hc : c ≠ 0) :
    E P (fun z => u z.1 * v z.2 / c * ((F z.1 + G z.2) / c - 1)) =
      (E P (fun z => u z.1 * v z.2 * F z.1) +
        E P (fun z => u z.1 * v z.2 * G z.2)) / c ^ 2 -
          E P (fun z => u z.1 * v z.2) / c := by
  have hpoint (z : X × Y) :
      u z.1 * v z.2 / c * ((F z.1 + G z.2) / c - 1) =
      (u z.1 * v z.2 * F z.1 + u z.1 * v z.2 * G z.2) / c ^ 2 -
        u z.1 * v z.2 / c := by
    field_simp [hc]
  simp only [hpoint, contact_q_E_sub, pairCharge_E_div, contact_E_add]

lemma pairCharge_H_additive_product (P : Law X Y) (u F : X → ℝ) (v G : Y → ℝ)
    (c : ℝ) (hc : c ≠ 0) :
    E (productLaw P) (fun z => u z.1 * v z.2 / c * ((F z.1 + G z.2) / c - 1)) =
      (E P (fun z => u z.1 * F z.1) * E P (fun z => v z.2) +
        E P (fun z => u z.1) * E P (fun z => v z.2 * G z.2)) / c ^ 2 -
          E P (fun z => u z.1) * E P (fun z => v z.2) / c := by
  have hf : (fun z : X × Y => u z.1 * v z.2 * F z.1) =
      (fun z => (u z.1 * F z.1) * v z.2) := by funext z; ring
  have hg : (fun z : X × Y => u z.1 * v z.2 * G z.2) =
      (fun z => u z.1 * (v z.2 * G z.2)) := by funext z; ring
  rw [pairCharge_H_additive_expectation _ _ _ _ _ _ hc, hf, hg,
    pairCharge_E_product P (fun x => u x * F x) v,
    pairCharge_E_product P u (fun y => v y * G y), pairCharge_E_product]


/-- The unaveraged contact endpoint for `H` and `B0`. -/
lemma pairCharge_HB0_joint {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (DX : X → ℝ) (DY : Y → ℝ)
    (hDX : ∀ x, DX x = (∑ y, P (x,y) * (V P R y)^2) / stoch_to_det.mX P x)
    (hDY : ∀ y, DY y = (∑ x, P (x,y) * (U P R x)^2) / stoch_to_det.mY P y) :
    E P (fun z => U P R z.1 * V P R z.2 / s P R *
      ((DX z.1 + DY z.2) / s P R - 1)) =
      J P R / (s P R)^2 - E P (fun z => U P R z.1 * V P R z.2) / s P R -
        (E P (fun z => U P R z.1 * (DX z.1)^2) +
          E P (fun z => V P R z.2 * (DY z.2)^2)) / (2 * (s P R)^2) := by
  have hsne := (contact_moments hpair).s_pos.ne'
  have hX := pairCharge_UV_row_field hpair DX DX hDX
  have hY := pairCharge_UV_column_field hpair DY DY hDY
  have hXsquare : E P (fun z => U P R z.1 * DX z.1 * DX z.1) =
      E P (fun z => U P R z.1 * (DX z.1)^2) := by congr 1; funext z; ring
  have hYsquare : E P (fun z => V P R z.2 * DY z.2 * DY z.2) =
      E P (fun z => V P R z.2 * (DY z.2)^2) := by congr 1; funext z; ring
  rw [(pairCharge_defect_X_moments hpair DX hDX).2.2, hXsquare] at hX
  rw [(pairCharge_defect_Y_moments hpair DY hDY).2.2, hYsquare] at hY
  rw [pairCharge_H_additive_expectation _ _ _ _ _ _ hsne, hX, hY]
  field_simp [hsne]
  ring

/-- The product endpoint for `H` and `B0`. -/
lemma pairCharge_HB0_product {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (DX : X → ℝ) (DY : Y → ℝ)
    (hDX : ∀ x, DX x = (∑ y, P (x,y) * (V P R y)^2) / stoch_to_det.mX P x)
    (hDY : ∀ y, DY y = (∑ x, P (x,y) * (U P R x)^2) / stoch_to_det.mY P y) :
    E (productLaw P) (fun z => U P R z.1 * V P R z.2 / s P R *
      ((DX z.1 + DY z.2) / s P R - 1)) =
      (3 / 2 : ℝ) * ((A0 P R - B0 P R) / s P R)^2 +
        J P R / (2 * s P R) - A0 P R * B0 P R / s P R := by
  have hsne := (contact_moments hpair).s_pos.ne'
  rw [pairCharge_H_additive_product _ _ _ _ _ _ hsne,
    (pairCharge_defect_X_moments hpair DX hDX).2.1,
    (pairCharge_defect_Y_moments hpair DY hDY).2.1,
    (pairCharge_mean_UV hpair).1, (pairCharge_mean_UV hpair).2]
  have hs : s P R = A0 P R + B0 P R := rfl
  field_simp [hsne]
  rw [hs]
  ring

end

end NaturalLatents.General
