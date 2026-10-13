-- Adapted from the author's earlier repository (StochasticToDeterministicLatents);
-- modified: module paths renamed; declarations unused by the main theorems removed.
import NaturalLatents.General.PairCharge.Gram

/-!
# Pair charge: features, reversal and averaged identities

Fourth part of the pair charge. The raw conditional features on the whole marginal rectangle,
their additive variance and covariance bounds, the exchange of the two contacts, and the
identities for the unaveraged and averaged endpoints of the entropy payments.

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

/-- The row defect field used throughout the raw pair-charge estimates. -/
abbrev pairCharge_rawDX (P R : Law X Y) : X → ℝ := fun x =>
  (∑ y, P (x,y) * (V P R y)^2) / stoch_to_det.mX P x

/-- The column defect field used throughout the raw pair-charge estimates. -/
abbrev pairCharge_rawDY (P R : Law X Y) : Y → ℝ := fun y =>
  (∑ x, P (x,y) * (U P R x)^2) / stoch_to_det.mY P y

/-- The combined raw feature built from the row and column defect fields. -/
abbrev pairCharge_rawC (P R : Law X Y) : X × Y → ℝ := fun z =>
  ((pairCharge_rawDX P R z.1 + pairCharge_rawDY P R z.2) / s P R - 1) +
  (((∑ y, P (z.1,y) * pairCharge_rawDY P R y) / stoch_to_det.mX P z.1 +
    (∑ x, P (x,z.2) * pairCharge_rawDX P R x) / stoch_to_det.mY P z.2) / s P R - 1)

/-- The linear raw feature paired with `pairCharge_rawC`. -/
abbrev pairCharge_rawL (P R : Law X Y) : X × Y → ℝ := fun z =>
  U P R z.1 + V P R z.2 + s P R

lemma pairCharge_raw_feature_operator_bridge {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R)
    (B : ((X → ℝ) × (Y → ℝ)) →ₗ[ℝ] ((X → ℝ) × (Y → ℝ)) →ₗ[ℝ] ℝ)
    (K : ((X → ℝ) × (Y → ℝ)) →ₗ[ℝ] ((X → ℝ) × (Y → ℝ)))
    (hB : ∀ p q, B p q = E P (fun z => p.1 z.1 * q.1 z.1) +
      E P (fun z => p.2 z.2 * q.2 z.2))
    (hKX : ∀ p, (K p).1 = fun x => (∑ y, P (x,y) * p.2 y) / stoch_to_det.mX P x)
    (hKY : ∀ p, (K p).2 = fun y => (∑ x, P (x,y) * p.1 x) / stoch_to_det.mY P y) :
    let DX := pairCharge_rawDX P R
    let DY := pairCharge_rawDY P R
    let u : (X → ℝ) × (Y → ℝ) := (fun x => U P R x + A0 P R, fun y => V P R y + B0 P R)
    let d := u - (2 : ℝ) • K u
    let p := d + K d
    let Craw : X × Y → ℝ := fun z =>
      ((DX z.1 + DY z.2) / s P R - 1) +
      (((∑ y, P (z.1,y) * DY y) / stoch_to_det.mX P z.1 +
        (∑ x, P (x,z.2) * DX x) / stoch_to_det.mY P z.2) / s P R - 1)
    (∀ x ∈ XSupport S, d.1 x = DX x - (2 * B0 P R - A0 P R)) ∧
    (∀ y ∈ YSupport S, d.2 y = DY y - (2 * A0 P R - B0 P R)) ∧
    (∀ z ∈ MarginalRectangle S, (p.1 z.1 + p.2 z.2) / s P R = Craw z) ∧
    B d d = E P (fun z => (DX z.1 - (2 * B0 P R - A0 P R))^2) +
      E P (fun z => (DY z.2 - (2 * A0 P R - B0 P R))^2) := by
  let DX := pairCharge_rawDX P R
  let DY := pairCharge_rawDY P R
  let mX := 2 * B0 P R - A0 P R
  let mY := 2 * A0 P R - B0 P R
  let u : (X → ℝ) × (Y → ℝ) := (fun x => U P R x + A0 P R, fun y => V P R y + B0 P R)
  let d := u - (2 : ℝ) • K u
  let p := d + K d
  let Craw : X × Y → ℝ := fun z =>
    ((DX z.1 + DY z.2) / s P R - 1) +
    (((∑ y, P (z.1,y) * DY y) / stoch_to_det.mX P z.1 +
      (∑ x, P (x,z.2) * DX x) / stoch_to_det.mY P z.2) / s P R - 1)
  change (∀ x ∈ XSupport S, d.1 x = DX x - mX) ∧
    (∀ y ∈ YSupport S, d.2 y = DY y - mY) ∧
    (∀ z ∈ MarginalRectangle S, (p.1 z.1 + p.2 z.2) / s P R = Craw z) ∧
    B d d = E P (fun z => (DX z.1 - mX)^2) + E P (fun z => (DY z.2 - mY)^2)
  have hdX : ∀ x ∈ XSupport S, d.1 x = DX x - mX := by
    intro x hx
    change U P R x + A0 P R - 2 * (K u).1 x = DX x - mX
    rw [hKX]
    exact (pairCharge_contact_defect_X hpair hx).symm
  have hdY : ∀ y ∈ YSupport S, d.2 y = DY y - mY := by
    intro y hy
    change V P R y + B0 P R - 2 * (K u).2 y = DY y - mY
    rw [hKY]
    exact (pairCharge_contact_defect_Y hpair hy).symm
  have hpX : ∀ x ∈ XSupport S, p.1 x =
      DX x + (∑ y, P (x,y) * DY y) / stoch_to_det.mX P x - s P R := by
    intro x hx
    have hxne := (contact_mX_pos hpair.2.1 hpair.2.2.2.1 hx).ne'
    have hc := pairCharge_cond_X_congr_support hpair.2.1 d.2 (fun y => DY y - mY) hdY x
    have ha : (∑ y, P (x,y) * (DY y - mY)) / stoch_to_det.mX P x =
        (∑ y, P (x,y) * DY y) / stoch_to_det.mX P x - mY := by
      simpa only [one_mul, sub_eq_add_neg] using pairCharge_cond_X_affine DY 1 (-mY) hxne
    change d.1 x + (K d).1 x = _
    rw [hdX x hx, hKX]
    dsimp only
    rw [hc, ha]
    have hs := pairCharge_s_eq_A0_add_B0 P R
    dsimp [mX, mY]
    linarith
  have hpY : ∀ y ∈ YSupport S, p.2 y =
      DY y + (∑ x, P (x,y) * DX x) / stoch_to_det.mY P y - s P R := by
    intro y hy
    have hyne := (contact_mY_pos hpair.2.1 hpair.2.2.2.1 hy).ne'
    have hc := pairCharge_cond_Y_congr_support hpair.2.1 d.1 (fun x => DX x - mX) hdX y
    have ha : (∑ x, P (x,y) * (DX x - mX)) / stoch_to_det.mY P y =
        (∑ x, P (x,y) * DX x) / stoch_to_det.mY P y - mX := by
      simpa only [one_mul, sub_eq_add_neg] using pairCharge_cond_Y_affine DX 1 (-mX) hyne
    change d.2 y + (K d).2 y = _
    rw [hdY y hy, hKY]
    dsimp only
    rw [hc, ha]
    have hs := pairCharge_s_eq_A0_add_B0 P R
    dsimp [mX, mY]
    linarith
  refine ⟨hdX, hdY, ?_, ?_⟩
  · intro z hz
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hz
    rw [hpX z.1 hx, hpY z.2 hy]
    dsimp [Craw]
    field_simp [(contact_moments hpair).s_pos.ne']
    ring
  · rw [hB]
    have hxE : E P (fun z => d.1 z.1 * d.1 z.1) =
        E P (fun z => (DX z.1 - mX)^2) := by
      apply pairCharge_E_congr_positive hpair.2.1.1
      intro z hz
      rw [hdX z.1 (Finset.mem_image.mpr ⟨z, pairCharge_mem_S_of_pos hpair.2.1 hz, rfl⟩)]
      ring
    have hyE : E P (fun z => d.2 z.2 * d.2 z.2) =
        E P (fun z => (DY z.2 - mY)^2) := by
      apply pairCharge_E_congr_positive hpair.2.1.1
      intro z hz
      rw [hdY z.2 (Finset.mem_image.mpr ⟨z, pairCharge_mem_S_of_pos hpair.2.1 hz, rfl⟩)]
      ring
    rw [hxE, hyE]

lemma pairCharge_raw_additive_variance_bound {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    let DX := pairCharge_rawDX P R
    let DY := pairCharge_rawDY P R
    let C := pairCharge_rawC P R
    let xP := (E P (fun z => (DX z.1 - (2 * B0 P R - A0 P R))^2) +
      E P (fun z => (DY z.2 - (2 * A0 P R - B0 P R))^2)) / (s P R)^2
    let t0 := 6 * (A0 P R * B0 P R / (s P R)^2) - 1 - contactj P R
    60 * (E (productLaw P) (fun z => (C z)^2) / 30 +
      E P (fun z => (C z)^2) / 20) ≤ (17/10 : ℝ) * t0 + (23/4 : ℝ) * xP := by
  let DX := pairCharge_rawDX P R
  let DY := pairCharge_rawDY P R
  let C := pairCharge_rawC P R
  let n := E P (fun z => (DX z.1 - (2 * B0 P R - A0 P R))^2) +
    E P (fun z => (DY z.2 - (2 * A0 P R - B0 P R))^2)
  let xP := n / (s P R)^2
  let t0 := 6 * (A0 P R * B0 P R / (s P R)^2) - 1 - contactj P R
  change 60 * (E (productLaw P) (fun z => (C z)^2) / 30 +
    E P (fun z => (C z)^2) / 20) ≤ (17/10 : ℝ) * t0 + (23/4 : ℝ) * xP
  obtain ⟨B, K, hB, hKX, hKY, hself, hpos, hmean⟩ := pairCharge_finite_conditional_geometry hpair
  let u : (X → ℝ) × (Y → ℝ) :=
    (fun x => U P R x + A0 P R, fun y => V P R y + B0 P R)
  let d := u - (2 : ℝ) • K u
  let p := d + K d
  let Cop : X × Y → ℝ := fun z => (p.1 z.1 + p.2 z.2) / s P R
  have hb := pairCharge_raw_feature_operator_bridge hpair B K hB hKX hKY
  change (∀ x ∈ XSupport S, d.1 x = DX x - (2 * B0 P R - A0 P R)) ∧
    (∀ y ∈ YSupport S, d.2 y = DY y - (2 * A0 P R - B0 P R)) ∧
    (∀ z ∈ MarginalRectangle S, Cop z = C z) ∧ B d d = n at hb
  have he := pairCharge_E_congr_rectangle hpair.2.1 (fun z => (Cop z)^2) (fun z => (C z)^2)
    (fun z hz => congrArg (fun q : ℝ => q^2) (hb.2.2.1 z hz))
  have hv := pairCharge_contact_additive_variance_bound hpair B K hB hKX hKY hself hpos hmean
  change 60 * (s P R)^2 *
    (E (productLaw P) (fun z => (Cop z)^2) / 30 + E P (fun z => (Cop z)^2) / 20) ≤
    (17/10 : ℝ) * (6 * A0 P R * B0 P R - (s P R)^2 - J P R) +
      (23/4 : ℝ) * B d d at hv
  rw [he.1, he.2, hb.2.2.2] at hv
  have hs := (contact_moments hpair).s_pos
  have hid : ((17/10 : ℝ) * t0 + (23/4 : ℝ) * xP) * (s P R)^2 =
      (17/10 : ℝ) * (6 * A0 P R * B0 P R - (s P R)^2 - J P R) +
        (23/4 : ℝ) * n := by
    dsimp [t0, xP, contactj]
    field_simp [hs.ne']
  apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hs)).mp
  rw [hid]
  nlinarith [hv]

-- The raw fields on the whole marginal rectangle.
lemma pairCharge_raw_LC_identity {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    let DX := pairCharge_rawDX P R
    let DY := pairCharge_rawDY P R
    let C := pairCharge_rawC P R
    let L := pairCharge_rawL P R
    let n := E P (fun z => (DX z.1 - (2 * B0 P R - A0 P R))^2) +
      E P (fun z => (DY z.2 - (2 * A0 P R - B0 P R))^2)
    let e := E P (fun z => (DX z.1 - (2 * B0 P R - A0 P R)) *
      (DY z.2 - (2 * A0 P R - B0 P R)))
    let xP := n / (s P R)^2
    let cP := 2 * e / (s P R)^2
    let t0 := 6 * (A0 P R * B0 P R / (s P R)^2) - 1 - contactj P R
    (E (productLaw P) (fun z => L z * C z) + E P (fun z => L z * C z)) / 12 =
      s P R / 48 * (15 * t0 - 7 * xP - 2 * cP) := by
  let DX := pairCharge_rawDX P R
  let DY := pairCharge_rawDY P R
  let C := pairCharge_rawC P R
  let L := pairCharge_rawL P R
  let n := E P (fun z => (DX z.1 - (2 * B0 P R - A0 P R))^2) +
    E P (fun z => (DY z.2 - (2 * A0 P R - B0 P R))^2)
  let e := E P (fun z => (DX z.1 - (2 * B0 P R - A0 P R)) *
    (DY z.2 - (2 * A0 P R - B0 P R)))
  let xP := n / (s P R)^2
  let cP := 2 * e / (s P R)^2
  let t0 := 6 * (A0 P R * B0 P R / (s P R)^2) - 1 - contactj P R
  let T := 6 * A0 P R * B0 P R - (s P R)^2 - J P R
  change (E (productLaw P) (fun z => L z * C z) + E P (fun z => L z * C z)) / 12 =
    s P R / 48 * (15 * t0 - 7 * xP - 2 * cP)
  obtain ⟨B, K, hB, hKX, hKY, hself, hpos, hmean⟩ := pairCharge_finite_conditional_geometry hpair
  let u : (X → ℝ) × (Y → ℝ) :=
    (fun x => U P R x + A0 P R, fun y => V P R y + B0 P R)
  let d := u - (2 : ℝ) • K u
  let p := d + K d
  let Cop : X × Y → ℝ := fun z => (p.1 z.1 + p.2 z.2) / s P R
  have hb := pairCharge_raw_feature_operator_bridge hpair B K hB hKX hKY
  change (∀ x ∈ XSupport S, d.1 x = DX x - (2 * B0 P R - A0 P R)) ∧
    (∀ y ∈ YSupport S, d.2 y = DY y - (2 * A0 P R - B0 P R)) ∧
    (∀ z ∈ MarginalRectangle S, Cop z = C z) ∧ B d d = n at hb
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
  have hL (z : X × Y) : L z = u.1 z.1 + u.2 z.2 := by
    dsimp [L, u, pairCharge_rawL]
    rw [pairCharge_s_eq_A0_add_B0]
    ring
  have he := pairCharge_E_congr_rectangle hpair.2.1
    (fun z => (u.1 z.1 + u.2 z.2) * Cop z) (fun z => L z * C z)
    (fun z hz => by rw [hb.2.2.1 z hz, hL])
  have hcov := pairCharge_additive_covariance_geometry hpair.2.1.1 B K hB hKX hKY
    u p huX huY hpX hpY
  have hscale (Q : Law X Y) :
      E Q (fun z => (u.1 z.1 + u.2 z.2) * Cop z) =
      E Q (fun z => (u.1 z.1 + u.2 z.2) * (p.1 z.1 + p.2 z.2)) / s P R := by
    calc
      _ = E Q (fun z => ((u.1 z.1 + u.2 z.2) * (p.1 z.1 + p.2 z.2)) / s P R) := by
        congr 1
        funext z
        dsimp [Cop]
        ring
      _ = _ := pairCharge_E_div Q _ _
  have hQ : E (productLaw P) (fun z => L z * C z) = B u p / s P R := by
    rw [← he.2, hscale, hcov.1]
  have hP : E P (fun z => L z * C z) = (B u p + B u (K p)) / s P R := by
    rw [← he.1, hscale, hcov.2]
  have hcross (q : (X → ℝ) × (Y → ℝ)) :
      B q (K q) = 2 * E P (fun z => q.1 z.1 * q.2 z.2) := by
    rw [hB, hKX, hKY, pairCharge_cond_X_inner hpair.2.1.1]
    rw [pairCharge_E_mul_comm P (fun z => q.2 z.2)
      (fun z => (∑ x, P (x,z.2) * q.1 x) / stoch_to_det.mY P z.2),
      pairCharge_cond_Y_inner hpair.2.1.1]
    ring
  have henergy : B u d = T := by
    change B u (u - (2 : ℝ) • K u) = T
    rw [map_sub, map_smul, smul_eq_mul, hB, hcross]
    change E P (fun z => (U P R z.1 + A0 P R) * (U P R z.1 + A0 P R)) +
      E P (fun z => (V P R z.2 + B0 P R) * (V P R z.2 + B0 P R)) -
      2 * (2 * E P (fun z => (U P R z.1 + A0 P R) * (V P R z.2 + B0 P R))) = T
    have hg := pairCharge_contact_gram_energy hpair
    simp only [pow_two] at hg
    linarith [hg]
  have hde : B d (K d) = 2 * e := by
    rw [hcross]
    congr 1
    apply pairCharge_E_congr_positive hpair.2.1.1
    intro z hz
    have hzS := pairCharge_mem_S_of_pos hpair.2.1 hz
    rw [hb.1 z.1 (Finset.mem_image.mpr ⟨z, hzS, rfl⟩),
      hb.2.1 z.2 (Finset.mem_image.mpr ⟨z, hzS, rfl⟩)]
  have hid := pairCharge_operator_LC_identity B K hself u
  change 4 * (2 * B u p + B u (K p)) =
    15 * B u d - 7 * B d d - 2 * B d (K d) at hid
  rw [henergy, hb.2.2.2, hde] at hid
  have hrhs : s P R / 48 * (15 * t0 - 7 * xP - 2 * cP) =
      (15 * T - 7 * n - 4 * e) / (48 * s P R) := by
    dsimp [t0, xP, cP, T, contactj]
    field_simp [(contact_moments hpair).s_pos.ne']
    ring
  rw [hQ, hP, hrhs]
  calc
    _ = (4 * (2 * B u p + B u (K p))) / (48 * s P R) := by ring
    _ = _ := by rw [hid]; ring

lemma pairCharge_raw_LC_bound {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    let DX := pairCharge_rawDX P R
    let DY := pairCharge_rawDY P R
    let C := pairCharge_rawC P R
    let L := pairCharge_rawL P R
    let xP := (E P (fun z => (DX z.1 - (2 * B0 P R - A0 P R))^2) +
      E P (fun z => (DY z.2 - (2 * A0 P R - B0 P R))^2)) / (s P R)^2
    let t0 := 6 * (A0 P R * B0 P R / (s P R)^2) - 1 - contactj P R
    s P R / 48 * (15 * t0 - 8 * xP + xP^2 / t0) ≤
      (E (productLaw P) (fun z => L z * C z) + E P (fun z => L z * C z)) / 12 := by
  dsimp only
  rw [pairCharge_raw_LC_identity hpair]
  have hg := pairCharge_raw_gram_bounds hpair
  dsimp only at hg
  have hs := (contact_moments hpair).s_pos
  have hquot (q : ℝ) : q^2 / (2 * (6 * (A0 P R * B0 P R / (s P R)^2) - 1 - contactj P R)) =
      (q^2 / (6 * (A0 P R * B0 P R / (s P R)^2) - 1 - contactj P R)) / 2 := by
    rw [mul_comm (2 : ℝ) _, div_mul_eq_div_div]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hs.le (by norm_num))
  rw [hquot] at hg
  linarith [hg.2.2.2]

lemma pairCharge_raw_LC_average_bound {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    let DX := pairCharge_rawDX (X := X) (Y := Y)
    let DY := pairCharge_rawDY (X := X) (Y := Y)
    let C := pairCharge_rawC (X := X) (Y := Y)
    let L := pairCharge_rawL (X := X) (Y := Y)
    let xP := (E P (fun z => (DX P R z.1 - (2 * B0 P R - A0 P R))^2) +
      E P (fun z => (DY P R z.2 - (2 * A0 P R - B0 P R))^2)) / (s P R)^2
    let xR := (E R (fun z => (DX R P z.1 - (2 * B0 R P - A0 R P))^2) +
      E R (fun z => (DY R P z.2 - (2 * A0 R P - B0 R P))^2)) / (s R P)^2
    let xavg := (xP + xR) / 2
    let t0 := 6 * (A0 P R * B0 P R / (s P R)^2) - 1 - contactj P R
    let NP := (E (productLaw P) (fun z => L P R z * C P R z) +
      E P (fun z => L P R z * C P R z)) / 12
    let NR := (E (productLaw R) (fun z => L R P z * C R P z) +
      E R (fun z => L R P z * C R P z)) / 12
    0 < t0 ∧ 0 ≤ xavg ∧ xavg ≤ 2 * t0 ∧
      s P R / 48 * (15 * t0 - 8 * xavg + xavg^2 / t0) ≤ (NP + NR) / 2 := by
  let DX := pairCharge_rawDX (X := X) (Y := Y)
  let DY := pairCharge_rawDY (X := X) (Y := Y)
  let C := pairCharge_rawC (X := X) (Y := Y)
  let L := pairCharge_rawL (X := X) (Y := Y)
  let xP := (E P (fun z => (DX P R z.1 - (2 * B0 P R - A0 P R))^2) +
    E P (fun z => (DY P R z.2 - (2 * A0 P R - B0 P R))^2)) / (s P R)^2
  let xR := (E R (fun z => (DX R P z.1 - (2 * B0 R P - A0 R P))^2) +
    E R (fun z => (DY R P z.2 - (2 * A0 R P - B0 R P))^2)) / (s R P)^2
  let xavg := (xP + xR) / 2
  let t0 := 6 * (A0 P R * B0 P R / (s P R)^2) - 1 - contactj P R
  let t0r := 6 * (A0 R P * B0 R P / (s R P)^2) - 1 - contactj R P
  let NP := (E (productLaw P) (fun z => L P R z * C P R z) +
    E P (fun z => L P R z * C P R z)) / 12
  let NR := (E (productLaw R) (fun z => L R P z * C R P z) +
    E R (fun z => L R P z * C R P z)) / 12
  change 0 < t0 ∧ 0 ≤ xavg ∧ xavg ≤ 2 * t0 ∧
    s P R / 48 * (15 * t0 - 8 * xavg + xavg^2 / t0) ≤ (NP + NR) / 2
  have ht0r : t0r = t0 := by
    dsimp [t0r, t0]
    rw [pairCharge_v_reverse hpair, pairCharge_contactj_reverse hpair]
  have hgP := pairCharge_raw_gram_bounds hpair
  have hgR := pairCharge_raw_gram_bounds (pairCharge_pair_reverse hpair)
  have ht : 0 < t0 := hgP.1
  have hxP : 0 ≤ xP := hgP.2.1
  have hxR : 0 ≤ xR := hgR.2.1
  have hxPhi : xP ≤ 2 * t0 := hgP.2.2.1
  have hxRhi : xR ≤ 2 * t0 := by
    have hi := hgR.2.2.1
    change xR ≤ 2 * t0r at hi
    rw [ht0r] at hi
    exact hi
  have hP := pairCharge_raw_LC_bound hpair
  change s P R / 48 * (15 * t0 - 8 * xP + xP^2 / t0) ≤ NP at hP
  have hR := pairCharge_raw_LC_bound (pairCharge_pair_reverse hpair)
  change s R P / 48 * (15 * t0r - 8 * xR + xR^2 / t0r) ≤ NR at hR
  rw [ht0r, pairCharge_s_reverse hpair] at hR
  have hx : 0 ≤ xavg := by dsimp [xavg]; linarith
  have hxhi : xavg ≤ 2 * t0 := by dsimp [xavg]; linarith
  have hconv : xavg^2 / t0 ≤ (xP^2 / t0 + xR^2 / t0) / 2 := by
    have hc : xavg^2 ≤ (xP^2 + xR^2) / 2 := by
      dsimp [xavg]
      nlinarith [sq_nonneg (xP - xR)]
    calc
      _ ≤ ((xP^2 + xR^2) / 2) / t0 := div_le_div_of_nonneg_right hc ht.le
      _ = _ := by ring
  refine ⟨ht, hx, hxhi, ?_⟩
  have hs := (contact_moments hpair).s_pos
  have hscaled := mul_le_mul_of_nonneg_left hconv (div_nonneg hs.le (show (0 : ℝ) ≤ 48 by norm_num))
  dsimp [xavg] at hscaled ⊢
  nlinarith [hP, hR, hscaled]

lemma pairCharge_raw_additive_variance_average_bound {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    let DX := pairCharge_rawDX (X := X) (Y := Y)
    let DY := pairCharge_rawDY (X := X) (Y := Y)
    let C := pairCharge_rawC (X := X) (Y := Y)
    let xP := (E P (fun z => (DX P R z.1 - (2 * B0 P R - A0 P R))^2) +
      E P (fun z => (DY P R z.2 - (2 * A0 P R - B0 P R))^2)) / (s P R)^2
    let xR := (E R (fun z => (DX R P z.1 - (2 * B0 R P - A0 R P))^2) +
      E R (fun z => (DY R P z.2 - (2 * A0 R P - B0 R P))^2)) / (s R P)^2
    let xavg := (xP + xR) / 2
    let t := (1/2 : ℝ) - contactj P R
    let WP := E (productLaw P) (fun z => (C P R z)^2) / 30 +
      E P (fun z => (C P R z)^2) / 20
    let WR := E (productLaw R) (fun z => (C R P z)^2) / 30 +
      E R (fun z => (C R P z)^2) / 20
    0 < t ∧ (WP + WR) / 2 ≤ ((17/10 : ℝ) * t + (23/4 : ℝ) * xavg) / 60 := by
  let DX := pairCharge_rawDX (X := X) (Y := Y)
  let DY := pairCharge_rawDY (X := X) (Y := Y)
  let C := pairCharge_rawC (X := X) (Y := Y)
  let xP := (E P (fun z => (DX P R z.1 - (2 * B0 P R - A0 P R))^2) +
    E P (fun z => (DY P R z.2 - (2 * A0 P R - B0 P R))^2)) / (s P R)^2
  let xR := (E R (fun z => (DX R P z.1 - (2 * B0 R P - A0 R P))^2) +
    E R (fun z => (DY R P z.2 - (2 * A0 R P - B0 R P))^2)) / (s R P)^2
  let xavg := (xP + xR) / 2
  let t := (1/2 : ℝ) - contactj P R
  let t0 := 6 * (A0 P R * B0 P R / (s P R)^2) - 1 - contactj P R
  let t0r := 6 * (A0 R P * B0 R P / (s R P)^2) - 1 - contactj R P
  let WP := E (productLaw P) (fun z => (C P R z)^2) / 30 +
    E P (fun z => (C P R z)^2) / 20
  let WR := E (productLaw R) (fun z => (C R P z)^2) / 30 +
    E R (fun z => (C R P z)^2) / 20
  change 0 < t ∧ (WP + WR) / 2 ≤ ((17/10 : ℝ) * t + (23/4 : ℝ) * xavg) / 60
  have ht : 0 < t := by dsimp [t]; linarith [pairCharge_contactj_lt_half hpair]
  have ht0r : t0r = t0 := by
    dsimp [t0r, t0]
    rw [pairCharge_v_reverse hpair, pairCharge_contactj_reverse hpair]
  have ht0le : t0 ≤ t := by dsimp [t0, t]; linarith [(pairCharge_v_bounds hpair).2]
  have hP := pairCharge_raw_additive_variance_bound hpair
  change 60 * WP ≤ (17/10 : ℝ) * t0 + (23/4 : ℝ) * xP at hP
  have hR := pairCharge_raw_additive_variance_bound (pairCharge_pair_reverse hpair)
  change 60 * WR ≤ (17/10 : ℝ) * t0r + (23/4 : ℝ) * xR at hR
  rw [ht0r] at hR
  refine ⟨ht, ?_⟩
  dsimp [xavg]
  linarith [hP, hR, ht0le]

lemma pairCharge_raw_C_means {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    let C := pairCharge_rawC P R
    E P C = 0 ∧ E (productLaw P) C = 0 := by
  let DX := pairCharge_rawDX P R
  let DY := pairCharge_rawDY P R
  let PX : X → ℝ := fun x => (∑ y, P (x,y) * DY y) / stoch_to_det.mX P x
  let PY : Y → ℝ := fun y => (∑ x, P (x,y) * DX x) / stoch_to_det.mY P y
  let C : X × Y → ℝ := fun z =>
    ((DX z.1 + DY z.2) / s P R - 1) + ((PX z.1 + PY z.2) / s P R - 1)
  change E P C = 0 ∧ E (productLaw P) C = 0
  have hDX : E P (fun z => DX z.1) = 2 * B0 P R - A0 P R := by
    change E P (fun z => (∑ y, P (z.1,y) * (V P R y)^2) / stoch_to_det.mX P z.1) = _
    rw [pairCharge_cond_X_mean hpair.2.1.1, (contact_moments hpair).V2]
  have hDY : E P (fun z => DY z.2) = 2 * A0 P R - B0 P R := by
    change E P (fun z => (∑ x, P (x,z.2) * (U P R x)^2) / stoch_to_det.mY P z.2) = _
    rw [pairCharge_cond_Y_mean hpair.2.1.1, (contact_moments hpair).U2]
  have hPX : E P (fun z => PX z.1) = 2 * A0 P R - B0 P R := by
    change E P (fun z => (∑ y, P (z.1,y) * DY y) / stoch_to_det.mX P z.1) = _
    rw [pairCharge_cond_X_mean hpair.2.1.1, hDY]
  have hPY : E P (fun z => PY z.2) = 2 * B0 P R - A0 P R := by
    change E P (fun z => (∑ x, P (x,z.2) * DX x) / stoch_to_det.mY P z.2) = _
    rw [pairCharge_cond_Y_mean hpair.2.1.1, hDX]
  have hs := pairCharge_s_eq_A0_add_B0 P R
  constructor
  · simp only [C, contact_q_E_add, contact_q_E_sub, pairCharge_E_div, contact_q_E_const hpair.2.1.1,
      hDX, hDY, hPX, hPY]
    field_simp [(contact_moments hpair).s_pos.ne']
    linarith [hs]
  · simp only [C, contact_q_E_add, contact_q_E_sub, pairCharge_E_div,
      contact_q_E_const (pairCharge_product_isPMF hpair.2.1.1),
      pairCharge_E_product_fst hpair.2.1.1, pairCharge_E_product_snd hpair.2.1.1,
      hDX, hDY, hPX, hPY]
    field_simp [(contact_moments hpair).s_pos.ne']
    linarith [hs]

-- Actual contact reversal and finite feature identities.

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
  rw [contact_q_E_fst R F, contact_q_E_fst P (fun x => (f P R x)^3 * F x)]
  apply Finset.sum_congr rfl
  intro x _
  rw [← contact_f_cube hpair x]
  ring

lemma pairCharge_E_reverse_snd {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (G : Y → ℝ) :
    E R (fun z => G z.2) = E P (fun z => (g P R z.2)^3 * G z.2) := by
  rw [contact_q_E_snd R G, contact_q_E_snd P (fun y => (g P R y)^3 * G y)]
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

lemma pairCharge_cond_X_defect_field_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (DY DYp : Y → ℝ)
    (hDY : ∀ y ∈ YSupport S, g P R y * DYp y = DY y)
    {x : X} (hx : x ∈ XSupport S) :
    f P R x * ((∑ y, R (x,y) * DYp y) / stoch_to_det.mX R x) =
      (∑ y, P (x,y) * (g P R y * DY y)) / stoch_to_det.mX P x := by
  rw [pairCharge_cond_X_reverse_weight hpair DYp hx]
  apply pairCharge_cond_X_congr_support hpair.2.1
  intro y hy
  rw [show (g P R y)^2 * DYp y = g P R y * (g P R y * DYp y) by ring,
    hDY y hy]

lemma pairCharge_cond_Y_defect_field_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (DX DXp : X → ℝ)
    (hDX : ∀ x ∈ XSupport S, f P R x * DXp x = DX x)
    {y : Y} (hy : y ∈ YSupport S) :
    g P R y * ((∑ x, R (x,y) * DXp x) / stoch_to_det.mY R y) =
      (∑ x, P (x,y) * (f P R x * DX x)) / stoch_to_det.mY P y := by
  rw [pairCharge_cond_Y_reverse_weight hpair DXp hy]
  apply pairCharge_cond_Y_congr_support hpair.2.1
  intro x hx
  rw [show (f P R x)^2 * DXp x = f P R x * (f P R x * DXp x) by ring,
    hDX x hx]

lemma pairCharge_omega_X_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (DX DXp : X → ℝ) (DY DYp : Y → ℝ)
    (hDX : ∀ x ∈ XSupport S, f P R x * DXp x = DX x)
    (hDY : ∀ y ∈ YSupport S, g P R y * DYp y = DY y) :
    E R (fun z => U R P z.1 * DXp z.1 *
      ((∑ y, R (z.1,y) * DYp y) / stoch_to_det.mX R z.1)) =
    -E P (fun z => U P R z.1 * DX z.1 *
      ((∑ y, P (z.1,y) * DY y) / stoch_to_det.mX P z.1)) -
      E P (fun z => U P R z.1 * V P R z.2 * DX z.1 * DY z.2) := by
  have hreverse :
      E R (fun z => U R P z.1 * DXp z.1 *
        ((∑ y, R (z.1,y) * DYp y) / stoch_to_det.mX R z.1)) =
        -E P (fun z => U P R z.1 * DX z.1 * (g P R z.2 * DY z.2)) := by
    rw [pairCharge_E_reverse_fst hpair (fun x => U R P x * DXp x *
      ((∑ y, R (x,y) * DYp y) / stoch_to_det.mX R x))]
    calc
      _ = E P (fun z => -1 * ((U P R z.1 * DX z.1) *
          ((∑ y, P (z.1,y) * (g P R y * DY y)) / stoch_to_det.mX P z.1))) := by
        apply pairCharge_E_congr_positive hpair.2.1.1
        intro z hz
        have hzS := pairCharge_mem_S_of_pos hpair.2.1 hz
        have hx : z.1 ∈ XSupport S := Finset.mem_image.mpr ⟨z, hzS, rfl⟩
        calc
          _ = (f P R z.1 * U R P z.1) * (f P R z.1 * DXp z.1) *
              (f P R z.1 * ((∑ y, R (z.1,y) * DYp y) / stoch_to_det.mX R z.1)) := by ring
          _ = _ := by
            rw [pairCharge_U_reverse_scaled hpair hx, hDX _ hx,
              pairCharge_cond_X_defect_field_reverse hpair DY DYp hDY hx]
            ring
      _ = _ := by
        rw [contact_q_E_scale, pairCharge_cond_X_inner hpair.2.1.1
          (fun x => U P R x * DX x) (fun y => g P R y * DY y)]
        ring
  have hbase := pairCharge_cond_X_inner hpair.2.1.1 (fun x => U P R x * DX x) DY
  have hexpand : E P (fun z => U P R z.1 * DX z.1 * (g P R z.2 * DY z.2)) =
      E P (fun z => U P R z.1 * DX z.1 * DY z.2) +
        E P (fun z => U P R z.1 * V P R z.2 * DX z.1 * DY z.2) := by
    calc
      _ = E P (fun z => U P R z.1 * DX z.1 * DY z.2 +
          U P R z.1 * V P R z.2 * DX z.1 * DY z.2) := by
        congr 1
        funext z
        unfold g
        ring
      _ = _ := contact_q_E_add _ _ _
  linarith only [hreverse, hbase, hexpand]

lemma pairCharge_omega_Y_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (DX DXp : X → ℝ) (DY DYp : Y → ℝ)
    (hDX : ∀ x ∈ XSupport S, f P R x * DXp x = DX x)
    (hDY : ∀ y ∈ YSupport S, g P R y * DYp y = DY y) :
    E R (fun z => V R P z.2 * DYp z.2 *
      ((∑ x, R (x,z.2) * DXp x) / stoch_to_det.mY R z.2)) =
    -E P (fun z => V P R z.2 * DY z.2 *
      ((∑ x, P (x,z.2) * DX x) / stoch_to_det.mY P z.2)) -
      E P (fun z => U P R z.1 * V P R z.2 * DX z.1 * DY z.2) := by
  have hreverse :
      E R (fun z => V R P z.2 * DYp z.2 *
        ((∑ x, R (x,z.2) * DXp x) / stoch_to_det.mY R z.2)) =
        -E P (fun z => (f P R z.1 * DX z.1) * (V P R z.2 * DY z.2)) := by
    rw [pairCharge_E_reverse_snd hpair (fun y => V R P y * DYp y *
      ((∑ x, R (x,y) * DXp x) / stoch_to_det.mY R y))]
    calc
      _ = E P (fun z => -1 *
          (((∑ x, P (x,z.2) * (f P R x * DX x)) / stoch_to_det.mY P z.2) *
            (V P R z.2 * DY z.2))) := by
        apply pairCharge_E_congr_positive hpair.2.1.1
        intro z hz
        have hzS := pairCharge_mem_S_of_pos hpair.2.1 hz
        have hy : z.2 ∈ YSupport S := Finset.mem_image.mpr ⟨z, hzS, rfl⟩
        calc
          _ = (g P R z.2 * V R P z.2) * (g P R z.2 * DYp z.2) *
              (g P R z.2 * ((∑ x, R (x,z.2) * DXp x) / stoch_to_det.mY R z.2)) := by ring
          _ = _ := by
            rw [pairCharge_V_reverse_scaled hpair hy, hDY _ hy,
              pairCharge_cond_Y_defect_field_reverse hpair DX DXp hDX hy]
            ring
      _ = _ := by
        rw [contact_q_E_scale, pairCharge_cond_Y_inner hpair.2.1.1
          (fun x => f P R x * DX x) (fun y => V P R y * DY y)]
        ring
  have hbase := pairCharge_cond_Y_inner hpair.2.1.1 DX (fun y => V P R y * DY y)
  have hbase' : E P (fun z => V P R z.2 * DY z.2 *
      ((∑ x, P (x,z.2) * DX x) / stoch_to_det.mY P z.2)) =
      E P (fun z => DX z.1 * (V P R z.2 * DY z.2)) := by
    calc
      _ = E P (fun z => ((∑ x, P (x,z.2) * DX x) / stoch_to_det.mY P z.2) *
          (V P R z.2 * DY z.2)) := by congr 1; funext z; ring
      _ = _ := hbase
  have hexpand : E P (fun z => (f P R z.1 * DX z.1) * (V P R z.2 * DY z.2)) =
      E P (fun z => DX z.1 * (V P R z.2 * DY z.2)) +
        E P (fun z => U P R z.1 * V P R z.2 * DX z.1 * DY z.2) := by
    calc
      _ = E P (fun z => DX z.1 * (V P R z.2 * DY z.2) +
          U P R z.1 * V P R z.2 * DX z.1 * DY z.2) := by
        congr 1
        funext z
        unfold f
        ring
      _ = _ := contact_q_E_add _ _ _
  linarith only [hreverse, hbase', hexpand]

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
  simp only [hpoint, contact_q_E_sub, pairCharge_E_div, contact_q_E_add]

lemma pairCharge_E_product_three_fst (P : Law X Y) (u F : X → ℝ) (v : Y → ℝ) :
    E (productLaw P) (fun z => u z.1 * v z.2 * F z.1) =
      E P (fun z => u z.1 * F z.1) * E P (fun z => v z.2) := by
  calc
    _ = E (productLaw P) (fun z => (u z.1 * F z.1) * v z.2) := by
      congr 1
      funext z
      ring
    _ = _ := pairCharge_E_product P (fun x => u x * F x) v

lemma pairCharge_E_product_three_snd (P : Law X Y) (u : X → ℝ) (v G : Y → ℝ) :
    E (productLaw P) (fun z => u z.1 * v z.2 * G z.2) =
      E P (fun z => u z.1) * E P (fun z => v z.2 * G z.2) := by
  calc
    _ = E (productLaw P) (fun z => u z.1 * (v z.2 * G z.2)) := by
      congr 1
      funext z
      ring
    _ = _ := pairCharge_E_product P u (fun y => v y * G y)

lemma pairCharge_H_additive_product (P : Law X Y) (u F : X → ℝ) (v G : Y → ℝ)
    (c : ℝ) (hc : c ≠ 0) :
    E (productLaw P) (fun z => u z.1 * v z.2 / c * ((F z.1 + G z.2) / c - 1)) =
      (E P (fun z => u z.1 * F z.1) * E P (fun z => v z.2) +
        E P (fun z => u z.1) * E P (fun z => v z.2 * G z.2)) / c ^ 2 -
          E P (fun z => u z.1) * E P (fun z => v z.2) / c := by
  rw [pairCharge_H_additive_expectation _ _ _ _ _ _ hc,
    pairCharge_E_product_three_fst, pairCharge_E_product_three_snd, pairCharge_E_product]

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
  have hs := pairCharge_s_eq_A0_add_B0 P R
  field_simp [hsne]
  rw [hs]
  ring

lemma pairCharge_U_column_defect {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (DY : Y → ℝ)
    (hDY : ∀ y, DY y = pairCharge_rawDY P R y) :
    E P (fun z => U P R z.1 * DY z.2) =
      (E P (fun z => V P R z.2 * DY z.2) - E P (fun z => (DY z.2)^2)) / 2 := by
  simpa only [pow_two] using pairCharge_column_field hpair DY DY hDY

lemma pairCharge_V_row_defect {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (DX : X → ℝ)
    (hDX : ∀ x, DX x = pairCharge_rawDX P R x) :
    E P (fun z => DX z.1 * V P R z.2) =
      (E P (fun z => U P R z.1 * DX z.1) - E P (fun z => (DX z.1)^2)) / 2 := by
  simpa only [mul_comm, pow_two] using pairCharge_row_field hpair DX DX hDX

/-- The unaveraged contact endpoint for `H` and `B1`. -/
lemma pairCharge_HB1_joint {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R)
    (DX : X → ℝ) (DY : Y → ℝ) (PX : X → ℝ) (PY : Y → ℝ)
    (hDX : ∀ x, DX x = (∑ y, P (x,y) * (V P R y)^2) / stoch_to_det.mX P x)
    (hDY : ∀ y, DY y = (∑ x, P (x,y) * (U P R x)^2) / stoch_to_det.mY P y)
    (hPX : ∀ x, PX x = (∑ y, P (x,y) * DY y) / stoch_to_det.mX P x)
    (hPY : ∀ y, PY y = (∑ x, P (x,y) * DX x) / stoch_to_det.mY P y) :
    E P (fun z => U P R z.1 * V P R z.2 / s P R *
      ((PX z.1 + PY z.2) / s P R - 1)) =
      (E P (fun z => (DX z.1)^2) + E P (fun z => (DY z.2)^2)) / (2 * (s P R)^2) -
        E P (fun z => U P R z.1 * V P R z.2) / s P R -
          (E P (fun z => U P R z.1 * DX z.1 * PX z.1) +
            E P (fun z => V P R z.2 * DY z.2 * PY z.2)) / (2 * (s P R)^2) := by
  have hsne := (contact_moments hpair).s_pos.ne'
  have hU2PX : E P (fun z => (U P R z.1)^2 * PX z.1) =
      E P (fun z => (DY z.2)^2) := by
    simp_rw [hPX]
    rw [pairCharge_cond_X_inner hpair.2.1.1 (fun x => (U P R x)^2) DY]
    have htower := pairCharge_cond_Y_inner hpair.2.1.1 (fun x => (U P R x)^2) DY
    simp_rw [← hDY] at htower
    calc
      _ = E P (fun z => DY z.2 * DY z.2) := htower.symm
      _ = _ := by congr 1; funext z; ring
  have hV2PY : E P (fun z => (V P R z.2)^2 * PY z.2) =
      E P (fun z => (DX z.1)^2) := by
    have hfirst : E P (fun z => (V P R z.2)^2 * PY z.2) =
        E P (fun z => DX z.1 * (V P R z.2)^2) := by
      simp_rw [hPY]
      calc
        _ = E P (fun z => ((∑ x, P (x,z.2) * DX x) / stoch_to_det.mY P z.2) *
            (V P R z.2)^2) := by congr 1; funext z; ring
        _ = _ := pairCharge_cond_Y_inner hpair.2.1.1 DX (fun y => (V P R y)^2)
    rw [hfirst]
    have htower := pairCharge_cond_X_inner hpair.2.1.1 DX (fun y => (V P R y)^2)
    simp_rw [← hDX] at htower
    calc
      _ = E P (fun z => DX z.1 * DX z.1) := htower.symm
      _ = _ := by congr 1; funext z; ring
  have hX := pairCharge_UV_row_field hpair DX PX hDX
  have hY := pairCharge_UV_column_field hpair DY PY hDY
  rw [hU2PX] at hX
  rw [hV2PY] at hY
  rw [pairCharge_H_additive_expectation _ _ _ _ _ _ hsne, hX, hY]
  field_simp [hsne]
  ring

/-- The unaveraged product endpoint for `H` and `B1`. -/
lemma pairCharge_HB1_product {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R)
    (DX : X → ℝ) (DY : Y → ℝ) (PX : X → ℝ) (PY : Y → ℝ)
    (hDX : ∀ x, DX x = (∑ y, P (x,y) * (V P R y)^2) / stoch_to_det.mX P x)
    (hDY : ∀ y, DY y = (∑ x, P (x,y) * (U P R x)^2) / stoch_to_det.mY P y)
    (hPX : ∀ x, PX x = (∑ y, P (x,y) * DY y) / stoch_to_det.mX P x)
    (hPY : ∀ y, PY y = (∑ x, P (x,y) * DX x) / stoch_to_det.mY P y) :
    E (productLaw P) (fun z => U P R z.1 * V P R z.2 / s P R *
      ((PX z.1 + PY z.2) / s P R - 1)) =
      -(3 / 4 : ℝ) * ((A0 P R - B0 P R) / s P R)^2 +
        J P R / (4 * s P R) - A0 P R * B0 P R / s P R +
          (A0 P R * E P (fun z => (DX z.1)^2) +
            B0 P R * E P (fun z => (DY z.2)^2)) / (2 * (s P R)^2) := by
  have hsne := (contact_moments hpair).s_pos.ne'
  have hUPX : E P (fun z => U P R z.1 * PX z.1) =
      ((-3 * (A0 P R - B0 P R) - J P R) / 2 -
        E P (fun z => (DY z.2)^2)) / 2 := by
    simp_rw [hPX]
    rw [pairCharge_cond_X_inner hpair.2.1.1 (U P R) DY, pairCharge_U_column_defect hpair DY hDY,
      (pairCharge_defect_Y_moments hpair DY hDY).2.1]
  have hVPY : E P (fun z => V P R z.2 * PY z.2) =
      ((3 * (A0 P R - B0 P R) - J P R) / 2 -
        E P (fun z => (DX z.1)^2)) / 2 := by
    have htower := pairCharge_cond_Y_inner hpair.2.1.1 DX (V P R)
    simp_rw [← hPY] at htower
    calc
      _ = E P (fun z => PY z.2 * V P R z.2) := by congr 1; funext z; ring
      _ = E P (fun z => DX z.1 * V P R z.2) := htower
      _ = _ := by rw [pairCharge_V_row_defect hpair DX hDX,
        (pairCharge_defect_X_moments hpair DX hDX).2.1]
  rw [pairCharge_H_additive_product _ _ _ _ _ _ hsne, hUPX, hVPY,
    (pairCharge_mean_UV hpair).1, (pairCharge_mean_UV hpair).2]
  have hs := pairCharge_s_eq_A0_add_B0 P R
  field_simp [hsne]
  rw [hs]
  ring

/-- Connects conditional second moments to the defect norm. -/
lemma pairCharge_defects_second_moment_identity {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (DX : X → ℝ) (DY : Y → ℝ)
    (hDX : ∀ x, DX x = (∑ y, P (x,y) * (V P R y)^2) / stoch_to_det.mX P x)
    (hDY : ∀ y, DY y = (∑ x, P (x,y) * (U P R x)^2) / stoch_to_det.mY P y) :
    (E P (fun z => (DX z.1)^2) + E P (fun z => (DY z.2)^2)) / (s P R)^2 =
      5 - 18 * (A0 P R * B0 P R / (s P R)^2) +
        (E P (fun z => (DX z.1 - (2 * B0 P R - A0 P R))^2) +
          E P (fun z => (DY z.2 - (2 * A0 P R - B0 P R))^2)) / (s P R)^2 := by
  have hX := pairCharge_E_centered_square hpair.2.1.1 (fun z => DX z.1)
  have hY := pairCharge_E_centered_square hpair.2.1.1 (fun z => DY z.2)
  rw [(pairCharge_defect_X_moments hpair DX hDX).1] at hX
  rw [(pairCharge_defect_Y_moments hpair DY hDY).1] at hY
  rw [hX, hY]
  have hsne := (contact_moments hpair).s_pos.ne'
  have hs := pairCharge_s_eq_A0_add_B0 P R
  field_simp [hsne]
  rw [hs]
  ring

/-- All eight endpoint entries, combined with the two reversal cancellations. Here `HX`, `HY`, `HXp`,
`HYp` are the unnormalized second moments; `lam`, `om` are the unnormalized `Lambda` and `Omega`
numerators. -/
lemma pairCharge_HC_endpoint_sum
    (s a b J uv HX HY HXp HYp lam om lamp omp Z j v x M : ℝ)
    (hsne : s ≠ 0) (hs : s = a + b)
    (hj : j = J / s ^ 2) (hv : v = a * b / s ^ 2)
    (huv : uv = (s + J) / 4)
    (hLamp : lamp = -lam) (hOmp : omp = -om - 2 * Z)
    (hH : (HX + HY + HXp + HYp) / (2 * s ^ 2) = 5 - 18 * v + x)
    (hM : M = (a * HX + b * HY + b * HXp + a * HYp) / (2 * s ^ 2)) :
    (((3 / 2 : ℝ) * ((a - b) / s) ^ 2 + J / (2 * s) - a * b / s) +
      (J / s ^ 2 - uv / s - lam / (2 * s ^ 2)) +
      (-(3 / 4 : ℝ) * ((a - b) / s) ^ 2 + J / (4 * s) - a * b / s +
        (a * HX + b * HY) / (2 * s ^ 2)) +
      ((HX + HY) / (2 * s ^ 2) - uv / s - om / (2 * s ^ 2)) +
      ((3 / 2 : ℝ) * ((b - a) / s) ^ 2 + J / (2 * s) - a * b / s) +
      (J / s ^ 2 - uv / s - lamp / (2 * s ^ 2)) +
      (-(3 / 4 : ℝ) * ((b - a) / s) ^ 2 + J / (4 * s) - a * b / s +
        (b * HXp + a * HYp) / (2 * s ^ 2)) +
      ((HXp + HYp) / (2 * s ^ 2) - uv / s - omp / (2 * s ^ 2))) / 2 =
      j - (1 / 4 : ℝ) + x / 2 + 12 * ((1 / 4 : ℝ) - v) +
        s * (j / 4 - 2 * v) + M / 2 + Z / (2 * s ^ 2) := by
  have hx : x = (HX + HY + HXp + HYp) / (2 * s ^ 2) - 5 + 18 * (a * b / s ^ 2) := by
    rw [hv] at hH
    linarith only [hH]
  rw [hx, hj, hv, huv, hLamp, hOmp, hM]
  field_simp [hsne]
  rw [hs]
  ring

omit [DecidableEq X] [DecidableEq Y] in
/-- Weighted finite Cauchy-Schwarz from a nonnegative quadratic. -/
lemma pairCharge_E_cauchy {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F G : X × Y → ℝ) :
    (E P (fun z => F z*G z))^2 ≤
      E P (fun z => (F z)^2)*E P (fun z => (G z)^2) := by
  let a := E P (fun z => (F z)^2)
  let c := E P (fun z => F z*G z)
  let b := E P (fun z => (G z)^2)
  have ha : 0 ≤ a := contact_E_nonneg hP _ (fun _ => sq_nonneg _)
  by_cases haz : a = 0
  · have hcz : c = 0 := by
      apply Finset.sum_eq_zero
      intro z _
      by_cases hpz : P z = 0
      · simp [hpz]
      · have hz : 0 < P z := lt_of_le_of_ne (hP.nonneg z) (Ne.symm hpz)
        have hF := contact_weighted_sq_zero hP F haz hz
        simp [hF]
    change c^2 ≤ a*b
    rw [hcz,haz]
    norm_num
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
    have hn := contact_E_nonneg hP (fun z => (a*G z-c*F z)^2) (fun _ => sq_nonneg _)
    have hid : E P (fun z => (a*G z-c*F z)^2) = a^2*b-2*a*c*c+c^2*a := by
      calc
        _ = E P (fun z => (a^2*(G z)^2-2*a*c*(F z*G z))+c^2*(F z)^2) := by
          congr 1
          funext z
          ring
        _ = _ := by simp only [contact_q_E_add,contact_q_E_sub,contact_q_E_scale];rfl
    rw [hid] at hn
    change c^2 ≤ a*b
    apply (mul_le_mul_iff_of_pos_left hap).mp
    nlinarith only [hn]

end

end StochasticToDeterministicLatents.General
