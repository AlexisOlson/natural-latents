-- Adapted from the author's earlier repository (StochasticToDeterministicLatents);
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised; namespace renamed to NaturalLatents.General.
import NaturalLatents.General.PairCharge.Entropy
import NaturalLatents.General.PairCharge.Features
import NaturalLatents.General.PairCharge.Certificate
import NaturalLatents.General.PairCharge.Correction

/-!
# The pair charge C

On every pair of distinct positive contacts `P`, `R` of a common feasible kernel on a common finite
support (holes allowed),

    (I P + I R) / 2 + (23/250) * Psi (s P R) ≥ 7/60,

that is `PC CommonSupportPairs (23/250) (7/60)` (`pairCharge_C`). For `s ≤ 1` the averaged information
is at least `3 y^2 / B(s, j)` (an entropy payment for the statistic `UV/s + (U + V + s)/5` corrected by
`λ(s) u ((DX + DY)/s - 1)`, whose residual is bounded by a feasibility-Hessian inequality), and a
scalar certificate (three positive quartics and an exact interpolation in `j`) closes the charge
against the price `(23/250) Psi s ≥ (103/1000) s + (23/1000) s^2`. For `1 ≤ s < 2` the price alone pays.

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
  intro gap D N W
  let Q := productLaw P
  let B : X × Y → ℝ := fun z => -lam*C z
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
    dsimp [gap, Q, E]
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

private lemma pairCharge_statistic_correction_split (P R Q : Law X Y) :
    E Q (fun z => pairCharge_statistic P R z * pairCharge_correction P R z) =
      E Q (fun z => U P R z.1 * V P R z.2 / s P R * pairCharge_correction P R z) +
      (1/5 : ℝ) * E Q (fun z =>
        (U P R z.1 + V P R z.2 + s P R) * pairCharge_correction P R z) := by
  have hp (z : X × Y) : pairCharge_statistic P R z * pairCharge_correction P R z =
      U P R z.1 * V P R z.2 / s P R * pairCharge_correction P R z +
      (1/5 : ℝ) * ((U P R z.1 + V P R z.2 + s P R) * pairCharge_correction P R z) := by
    unfold pairCharge_statistic
    ring
  simp only [hp, contact_E_add, contact_q_E_scale]

/-- The paired change of measure gives the averaged statistic-correction product. -/
lemma pairCharge_statistic_correction_average {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    ((E (productLaw P) (fun z => pairCharge_statistic P R z * pairCharge_correction P R z) +
        E P (fun z => pairCharge_statistic P R z * pairCharge_correction P R z)) +
      (E (productLaw R) (fun z => pairCharge_statistic R P z * pairCharge_correction R P z) +
        E R (fun z => pairCharge_statistic R P z * pairCharge_correction R P z))) / 2 =
    contactj P R * (1 - s P R / 4) - 1/4
      + (3/2 - s P R / 2) * (1 - 4 * (A0 P R * B0 P R / (s P R)^2))
      - (pairCharge_defectNorm P R + pairCharge_defectNorm R P) / (20 * s P R) := by
  have hrev := pairCharge_pair_reverse hpair
  have hsrev := pairCharge_s_reverse hpair
  have harev := (pairCharge_mean_losses_reverse hpair).1
  have hbrev := (pairCharge_mean_losses_reverse hpair).2
  have hJrev := pairCharge_J_reverse hpair
  have hDXscale : ∀ x ∈ XSupport S,
      f P R x * pairCharge_rawDX R P x = pairCharge_rawDX P R x := by
    intro x hx
    exact pairCharge_cond_defect_X_reverse hpair hx
  have hDYscale : ∀ y ∈ YSupport S,
      g P R y * pairCharge_rawDY R P y = pairCharge_rawDY P R y := by
    intro y hy
    exact pairCharge_cond_defect_Y_reverse hpair hy
  have hlamX := pairCharge_lambda_X_reverse hpair
    (pairCharge_rawDX P R) (pairCharge_rawDX R P) hDXscale
  have hlamY := pairCharge_lambda_Y_reverse hpair
    (pairCharge_rawDY P R) (pairCharge_rawDY R P) hDYscale
  have hQP := pairCharge_HB0_product hpair (pairCharge_rawDX P R) (pairCharge_rawDY P R)
    (fun _ => rfl) (fun _ => rfl)
  have hPP := pairCharge_HB0_joint hpair (pairCharge_rawDX P R) (pairCharge_rawDY P R)
    (fun _ => rfl) (fun _ => rfl)
  have hQR := pairCharge_HB0_product hrev (pairCharge_rawDX R P) (pairCharge_rawDY R P)
    (fun _ => rfl) (fun _ => rfl)
  have hRR := pairCharge_HB0_joint hrev (pairCharge_rawDX R P) (pairCharge_rawDY R P)
    (fun _ => rfl) (fun _ => rfl)
  have huvP : E P (fun z => U P R z.1 * V P R z.2) = (s P R + J P R) / 4 := by
    linarith only [(contact_moments hpair).quartic]
  have huvR : E R (fun z => U R P z.1 * V R P z.2) = (s P R + J P R) / 4 := by
    rw [← hsrev, ← hJrev]
    linarith only [(contact_moments hrev).quartic]
  rw [huvP] at hPP
  rw [huvR, hlamX, hlamY] at hRR
  have hLP := pairCharge_linear_correction hpair
  have hLR := pairCharge_linear_correction hrev
  have hsplit :
      ((E (productLaw P) (fun z => pairCharge_statistic P R z * pairCharge_correction P R z) +
          E P (fun z => pairCharge_statistic P R z * pairCharge_correction P R z)) +
        (E (productLaw R) (fun z => pairCharge_statistic R P z * pairCharge_correction R P z) +
          E R (fun z => pairCharge_statistic R P z * pairCharge_correction R P z))) / 2 =
      ((E (productLaw P) (fun z => U P R z.1 * V P R z.2 / s P R * pairCharge_correction P R z) +
          E P (fun z => U P R z.1 * V P R z.2 / s P R * pairCharge_correction P R z)) +
        (E (productLaw R) (fun z => U R P z.1 * V R P z.2 / s R P * pairCharge_correction R P z) +
          E R (fun z => U R P z.1 * V R P z.2 / s R P * pairCharge_correction R P z)) +
        (1/5 : ℝ) * ((E (productLaw P) (fun z =>
            (U P R z.1 + V P R z.2 + s P R) * pairCharge_correction P R z) +
          E P (fun z => (U P R z.1 + V P R z.2 + s P R) * pairCharge_correction P R z)) +
          (E (productLaw R) (fun z =>
            (U R P z.1 + V R P z.2 + s R P) * pairCharge_correction R P z) +
          E R (fun z => (U R P z.1 + V R P z.2 + s R P) * pairCharge_correction R P z)))) / 2 := by
    simp only [pairCharge_statistic_correction_split]
    ring
  rw [hsplit, hQP, hPP, hQR, hRR, hLP, hLR, hsrev, harev, hbrev, hJrev]
  unfold contactj
  field_simp [(contact_moments hpair).s_pos.ne']
  have hs : s P R = A0 P R + B0 P R := rfl
  rw [hs]
  ring


/-- The entropy-payment residual for the statistic with correction at slope `lam`. -/
abbrev pairCharge_residual (P R : Law X Y) (lam : ℝ) : ℝ :=
  (E (productLaw P) (fun z => (pairCharge_statistic P R z
        - E (productLaw P) (pairCharge_statistic P R))^2) / 3
    + E P (fun z => (pairCharge_statistic P R z - E P (pairCharge_statistic P R))^2) / 6
    + (E P (pairCharge_statistic P R) - E (productLaw P) (pairCharge_statistic P R))^2 / 12)
  - 2 * lam * ((E (productLaw P) (fun z => pairCharge_statistic P R z * pairCharge_correction P R z)
      + E P (fun z => pairCharge_statistic P R z * pairCharge_correction P R z)) / 12)
  + lam^2 * (E (productLaw P) (fun z => (pairCharge_correction P R z)^2) / 30
      + E P (fun z => (pairCharge_correction P R z)^2) / 20)

private lemma pairCharge_residual_expansion {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (lam : ℝ) :
    let t := s P R
    let jj := contactj P R
    let vv := A0 P R * B0 P R / t^2
    let hh := (1 + t * jj) / 4
    pairCharge_residual P R lam =
      ((9 * vv - 2) / 3 + jj / 6 - t^2 * vv^2 / 4 - t * vv * hh / 6 - hh^2 / 12 +
        2 * (1/5) * t * (3/8 - 2 * vv - jj / 6 + t * (vv / 3 + jj / 24)) +
        (1/5)^2 * t * (7/12 - t / 2 + 2 * t * vv / 3 + t * jj / 12)) -
      lam / 6 * (E (productLaw P) (fun z => pairCharge_statistic P R z * pairCharge_correction P R z) +
        E P (fun z => pairCharge_statistic P R z * pairCharge_correction P R z)) +
      lam^2 * (5 * pairCharge_defectNorm P R + 6 * pairCharge_defectCross P R) / (60 * t^2) := by
  have hd := (pairCharge_fixed_coefficient_data hpair (1/5 : ℝ)).2
  have hb := pairCharge_correction_second_moments hpair
  unfold pairCharge_residual
  rw [hd, hb.1, hb.2]
  ring

/-- The averaged residual is bounded by the scalar denominator divided by `192`. -/
lemma pairCharge_residual_bound {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (hs1 : s P R ≤ 1) :
    192 * ((pairCharge_residual P R (pairChargeSlope (s P R)) +
        pairCharge_residual R P (pairChargeSlope (s P R))) / 2) ≤
      pairChargeDenominator (s P R) (contactj P R) := by
  let t := s P R
  let jj := contactj P R
  let vv := A0 P R * B0 P R / t^2
  let hh := (1 + t * jj) / 4
  let D := (9 * vv - 2) / 3 + jj / 6 - t^2 * vv^2 / 4 - t * vv * hh / 6 - hh^2 / 12 +
    2 * (1/5) * t * (3/8 - 2 * vv - jj / 6 + t * (vv / 3 + jj / 24)) +
    (1/5)^2 * t * (7/12 - t / 2 + 2 * t * vv / 3 + t * jj / 12)
  let rho := (pairCharge_defectNorm P R + pairCharge_defectNorm R P) / 2
  let cross := (pairCharge_defectCross P R + pairCharge_defectCross R P) / 2
  let Xc := ((E (productLaw P) (fun z => pairCharge_statistic P R z * pairCharge_correction P R z) +
      E P (fun z => pairCharge_statistic P R z * pairCharge_correction P R z)) +
    (E (productLaw R) (fun z => pairCharge_statistic R P z * pairCharge_correction R P z) +
      E R (fun z => pairCharge_statistic R P z * pairCharge_correction R P z))) / 2
  have hs := (contact_moments hpair).s_pos
  have hrev := pairCharge_pair_reverse hpair
  have hsrev := pairCharge_s_reverse hpair
  have hjrev := pairCharge_contactj_reverse hpair
  have hvrev := pairCharge_v_reverse hpair
  have hX : Xc = jj * (1 - t / 4) - 1/4 + (3/2 - t / 2) * (1 - 4 * vv) - rho / (10 * t) := by
    have hx := pairCharge_statistic_correction_average hpair
    change Xc = _ at hx
    rw [hx]
    dsimp only [jj, t, vv, rho]
    ring
  have hQP := pairCharge_correction_hessian hpair (pairChargeSlope t) (pairChargeWeight t)
  have hQR := pairCharge_correction_hessian hrev (pairChargeSlope t) (pairChargeWeight t)
  have hTrev : 6 * A0 R P * B0 R P - (s R P)^2 - J R P =
      6 * A0 P R * B0 P R - t^2 - J P R := by
    rw [hsrev, (pairCharge_mean_losses_reverse hpair).1,
      (pairCharge_mean_losses_reverse hpair).2, pairCharge_J_reverse hpair]
    dsimp only [t]
    ring
  rw [hTrev] at hQR
  have hT : 6 * A0 P R * B0 P R - t^2 - J P R = t^2 * (6 * vv - 1 - jj) := by
    dsimp only [t, vv, jj, contactj]
    field_simp [hs.ne']
  change 0 ≤ 36 * (pairChargeSlope t)^2 *
    (pairCharge_defectNorm P R - 4 * pairCharge_defectCross P R) -
    12 * pairChargeSlope t * pairChargeWeight t * pairCharge_defectNorm P R +
    (pairChargeWeight t)^2 * (6 * A0 P R * B0 P R - t^2 - J P R) at hQP
  rw [hT] at hQP hQR
  have hQ : 0 ≤ 36 * (pairChargeSlope t)^2 * (rho - 4 * cross) -
      12 * pairChargeSlope t * pairChargeWeight t * rho +
      (pairChargeWeight t)^2 * (t^2 * (6 * vv - 1 - jj)) := by
    dsimp only [rho, cross]
    linarith only [hQP, hQR]
  have hp := pairCharge_residual_expansion hpair (pairChargeSlope t)
  have hr := pairCharge_residual_expansion hrev (pairChargeSlope t)
  dsimp only at hp hr
  rw [hvrev, hjrev, hsrev] at hr
  have havg : (pairCharge_residual P R (pairChargeSlope t) +
      pairCharge_residual R P (pairChargeSlope t)) / 2 =
      D - pairChargeSlope t / 6 * Xc +
        (pairChargeSlope t)^2 * (5 * rho + 6 * cross) / (60 * t^2) := by
    rw [hp, hr]
    dsimp only [D, hh, rho, cross, Xc, t, vv, jj]
    ring
  have hbound := pairCharge_residual_le_denominator t jj vv rho cross D Xc
    hs hs1 (pairCharge_contactj_bounds hpair).2 (pairCharge_v_bounds hpair).2 rfl hX hQ
  rw [havg]
  exact hbound


private lemma pairCharge_statistic_gap_lower {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    (1 - s P R + s P R * contactj P R) / 4 ≤
      E P (pairCharge_statistic P R) - E (productLaw P) (pairCharge_statistic P R) := by
  have hg := (pairCharge_fixed_coefficient_data hpair (1/5 : ℝ)).1
  change E P (pairCharge_statistic P R) - E (productLaw P) (pairCharge_statistic P R) =
    (1 + s P R * contactj P R) / 4 - s P R * (A0 P R * B0 P R / (s P R)^2) at hg
  rw [hg]
  exact pairCharge_fixed_floor_gap (s P R) (contactj P R)
    (A0 P R * B0 P R / (s P R)^2) ((1 + s P R * contactj P R) / 4)
    (contact_moments hpair).s_pos.le (pairCharge_v_bounds hpair).2 rfl

/-- The positive scalar denominator gives the averaged information floor. -/
lemma pairCharge_information_floor {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (hs1 : s P R ≤ 1) :
    0 < pairChargeDenominator (s P R) (contactj P R) ∧
    3 * (1 - s P R + s P R * contactj P R)^2 / pairChargeDenominator (s P R) (contactj P R) ≤
      (I P + I R) / 2 := by
  let t := s P R
  let jj := contactj P R
  let y := 1 - t + t * jj
  let rp := pairCharge_residual P R (pairChargeSlope t)
  let rm := pairCharge_residual R P (pairChargeSlope t)
  let gp := E P (pairCharge_statistic P R) - E (productLaw P) (pairCharge_statistic P R)
  let gm := E R (pairCharge_statistic R P) - E (productLaw R) (pairCharge_statistic R P)
  have hrev := pairCharge_pair_reverse hpair
  have hy : 0 < y := pairCharge_fixed_floor_y_pos t jj
    (contact_moments hpair).s_pos.le hs1 (by linarith [(pairCharge_contactj_bounds hpair).1])
  have hgp : y / 4 ≤ gp := pairCharge_statistic_gap_lower hpair
  have hgm : y / 4 ≤ gm := by
    have h := pairCharge_statistic_gap_lower hrev
    rw [pairCharge_s_reverse hpair, pairCharge_contactj_reverse hpair] at h
    exact h
  have hgpne : gp ≠ 0 := ne_of_gt (by linarith only [hy, hgp])
  have hgmne : gm ≠ 0 := ne_of_gt (by linarith only [hy, hgm])
  have hmeansP := pairCharge_correction_means hpair
  have hmeansR := pairCharge_correction_means hrev
  have hp : 0 < rp ∧ gp^2 / (4 * rp) ≤ I P :=
    pairCharge_residual_information hpair.2.1.1
      (pairCharge_statistic P R) (pairCharge_correction P R) hmeansP.1 hmeansP.2
      hgpne (pairChargeSlope t)
  have hm : 0 < rm ∧ gm^2 / (4 * rm) ≤ I R :=
    pairCharge_residual_information hpair.2.2.1.1
      (pairCharge_statistic R P) (pairCharge_correction R P) hmeansR.1 hmeansR.2
      hgmne (pairChargeSlope t)
  have havg := pairCharge_average_KL_separate (I P) (I R) rp rm gp gm y
    hp.1 hm.1 hy.le hgp hgm hp.2 hm.2
  have hres : 0 < (rp + rm) / 2 := by linarith only [hp.1, hm.1]
  have hbound := pairCharge_residual_bound hpair hs1
  change 192 * ((rp + rm) / 2) ≤ pairChargeDenominator t jj at hbound
  have hresD : (rp + rm) / 2 ≤ pairChargeDenominator t jj / 192 := by
    linarith only [hbound]
  have hproj := pairCharge_projection_information ((I P + I R) / 2) y
    ((rp + rm) / 2) (pairChargeDenominator t jj / 192) hres hresD havg
  have hden : 192 * (pairChargeDenominator t jj / 192) = pairChargeDenominator t jj := by ring
  refine ⟨?_, ?_⟩
  · linarith only [hproj.1]
  · rw [hden] at hproj
    exact hproj.2

/-- The pair charge C on common finite supports, including supports with holes. -/
theorem pairCharge_C : PC (X := X) (Y := Y) CommonSupportPairs (23/250) (7/60) := by
  intro S w P R hpair
  have hm := contact_moments hpair
  have hprice := pairCharge_price hm.s_pos.le hm.s_lt_two.le
  by_cases hs1 : s P R ≤ 1
  · have hfloor := pairCharge_information_floor hpair hs1
    have hj := pairCharge_contactj_bounds hpair
    have hcert := pairCharge_scalar_certificate hm.s_pos.le hs1 hj.1 hj.2
    have hinfo : pairChargeProfile (s P R) < (I P + I R) / 2 :=
      lt_of_lt_of_le ((lt_div_iff₀ hfloor.1).2 hcert) hfloor.2
    unfold pairChargeProfile at hinfo
    linarith only [hinfo, hprice]
  · have hP : 0 ≤ I P := stoch_to_det.Knat_nonneg hpair.2.1.1
    have hR : 0 ≤ I R := stoch_to_det.Knat_nonneg hpair.2.2.1.1
    have hs : 1 < s P R := lt_of_not_ge hs1
    have hsquare : 1 ≤ (s P R)^2 := by nlinarith only [hs, sq_nonneg (s P R - 1)]
    nlinarith only [hP, hR, hs, hsquare, hprice]

end

end NaturalLatents.General
