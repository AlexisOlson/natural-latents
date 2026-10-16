-- Original work by Alexis Olson, Apache-2.0 (see NOTICE), October 2026, first written on an unpublished branch of
-- github.com/AlexisOlson/stochastic-to-deterministic-latents; reorganised for this repository
-- (namespace NaturalLatents.General, declarations renamed, unused material removed).
-- This file builds on and cites the definitions of DLorell/stoch_to_det (Apache-2.0).
import NaturalLatents.General.PairCharge.Information
import NaturalLatents.General.PairCharge.Features
import NaturalLatents.General.PairCharge.Certificate
import NaturalLatents.General.PairCharge.Correction

/-!
# The pair charge C

On every pair of distinct positive contacts `P`, `R` of a common feasible kernel on a common finite
support (holes allowed),

    (I P + I R) / 2 + (23/250) * separationPrice (separation P R) ≥ 7/60,

that is `HasPairCharge CommonSupportPair (23/250) (7/60)` (`pairCharge_C`). For `s ≤ 1` the averaged information
is at least `3 y^2 / B(s, j)` (an entropy payment for the statistic `UV/s + (U + V + s)/5` corrected by
`λ(s) u ((DX + DY)/s - 1)`, whose residual is bounded by a feasibility-Hessian inequality), and a
scalar certificate (three positive quartics and an exact interpolation in `gammaPrice`) closes the charge
against the price `(23/250) separationPrice s ≥ (103/1000) s + (23/1000) s^2`. For `1 ≤ s < 2` the price alone pays.

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

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_expect_covariance_raw {M : Law X Y} (hM : stoch_to_det.IsPMF M)
    (F G : X × Y → ℝ) :
    expect M (fun z => (F z-expect M F)*(G z-expect M G)) =
      expect M (fun z => F z*G z)-expect M F*expect M G := by
  simpa only [expect,mul_assoc] using pairCharge_covariance_raw M F G hM.total

/-- KL payment for `F - λ u C`, with both endpoint means of `C` zero. -/
lemma pairCharge_residual_information {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F C : X × Y → ℝ) (hCP : expect P C = 0) (hCQ : expect (marginalProduct P) C = 0)
    (hg : expect P F-expect (marginalProduct P) F ≠ 0) (lam : ℝ) :
    let gap := expect P F-expect (marginalProduct P) F
    let D := expect (marginalProduct P) (fun z => (F z-expect (marginalProduct P) F)^2)/3 +
      expect P (fun z => (F z-expect P F)^2)/6+gap^2/12
    let N := (expect (marginalProduct P) (fun z => F z*C z)+expect P (fun z => F z*C z))/12
    let W := expect (marginalProduct P) (fun z => (C z)^2)/30+expect P (fun z => (C z)^2)/20
    0 < D-2*lam*N+lam^2*W ∧ gap^2/(4*(D-2*lam*N+lam^2*W)) ≤ stoch_to_det.Knat P := by
  intro gap D N W
  let Q := marginalProduct P
  let B : X × Y → ℝ := fun z => -lam*C z
  let residual := D-2*lam*N+lam^2*W
  change 0 < residual ∧ gap^2/(4*residual) ≤ stoch_to_det.Knat P
  have hQ := pairCharge_product_isPMF hP
  have hBP : expect P B = 0 := by
    simp only [B, contact_q_expect_scale, hCP, mul_zero]
  have hBQ : expect Q B = 0 := by
    simp only [Q, B, contact_q_expect_scale, hCQ, mul_zero]
  have he : (∑ z, (P z-Q z)*F z) = gap := by
    dsimp [gap, Q, expect]
    simp only [sub_mul,Finset.sum_sub_distrib]
  have hB : (∑ z, (P z-Q z)*B z) = 0 := by
    simp only [sub_mul,Finset.sum_sub_distrib]
    change expect P B-expect Q B = 0
    simp only [hBP, hBQ, sub_self]
  have hcov (M : Law X Y) (hM : stoch_to_det.IsPMF M)
      (hMB : expect M B = 0) :
      expect M (fun z => (F z-expect M F)*(B z-expect M B)) = -lam*expect M (fun z => F z*C z) := by
    rw [pairCharge_expect_covariance_raw hM,hMB,mul_zero,sub_zero]
    simp only [B, mul_left_comm (F _) (-lam), contact_q_expect_scale]
  have hvar (M : Law X Y) (hMB : expect M B = 0) :
      expect M (fun z => (B z-expect M B)^2) = lam^2*expect M (fun z => (C z)^2) := by
    rw [hMB]
    simp only [B, sub_zero, mul_pow, neg_sq, contact_q_expect_scale]
  have hpay (τ : ℝ) : τ*gap ≤ stoch_to_det.Knat P+τ^2*residual := by
    have hp := pairCharge_entropy_linear_field_affine P Q F B hP.nonneg hQ.nonneg
      (stoch_to_det.joint_absCont_product hP) hP.total hQ.total hB τ
    rw [he] at hp
    simp only [mul_assoc] at hp
    change τ*gap ≤ stoch_to_det.Knat P+τ^2*(
      expect Q (fun z => (F z-expect Q F)^2)/3+
      expect P (fun z => (F z-expect P F)^2)/6+gap^2/12+
      expect Q (fun z => (F z-expect Q F)*(B z-expect Q B))/6+
      expect P (fun z => (F z-expect P F)*(B z-expect P B))/6+
      expect Q (fun z => (B z-expect Q B)^2)/30+
      expect P (fun z => (B z-expect P B)^2)/20) at hp
    rw [hcov Q hQ hBQ,hcov P hP hBP,hvar Q hBQ,hvar P hBP] at hp
    convert hp using 1
    dsimp [residual, D, N, W]
    ring
  have hr : 0 < residual := pairCharge_payment_positive (stoch_to_det.Knat P) gap residual hpay hg
  refine ⟨hr,?_⟩
  apply (div_le_iff₀ (show 0 < 4*residual by positivity)).2
  have hp := pairCharge_payment_bound (stoch_to_det.Knat P) gap residual hpay
  nlinarith only [hp]

-- Actual averaged contact covariance.

/-- The reciprocal mean step with separate positive mean gaps. -/
lemma pairCharge_average_KL_separate (Ip Im Vp Vm gp gm y : ℝ)
    (hVp : 0 < Vp) (hVm : 0 < Vm) (hy : 0 ≤ y)
    (hgp : y/4 ≤ gp) (hgm : y/4 ≤ gm)
    (hIp : gp^2/(4*Vp) ≤ Ip) (hIm : gm^2/(4*Vm) ≤ Im) :
    y^2/(64*((Vp+Vm)/2)) ≤ (Ip+Im)/2 := by
  have hip : (y/4)^2/(4*Vp) ≤ Ip := le_trans (by gcongr) hIp
  have him : (y/4)^2/(4*Vm) ≤ Im := le_trans (by gcongr) hIm
  exact pairCharge_average_KL Ip Im Vp Vm (y/4) y hVp hVm hy le_rfl hip him

private lemma pairCharge_statistic_correction_split (P R Q : Law X Y) :
    expect Q (fun z => pairCharge_statistic P R z * pairCharge_correction P R z) =
      expect Q (fun z => stoch_to_det.contactSecantX P R z.1 * stoch_to_det.contactSecantY P R z.2 / separation P R * pairCharge_correction P R z) +
      (1/5 : ℝ) * expect Q (fun z =>
        (stoch_to_det.contactSecantX P R z.1 + stoch_to_det.contactSecantY P R z.2 + separation P R) * pairCharge_correction P R z) := by
  have hp (z : X × Y) : pairCharge_statistic P R z * pairCharge_correction P R z =
      stoch_to_det.contactSecantX P R z.1 * stoch_to_det.contactSecantY P R z.2 / separation P R * pairCharge_correction P R z +
      (1/5 : ℝ) * ((stoch_to_det.contactSecantX P R z.1 + stoch_to_det.contactSecantY P R z.2 + separation P R) * pairCharge_correction P R z) := by
    unfold pairCharge_statistic
    ring
  simp only [hp, contact_expect_add, contact_q_expect_scale]

/-- The paired change of measure gives the averaged statistic-correction product. -/
lemma pairCharge_statistic_correction_average {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) :
    ((expect (marginalProduct P) (fun z => pairCharge_statistic P R z * pairCharge_correction P R z) +
        expect P (fun z => pairCharge_statistic P R z * pairCharge_correction P R z)) +
      (expect (marginalProduct R) (fun z => pairCharge_statistic R P z * pairCharge_correction R P z) +
        expect R (fun z => pairCharge_statistic R P z * pairCharge_correction R P z))) / 2 =
    quarticRatio P R * (1 - separation P R / 4) - 1/4
      + (3/2 - separation P R / 2) * (1 - 4 * (defectX P R * defectY P R / (separation P R)^2))
      - (pairCharge_defectNorm P R + pairCharge_defectNorm R P) / (20 * separation P R) := by
  have hrev := pairCharge_pair_reverse hpair
  have hsrev := pairCharge_separation_reverse hpair
  have harev := (pairCharge_mean_losses_reverse hpair).1
  have hbrev := (pairCharge_mean_losses_reverse hpair).2
  have hJrev := pairCharge_quarticMoment_reverse hpair
  have hlamX := pairCharge_secantX_defect_square_reverse hpair
    (pairCharge_rawDefectX P R) (pairCharge_rawDefectX R P)
    (fun _ hx => pairCharge_cond_defect_X_reverse hpair hx)
  have hlamY := pairCharge_secantY_defect_square_reverse hpair
    (pairCharge_rawDefectY P R) (pairCharge_rawDefectY R P)
    (fun _ hy => pairCharge_cond_defect_Y_reverse hpair hy)
  have hQP := pairCharge_secantStatistic_correction_product hpair (pairCharge_rawDefectX P R) (pairCharge_rawDefectY P R)
    (fun _ => rfl) (fun _ => rfl)
  have hPP := pairCharge_secantStatistic_correction_joint hpair (pairCharge_rawDefectX P R) (pairCharge_rawDefectY P R)
    (fun _ => rfl) (fun _ => rfl)
  have hQR := pairCharge_secantStatistic_correction_product hrev (pairCharge_rawDefectX R P) (pairCharge_rawDefectY R P)
    (fun _ => rfl) (fun _ => rfl)
  have hRR := pairCharge_secantStatistic_correction_joint hrev (pairCharge_rawDefectX R P) (pairCharge_rawDefectY R P)
    (fun _ => rfl) (fun _ => rfl)
  have huvP : expect P (fun z => stoch_to_det.contactSecantX P R z.1 * stoch_to_det.contactSecantY P R z.2) = (separation P R + quarticMoment P R) / 4 := by
    linarith only [(contact_moments hpair).quartic_identity]
  have huvR : expect R (fun z => stoch_to_det.contactSecantX R P z.1 * stoch_to_det.contactSecantY R P z.2) = (separation P R + quarticMoment P R) / 4 := by
    rw [← hsrev, ← hJrev]
    linarith only [(contact_moments hrev).quartic_identity]
  rw [huvP] at hPP
  rw [huvR, hlamX, hlamY] at hRR
  have hLP := pairCharge_linear_correction hpair
  have hLR := pairCharge_linear_correction hrev
  simp only [pairCharge_statistic_correction_split]
  rw [hQP, hPP, hQR, hRR, hsrev, harev, hbrev, hJrev]
  rw [hsrev, harev, hbrev, hJrev] at hLR
  unfold quarticRatio
  linear_combination (norm := skip) hLP / 10 + hLR / 10
  field_simp [(contact_moments hpair).separation_pos.ne']
  rw [show separation P R = defectX P R + defectY P R from rfl]
  ring


/-- The entropy-payment residual for the statistic with correction at slope `lam`. -/
abbrev pairCharge_residual (P R : Law X Y) (lam : ℝ) : ℝ :=
  (expect (marginalProduct P) (fun z => (pairCharge_statistic P R z
        - expect (marginalProduct P) (pairCharge_statistic P R))^2) / 3
    + expect P (fun z => (pairCharge_statistic P R z - expect P (pairCharge_statistic P R))^2) / 6
    + (expect P (pairCharge_statistic P R) - expect (marginalProduct P) (pairCharge_statistic P R))^2 / 12)
  - 2 * lam * ((expect (marginalProduct P) (fun z => pairCharge_statistic P R z * pairCharge_correction P R z)
      + expect P (fun z => pairCharge_statistic P R z * pairCharge_correction P R z)) / 12)
  + lam^2 * (expect (marginalProduct P) (fun z => (pairCharge_correction P R z)^2) / 30
      + expect P (fun z => (pairCharge_correction P R z)^2) / 20)

private lemma pairCharge_residual_expansion {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (lam : ℝ) :
    let t := separation P R
    let jj := quarticRatio P R
    let vv := defectX P R * defectY P R / t^2
    let hh := (1 + t * jj) / 4
    pairCharge_residual P R lam =
      ((9 * vv - 2) / 3 + jj / 6 - t^2 * vv^2 / 4 - t * vv * hh / 6 - hh^2 / 12 +
        2 * (1/5) * t * (3/8 - 2 * vv - jj / 6 + t * (vv / 3 + jj / 24)) +
        (1/5)^2 * t * (7/12 - t / 2 + 2 * t * vv / 3 + t * jj / 12)) -
      lam / 6 * (expect (marginalProduct P) (fun z => pairCharge_statistic P R z * pairCharge_correction P R z) +
        expect P (fun z => pairCharge_statistic P R z * pairCharge_correction P R z)) +
      lam^2 * (5 * pairCharge_defectNorm P R + 6 * pairCharge_defectCross P R) / (60 * t^2) := by
  have hd := (pairCharge_fixed_coefficient_data hpair (1/5 : ℝ)).2
  have hb := pairCharge_correction_second_moments hpair
  unfold pairCharge_residual
  rw [hd, hb.1, hb.2]
  ring

/-- The averaged residual is bounded by the scalar denominator divided by `192`. -/
lemma pairCharge_residual_bound {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (hs1 : separation P R ≤ 1) :
    192 * ((pairCharge_residual P R (pairChargeSlope (separation P R)) +
        pairCharge_residual R P (pairChargeSlope (separation P R))) / 2) ≤
      pairChargeDenominator (separation P R) (quarticRatio P R) := by
  let t := separation P R
  let jj := quarticRatio P R
  let vv := defectX P R * defectY P R / t^2
  let hh := (1 + t * jj) / 4
  let D := (9 * vv - 2) / 3 + jj / 6 - t^2 * vv^2 / 4 - t * vv * hh / 6 - hh^2 / 12 +
    2 * (1/5) * t * (3/8 - 2 * vv - jj / 6 + t * (vv / 3 + jj / 24)) +
    (1/5)^2 * t * (7/12 - t / 2 + 2 * t * vv / 3 + t * jj / 12)
  let rho := (pairCharge_defectNorm P R + pairCharge_defectNorm R P) / 2
  let cross := (pairCharge_defectCross P R + pairCharge_defectCross R P) / 2
  let Xc := ((expect (marginalProduct P) (fun z => pairCharge_statistic P R z * pairCharge_correction P R z) +
      expect P (fun z => pairCharge_statistic P R z * pairCharge_correction P R z)) +
    (expect (marginalProduct R) (fun z => pairCharge_statistic R P z * pairCharge_correction R P z) +
      expect R (fun z => pairCharge_statistic R P z * pairCharge_correction R P z))) / 2
  have hs := (contact_moments hpair).separation_pos
  have hrev := pairCharge_pair_reverse hpair
  have hsrev := pairCharge_separation_reverse hpair
  have hjrev := pairCharge_quarticRatio_reverse hpair
  have hvrev := pairCharge_defectProductRatio_reverse hpair
  have hX : Xc = jj * (1 - t / 4) - 1/4 + (3/2 - t / 2) * (1 - 4 * vv) - rho / (10 * t) := by
    have hx := pairCharge_statistic_correction_average hpair
    change Xc = _ at hx
    rw [hx]
    dsimp only [jj, t, vv, rho]
    ring
  have hQP := pairCharge_correction_hessian hpair (pairChargeSlope t) (pairChargeWeight t)
  have hQR := pairCharge_correction_hessian hrev (pairChargeSlope t) (pairChargeWeight t)
  have hTrev : 6 * defectX R P * defectY R P - (separation R P)^2 - quarticMoment R P =
      6 * defectX P R * defectY P R - t^2 - quarticMoment P R := by
    rw [hsrev, (pairCharge_mean_losses_reverse hpair).1,
      (pairCharge_mean_losses_reverse hpair).2, pairCharge_quarticMoment_reverse hpair]
    dsimp only [t]
    ring
  rw [hTrev] at hQR
  have hT : 6 * defectX P R * defectY P R - t^2 - quarticMoment P R = t^2 * (6 * vv - 1 - jj) := by
    dsimp only [t, vv, jj, quarticRatio]
    field_simp [hs.ne']
  change 0 ≤ 36 * (pairChargeSlope t)^2 *
    (pairCharge_defectNorm P R - 4 * pairCharge_defectCross P R) -
    12 * pairChargeSlope t * pairChargeWeight t * pairCharge_defectNorm P R +
    (pairChargeWeight t)^2 * (6 * defectX P R * defectY P R - t^2 - quarticMoment P R) at hQP
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
    hs hs1 (pairCharge_quarticRatio_bounds hpair).2 (defect_bounds hpair).2 rfl hX hQ
  rw [havg]
  exact hbound


private lemma pairCharge_statistic_gap_lower {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) :
    (1 - separation P R + separation P R * quarticRatio P R) / 4 ≤
      expect P (pairCharge_statistic P R) - expect (marginalProduct P) (pairCharge_statistic P R) := by
  have hg := (pairCharge_fixed_coefficient_data hpair (1/5 : ℝ)).1
  change expect P (pairCharge_statistic P R) - expect (marginalProduct P) (pairCharge_statistic P R) =
    (1 + separation P R * quarticRatio P R) / 4 - separation P R * (defectX P R * defectY P R / (separation P R)^2) at hg
  rw [hg]
  exact pairCharge_fixed_floor_gap (separation P R) (quarticRatio P R)
    (defectX P R * defectY P R / (separation P R)^2) ((1 + separation P R * quarticRatio P R) / 4)
    (contact_moments hpair).separation_pos.le (defect_bounds hpair).2 rfl

/-- The positive scalar denominator gives the averaged information floor. -/
lemma pairCharge_information_floor {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (hs1 : separation P R ≤ 1) :
    0 < pairChargeDenominator (separation P R) (quarticRatio P R) ∧
    3 * (1 - separation P R + separation P R * quarticRatio P R)^2 / pairChargeDenominator (separation P R) (quarticRatio P R) ≤
      (stoch_to_det.Knat P + stoch_to_det.Knat R) / 2 := by
  let t := separation P R
  let jj := quarticRatio P R
  let y := 1 - t + t * jj
  let rp := pairCharge_residual P R (pairChargeSlope t)
  let rm := pairCharge_residual R P (pairChargeSlope t)
  let gp := expect P (pairCharge_statistic P R) - expect (marginalProduct P) (pairCharge_statistic P R)
  let gm := expect R (pairCharge_statistic R P) - expect (marginalProduct R) (pairCharge_statistic R P)
  have hrev := pairCharge_pair_reverse hpair
  have hy : 0 < y := pairCharge_fixed_floor_y_pos t jj
    (contact_moments hpair).separation_pos.le hs1 (by linarith [(pairCharge_quarticRatio_bounds hpair).1])
  have hgp : y / 4 ≤ gp := pairCharge_statistic_gap_lower hpair
  have hgm : y / 4 ≤ gm := by
    have h := pairCharge_statistic_gap_lower hrev
    rw [pairCharge_separation_reverse hpair, pairCharge_quarticRatio_reverse hpair] at h
    exact h
  have hgpne : gp ≠ 0 := ne_of_gt (by linarith only [hy, hgp])
  have hgmne : gm ≠ 0 := ne_of_gt (by linarith only [hy, hgm])
  have hmeansP := pairCharge_correction_means hpair
  have hmeansR := pairCharge_correction_means hrev
  have hp : 0 < rp ∧ gp^2 / (4 * rp) ≤ stoch_to_det.Knat P :=
    pairCharge_residual_information hpair.2.1.1
      (pairCharge_statistic P R) (pairCharge_correction P R) hmeansP.1 hmeansP.2
      hgpne (pairChargeSlope t)
  have hm : 0 < rm ∧ gm^2 / (4 * rm) ≤ stoch_to_det.Knat R :=
    pairCharge_residual_information hpair.2.2.1.1
      (pairCharge_statistic R P) (pairCharge_correction R P) hmeansR.1 hmeansR.2
      hgmne (pairChargeSlope t)
  have havg := pairCharge_average_KL_separate (stoch_to_det.Knat P) (stoch_to_det.Knat R) rp rm gp gm y
    hp.1 hm.1 hy.le hgp hgm hp.2 hm.2
  have hres : 0 < (rp + rm) / 2 := by linarith only [hp.1, hm.1]
  have hbound := pairCharge_residual_bound hpair hs1
  change 192 * ((rp + rm) / 2) ≤ pairChargeDenominator t jj at hbound
  have hresD : (rp + rm) / 2 ≤ pairChargeDenominator t jj / 192 := by
    linarith only [hbound]
  have hproj := pairCharge_projection_information ((stoch_to_det.Knat P + stoch_to_det.Knat R) / 2) y
    ((rp + rm) / 2) (pairChargeDenominator t jj / 192) hres hresD havg
  have hden : 192 * (pairChargeDenominator t jj / 192) = pairChargeDenominator t jj := by ring
  refine ⟨?_, ?_⟩
  · linarith only [hproj.1]
  · rw [hden] at hproj
    exact hproj.2

/-- The pair charge C on common finite supports, including supports with holes. -/
theorem pairCharge_C : HasPairCharge (X := X) (Y := Y) CommonSupportPair (23/250) (7/60) := by
  intro S w P R hpair
  have hm := contact_moments hpair
  have hprice := pairCharge_price hm.separation_pos.le hm.separation_lt_two.le
  by_cases hs1 : separation P R ≤ 1
  · have hfloor := pairCharge_information_floor hpair hs1
    have hj := pairCharge_quarticRatio_bounds hpair
    have hcert := pairCharge_scalar_certificate hm.separation_pos.le hs1 hj.1 hj.2
    have hinfo : pairChargeProfile (separation P R) < (stoch_to_det.Knat P + stoch_to_det.Knat R) / 2 :=
      lt_of_lt_of_le ((lt_div_iff₀ hfloor.1).2 hcert) hfloor.2
    unfold pairChargeProfile at hinfo
    linarith only [hinfo, hprice]
  · have hP : 0 ≤ stoch_to_det.Knat P := stoch_to_det.Knat_nonneg hpair.2.1.1
    have hR : 0 ≤ stoch_to_det.Knat R := stoch_to_det.Knat_nonneg hpair.2.2.1.1
    have hs : 1 < separation P R := lt_of_not_ge hs1
    have hsquare : 1 ≤ (separation P R)^2 := by nlinarith only [hs, sq_nonneg (separation P R - 1)]
    nlinarith only [hP, hR, hs, hsquare, hprice]

end

end NaturalLatents.General
