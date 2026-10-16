-- Original work by Alexis Olson, Apache-2.0 (see NOTICE), October 2026, written for this repository
-- (namespace NaturalLatents.General); not part of the earlier repository
-- github.com/AlexisOlson/stochastic-to-deterministic-latents.
-- This file builds on and cites the definitions of DLorell/stoch_to_det (Apache-2.0).
import NaturalLatents.General.Definitions

/-!
# Scalar certificates for pair charge C

The price and polynomial inequalities used by the pair charge C.

## Attribution

Original work by Alexis Olson, October 2026, written for this repository; not part of the
earlier repository github.com/AlexisOlson/stochastic-to-deterministic-latents.
This file builds on and cites the definitions of
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
-/

namespace NaturalLatents.General

noncomputable section

/-- The profile left after the price: `G(s) = 7/60 - (103/1000) s - (23/1000) s^2`. -/
abbrev pairChargeProfile (s : ℝ) : ℝ := 7/60 - 103 * s / 1000 - 23 * s^2 / 1000

/-- The correction slope `λ(s) = (27 - 55 s)/40`. -/
abbrev pairChargeSlope (s : ℝ) : ℝ := (27 - 55 * s) / 40

/-- The Hessian weight `k(s) = 13 λ(s) + 2 s`. -/
abbrev pairChargeWeight (s : ℝ) : ℝ := 13 * pairChargeSlope s + 2 * s

/-- The residual denominator `B(s, j)` (paper §4.4, display (B)); not the latent budget `B`. -/
abbrev pairChargeDenominator (s j : ℝ) : ℝ :=
  15 + 32 * j - (178/25 + 74 * j / 5) * s + (21/25 + 46 * j / 25 - j^2) * s^2
    - 32 * pairChargeSlope s * (j * (1 - s / 4) - 1/4)
    + 2/15 * (pairChargeWeight s)^2 * (1/2 - j)

/-- The scalar quantity of the certificate, `F(s, j) = 3 (1 - s + s j)^2 - G(s) B(s, j)`. -/
abbrev pairChargeScalar (s j : ℝ) : ℝ :=
  3 * (1 - s + s * j)^2 - pairChargeProfile s * pairChargeDenominator s j

/-- C8, (PRICE) and (PRICE-INTEGRAL): `(103/1000) t + (23/1000) t^2 ≤ (23/250) separationPrice t` on `[0, 2]`.
The derivative of `(23/250) separationPrice - 103 t/1000 - 23 t^2/1000` is
`((1071/64000)(t - 170/1071)^2 + 1343/17136000 + (69/32000) t^2 (2 - t)) / affinityPoly t ≥ 0`. -/
lemma pairCharge_price {t : ℝ} (ht : 0 ≤ t) (ht2 : t ≤ 2) :
    103 * t / 1000 + 23 * t^2 / 1000 ≤ (23/250 : ℝ) * separationPrice t := by
  let F : ℝ → ℝ := fun x => (23/250) * (-2 * Real.log (affinityPoly x)) -
    (103*x/1000 + 23*x^2/1000)
  have hd (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 2) :
      HasDerivAt F (((1071/64000) * (x - 170/1071)^2 + 1343/17136000 +
        (69/32000) * x^2 * (2 - x)) / affinityPoly x) x := by
    have hb : affinityPoly x ≠ 0 := (affinityPoly_pos x hx.2).ne'
    have hbd : HasDerivAt affinityPoly (-9/16 + 3*x/32) x := by
      have hid : affinityPoly = (fun y : ℝ => 1 - (9/16)*y + (3/64)*y^2) := by
        funext y
        unfold affinityPoly
        ring
      rw [hid]
      apply (((hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_id x).const_mul (9/16))).add
        (((hasDerivAt_id x).pow 2).const_mul (3/64))).congr_deriv
      norm_num
      ring
    have hp := (((hbd.log hb).const_mul (-2)).const_mul (23/250)).sub
      (((hasDerivAt_id x).const_mul (103/1000)).add
        (((hasDerivAt_id x).pow 2).const_mul (23/1000)))
    have hid : F = ((fun y : ℝ => (23/250) * (-2*Real.log (affinityPoly y))) -
      ((fun y : ℝ => (103/1000)*id y) + (fun y : ℝ => (23/1000)*(id^2) y))) := by
      funext y
      dsimp [F]
      ring
    rw [hid]
    apply hp.congr_deriv
    norm_num only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    field_simp [hb]
    unfold affinityPoly
    ring
  have hm : MonotoneOn F (Set.Icc (0:ℝ) 2) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 2)
    · intro x hx
      exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Set.Icc (0:ℝ) 2 := interior_subset hx
      rw [(hd x hx').deriv]
      have hp : 0 ≤ (1071/64000 : ℝ) * (x - 170/1071)^2 + 1343/17136000 +
          (69/32000) * x^2 * (2 - x) := by
        exact add_nonneg (add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
          (by norm_num)) (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg x))
            (sub_nonneg.mpr hx'.2))
      exact div_nonneg hp (affinityPoly_pos x hx'.2).le
  have h := hm (by simp) ⟨ht, ht2⟩ ht
  have hzero : F 0 = 0 := by simp [F, affinityPoly]
  rw [hzero] at h
  dsimp [F, separationPrice] at h ⊢
  linarith

/-- C9, edge `j = 1/16`: `F_l = M_l + (2907750 + 6796995 s + 137267 s^2 + 6234675 s^3 + 528825 s^4)/2880000000`. -/
lemma pairCharge_quartic_low {s : ℝ} (hs : 0 ≤ s) :
    0 < pairChargeScalar s (1/16) := by
  have hcert : pairChargeScalar s (1/16) =
      (17/500) * (s - 3/4)^2 + s * (s - 39/50)^2 * (267/200 + (43/125) * s) +
      (2907750 + 6796995*s + 137267*s^2 + 6234675*s^3 + 528825*s^4) / 2880000000 := by
    unfold pairChargeScalar pairChargeProfile pairChargeDenominator pairChargeSlope pairChargeWeight
    ring
  have hM : 0 ≤ (17/500 : ℝ) * (s - 3/4)^2 +
      s * (s - 39/50)^2 * (267/200 + (43/125) * s) :=
    add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (mul_nonneg (mul_nonneg hs (sq_nonneg _))
        (add_nonneg (by norm_num) (mul_nonneg (by norm_num) hs)))
  have hN : 0 < (2907750 + 6796995*s + 137267*s^2 + 6234675*s^3 + 528825*s^4) /
      (2880000000 : ℝ) := by
    apply div_pos _ (by norm_num)
    nlinarith only [hs, sq_nonneg s, pow_nonneg hs 3, pow_nonneg hs 4]
  rw [hcert]
  exact add_pos_of_nonneg_of_pos hM hN

/-- C9, edge `j = 1/2`: `F_h = M_h + (8000 + 10005 s + 116424 s^2 + 612 s^3 + 828 s^4)/3600000`. -/
lemma pairCharge_quartic_high {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < pairChargeScalar s (1/2) := by
  have hcert : pairChargeScalar s (1/2) =
      (8/5 - (21/40)*s) * (s - 1/12)^2 + s^3 * (3/1000 + (23/250)*(1 - s)) +
      (8000 + 10005*s + 116424*s^2 + 612*s^3 + 828*s^4) / 3600000 := by
    unfold pairChargeScalar pairChargeProfile pairChargeDenominator pairChargeSlope pairChargeWeight
    ring
  have hcoef : 0 ≤ (8/5 : ℝ) - (21/40)*s := by linarith
  have hM : 0 ≤ (8/5 - (21/40)*s) * (s - 1/12)^2 +
      s^3 * (3/1000 + (23/250)*(1 - s)) :=
    add_nonneg (mul_nonneg hcoef (sq_nonneg _))
      (mul_nonneg (pow_nonneg hs 3)
        (add_nonneg (by norm_num) (mul_nonneg (by norm_num) (sub_nonneg.mpr hs1))))
  have hN : 0 < (8000 + 10005*s + 116424*s^2 + 612*s^3 + 828*s^4) /
      (3600000 : ℝ) := by
    apply div_pos _ (by norm_num)
    nlinarith only [hs, sq_nonneg s, pow_nonneg hs 3, pow_nonneg hs 4]
  rw [hcert]
  exact add_pos_of_nonneg_of_pos hM hN

/-- C9, the Bernstein middle coefficient
`F_m = (F_l + F_h)/2 - (49/512)(3 + G(s)) s^2 = M_m + (77550 + 106007463 s + 57708163 s^2 + 5565 s^3 + 469995 s^4)/1152000000`. -/
lemma pairCharge_quartic_mid {s : ℝ} (hs : 0 ≤ s) :
    0 < (pairChargeScalar s (1/16) + pairChargeScalar s (1/2)) / 2
      - 49/512 * (3 + pairChargeProfile s) * s^2 := by
  have hcert : (pairChargeScalar s (1/16) + pairChargeScalar s (1/2)) / 2 -
      49/512 * (3 + pairChargeProfile s) * s^2 =
      (3/20) * (s - 1/3)^2 + s * (s - 4/5)^2 * (2/5 + (16/125)*s) +
      (77550 + 106007463*s + 57708163*s^2 + 5565*s^3 + 469995*s^4) / 1152000000 := by
    unfold pairChargeScalar pairChargeProfile pairChargeDenominator pairChargeSlope pairChargeWeight
    ring
  have hM : 0 ≤ (3/20 : ℝ) * (s - 1/3)^2 +
      s * (s - 4/5)^2 * (2/5 + (16/125)*s) :=
    add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (mul_nonneg (mul_nonneg hs (sq_nonneg _))
        (add_nonneg (by norm_num) (mul_nonneg (by norm_num) hs)))
  have hN : 0 < (77550 + 106007463*s + 57708163*s^2 + 5565*s^3 + 469995*s^4) /
      (1152000000 : ℝ) := by
    apply div_pos _ (by norm_num)
    nlinarith only [hs, sq_nonneg s, pow_nonneg hs 3, pow_nonneg hs 4]
  rw [hcert]
  exact add_pos_of_nonneg_of_pos hM hN

/-- C9, (INTERPOLATION) and (SCALAR): `G(s) B(s, j) < 3 (1 - s + s j)^2` on `[0,1] × [1/16, 1/2]`.
With `q = (16 j - 1)/7`, `F(s, j) = (1-q)^2 F_l + 2 q (1-q) F_m + q^2 F_h` exactly. -/
lemma pairCharge_scalar_certificate {s j : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hjlo : 1/16 ≤ j) (hjhi : j ≤ 1/2) :
    pairChargeProfile s * pairChargeDenominator s j < 3 * (1 - s + s * j)^2 := by
  let q : ℝ := (16*j - 1)/7
  let m : ℝ := (pairChargeScalar s (1/16) + pairChargeScalar s (1/2))/2 -
    49/512 * (3 + pairChargeProfile s) * s^2
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  have hlo := pairCharge_quartic_low hs
  have hhi := pairCharge_quartic_high hs hs1
  have hmid : 0 < m := pairCharge_quartic_mid hs
  have hid : pairChargeScalar s j =
      (1 - q)^2 * pairChargeScalar s (1/16) + 2*q*(1-q)*m +
        q^2 * pairChargeScalar s (1/2) := by
    dsimp [q, m, pairChargeScalar, pairChargeProfile, pairChargeDenominator,
      pairChargeSlope, pairChargeWeight]
    ring
  have hmidterm : 0 ≤ 2*q*(1-q)*m :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hq0) (sub_nonneg.mpr hq1)) hmid.le
  have hf : 0 < pairChargeScalar s j := by
    rw [hid]
    by_cases hhalf : q ≤ 1/2
    · have hleft : 0 < 1 - q := by linarith
      exact add_pos_of_pos_of_nonneg
        (add_pos_of_pos_of_nonneg (mul_pos (sq_pos_of_pos hleft) hlo) hmidterm)
        (mul_nonneg (sq_nonneg q) hhi.le)
    · have hright : 0 < q := by linarith
      exact add_pos_of_nonneg_of_pos
        (add_nonneg (mul_nonneg (sq_nonneg (1-q)) hlo.le) hmidterm)
        (mul_pos (sq_pos_of_pos hright) hhi)
  dsimp [pairChargeScalar] at hf
  linarith

/-- C6, the asymmetry bracket of (R4): at least `70` (hence nonnegative) on `0 ≤ s ≤ 1`, `j ≤ 1/2`,
for every `w = z^2 ≥ 0`. -/
lemma pairCharge_asymmetry_bracket {s j w : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hj : j ≤ 1/2)
    (hw : 0 ≤ w) :
    70 ≤ 48 * (3 - 101 * s / 120 + (7/200 - j / 24) * s^2 + s^2 * w / 16)
      + 32 * pairChargeSlope s * (3/2 - s / 2) + (pairChargeWeight s)^2 / 5 := by
  have hsw := mul_nonneg (sq_nonneg s) hw
  have hsj := mul_nonneg (sq_nonneg s) (show 0 ≤ (1/2 : ℝ) - j by linarith)
  have hsquare : 0 ≤ s^2 := pow_nonneg hs 2
  have hlinear := mul_nonneg (by norm_num : (0 : ℝ) ≤ 5751/200)
    (sub_nonneg.mpr hs1)
  have hshift := mul_nonneg (by norm_num : (0 : ℝ) ≤ 115333/1600) (sq_nonneg (1-s))
  unfold pairChargeWeight pairChargeSlope
  ring_nf at hsquare hlinear hshift hsw hsj ⊢
  linarith only [hsquare, hlinear, hshift, hsw, hsj]

/-- C5-C6, (R3)/(R4) as one exact identity. `D` is the integrated variance of the statistic in the form of
`pairCharge_fixed_coefficient_data` at `c = 1/5`; `Xc` is the averaged correction product (X);
`rho`, `h` are the averaged defect norm and cross moment; `v = a b / s^2`, so `z^2 = 1 - 4 v`. -/
lemma pairCharge_residual_identity (s j v rho h D Xc : ℝ) (hs : s ≠ 0)
    (hD : D = (9 * v - 2) / 3 + j / 6 - s^2 * v^2 / 4 - s * v * ((1 + s * j) / 4) / 6
      - ((1 + s * j) / 4)^2 / 12
      + 2 * (1/5) * s * (3/8 - 2 * v - j / 6 + s * (v / 3 + j / 24))
      + (1/5)^2 * s * (7/12 - s / 2 + 2 * s * v / 3 + s * j / 12))
    (hX : Xc = j * (1 - s / 4) - 1/4 + (3/2 - s / 2) * (1 - 4 * v) - rho / (10 * s)) :
    192 * (D - pairChargeSlope s / 6 * Xc
        + (pairChargeSlope s)^2 * (5 * rho + 6 * h) / (60 * s^2)) =
      pairChargeDenominator s j
      - (1 - 4 * v) * (48 * (3 - 101 * s / 120 + (7/200 - j / 24) * s^2 + s^2 * (1 - 4 * v) / 16)
          + 32 * pairChargeSlope s * (3/2 - s / 2) + (pairChargeWeight s)^2 / 5)
      - 2 / (15 * s^2) * (36 * (pairChargeSlope s)^2 * (rho - 4 * h)
          - 12 * pairChargeSlope s * pairChargeWeight s * rho
          + (pairChargeWeight s)^2 * (s^2 * (6 * v - 1 - j))) := by
  subst D Xc
  unfold pairChargeDenominator pairChargeWeight pairChargeSlope
  field_simp [hs]
  ring

/-- C6, the direct residual bound `192 Res ≤ B(s, j)` in scalar form. -/
lemma pairCharge_residual_le_denominator (s j v rho h D Xc : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1) (hj : j ≤ 1/2) (hv : v ≤ 1/4)
    (hD : D = (9 * v - 2) / 3 + j / 6 - s^2 * v^2 / 4 - s * v * ((1 + s * j) / 4) / 6
      - ((1 + s * j) / 4)^2 / 12
      + 2 * (1/5) * s * (3/8 - 2 * v - j / 6 + s * (v / 3 + j / 24))
      + (1/5)^2 * s * (7/12 - s / 2 + 2 * s * v / 3 + s * j / 12))
    (hX : Xc = j * (1 - s / 4) - 1/4 + (3/2 - s / 2) * (1 - 4 * v) - rho / (10 * s))
    (hQ : 0 ≤ 36 * (pairChargeSlope s)^2 * (rho - 4 * h)
          - 12 * pairChargeSlope s * pairChargeWeight s * rho
          + (pairChargeWeight s)^2 * (s^2 * (6 * v - 1 - j))) :
    192 * (D - pairChargeSlope s / 6 * Xc
        + (pairChargeSlope s)^2 * (5 * rho + 6 * h) / (60 * s^2)) ≤
      pairChargeDenominator s j := by
  have hid := pairCharge_residual_identity s j v rho h D Xc hs.ne' hD hX
  have hz : 0 ≤ 1 - 4*v := by linarith
  have hb := pairCharge_asymmetry_bracket hs.le hs1 hj hz
  have hterm : 0 ≤ (1 - 4*v) *
      (48 * (3 - 101*s/120 + (7/200 - j/24)*s^2 + s^2*(1 - 4*v)/16) +
        32*pairChargeSlope s*(3/2 - s/2) + (pairChargeWeight s)^2/5) :=
    mul_nonneg hz (by linarith)
  have hfactor : 0 ≤ 2 / (15*s^2) := by positivity
  have hlast := mul_nonneg hfactor hQ
  linarith only [hid, hterm, hlast]


end

end NaturalLatents.General
