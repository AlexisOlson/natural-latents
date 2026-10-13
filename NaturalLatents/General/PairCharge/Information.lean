-- Original work by Alexis Olson, Apache-2.0 (see NOTICE), first developed in
-- github.com/AlexisOlson/stochastic-to-deterministic-latents; reorganised for this repository
-- (namespace NaturalLatents.General, declarations renamed, unused material removed).
-- This file builds on and cites the definitions of DLorell/stoch_to_det (Apache-2.0).
import NaturalLatents.General.PairCharge.MomentBounds

/-!
# Pair charge: entropy payments

A variance primitive gives an entropy payment by second derivatives. This module
proves the payment for an affine field with constant gap, with covariance and variance
identities and the resulting positive-residual bound. The support hypothesis permits
cells with zero joint mass and positive product mass.

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

/- The entropy payment is proved by second derivatives, avoiding integrals. -/

lemma pairCharge_covariance_raw {Ω : Type*} [Fintype Ω]
    (M A B : Ω → ℝ) (hMt : ∑ i, M i = 1) :
    (∑ i, M i * (A i - ∑ j, M j * A j) * (B i - ∑ j, M j * B j)) =
      (∑ i, M i * A i * B i) - (∑ i, M i * A i) * (∑ i, M i * B i) := by
  let a := ∑ i, M i * A i
  let b := ∑ i, M i * B i
  have he (i : Ω) : M i * (A i - a) * (B i - b) =
      M i * A i * B i - b * (M i * A i) - a * (M i * B i) + a * b * M i := by ring
  change (∑ i, M i * (A i - a) * (B i - b)) = _
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum, hMt, mul_one]
  change (∑ i, M i * A i * B i) - b * a - a * b + a * b =
    (∑ i, M i * A i * B i) - a * b
  ring


lemma pairCharge_variance_raw {Ω : Type*} [Fintype Ω]
    (M F : Ω → ℝ) (hM : ∑ i, M i = 1) :
    (∑ i, M i * (F i - ∑ j, M j * F j)^2) =
      (∑ i, M i * (F i)^2) - (∑ i, M i * F i)^2 := by
  simpa only [pow_two, mul_assoc] using pairCharge_covariance_raw M F F hM

lemma pairCharge_chi_square_completion {Ω : Type*} [Fintype Ω]
    (M d F : Ω → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hdzero : ∀ i, M i = 0 → d i = 0) (hd : ∑ i, d i = 0) (τ : ℝ) :
    0 ≤ (∑ i, (d i)^2 / M i) - 2 * τ * (∑ i, d i * F i) +
      τ^2 * (∑ i, M i * (F i - ∑ j, M j * F j)^2) := by
  let m := ∑ j, M j * F j
  have hcenter : (∑ i, d i * (F i - m)) = ∑ i, d i * F i := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hd, zero_mul,
      sub_zero]
  have hi (i : Ω) :
      (d i - τ * M i * (F i - m))^2 / M i =
        (d i)^2 / M i - 2 * τ * (d i * (F i - m)) +
          τ^2 * (M i * (F i - m)^2) := by
    by_cases hz : M i = 0
    · simp [hz, hdzero i hz]
    · field_simp [hz]
      ring
  have hpos : 0 ≤ ∑ i, (d i - τ * M i * (F i - m))^2 / M i := by
    exact Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hM i)
  calc
    0 ≤ ∑ i, (d i - τ * M i * (F i - m))^2 / M i := hpos
    _ = (∑ i, (d i)^2 / M i) - 2 * τ * (∑ i, d i * (F i - m)) +
        τ^2 * (∑ i, M i * (F i - m)^2) := by
      simp_rw [hi]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp only [← Finset.mul_sum]
    _ = _ := by rw [hcenter]

/-- A variance primitive gives the entropy payment. Null reference cells are allowed when the first law
also vanishes. -/
lemma pairCharge_entropy_path_payment {Ω : Type*} [Fintype Ω]
    (P Q : Ω → ℝ) (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 ≤ Q i)
    (hzero : ∀ i, Q i = 0 → P i = 0)
    (hPt : ∑ i, P i = 1) (hQt : ∑ i, Q i = 1)
    (A : ℝ → Ω → ℝ) (Δ : ℝ) (H H' : ℝ → ℝ)
    (hHcont : Continuous H) (hH0 : H 0 = 0) (hH'0 : H' 0 = 0)
    (hgap : ∀ u ∈ Set.Ico (0 : ℝ) 1, ∑ i, (P i - Q i) * A u i = Δ)
    (hH : ∀ u ∈ Set.Ico (0 : ℝ) 1, HasDerivAt H (H' u) u)
    (hH' : ∀ u ∈ Set.Ico (0 : ℝ) 1,
      HasDerivAt H'
        (∑ i, (Q i + u * (P i - Q i)) *
          (A u i - ∑ j, (Q j + u * (P j - Q j)) * A u j)^2) u)
    (τ : ℝ) :
    τ * Δ ≤ (∑ i, Q i * stoch_to_det.phi (P i / Q i)) + τ^2 * H 1 := by
  let d : Ω → ℝ := fun i => P i - Q i
  let M : ℝ → Ω → ℝ := fun u i => Q i + u * d i
  let K : ℝ → ℝ := fun u => ∑ i, Q i * stoch_to_det.phi (M u i / Q i)
  let K' : ℝ → ℝ := fun u => ∑ i, d i * Real.log (M u i / Q i)
  let B : ℝ → ℝ := fun u => K u - τ * Δ * u^2 + τ^2 * H u
  let B' : ℝ → ℝ := fun u => K' u - 2 * τ * Δ * u + τ^2 * H' u
  have hd : ∑ i, d i = 0 := by
    simp only [d, Finset.sum_sub_distrib, hPt, hQt, sub_self]
  have hMpos (u : ℝ) (hu : u ∈ Set.Ico (0 : ℝ) 1) (i : Ω)
      (hQi : Q i ≠ 0) : 0 < M u i := by
    have hQip : 0 < Q i := lt_of_le_of_ne (hQ i) (Ne.symm hQi)
    have he : M u i = (1 - u) * Q i + u * P i := by dsimp [M, d]; ring
    rw [he]
    exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hu.2) hQip)
      (mul_nonneg hu.1 (hP i))
  have hMzero (u : ℝ) (i : Ω) (hz : Q i = 0) : M u i = 0 := by
    simp [M, d, hz, hzero i hz]
  have hlin (u : ℝ) (i : Ω) :
      HasDerivAt (fun v => M v i / Q i) (d i / Q i) u := by
    simpa [M] using
      (((hasDerivAt_id u).mul_const (d i)).const_add (Q i)).div_const (Q i)
  have hratio (u : ℝ) (hu : u ∈ Set.Ico (0 : ℝ) 1) (i : Ω) (hz : Q i ≠ 0) :
      M u i / Q i ≠ 0 := div_ne_zero (hMpos u hu i hz).ne' hz
  have hdK (u : ℝ) (hu : u ∈ Set.Ico (0 : ℝ) 1) :
      HasDerivAt K (K' u) u := by
    have hcell (i : Ω) : HasDerivAt
        (fun v => Q i * stoch_to_det.phi (M v i / Q i))
        (d i * Real.log (M u i / Q i)) u := by
      by_cases hz : Q i = 0
      · have hdi : d i = 0 := by simp [d, hz, hzero i hz]
        simpa [hz, hdi] using (hasDerivAt_const u (0 : ℝ))
      · have hr := ((stoch_to_det.hasDerivAt_phi (hratio u hu i hz)).comp u (hlin u i)).const_mul (Q i)
        apply hr.congr_deriv
        field_simp [hz]
    simpa only [K, K'] using (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hcell i))
  have hdK' (u : ℝ) (hu : u ∈ Set.Ico (0 : ℝ) 1) :
      HasDerivAt K' (∑ i, (d i)^2 / M u i) u := by
    have hcell (i : Ω) : HasDerivAt
        (fun v => d i * Real.log (M v i / Q i)) ((d i)^2 / M u i) u := by
      by_cases hz : Q i = 0
      · have hdi : d i = 0 := by simp [d, hz, hzero i hz]
        simpa [hdi] using (hasDerivAt_const u (0 : ℝ))
      · have hr := ((hlin u i).log (hratio u hu i hz)).const_mul (d i)
        apply hr.congr_deriv
        field_simp [hz, (hMpos u hu i hz).ne']
    simpa only [K'] using (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hcell i))
  have hdB (u : ℝ) (hu : u ∈ Set.Ico (0 : ℝ) 1) : HasDerivAt B (B' u) u := by
    have hr := ((hdK u hu).sub (((hasDerivAt_id u).pow 2).const_mul (τ * Δ))).add
      ((hH u hu).const_mul (τ^2))
    apply hr.congr_deriv
    dsimp [B']
    ring
  have hdB' (u : ℝ) (hu : u ∈ Set.Ico (0 : ℝ) 1) : HasDerivAt B'
      ((∑ i, (d i)^2 / M u i) - 2 * τ * Δ +
        τ^2 * (∑ i, M u i * (A u i - ∑ j, M u j * A u j)^2)) u := by
    have hr := ((hdK' u hu).sub ((hasDerivAt_id u).const_mul (2 * τ * Δ))).add
      ((hH' u hu).const_mul (τ^2))
    apply hr.congr_deriv
    dsimp [M, d]
    ring
  have hB'nonnegDeriv (u : ℝ) (hu : u ∈ Set.Ico (0 : ℝ) 1) :
      0 ≤ (∑ i, (d i)^2 / M u i) - 2 * τ * Δ +
        τ^2 * (∑ i, M u i * (A u i - ∑ j, M u j * A u j)^2) := by
    have hMn : ∀ i, 0 ≤ M u i := by
      intro i
      by_cases hz : Q i = 0
      · rw [hMzero u i hz]
      · exact (hMpos u hu i hz).le
    have hdz : ∀ i, M u i = 0 → d i = 0 := by
      intro i hi
      by_cases hz : Q i = 0
      · simp [d, hz, hzero i hz]
      · exact False.elim ((hMpos u hu i hz).ne' hi)
    have hg : ∑ i, d i * A u i = Δ := by simpa only [d] using hgap u hu
    have hc := pairCharge_chi_square_completion (M u) d (A u) hMn hdz hd τ
    simpa only [hg] using hc
  have hB'0 : B' 0 = 0 := by
    have hc : K' 0 = 0 := by
      change (∑ i, d i * Real.log (M 0 i / Q i)) = 0
      apply Finset.sum_eq_zero
      intro i _
      by_cases hz : Q i = 0
      · simp [M, hz]
      · simp [M, hz]
    simp [B', hc, hH'0]
  have hB'cont : ContinuousOn B' (Set.Ico (0 : ℝ) 1) := by
    intro u hu
    exact (hdB' u hu).continuousAt.continuousWithinAt
  have hB'mono : MonotoneOn B' (Set.Ico (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico (0 : ℝ) 1) hB'cont
    · intro u hu
      exact (hdB' u (interior_subset hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [(hdB' u (interior_subset hu)).deriv]
      exact hB'nonnegDeriv u (interior_subset hu)
  have hB'nonneg (u : ℝ) (hu : u ∈ Set.Ico (0 : ℝ) 1) : 0 ≤ B' u := by
    have hh := hB'mono (by norm_num) hu hu.1
    simpa only [hB'0] using hh
  have hKcont : Continuous K := by
    apply continuous_finsetSum
    intro i _
    exact continuous_const.mul
      (stoch_to_det.continuous_phi.comp
        ((continuous_const.add (continuous_id.mul continuous_const)).div_const (Q i)))
  have hBcont : Continuous B :=
    (hKcont.sub (continuous_const.mul (continuous_id.pow 2))).add
      (continuous_const.mul hHcont)
  have hBmono : MonotoneOn B (Set.Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1) hBcont.continuousOn
    · intro u hu
      have hui : u ∈ Set.Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hu
      exact (hdB u ⟨hui.1.le, hui.2⟩).differentiableAt.differentiableWithinAt
    · intro u hu
      have hui : u ∈ Set.Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hu
      rw [(hdB u ⟨hui.1.le, hui.2⟩).deriv]
      exact hB'nonneg u ⟨hui.1.le, hui.2⟩
  have hK0 : K 0 = 0 := by
    change (∑ i, Q i * stoch_to_det.phi (M 0 i / Q i)) = 0
    apply Finset.sum_eq_zero
    intro i _
    by_cases hz : Q i = 0
    · simp [M, hz]
    · simp [M, hz, stoch_to_det.phi]
  have hpay := hBmono (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ 1)
  have hK1 : K 1 = ∑ i, Q i * stoch_to_det.phi (P i / Q i) := by
    change (∑ i, Q i * stoch_to_det.phi (M 1 i / Q i)) = _
    apply Finset.sum_congr rfl
    intro i _
    have he : M 1 i = P i := by dsimp [M, d]; ring
    rw [he]
  dsimp [B] at hpay
  rw [hK0, hH0, hK1] at hpay
  norm_num at hpay
  linarith

lemma pairCharge_payment_positive (K Δ D : ℝ)
    (hpay : ∀ τ : ℝ, τ * Δ ≤ K + τ^2 * D) (hΔ : Δ ≠ 0) : 0 < D := by
  by_contra hD
  have hDn : D ≤ 0 := le_of_not_gt hD
  have hp := hpay ((K + 1) / Δ)
  have he : (K + 1) / Δ * Δ = K + 1 := by field_simp [hΔ]
  have hneg : ((K + 1) / Δ)^2 * D ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hDn
  rw [he] at hp
  linarith

lemma pairCharge_payment_bound (K Δ D : ℝ)
    (hpay : ∀ τ : ℝ, τ * Δ ≤ K + τ^2 * D) : Δ^2 ≤ 4 * K * D := by
  have h := discrim_le_zero (a := D) (b := -Δ) (c := K) (fun x => by nlinarith [hpay x])
  unfold discrim at h
  nlinarith [h]

/-- Exact variance polynomial for A+uB when B has equal endpoint means. -/
lemma pairCharge_variance_linear_field {Ω : Type*} [Fintype Ω]
    (P Q A B : Ω → ℝ) (hPt : ∑ i, P i = 1) (hQt : ∑ i, Q i = 1)
    (hB : ∑ i, (P i - Q i) * B i = 0) (u : ℝ) :
    let Δ := ∑ i, (P i - Q i) * A i
    let VQA := ∑ i, Q i * (A i - ∑ j, Q j * A j)^2
    let VPA := ∑ i, P i * (A i - ∑ j, P j * A j)^2
    let VQB := ∑ i, Q i * (B i - ∑ j, Q j * B j)^2
    let VPB := ∑ i, P i * (B i - ∑ j, P j * B j)^2
    let CQ := ∑ i, Q i * (A i - ∑ j, Q j * A j) * (B i - ∑ j, Q j * B j)
    let CP := ∑ i, P i * (A i - ∑ j, P j * A j) * (B i - ∑ j, P j * B j)
    (∑ i, (Q i + u * (P i - Q i)) *
      (A i + u * B i - ∑ j, (Q j + u * (P j - Q j)) * (A j + u * B j))^2) =
      VQA + (VPA - VQA + Δ^2 + 2 * CQ) * u +
        (-Δ^2 + 2 * CP - 2 * CQ + VQB) * u^2 + (VPB - VQB) * u^3 := by
  dsimp only
  have hMt : ∑ i, (Q i + u * (P i - Q i)) = 1 := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib, hPt, hQt]
    ring
  have hBmean : (∑ i, P i * B i) = ∑ i, Q i * B i := by
    simp only [sub_mul, Finset.sum_sub_distrib] at hB
    linarith
  have hΔ : (∑ i, (P i - Q i) * A i) =
      (∑ i, P i * A i) - ∑ i, Q i * A i := by
    simp only [sub_mul, Finset.sum_sub_distrib]
  have hm : (∑ i, (Q i + u * (P i - Q i)) * (A i + u * B i)) =
      (∑ i, Q i * A i) +
        u * ((∑ i, P i * A i) - (∑ i, Q i * A i) + ∑ i, Q i * B i) := by
    have hc (i : Ω) : (Q i + u * (P i - Q i)) * (A i + u * B i) =
      Q i * A i + u * (P i * A i - Q i * A i + Q i * B i) +
        u^2 * (P i * B i - Q i * B i) := by ring
    simp_rw [hc]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hBmean]
    ring
  have hs : (∑ i, (Q i + u * (P i - Q i)) * (A i + u * B i)^2) =
      (∑ i, Q i * (A i)^2) +
        u * ((∑ i, P i * (A i)^2) - (∑ i, Q i * (A i)^2) +
          2 * (∑ i, Q i * A i * B i)) +
        u^2 * (2 * (∑ i, P i * A i * B i) -
          2 * (∑ i, Q i * A i * B i) + ∑ i, Q i * (B i)^2) +
        u^3 * ((∑ i, P i * (B i)^2) - ∑ i, Q i * (B i)^2) := by
    have hc (i : Ω) : (Q i + u * (P i - Q i)) * (A i + u * B i)^2 =
      Q i * (A i)^2 +
        u * (P i * (A i)^2 - Q i * (A i)^2 + 2 * (Q i * A i * B i)) +
        u^2 * (2 * (P i * A i * B i) - 2 * (Q i * A i * B i) + Q i * (B i)^2) +
        u^3 * (P i * (B i)^2 - Q i * (B i)^2) := by ring
    simp_rw [hc]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [pairCharge_variance_raw _ (fun i => A i + u * B i) hMt, hm, hs,
    pairCharge_variance_raw Q A hQt, pairCharge_variance_raw P A hPt,
    pairCharge_variance_raw Q B hQt, pairCharge_variance_raw P B hPt,
    pairCharge_covariance_raw Q A B hQt, pairCharge_covariance_raw P A B hPt,
    hBmean, hΔ]
  ring

/-- The entropy payment for an affine field of constant gap, with the exact covariance and variance
weights. -/
lemma pairCharge_entropy_linear_field_affine {Ω : Type*} [Fintype Ω]
    (P Q A B : Ω → ℝ) (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 ≤ Q i)
    (hzero : ∀ i, Q i = 0 → P i = 0)
    (hPt : ∑ i, P i = 1) (hQt : ∑ i, Q i = 1)
    (hB : ∑ i, (P i - Q i) * B i = 0) (τ : ℝ) :
    let Δ := ∑ i, (P i - Q i) * A i
    let VQA := ∑ i, Q i * (A i - ∑ j, Q j * A j)^2
    let VPA := ∑ i, P i * (A i - ∑ j, P j * A j)^2
    let VQB := ∑ i, Q i * (B i - ∑ j, Q j * B j)^2
    let VPB := ∑ i, P i * (B i - ∑ j, P j * B j)^2
    let CQ := ∑ i, Q i * (A i - ∑ j, Q j * A j) * (B i - ∑ j, Q j * B j)
    let CP := ∑ i, P i * (A i - ∑ j, P j * A j) * (B i - ∑ j, P j * B j)
    τ * Δ ≤ (∑ i, Q i * stoch_to_det.phi (P i / Q i)) +
      τ^2 * (VQA / 3 + VPA / 6 + Δ^2 / 12 + CQ / 6 + CP / 6 +
        VQB / 30 + VPB / 20) := by
  dsimp only
  let Δ := ∑ i, (P i - Q i) * A i
  let VQA := ∑ i, Q i * (A i - ∑ j, Q j * A j)^2
  let VPA := ∑ i, P i * (A i - ∑ j, P j * A j)^2
  let VQB := ∑ i, Q i * (B i - ∑ j, Q j * B j)^2
  let VPB := ∑ i, P i * (B i - ∑ j, P j * B j)^2
  let CQ := ∑ i, Q i * (A i - ∑ j, Q j * A j) * (B i - ∑ j, Q j * B j)
  let CP := ∑ i, P i * (A i - ∑ j, P j * A j) * (B i - ∑ j, P j * B j)
  let c0 := VQA
  let c1 := VPA - VQA + Δ^2 + 2 * CQ
  let c2 := -Δ^2 + 2 * CP - 2 * CQ + VQB
  let c3 := VPB - VQB
  let H : ℝ → ℝ := fun u => c0 * u^2 / 2 + c1 * u^3 / 6 +
    c2 * u^4 / 12 + c3 * u^5 / 20
  let H' : ℝ → ℝ := fun u => c0 * u + c1 * u^2 / 2 +
    c2 * u^3 / 3 + c3 * u^4 / 4
  have hHcont : Continuous H := by dsimp [H]; fun_prop
  have hH0 : H 0 = 0 := by simp [H]
  have hH'0 : H' 0 = 0 := by simp [H']
  have hHd (u : ℝ) (_hu : u ∈ Set.Ico (0 : ℝ) 1) : HasDerivAt H (H' u) u := by
    have hi := hasDerivAt_id u
    have hr := (((((hi.pow 2).const_mul c0).div_const 2).add
      (((hi.pow 3).const_mul c1).div_const 6)).add
      (((hi.pow 4).const_mul c2).div_const 12)).add
      (((hi.pow 5).const_mul c3).div_const 20)
    apply hr.congr_deriv
    dsimp [H']
    ring
  have hHdd (u : ℝ) (_hu : u ∈ Set.Ico (0 : ℝ) 1) :
      HasDerivAt H'
        (∑ i, (Q i + u * (P i - Q i)) *
          (A i + u * B i - ∑ j, (Q j + u * (P j - Q j)) * (A j + u * B j))^2) u := by
    have hi := hasDerivAt_id u
    have h1 := hi.const_mul c0
    have h2 := ((hi.pow 2).const_mul c1).div_const 2
    have h3 := ((hi.pow 3).const_mul c2).div_const 3
    have h4 := ((hi.pow 4).const_mul c3).div_const 4
    have hr := ((h1.add h2).add h3).add h4
    apply hr.congr_deriv
    rw [pairCharge_variance_linear_field P Q A B hPt hQt hB u]
    dsimp [c0, c1, c2, c3, VQA, VPA, VQB, VPB, CQ, CP, Δ]
    ring
  have hgap (u : ℝ) (_hu : u ∈ Set.Ico (0 : ℝ) 1) :
      (∑ i, (P i - Q i) * (A i + u * B i)) = Δ := by
    have he (i : Ω) : (P i - Q i) * (A i + u * B i) =
        (P i - Q i) * A i + u * ((P i - Q i) * B i) := by ring
    simp_rw [he]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hB, mul_zero, add_zero]
    rfl
  have hp := pairCharge_entropy_path_payment P Q hP hQ hzero hPt hQt
    (fun u i => A i + u * B i) Δ H H' hHcont hH0 hH'0 hgap hHd hHdd τ
  have he : H 1 = VQA / 3 + VPA / 6 + Δ^2 / 12 + CQ / 6 + CP / 6 +
      VQB / 30 + VPB / 20 := by
    dsimp [H, c0, c1, c2, c3]
    ring
  rw [he] at hp
  exact hp

end

end NaturalLatents.General
