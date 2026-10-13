-- Adapted from the author's earlier repository (StochasticToDeterministicLatents);
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised.
import NaturalLatents.General.Contact

/-!
# Pair charge: scalar payments and symmetries

This module supplies scalar inequalities used to prove the pair-charge statement. It includes
the cubic logarithmic price, the exact rational
polynomial certificates on the regions of the `(s, j)` rectangle, the payments that follow from
a fixed common coefficient, the spectral-gap identity and the cubic-error payment, then the
bounds on the contact moment `contactj` and the exchange of the two contacts, with the fixed
endpoint tables used later.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
This file retains that source's definitions and lemmas where cited, together with
material adapted from the author's earlier repository.
-/

namespace StochasticToDeterministicLatents.General

noncomputable section

open scoped BigOperators
open MeasureTheory ProbabilityTheory

variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- The cubic logarithmic price. -/
lemma pairCharge_cubic_price {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    9*t/8 + 57*t^2/256 + t^3/16 ≤ Psi t := by
  let F : ℝ → ℝ := fun x => -2 * Real.log (b x) - (9*x/8 + 57*x^2/256 + x^3/16)
  have hd (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt F (x^2*(84+693*x-72*x^2)/(8192*b x)) x := by
    have hb : b x ≠ 0 := (b_pos x (by linarith [hx.2])).ne'
    have hbd : HasDerivAt b (-9/16 + 3*x/32) x := by
      have hid : b = (fun y : ℝ => 1 - (9/16)*y + (3/64)*y^2) := by
        funext y
        unfold b
        ring
      rw [hid]
      apply (((hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_id x).const_mul (9/16))).add
        (((hasDerivAt_id x).pow 2).const_mul (3/64))).congr_deriv
      norm_num
      ring
    have hp := ((hbd.log hb).const_mul (-2)).sub
      ((((hasDerivAt_id x).const_mul (9/8)).add
        (((hasDerivAt_id x).pow 2).const_mul (57/256))).add
        (((hasDerivAt_id x).pow 3).const_mul (1/16)))
    have hid : F = ((fun y : ℝ => -2*Real.log (b y)) -
      (((fun y : ℝ => (9/8)*id y) + (fun y : ℝ => (57/256)*(id^2) y)) +
        (fun y : ℝ => (1/16)*(id^3) y))) := by
      funext y
      dsimp [F]
      ring
    rw [hid]
    apply hp.congr_deriv
    norm_num only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    field_simp [hb]
    unfold b
    ring
  have hm : MonotoneOn F (Set.Icc (0:ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · intro x hx
      exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Set.Icc (0:ℝ) 1 := interior_subset hx
      rw [(hd x hx').deriv]
      have hsq : x^2 ≤ 1 := by nlinarith [hx'.1, hx'.2]
      have hp : 0 ≤ 84+693*x-72*x^2 := by nlinarith [hx'.1]
      exact div_nonneg (mul_nonneg (sq_nonneg x) hp) (mul_nonneg (by norm_num) (b_pos x (by linarith [hx'.2])).le)
  have h := hm (by simp) ⟨ht,ht1⟩ ht
  have hzero : F 0 = 0 := by simp [F,b]
  rw [hzero] at h
  dsimp [F,Psi] at h ⊢
  linarith

lemma pairCharge_tail_Psi {t : ℝ} (ht1 : 1 ≤ t) (ht2 : t ≤ 2) :
    (6 : ℝ) / 5 ≤ Psi t := by
  have ht0 : 0 ≤ t := by linarith
  have hb0 : 0 < b t := b_pos t ht2
  have hprod : 0 ≤ (t - 1) * (11 - t) :=
    mul_nonneg (by linarith) (by linarith)
  have hbhalf : b t ≤ (1 : ℝ) / 2 := by
    unfold b
    nlinarith
  have hl := Real.log_le_log hb0 hbhalf
  have hhalf := stoch_to_det.log_le_quadratic_at_one
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 : ℝ) / 2 ≤ 1)
  norm_num at hhalf
  unfold Psi
  linarith

/-- Region 5: the separation price alone pays the charge. -/
lemma pairCharge_region5 {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (hs : 1 ≤ s P R) :
    (3 : ℝ) / 25 ≤ (I P + I R) / 2 + (1 / 10) * Psi (s P R) := by
  have hm := contact_moments hpair
  have hcost := pairCharge_tail_Psi hs hm.s_lt_two.le
  have hP : 0 ≤ I P := stoch_to_det.Knat_nonneg hpair.2.1.1
  have hR : 0 ≤ I R := stoch_to_det.Knat_nonneg hpair.2.2.1.1
  linarith

-- Each identity below is an exact degree-(5,2) Bernstein decomposition.
/-- The cubic part of the charge left after paying the logarithmic price. -/
abbrev pairChargeCubicRemainder (s : ℝ) : ℝ :=
  (3 / 25 : ℝ) - 9 * s / 80 - 57 * s ^ 2 / 2560 - s ^ 3 / 160

/-- The common denominator polynomial in the low-`j` rectangle certificates. -/
abbrev pairChargeLowDenominator (s j : ℝ) : ℝ :=
  15 - 7 * s + s ^ 2 + (32 - 18 * s + 3 * s ^ 2) * j - s ^ 2 * j ^ 2

/-- Turn a nonnegative Bernstein remainder and a positive reserved payment into
the strict inequality used by the rectangle certificates. -/
lemma pairCharge_of_bernstein_reserve {value reserve : ℝ}
    (hremainder : 0 ≤ value - reserve) (hreserve : 0 < reserve) : 0 < value := by
  linarith

/-- Exact rational Bernstein certificate on the region region_small_low. -/
lemma pairCharge_region_small_low (s j : ℝ)
    (hspos : 0 < s) (hshi : s ≤ (1 / 3 : ℝ))
    (hjlo : (1 / 16 : ℝ) ≤ j) (hjhi : j ≤ (5 / 16 : ℝ)) :
    pairChargeCubicRemainder s *
      pairChargeLowDenominator s j
      < 3 * (1 - s + s * j) ^ 2 := by
  let x : ℝ := 3 * (s - 0)
  let y : ℝ := 4 * (j - (1 / 16 : ℝ))
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hxc : 0 ≤ 1 - x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hyc : 0 ≤ 1 - y := by dsimp [y]; linarith
  have hcert :
      3 * (1 - s + s * j) ^ 2 -
        pairChargeCubicRemainder s *
          pairChargeLowDenominator s j -
        (1 / 10 : ℝ) * s =
        (24 / 25 : ℝ) * (1 - x) ^ 5 * (1 - y) ^ 2
        + (24 / 25 : ℝ) * (1 - x) ^ 5 * y * (1 - y)
        + (185 / 48 : ℝ) * x * (1 - x) ^ 4 * (1 - y) ^ 2
        + (2333 / 600 : ℝ) * x * (1 - x) ^ 4 * y * (1 - y)
        + (41 / 1200 : ℝ) * x * (1 - x) ^ 4 * y ^ 2
        + (231719 / 38400 : ℝ) * x ^ 2 * (1 - x) ^ 3 * (1 - y) ^ 2
        + (39593 / 6400 : ℝ) * x ^ 2 * (1 - x) ^ 3 * y * (1 - y)
        + (6671 / 38400 : ℝ) * x ^ 2 * (1 - x) ^ 3 * y ^ 2
        + (6331687 / 1382400 : ℝ) * x ^ 3 * (1 - x) ^ 2 * (1 - y) ^ 2
        + (15471 / 3200 : ℝ) * x ^ 3 * (1 - x) ^ 2 * y * (1 - y)
        + (441281 / 1382400 : ℝ) * x ^ 3 * (1 - x) ^ 2 * y ^ 2
        + (444246739 / 265420800 : ℝ) * x ^ 4 * (1 - x) * (1 - y) ^ 2
        + (247204543 / 132710400 : ℝ) * x ^ 4 * (1 - x) * y * (1 - y)
        + (67271899 / 265420800 : ℝ) * x ^ 4 * (1 - x) * y ^ 2
        + (62040611 / 265420800 : ℝ) * x ^ 5 * (1 - y) ^ 2
        + (113945773 / 398131200 : ℝ) * x ^ 5 * y * (1 - y)
        + (1306661 / 17694720 : ℝ) * x ^ 5 * y ^ 2 := by
    dsimp [x, y]
    ring
  have hnonneg :
      0 ≤ 3 * (1 - s + s * j) ^ 2 -
        pairChargeCubicRemainder s *
          pairChargeLowDenominator s j -
        (1 / 10 : ℝ) * s := by
    rw [hcert]
    positivity
  have hpaid : 0 < (1 / 10 : ℝ) * s := by positivity
  have hpositive := pairCharge_of_bernstein_reserve hnonneg hpaid
  linarith only [hpositive]

/-- Exact rational Bernstein certificate on the region region_middle. -/
lemma pairCharge_region_middle (s j : ℝ)
    (hslo : (1 / 3 : ℝ) ≤ s) (hshi : s ≤ (1 / 2 : ℝ))
    (hjlo : (1 / 16 : ℝ) ≤ j) (hjhi : j ≤ (1 / 2 : ℝ)) :
    pairChargeCubicRemainder s *
      pairChargeLowDenominator s j
      < 3 * (1 - s + s * j) ^ 2 := by
  let x : ℝ := 6 * (s - (1 / 3 : ℝ))
  let y : ℝ := (16 / 7 : ℝ) * (j - (1 / 16 : ℝ))
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hxc : 0 ≤ 1 - x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hyc : 0 ≤ 1 - y := by dsimp [y]; linarith
  have hcert :
      3 * (1 - s + s * j) ^ 2 -
        pairChargeCubicRemainder s *
          pairChargeLowDenominator s j -
        (1 / 100 : ℝ) =
        (68233763 / 265420800 : ℝ) * (1 - x) ^ 5 * (1 - y) ^ 2
        + (2449787 / 12441600 : ℝ) * (1 - x) ^ 5 * y * (1 - y)
        + (22081 / 4147200 : ℝ) * (1 - x) ^ 5 * y ^ 2
        + (278570653 / 265420800 : ℝ) * x * (1 - x) ^ 4 * (1 - y) ^ 2
        + (16901539 / 16588800 : ℝ) * x * (1 - x) ^ 4 * y * (1 - y)
        + (1500643 / 4147200 : ℝ) * x * (1 - x) ^ 4 * y ^ 2
        + (99271277 / 58982400 : ℝ) * x ^ 2 * (1 - x) ^ 3 * (1 - y) ^ 2
        + (7853489 / 3686400 : ℝ) * x ^ 2 * (1 - x) ^ 3 * y * (1 - y)
        + (3810947 / 2764800 : ℝ) * x ^ 2 * (1 - x) ^ 3 * y ^ 2
        + (4334789 / 3276800 : ℝ) * x ^ 3 * (1 - x) ^ 2 * (1 - y) ^ 2
        + (3314183 / 1474560 : ℝ) * x ^ 3 * (1 - x) ^ 2 * y * (1 - y)
        + (807 / 400 : ℝ) * x ^ 3 * (1 - x) ^ 2 * y ^ 2
        + (80109569 / 157286400 : ℝ) * x ^ 4 * (1 - x) * (1 - y) ^ 2
        + (5872843 / 4915200 : ℝ) * x ^ 4 * (1 - x) * y * (1 - y)
        + (649099 / 491520 : ℝ) * x ^ 4 * (1 - x) * y ^ 2
        + (4039723 / 52428800 : ℝ) * x ^ 5 * (1 - y) ^ 2
        + (418951 / 1638400 : ℝ) * x ^ 5 * y * (1 - y)
        + (53241 / 163840 : ℝ) * x ^ 5 * y ^ 2 := by
    dsimp [x, y]
    ring
  have hnonneg :
      0 ≤ 3 * (1 - s + s * j) ^ 2 -
        pairChargeCubicRemainder s *
          pairChargeLowDenominator s j -
        (1 / 100 : ℝ) := by
    rw [hcert]
    positivity
  have hpositive := pairCharge_of_bernstein_reserve hnonneg (by positivity)
  linarith only [hpositive]

/-- Exact rational Bernstein certificate on the region region_high_lower. -/
lemma pairCharge_region_high_lower (s j : ℝ)
    (hslo : (1 / 2 : ℝ) ≤ s) (hshi : s ≤ (3 / 4 : ℝ))
    (hjlo : (1 / 16 : ℝ) ≤ j) (hjhi : j ≤ (1 / 2 : ℝ)) :
    pairChargeCubicRemainder s *
      pairChargeLowDenominator s j
      < 3 * (1 - s + s * j) ^ 2 := by
  let x : ℝ := 4 * (s - (1 / 2 : ℝ))
  let y : ℝ := (16 / 7 : ℝ) * (j - (1 / 16 : ℝ))
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hxc : 0 ≤ 1 - x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hyc : 0 ≤ 1 - y := by dsimp [y]; linarith
  have hcert :
      3 * (1 - s + s * j) ^ 2 -
        pairChargeCubicRemainder s *
          pairChargeLowDenominator s j -
        (1 / 100 : ℝ) =
        (4039723 / 52428800 : ℝ) * (1 - x) ^ 5 * (1 - y) ^ 2
        + (418951 / 1638400 : ℝ) * (1 - x) ^ 5 * y * (1 - y)
        + (53241 / 163840 : ℝ) * (1 - x) ^ 5 * y ^ 2
        + (10441753 / 52428800 : ℝ) * x * (1 - x) ^ 4 * (1 - y) ^ 2
        + (1150233 / 819200 : ℝ) * x * (1 - x) ^ 4 * y * (1 - y)
        + (340963 / 163840 : ℝ) * x * (1 - x) ^ 4 * y ^ 2
        + (15974493 / 104857600 : ℝ) * x ^ 2 * (1 - x) ^ 3 * (1 - y) ^ 2
        + (63821 / 20480 : ℝ) * x ^ 2 * (1 - x) ^ 3 * y * (1 - y)
        + (8257987 / 1638400 : ℝ) * x ^ 2 * (1 - x) ^ 3 * y ^ 2
        + (1731499 / 52428800 : ℝ) * x ^ 3 * (1 - x) ^ 2 * (1 - y) ^ 2
        + (22823941 / 6553600 : ℝ) * x ^ 3 * (1 - x) ^ 2 * y * (1 - y)
        + (4820473 / 819200 : ℝ) * x ^ 3 * (1 - x) ^ 2 * y ^ 2
        + (17095043 / 838860800 : ℝ) * x ^ 4 * (1 - x) * (1 - y) ^ 2
        + (51231257 / 26214400 : ℝ) * x ^ 4 * (1 - x) * y * (1 - y)
        + (43874453 / 13107200 : ℝ) * x ^ 4 * (1 - x) * y ^ 2
        + (14760583 / 838860800 : ℝ) * x ^ 5 * (1 - y) ^ 2
        + (11522713 / 26214400 : ℝ) * x ^ 5 * y * (1 - y)
        + (9793201 / 13107200 : ℝ) * x ^ 5 * y ^ 2 := by
    dsimp [x, y]
    ring
  have hnonneg :
      0 ≤ 3 * (1 - s + s * j) ^ 2 -
        pairChargeCubicRemainder s *
          pairChargeLowDenominator s j -
        (1 / 100 : ℝ) := by
    rw [hcert]
    positivity
  have hpositive := pairCharge_of_bernstein_reserve hnonneg (by positivity)
  linarith only [hpositive]

/-- Exact rational Bernstein certificate on the region region_high_upper. -/
lemma pairCharge_region_high_upper (s j : ℝ)
    (hslo : (3 / 4 : ℝ) ≤ s) (hshi : s ≤ 1)
    (hjlo : (1 / 16 : ℝ) ≤ j) (hjhi : j ≤ (1 / 2 : ℝ)) :
    pairChargeCubicRemainder s *
      pairChargeLowDenominator s j
      < 3 * (1 - s + s * j) ^ 2 := by
  let x : ℝ := 4 * (s - (3 / 4 : ℝ))
  let y : ℝ := (16 / 7 : ℝ) * (j - (1 / 16 : ℝ))
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hxc : 0 ≤ 1 - x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hyc : 0 ≤ 1 - y := by dsimp [y]; linarith
  have hcert :
      3 * (1 - s + s * j) ^ 2 -
        pairChargeCubicRemainder s *
          pairChargeLowDenominator s j -
        (1 / 100 : ℝ) =
        (14760583 / 838860800 : ℝ) * (1 - x) ^ 5 * (1 - y) ^ 2
        + (11522713 / 26214400 : ℝ) * (1 - x) ^ 5 * y * (1 - y)
        + (9793201 / 13107200 : ℝ) * (1 - x) ^ 5 * y ^ 2
        + (130510787 / 838860800 : ℝ) * x * (1 - x) ^ 4 * (1 - y) ^ 2
        + (63995873 / 26214400 : ℝ) * x * (1 - x) ^ 4 * y * (1 - y)
        + (54057557 / 13107200 : ℝ) * x * (1 - x) ^ 4 * y ^ 2
        + (6017087 / 10485760 : ℝ) * x ^ 2 * (1 - x) ^ 3 * (1 - y) ^ 2
        + (35588557 / 6553600 : ℝ) * x ^ 2 * (1 - x) ^ 3 * y * (1 - y)
        + (7366249 / 819200 : ℝ) * x ^ 2 * (1 - x) ^ 3 * y ^ 2
        + (25281049 / 26214400 : ℝ) * x ^ 3 * (1 - x) ^ 2 * (1 - y) ^ 2
        + (9896911 / 1638400 : ℝ) * x ^ 3 * (1 - x) ^ 2 * y * (1 - y)
        + (794817 / 81920 : ℝ) * x ^ 3 * (1 - x) ^ 2 * y ^ 2
        + (151889 / 204800 : ℝ) * x ^ 4 * (1 - x) * (1 - y) ^ 2
        + (275031 / 81920 : ℝ) * x ^ 4 * (1 - x) * y * (1 - y)
        + (132863 / 25600 : ℝ) * x ^ 4 * (1 - x) * y ^ 2
        + (698307 / 3276800 : ℝ) * x ^ 5 * (1 - y) ^ 2
        + (19083 / 25600 : ℝ) * x ^ 5 * y * (1 - y)
        + (56449 / 51200 : ℝ) * x ^ 5 * y ^ 2 := by
    dsimp [x, y]
    ring
  have hnonneg :
      0 ≤ 3 * (1 - s + s * j) ^ 2 -
        pairChargeCubicRemainder s *
          pairChargeLowDenominator s j -
        (1 / 100 : ℝ) := by
    rw [hcert]
    positivity
  have hpositive := pairCharge_of_bernstein_reserve hnonneg (by positivity)
  linarith only [hpositive]

/-- One scalar split combines the exact rectangle certificates. -/
lemma pairCharge_region_high (s j : ℝ)
    (hslo : (1 / 2 : ℝ) ≤ s) (hshi : s ≤ 1)
    (hjlo : (1 / 16 : ℝ) ≤ j) (hjhi : j ≤ (1 / 2 : ℝ)) :
    pairChargeCubicRemainder s *
      pairChargeLowDenominator s j
      < 3 * (1 - s + s * j) ^ 2 := by
  by_cases hsmid : s ≤ (3 / 4 : ℝ)
  · exact pairCharge_region_high_lower s j hslo hsmid hjlo hjhi
  · exact pairCharge_region_high_upper s j (le_of_lt (lt_of_not_ge hsmid)) hshi hjlo hjhi

/-- The denominator polynomial shared by the high-`j` payment certificates. -/
abbrev pairChargeHighDenominator (s j : ℝ) : ℝ :=
  15 + 32 * j - ((50 / 9 : ℝ) + 70 * j / 3) * s +
    ((5 / 9 : ℝ) + 46 * j / 9 - j ^ 2) * s ^ 2 -
    (5120 / 529 : ℝ) * ((1 / 2 : ℝ) - 5 * s / 12) *
      ((23 / 4 : ℝ) * (j - (1 / 4 : ℝ) +
        s * ((1 / 4 : ℝ) - 171 * j / 100) - s ^ 2 / 160) -
        ((1 / 2 : ℝ) - 5 * s / 12) * ((17 / 10 : ℝ) * ((1 / 2 : ℝ) - j)))

/-- Exact polynomial certificate on `s ∈ [0, 1/6]`. -/
lemma pairCharge_scalar_high_payment_lower (s j : ℝ)
    (hslo : 0 ≤ s) (hshi : s ≤ (1 / 6 : ℝ))
    (hjlo : (5 / 16 : ℝ) ≤ j) (hjhi : j ≤ (1 / 2 : ℝ)) :
    (1 / 100 : ℝ) + 49 * s ^ 2 / 12800 <
      3 * (1 - s + s * j) ^ 2 -
      pairChargeCubicRemainder s *
        pairChargeHighDenominator s j := by
  let x : ℝ := 6 * (s - 0)
  let y : ℝ := (16 / 3 : ℝ) * (j - (5 / 16 : ℝ))
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hxc : 0 ≤ 1 - x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hyc : 0 ≤ 1 - y := by dsimp [y]; linarith
  have hcert :
      3 * (1 - s + s * j) ^ 2 -
      pairChargeCubicRemainder s *
        pairChargeHighDenominator s j - (1 / 100 : ℝ) - 49 * s ^ 2 / 12800 - (1 / 1000 : ℝ) =
        (55621 / 529000 : ℝ) * (1 - x) ^ 6 * (1 - y) ^ 2
        + (55261 / 264500 : ℝ) * (1 - x) ^ 6 * y * (1 - y)
        + (2387 / 23000 : ℝ) * (1 - x) ^ 6 * y ^ 2
        + (9319591 / 19044000 : ℝ) * x * (1 - x) ^ 5 * (1 - y) ^ 2
        + (181811 / 190440 : ℝ) * x * (1 - x) ^ 5 * y * (1 - y)
        + (385283 / 828000 : ℝ) * x * (1 - x) ^ 5 * y ^ 2
        + (168508453 / 182822400 : ℝ) * x ^ 2 * (1 - x) ^ 4 * (1 - y) ^ 2
        + (649991131 / 365644800 : ℝ) * x ^ 2 * (1 - x) ^ 4 * y * (1 - y)
        + (13656013 / 15897600 : ℝ) * x ^ 2 * (1 - x) ^ 4 * y ^ 2
        + (15695301743 / 17550950400 : ℝ) * x ^ 3 * (1 - x) ^ 3 * (1 - y) ^ 2
        + (60943178021 / 35101900800 : ℝ) * x ^ 3 * (1 - x) ^ 3 * y * (1 - y)
        + (162933349 / 190771200 : ℝ) * x ^ 3 * (1 - x) ^ 3 * y ^ 2
        + (9483308146451 / 20218694860800 : ℝ) * x ^ 4 * (1 - x) ^ 2 * (1 - y) ^ 2
        + (1207200360193 / 1263668428800 : ℝ) * x ^ 4 * (1 - x) ^ 2 * y * (1 - y)
        + (6929618053 / 13735526400 : ℝ) * x ^ 4 * (1 - x) ^ 2 * y ^ 2
        + (831283877423 / 6593052672000 : ℝ) * x ^ 5 * (1 - x) * (1 - y) ^ 2
        + (120661115191 / 412065792000 : ℝ) * x ^ 5 * (1 - x) * y * (1 - y)
        + (18426194957 / 103016448000 : ℝ) * x ^ 5 * (1 - x) * y ^ 2
        + (1399241310791 / 101093474304000 : ℝ) * x ^ 6 * (1 - y) ^ 2
        + (52809058481 / 1263668428800 : ℝ) * x ^ 6 * y * (1 - y)
        + (2127437197 / 68677632000 : ℝ) * x ^ 6 * y ^ 2 := by
    dsimp [x, y]
    ring
  have hnonneg :
      0 ≤ 3 * (1 - s + s * j) ^ 2 -
      pairChargeCubicRemainder s *
        pairChargeHighDenominator s j - (1 / 100 : ℝ) - 49 * s ^ 2 / 12800 - (1 / 1000 : ℝ) := by
    rw [hcert]
    positivity
  have hpositive := pairCharge_of_bernstein_reserve hnonneg (by positivity)
  linarith only [hpositive]

/-- Exact polynomial certificate on `s ∈ [1/6, 1/3]`. -/
lemma pairCharge_scalar_high_payment_upper (s j : ℝ)
    (hslo : (1 / 6 : ℝ) ≤ s) (hshi : s ≤ (1 / 3 : ℝ))
    (hjlo : (5 / 16 : ℝ) ≤ j) (hjhi : j ≤ (1 / 2 : ℝ)) :
    (1 / 100 : ℝ) + 49 * s ^ 2 / 12800 <
      3 * (1 - s + s * j) ^ 2 -
      pairChargeCubicRemainder s *
        pairChargeHighDenominator s j := by
  let x : ℝ := 6 * (s - (1 / 6 : ℝ))
  let y : ℝ := (16 / 3 : ℝ) * (j - (5 / 16 : ℝ))
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hxc : 0 ≤ 1 - x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hyc : 0 ≤ 1 - y := by dsimp [y]; linarith
  have hcert :
      3 * (1 - s + s * j) ^ 2 -
      pairChargeCubicRemainder s *
        pairChargeHighDenominator s j - (1 / 100 : ℝ) - 49 * s ^ 2 / 12800 - (1 / 1000 : ℝ) =
        (1399241310791 / 101093474304000 : ℝ) * (1 - x) ^ 6 * (1 - y) ^ 2
        + (52809058481 / 1263668428800 : ℝ) * (1 - x) ^ 6 * y * (1 - y)
        + (2127437197 / 68677632000 : ℝ) * (1 - x) ^ 6 * y ^ 2
        + (6066814413509 / 151640211456000 : ℝ) * x * (1 - x) ^ 5 * (1 - y) ^ 2
        + (1977609613897 / 9477513216000 : ℝ) * x * (1 - x) ^ 5 * y * (1 - y)
        + (19867674589 / 103016448000 : ℝ) * x * (1 - x) ^ 5 * y ^ 2
        + (2344494904913 / 60656084582400 : ℝ) * x ^ 2 * (1 - x) ^ 4 * (1 - y) ^ 2
        + (2026409009587 / 3791005286400 : ℝ) * x ^ 2 * (1 - x) ^ 4 * y * (1 - y)
        + (23671813423 / 41206579200 : ℝ) * x ^ 2 * (1 - x) ^ 4 * y ^ 2
        + (221391454411 / 7582010572800 : ℝ) * x ^ 3 * (1 - x) ^ 3 * (1 - y) ^ 2
        + (834000774739 / 947751321600 : ℝ) * x ^ 3 * (1 - x) ^ 3 * y * (1 - y)
        + (2533255093 / 2575411200 : ℝ) * x ^ 3 * (1 - x) ^ 3 * y ^ 2
        + (364160634341 / 7582010572800 : ℝ) * x ^ 4 * (1 - x) ^ 2 * (1 - y) ^ 2
        + (42278699353 / 47387566080 : ℝ) * x ^ 4 * (1 - x) ^ 2 * y * (1 - y)
        + (4984997869 / 5150822400 : ℝ) * x ^ 4 * (1 - x) ^ 2 * y ^ 2
        + (218326235687 / 4738756608000 : ℝ) * x ^ 5 * (1 - x) * (1 - y) ^ 2
        + (116094585779 / 236937830400 : ℝ) * x ^ 5 * (1 - x) * y * (1 - y)
        + (3245939663 / 6438528000 : ℝ) * x ^ 5 * (1 - x) * y ^ 2
        + (12161783611 / 824131584000 : ℝ) * x ^ 6 * (1 - y) ^ 2
        + (5671576583 / 51508224000 : ℝ) * x ^ 6 * y * (1 - y)
        + (60121001 / 559872000 : ℝ) * x ^ 6 * y ^ 2 := by
    dsimp [x, y]
    ring
  have hnonneg :
      0 ≤ 3 * (1 - s + s * j) ^ 2 -
      pairChargeCubicRemainder s *
        pairChargeHighDenominator s j - (1 / 100 : ℝ) - 49 * s ^ 2 / 12800 - (1 / 1000 : ℝ) := by
    rw [hcert]
    positivity
  have hpositive := pairCharge_of_bernstein_reserve hnonneg (by positivity)
  linarith only [hpositive]

/-- The scalar high-`j` payment, with one extra rational rectangle split. -/
lemma pairCharge_scalar_high_payment (s j : ℝ)
    (hslo : 0 ≤ s) (hshi : s ≤ (1 / 3 : ℝ))
    (hjlo : (5 / 16 : ℝ) ≤ j) (hjhi : j ≤ (1 / 2 : ℝ)) :
    (1 / 100 : ℝ) + 49 * s ^ 2 / 12800 <
      3 * (1 - s + s * j) ^ 2 -
      pairChargeCubicRemainder s *
        pairChargeHighDenominator s j := by
  by_cases hsmid : s ≤ (1 / 6 : ℝ)
  · exact pairCharge_scalar_high_payment_lower s j hslo hsmid hjlo hjhi
  · exact pairCharge_scalar_high_payment_upper s j
      (le_of_lt (lt_of_not_ge hsmid)) hshi hjlo hjhi

/-- A fixed common coefficient cancels the defect `x`. The coefficient is `10 B / e` with `e = 23/4`.
This gives the variance payment directly and removes its sign cases and projection division. -/
lemma pairCharge_projection_residual_upper (D N W U A B d x : ℝ)
    (hB : 0 ≤ B)
    (hD : D ≤ U / 192)
    (hN : (A + B * x) / 12 ≤ N)
    (hW : W ≤ (d + (23 / 4 : ℝ) * x) / 60) :
    D - 2 * (40 * B / 23) * N + (40 * B / 23) ^ 2 * W ≤
      U / 192 - (5 / 3 : ℝ) * B * ((23 / 4 : ℝ) * A - B * d) /
        (23 / 4 : ℝ) ^ 2 := by
  have hNscaled := mul_le_mul_of_nonneg_left hN
    (show 0 ≤ 2 * (40 * B / 23) by positivity)
  have hWscaled := mul_le_mul_of_nonneg_left hW
    (sq_nonneg (40 * B / 23))
  calc
    D - 2 * (40 * B / 23) * N + (40 * B / 23) ^ 2 * W ≤
        U / 192 - 2 * (40 * B / 23) * ((A + B * x) / 12) +
          (40 * B / 23) ^ 2 * ((d + (23 / 4 : ℝ) * x) / 60) := by
      nlinarith only [hD, hNscaled, hWscaled]
    _ = U / 192 - (5 / 3 : ℝ) * B *
        ((23 / 4 : ℝ) * A - B * d) / (23 / 4 : ℝ) ^ 2 := by ring

/-- The denominator comparison after the fixed coefficient. All analytic obligations are the supplied
positive residual variance and one KL lower bound at that coefficient. -/
lemma pairCharge_projection_information (ibar y residual Dstar : ℝ)
    (hr : 0 < residual) (hrD : residual ≤ Dstar)
    (hinfo : y ^ 2 / (64 * residual) ≤ ibar) :
    0 < Dstar ∧ 3 * y ^ 2 / (192 * Dstar) ≤ ibar := by
  have hD : 0 < Dstar := lt_of_lt_of_le hr hrD
  refine ⟨hD, le_trans ?_ hinfo⟩
  have hres : 0 < 64 * residual := by positivity
  have hstar : 0 < 192 * Dstar := by positivity
  apply (div_le_div_iff₀ hstar hres).2
  have hmul := mul_le_mul_of_nonneg_left hrD (sq_nonneg y)
  nlinarith only [hmul]

/-- Scalar reciprocal step from the entropy payment and the fixed-coefficient payment. No sign
assumption on the individual informations is needed: their positive variance KL floors imply it. -/
lemma pairCharge_average_KL (Ip Im Vp Vm Delta y : ℝ)
    (hVp : 0 < Vp) (hVm : 0 < Vm) (hy : 0 ≤ y)
    (hDelta : y / 4 ≤ Delta)
    (hIp : Delta ^ 2 / (4 * Vp) ≤ Ip)
    (hIm : Delta ^ 2 / (4 * Vm) ≤ Im) :
    y ^ 2 / (64 * ((Vp + Vm) / 2)) ≤ (Ip + Im) / 2 := by
  have hDel0 : 0 ≤ Delta := by linarith
  have hproduct : 0 ≤ (Delta - y / 4) * (Delta + y / 4) := by
    apply mul_nonneg
    · linarith
    · linarith
  have hsquare : y ^ 2 ≤ 16 * Delta ^ 2 := by
    nlinarith only [hproduct]
  have hipmul := (div_le_iff₀ (show 0 < 4 * Vp by positivity)).mp hIp
  have himmul := (div_le_iff₀ (show 0 < 4 * Vm by positivity)).mp hIm
  have hip0 : 0 ≤ Ip := le_trans (by positivity) hIp
  have him0 : 0 ≤ Im := le_trans (by positivity) hIm
  have hipy : y ^ 2 ≤ 64 * Vp * Ip := by nlinarith only [hsquare, hipmul]
  have himy : y ^ 2 ≤ 64 * Vm * Im := by nlinarith only [hsquare, himmul]
  have hipyM := mul_le_mul_of_nonneg_left hipy hVm.le
  have himyP := mul_le_mul_of_nonneg_left himy hVp.le
  have hcombined : y ^ 2 * (Vp + Vm) ≤ 64 * Vp * Vm * (Ip + Im) := by
    nlinarith only [hipyM, himyP]
  have hgram : 4 * Vp * Vm ≤ (Vp + Vm) ^ 2 := by
    nlinarith [sq_nonneg (Vp - Vm)]
  have hupper := mul_le_mul_of_nonneg_right hgram
    (show 0 ≤ 16 * (Ip + Im) by positivity)
  have hfinal : y ^ 2 ≤ 16 * (Vp + Vm) * (Ip + Im) := by
    by_contra h
    have hgap : 0 < y ^ 2 - 16 * (Vp + Vm) * (Ip + Im) := by linarith
    have hpositive := mul_pos (show 0 < Vp + Vm by positivity) hgap
    nlinarith only [hcombined, hupper, hpositive]
  apply (div_le_iff₀ (show 0 < 64 * ((Vp + Vm) / 2) by positivity)).2
  nlinarith only [hfinal]

/-- The mean-gap numerator is positive on its full scalar rectangle. -/
lemma pairCharge_fixed_floor_y_pos (s j : ℝ)
    (hsnonneg : 0 ≤ s) (hshi : s ≤ 1) (hjpos : 0 < j) :
    0 < 1 - s + s * j := by
  have hsj : 0 ≤ s * j := mul_nonneg hsnonneg hjpos.le
  by_cases hs : s = 1
  · subst s
    simpa using hjpos
  · have : 0 < 1 - s := lt_of_le_of_ne (by linarith) (sub_ne_zero.mpr (Ne.symm hs)).symm
    linarith

/-- Denominator positivity, with the stronger bound `31/4`. -/
lemma pairCharge_fixed_floor_denominator (s j : ℝ)
    (hslo : 0 ≤ s) (hshi : s ≤ 1)
    (hjnonneg : 0 ≤ j) (hjhi : j ≤ (1 / 2 : ℝ)) :
    (31 / 4 : ℝ) ≤
      15 - 7 * s + s ^ 2 + (32 - 18 * s + 3 * s ^ 2) * j - s ^ 2 * j ^ 2 := by
  have hsrest : 0 ≤ 1 - s := by linarith
  have hsprod := mul_nonneg hslo hsrest
  have hs2 : s ^ 2 ≤ 1 := by nlinarith only [hsprod, hshi]
  have hjrest : 0 ≤ (1 / 2 : ℝ) - j := by linarith
  have hjprod := mul_nonneg hjnonneg hjrest
  have hj2 : j ^ 2 ≤ (1 / 4 : ℝ) := by nlinarith only [hjprod, hjhi]
  have hsj2 : s ^ 2 * j ^ 2 ≤ (1 / 4 : ℝ) := by
    calc
      s ^ 2 * j ^ 2 ≤ 1 * j ^ 2 :=
        mul_le_mul_of_nonneg_right hs2 (sq_nonneg j)
      _ ≤ (1 / 4 : ℝ) := by simpa using hj2
  have hcoef : 0 ≤ 32 - 18 * s + 3 * s ^ 2 := by
    nlinarith [sq_nonneg s]
  have hterm := mul_nonneg hcoef hjnonneg
  nlinarith [sq_nonneg s]

/-- The mean-gap comparison; the lower bound on `v` is unnecessary. -/
lemma pairCharge_fixed_floor_gap (s j v h : ℝ)
    (hslo : 0 ≤ s) (hvhi : v ≤ (1 / 4 : ℝ))
    (hh : h = (1 + s * j) / 4) :
    (1 - s + s * j) / 4 ≤ h - s * v := by
  have hsv := mul_le_mul_of_nonneg_left hvhi hslo
  rw [hh]
  nlinarith only [hsv]

/-- The variance replacement by the formal balanced endpoint. The exact difference is a product of two
nonnegative factors, so the proof avoids differentiation and any assumed realization of `v = 1/4`. -/
lemma pairCharge_fixed_floor_variance (s j v h D C E : ℝ)
    (hshi : s ≤ 1)
    (hjhi : j ≤ (1 / 2 : ℝ)) (hvhi : v ≤ (1 / 4 : ℝ))
    (hh : h = (1 + s * j) / 4)
    (hD : D = (9 * v - 2) / 3 + j / 6 - s ^ 2 * v ^ 2 / 4 -
      s * v * h / 6 - h ^ 2 / 12)
    (hC : C = s * ((3 / 8 : ℝ) - 2 * v - j / 6 +
      s * (v / 3 + j / 24)))
    (hE : E = s * ((7 / 12 : ℝ) - s / 2 + 2 * s * v / 3 + s * j / 12)) :
    192 * (D + C / 2 + E / 16) ≤
      15 - 7 * s + s ^ 2 + (32 - 18 * s + 3 * s ^ 2) * j - s ^ 2 * j ^ 2 := by
  have hcert :
      pairChargeLowDenominator s j -
        192 * (D + C / 2 + E / 16) =
      (1 - 4 * v) * (144 - 50 * s + (7 - 2 * j - 12 * v) * s ^ 2) := by
    rw [hD, hC, hE, hh]
    ring
  have hvfactor : 0 ≤ 1 - 4 * v := by linarith
  have hcoef : 0 ≤ 7 - 2 * j - 12 * v := by linarith
  have hbase : 0 ≤ 144 - 50 * s := by linarith
  have hfactor := mul_nonneg hvfactor
    (add_nonneg hbase (mul_nonneg hcoef (sq_nonneg s)))
  linarith only [hcert, hfactor]

/-- Exact algebraic comparison with `v = 1/4`. The stronger rectangle `v ≤ 1/4`, `j ≤ 1/2`, `s ≤ 1/3`
suffices. -/
lemma pairCharge_fixed_third_variance (s j v h D C E : ℝ)
    (hshi : s ≤ (1 / 3 : ℝ))
    (hjhi : j ≤ (1 / 2 : ℝ)) (hvhi : v ≤ (1 / 4 : ℝ))
    (hh : h = (1 + s * j) / 4)
    (hD : D = (9 * v - 2) / 3 + j / 6 - s ^ 2 * v ^ 2 / 4 -
      s * v * h / 6 - h ^ 2 / 12)
    (hC : C = s * ((3 / 8 : ℝ) - 2 * v - j / 6 +
      s * (v / 3 + j / 24)))
    (hE : E = s * ((7 / 12 : ℝ) - s / 2 + 2 * s * v / 3 + s * j / 12)) :
    192 * (D + 2 * C / 3 + E / 9) ≤
      15 + 32 * j - ((50 / 9 : ℝ) + 70 * j / 3) * s +
        ((5 / 9 : ℝ) + 46 * j / 9 - j ^ 2) * s ^ 2 := by
  have hcert :
      (15 + 32 * j - ((50 / 9 : ℝ) + 70 * j / 3) * s +
        ((5 / 9 : ℝ) + 46 * j / 9 - j ^ 2) * s ^ 2) -
        192 * (D + 2 * C / 3 + E / 9) =
      (1 - 4 * v) *
        (1296 - 594 * s + (101 - 18 * j - 108 * v) * s ^ 2) / 9 := by
    rw [hD, hC, hE, hh]
    ring
  have hvfactor : 0 ≤ 1 - 4 * v := by linarith
  have hcoef : 0 ≤ 101 - 18 * j - 108 * v := by linarith
  have hbase : 0 ≤ 1296 - 594 * s := by linarith
  have hfactor : 0 ≤ (1 - 4 * v) *
      (1296 - 594 * s + (101 - 18 * j - 108 * v) * s ^ 2) / 9 := by
    exact div_nonneg (mul_nonneg hvfactor
      (add_nonneg hbase (mul_nonneg hcoef (sq_nonneg s)))) (by norm_num)
  linarith only [hcert, hfactor]

/-- The complete-square asymmetry payment, with no variable divisor. -/
lemma pairCharge_asymmetry_payment (s z : ℝ) (hshi : s ≤ (1 / 2 : ℝ)) :
    -s ^ 2 / 160 ≤ (3 - s / 4) * z ^ 2 - 17 * s * |z| / 64 := by
  have hcoef : 0 ≤ (1 / 8 : ℝ) - s / 4 := by linarith
  have hterm := mul_nonneg hcoef (sq_nonneg z)
  have hcert : (3 - s / 4) * z ^ 2 - 17 * s * |z| / 64 + s ^ 2 / 160 =
      (23 / 8 : ℝ) * (|z| - 17 * s / 368) ^ 2 +
        (27 / 235520 : ℝ) * s ^ 2 + ((1 / 8 : ℝ) - s / 4) * z ^ 2 := by
    nlinarith only [sq_abs z]
  have hnonneg : 0 ≤ (3 - s / 4) * z ^ 2 - 17 * s * |z| / 64 + s ^ 2 / 160 := by
    rw [hcert]
    positivity
  linarith only [hnonneg]

/-- The bound on `F(t0) - F(t)` follows directly from `t0 ≤ t`; the `x²` term has a known sign, so no
elementary derivative is integrated. -/
lemma pairCharge_defect_parameter_payment (t t0 x : ℝ)
    (ht0 : 0 < t0) (ht : t0 ≤ t) :
    15 * t - 8 * x + x ^ 2 / t - 15 * (t - t0) ≤
      15 * t0 - 8 * x + x ^ 2 / t0 := by
  have hdiv : x ^ 2 / t ≤ x ^ 2 / t0 :=
    div_le_div_of_nonneg_left (sq_nonneg x) ht0 ht
  linarith only [hdiv]

/-- The covariance payment in full scalar form. Feature moments and covariances are explicit hypotheses;
the conclusion is the fixed covariance payment. Uses `pairCharge_asymmetry_payment` and
`pairCharge_defect_parameter_payment`. -/
lemma pairCharge_fixed_covariance
    (s j z v t t0 x HX HY HXp HYp a b hbar M Z NH NL : ℝ)
    (hspos : 0 < s) (hshi : s ≤ (1 / 3 : ℝ))
    (hjlo : (5 / 16 : ℝ) ≤ j) (hjhi : j < (1 / 2 : ℝ))
    (hv : v = (1 - z ^ 2) / 4)
    (ht : t = (1 / 2 : ℝ) - j) (ht0 : t0 = t - 3 * z ^ 2 / 2)
    (ht0pos : 0 < t0) (hxhi : x ≤ 2 * t0)
    (hHX : 0 ≤ HX) (hHY : 0 ≤ HY) (hHXp : 0 ≤ HXp) (hHYp : 0 ≤ HYp)
    (ha : a = s * (1 + z) / 2) (hb : b = s * (1 - z) / 2)
    (hbarMom : hbar = (HX + HY + HXp + HYp) / 2)
    (hbarScalar : hbar = (1 / 2 : ℝ) + x + 9 * z ^ 2 / 2)
    (hM : M = (a * HX + b * HY + b * HXp + a * HYp) / 2)
    (hNH : 12 * NH = j - (1 / 4 : ℝ) + x / 2 +
      12 * ((1 / 4 : ℝ) - v) + s * (j / 4 - 2 * v) + M / 2 + Z / (2 * s ^ 2))
    (hNL : s / 48 * (15 * t0 - 8 * x + x ^ 2 / t0) ≤ NL)
    (hZ : -(71 / 100 : ℝ) * j * s ≤ Z / (2 * s ^ 2)) :
    (13 / 36 : ℝ) ≤ (1 / 2 : ℝ) - 5 * s / 12 ∧
    (j - (1 / 4 : ℝ) + s * ((1 / 4 : ℝ) - 171 * j / 100) - s ^ 2 / 160) +
      ((1 / 2 : ℝ) - 5 * s / 12) * x + s * x ^ 2 / (12 * t) ≤
        12 * (NH + NL / 3) ∧
    (j - (1 / 4 : ℝ) + s * ((1 / 4 : ℝ) - 171 * j / 100) - s ^ 2 / 160) +
      ((1 / 2 : ℝ) - 5 * s / 12) * x ≤ 12 * (NH + NL / 3) := by
  have htpos : 0 < t := by rw [ht]; linarith
  have ht0le : t0 ≤ t := by rw [ht0]; nlinarith [sq_nonneg z]
  have hbarhi : hbar ≤ (17 / 16 : ℝ) := by
    rw [hbarScalar]
    nlinarith [sq_nonneg z]
  have hamin : s * (1 - |z|) / 2 ≤ a := by
    rw [ha]
    have hz := mul_le_mul_of_nonneg_left (neg_abs_le z) hspos.le
    nlinarith only [hz]
  have hbmin : s * (1 - |z|) / 2 ≤ b := by
    rw [hb]
    have hz := mul_le_mul_of_nonneg_left (le_abs_self z) hspos.le
    nlinarith only [hz]
  have hMmin : s * (1 - |z|) * hbar / 2 ≤ M := by
    rw [hM]
    calc
      s * (1 - |z|) * hbar / 2 =
          ((s * (1 - |z|) / 2) * HX + (s * (1 - |z|) / 2) * HY +
            (s * (1 - |z|) / 2) * HXp + (s * (1 - |z|) / 2) * HYp) / 2 := by
        rw [hbarMom]
        ring
      _ ≤ (a * HX + b * HY + b * HXp + a * HYp) / 2 := by
        have h1 := mul_le_mul_of_nonneg_right hamin hHX
        have h2 := mul_le_mul_of_nonneg_right hbmin hHY
        have h3 := mul_le_mul_of_nonneg_right hbmin hHXp
        have h4 := mul_le_mul_of_nonneg_right hamin hHYp
        linarith only [h1, h2, h3, h4]
  have hbarCost := mul_le_mul_of_nonneg_left hbarhi
    (show 0 ≤ s * |z| / 4 by positivity)
  have hsH : s * hbar / 4 = s / 8 + s * x / 4 + 9 * s * z ^ 2 / 8 := by
    rw [hbarScalar]
    ring
  have hMlo : s / 8 + s * x / 4 + 9 * s * z ^ 2 / 8 - 17 * s * |z| / 64 ≤ M / 2 := by
    nlinarith only [hMmin, hbarCost, hsH]
  have hF := pairCharge_defect_parameter_payment t t0 x ht0pos ht0le
  have hFscaled := mul_le_mul_of_nonneg_left hF
    (show 0 ≤ s / 12 by positivity)
  have hNLfour := mul_le_mul_of_nonneg_left hNL (show (0 : ℝ) ≤ 4 by norm_num)
  have hNLscaled : s / 12 * (15 * t0 - 8 * x + x ^ 2 / t0) ≤ 4 * NL := by
    nlinarith only [hNLfour]
  have hNLnew : 15 * s * t / 12 - 2 * s * x / 3 + s * x ^ 2 / (12 * t) -
      (5 / 4 : ℝ) * s * (t - t0) ≤ 4 * NL := by
    calc
      _ = s / 12 * (15 * t - 8 * x + x ^ 2 / t - 15 * (t - t0)) := by
        field_simp [htpos.ne']
        ring
      _ ≤ s / 12 * (15 * t0 - 8 * x + x ^ 2 / t0) := hFscaled
      _ ≤ 4 * NL := hNLscaled
  have hNHrewrite : 12 * NH = j - (1 / 4 : ℝ) + x / 2 + 3 * z ^ 2 +
      s * (j / 4 - (1 / 2 : ℝ) + z ^ 2 / 2) + M / 2 + Z / (2 * s ^ 2) := by
    rw [hNH, hv]
    ring
  have hsdiff : s * (t - t0) = 3 * s * z ^ 2 / 2 := by rw [ht0]; ring
  have hstd : 15 * s * t / 12 = 15 * s * ((1 / 2 : ℝ) - j) / 12 := by
    rw [ht]
  have haggregate :
      j - (1 / 4 : ℝ) + s * ((1 / 4 : ℝ) - 171 * j / 100) +
        ((1 / 2 : ℝ) - 5 * s / 12) * x + s * x ^ 2 / (12 * t) +
          (3 - s / 4) * z ^ 2 - 17 * s * |z| / 64 ≤ 12 * (NH + NL / 3) := by
    nlinarith only [hNHrewrite, hMlo, hZ, hNLnew, hsdiff, hstd]
  have hasym := pairCharge_asymmetry_payment s z (by linarith)
  have hpaid :
      (j - (1 / 4 : ℝ) + s * ((1 / 4 : ℝ) - 171 * j / 100) - s ^ 2 / 160) +
        ((1 / 2 : ℝ) - 5 * s / 12) * x + s * x ^ 2 / (12 * t) ≤
          12 * (NH + NL / 3) := by
    linarith only [haggregate, hasym]
  refine ⟨by linarith, hpaid, ?_⟩
  have htail : 0 ≤ s * x ^ 2 / (12 * t) := by positivity
  linarith only [hpaid, htail]

/-- Convert the feasible fractional-power payment to an exact cubic inequality. -/
lemma pairCharge_rpow_payment_cube {D A B : ℝ} (hD : 0 ≤ D)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hh : D ≤ A^((2:ℝ)/3)*B^((2:ℝ)/3)) : D^3 ≤ A^2*B^2 := by
  have hpowA : (A^((2:ℝ)/3))^3 = A^2 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hA]
    norm_num
  have hpowB : (B^((2:ℝ)/3))^3 = B^2 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hB]
    norm_num
  have hp := pow_le_pow_left₀ hD hh 3
  simpa only [mul_pow,hpowA,hpowB] using hp

/-- The rational cubic-error payment, obtained by raising to the sixth power. This avoids fractional
powers in the final charge and handles zero moments. -/
lemma pairCharge_cubic_error_scalar {ss JJ MU MV DX3 DY3 DD ZZ : ℝ}
    (hs : 0 < ss) (hJ : 0 ≤ JJ) (hJh : JJ ≤ ss^2/2)
    (hMU : 0 ≤ MU) (hMV : 0 ≤ MV)
    (hDX3 : 0 ≤ DX3) (hDY3 : 0 ≤ DY3) (hDD : 0 ≤ DD)
    (hMX : DX3 ≤ MV^2) (hMY : DY3 ≤ MU^2)
    (hMM : MU^2+MV^2 ≤ 4*ss*JJ)
    (hHC : DD ≤ DX3^((2:ℝ)/3)*DY3^((2:ℝ)/3))
    (hCS : ZZ^2 ≤ JJ*DD) :
    ZZ/(2*ss^2) ≥ -(71/100:ℝ)*(JJ/ss^2)*ss := by
  have hMp : MU*MV ≤ 2*ss*JJ := by
    nlinarith only [hMM,sq_nonneg (MU-MV)]
  have hD3 := pairCharge_rpow_payment_cube hDD hDX3 hDY3 hHC
  have hX2 := pow_le_pow_left₀ hDX3 hMX 2
  have hY2 := pow_le_pow_left₀ hDY3 hMY 2
  have hXY := mul_le_mul hX2 hY2 (sq_nonneg DY3) (sq_nonneg (MV^2))
  have hM4 := pow_le_pow_left₀ (mul_nonneg hMU hMV) hMp 4
  have hDu : DD^3 ≤ 16*ss^4*JJ^4 := by
    calc
      _ ≤ (MV^2)^2*(MU^2)^2 := le_trans hD3 hXY
      _ = (MU*MV)^4 := by ring
      _ ≤ (2*ss*JJ)^4 := hM4
      _ = _ := by ring
  have hZ3 := pow_le_pow_left₀ (sq_nonneg ZZ) hCS 3
  have hZ6 : ZZ^6 ≤ 16*ss^4*JJ^7 := by
    calc
      _ = (ZZ^2)^3 := by ring
      _ ≤ (JJ*DD)^3 := hZ3
      _ = JJ^3*DD^3 := by ring
      _ ≤ JJ^3*(16*ss^4*JJ^4) :=
        mul_le_mul_of_nonneg_left hDu (pow_nonneg hJ _)
      _ = _ := by ring
  have hsmall := mul_le_mul_of_nonneg_left hJh
    (show 0 ≤ 16*ss^4*JJ^6 by positivity)
  have hZu : ZZ^6 ≤ 8*(ss*JJ)^6 := by
    calc
      _ ≤ 16*ss^4*JJ^7 := hZ6
      _ = (16*ss^4*JJ^6)*JJ := by ring
      _ ≤ (16*ss^4*JJ^6)*(ss^2/2) := hsmall
      _ = _ := by ring
  have hbound : |ZZ| ≤ (71/50:ℝ)*ss*JJ := by
    by_contra h
    have hlt : (71/50:ℝ)*ss*JJ < |ZZ| := lt_of_not_ge h
    have hp := pow_lt_pow_left₀ hlt (show 0 ≤ (71/50:ℝ)*ss*JJ by positivity) (by norm_num : 6 ≠ 0)
    have hr := mul_le_mul_of_nonneg_right
      (show (8:ℝ) ≤ (71/50:ℝ)^6 by norm_num) (show 0 ≤ (ss*JJ)^6 by positivity)
    have hAbs6 : |ZZ|^6 = ZZ^6 := by
      calc
        _ = (|ZZ|^2)^3 := by ring
        _ = (ZZ^2)^3 := by rw [sq_abs]
        _ = _ := by ring
    rw [hAbs6] at hp
    nlinarith only [hZu,hp,hr]
  have hz : -(71/50:ℝ)*ss*JJ ≤ ZZ := by
    have ha := neg_abs_le ZZ
    linarith
  apply (le_div_iff₀ (show 0 < 2*ss^2 by positivity)).2
  have hsn : ss ≠ 0 := hs.ne'
  field_simp [hsn]
  nlinarith only [hz]

lemma pairCharge_pair_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) : CommonSupportPairs S w R P := by
  exact ⟨hpair.1, hpair.2.2.1, hpair.2.1, hpair.2.2.2.2.1,
    hpair.2.2.2.1, Ne.symm hpair.2.2.2.2.2⟩

lemma pairCharge_v_bounds {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    (2 : ℝ) / 9 ≤ A0 P R * B0 P R / (s P R)^2 ∧
      A0 P R * B0 P R / (s P R)^2 ≤ (1 : ℝ) / 4 := by
  have hm := contact_moments hpair
  have hU := contact_E_nonneg hpair.2.1.1 (fun z => (U P R z.1)^2)
    (fun _ => sq_nonneg _)
  have hV := contact_E_nonneg hpair.2.1.1 (fun z => (V P R z.2)^2)
    (fun _ => sq_nonneg _)
  rw [hm.U2] at hU
  rw [hm.V2] at hV
  have hs : 0 < (s P R)^2 := sq_pos_of_pos hm.s_pos
  have hsum : s P R = A0 P R + B0 P R := rfl
  constructor
  · apply (le_div_iff₀ hs).2
    nlinarith [mul_nonneg hU hV]
  · apply (div_le_iff₀ hs).2
    nlinarith [sq_nonneg (A0 P R - B0 P R)]

lemma pairCharge_J_nonneg {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) : 0 ≤ J P R := by
  exact contact_E_nonneg hpair.2.1.1 _ (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))

lemma pairCharge_contactj_nonneg {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) : 0 ≤ contactj P R := by
  exact div_nonneg (pairCharge_J_nonneg hpair) (sq_nonneg _)

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_E_centered_square {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F : X × Y → ℝ) :
    E P (fun z => (F z - E P F)^2) = E P (fun z => (F z)^2) - (E P F)^2 := by
  have h := contact_q_E_shift_sq hP F (-E P F)
  have heq : (fun z => (F z - E P F)^2) = (fun z => (F z + -E P F)^2) := by rfl
  rw [heq,h]
  ring

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_E_sq_ge_sq_E {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F : X × Y → ℝ) : (E P F)^2 ≤ E P (fun z => (F z)^2) := by
  rw [← sub_nonneg]
  rw [← pairCharge_E_centered_square hP F]
  exact contact_E_nonneg hP _ (fun z => sq_nonneg _)

lemma pairCharge_J_ge_uv_sq {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    (E P (fun z => U P R z.1 * V P R z.2))^2 ≤ J P R := by
  have h := pairCharge_E_sq_ge_sq_E hpair.2.1.1 (fun z => U P R z.1 * V P R z.2)
  convert h using 1
  unfold J
  congr 1
  funext z
  ring

lemma pairCharge_contactj_upper {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    contactj P R ≤ 6 * (A0 P R * B0 P R / (s P R)^2) - 1 ∧
      contactj P R ≤ (1 : ℝ) / 2 := by
  have hm := contact_moments hpair
  have hs : 0 < (s P R)^2 := sq_pos_of_pos hm.s_pos
  constructor
  · unfold contactj
    apply (div_le_iff₀ hs).2
    calc
      _ ≤ 6 * A0 P R * B0 P R - (s P R)^2 := hm.J_bound
      _ = (6 * (A0 P R * B0 P R / (s P R)^2) - 1) * (s P R)^2 := by
        field_simp [hm.s_pos.ne']
  · unfold contactj
    apply (div_le_iff₀ hs).2
    nlinarith [hm.J_bound, hm.scalar_bound]

lemma pairCharge_contactj_lower {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    (1 : ℝ) / 16 ≤ ((1 + s P R * contactj P R) / 4)^2 ∧
      ((1 + s P R * contactj P R) / 4)^2 ≤ contactj P R := by
  have hm := contact_moments hpair
  have hj := pairCharge_contactj_nonneg hpair
  have hs : 0 < (s P R)^2 := sq_pos_of_pos hm.s_pos
  have hcs := pairCharge_J_ge_uv_sq hpair
  have hc := hm.quartic
  have hden : s P R ≠ 0 := ne_of_gt hm.s_pos
  have hjs : contactj P R * (s P R)^2 = J P R := by
    unfold contactj
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hden)
  have hcov : s P R * ((1 + s P R * contactj P R) / 4) =
      E P (fun z => U P R z.1 * V P R z.2) := by
    nlinarith [hjs]
  constructor
  · have hh : (1 : ℝ) / 4 ≤ (1 + s P R * contactj P R) / 4 := by
      nlinarith [mul_nonneg hm.s_pos.le hj]
    nlinarith [sq_nonneg ((1 + s P R * contactj P R) / 4 - 1/4)]
  · have hsq : (s P R)^2 * ((1 + s P R * contactj P R) / 4)^2 =
        (E P (fun z => U P R z.1 * V P R z.2))^2 := by
      rw [← hcov]
      ring
    apply (mul_le_mul_iff_of_pos_left hs).mp
    nlinarith [hsq, hjs]

lemma pairCharge_contactj_bounds {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    (1 : ℝ) / 16 ≤ contactj P R ∧ contactj P R ≤ (1 : ℝ) / 2 := by
  have hl := pairCharge_contactj_lower hpair
  exact ⟨hl.1.trans hl.2, (pairCharge_contactj_upper hpair).2⟩

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_E_scale_prod (P : Law X Y) (F G : X × Y → ℝ) (a b : ℝ) :
    E P (fun z => (a * F z) * (b * G z)) = a * b * E P (fun z => F z * G z) := by
  calc
    _ = E P (fun z => (a * b) * (F z * G z)) := by
      congr 1
      funext z
      ring
    _ = _ := contact_q_E_scale P _ _

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_E_scale_sq (P : Law X Y) (F : X × Y → ℝ) (a : ℝ) :
    E P (fun z => (a * F z)^2) = a^2 * E P (fun z => (F z)^2) := by
  simpa only [pow_two] using pairCharge_E_scale_prod P F F a a

lemma pairCharge_maxcorr_sq {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (F : X → ℝ) (G : Y → ℝ)
    (hF : E P (fun z => F z.1) = 0) (hG : E P (fun z => G z.2) = 0) :
    4 * (E P (fun z => F z.1 * G z.2))^2 ≤
      E P (fun z => (F z.1)^2) * E P (fun z => (G z.2)^2) := by
  have hm := contact_moments hpair
  have hP := hpair.2.1.1
  have hA := contact_E_nonneg hP (fun z => (F z.1)^2) (fun _ => sq_nonneg _)
  by_cases hAz : E P (fun z => (F z.1)^2) = 0
  · have hc : E P (fun z => F z.1 * G z.2) = 0 := by
      unfold E
      apply Finset.sum_eq_zero
      intro z _
      by_cases hz : P z = 0
      · simp [hz]
      · have hzpos : 0 < P z := lt_of_le_of_ne (hP.nonneg z) (Ne.symm hz)
        have hFz := contact_weighted_sq_zero hP (fun z => F z.1) hAz hzpos
        simp [hFz]
    rw [hAz, hc]
    norm_num
  · have hApos : 0 < E P (fun z => (F z.1)^2) := lt_of_le_of_ne hA (Ne.symm hAz)
    have hscaled := hm.hessian
      (fun x => (2 * E P (fun z => F z.1 * G z.2)) * F x)
      (fun y => E P (fun z => (F z.1)^2) * G y)
      (by rw [contact_q_E_scale, hF, mul_zero])
      (by rw [contact_q_E_scale, hG, mul_zero])
    rw [pairCharge_E_scale_prod, pairCharge_E_scale_sq, pairCharge_E_scale_sq] at hscaled
    apply (mul_le_mul_iff_of_pos_left hApos).mp
    nlinarith [hscaled]

lemma pairCharge_mean_UV {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    E P (fun z => U P R z.1) = -A0 P R ∧
      E P (fun z => V P R z.2) = -B0 P R := by
  have hEf : E P (fun z => f P R z.1) = E P (fun z => U P R z.1) + 1 := by
    change E P (fun z => U P R z.1 + 1) = _
    rw [contact_E_add, contact_E_const hpair.2.1.1]
  have hEg : E P (fun z => g P R z.2) = E P (fun z => V P R z.2) + 1 := by
    change E P (fun z => V P R z.2 + 1) = _
    rw [contact_E_add, contact_E_const hpair.2.1.1]
  unfold A0 B0
  constructor <;> linarith

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_E_shift_cube {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F : X × Y → ℝ) (a : ℝ) :
    E P (fun z => (F z + a)^3) =
      E P (fun z => (F z)^3) + 3 * a * E P (fun z => (F z)^2) +
        3 * a^2 * E P F + a^3 := by
  calc
    _ = E P (fun z => (((F z)^3 + (3 * a) * (F z)^2) +
        (3 * a^2) * F z) + a^3) := by
      congr 1
      funext z
      ring
    _ = _ := by
      simp only [contact_E_add, contact_q_E_scale, contact_E_const hP]

lemma pairCharge_cubic_UV {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    E P (fun z => (U P R z.1)^3) = -3 * (A0 P R - B0 P R) ∧
      E P (fun z => (V P R z.2)^3) = 3 * (A0 P R - B0 P R) := by
  have hm := contact_moments hpair
  have hU := pairCharge_E_shift_cube hpair.2.1.1 (fun z => U P R z.1) 1
  have hV := pairCharge_E_shift_cube hpair.2.1.1 (fun z => V P R z.2) 1
  change E P (fun z => (f P R z.1)^3) = _ at hU
  change E P (fun z => (g P R z.2)^3) = _ at hV
  rw [hm.f3, hm.U2, (pairCharge_mean_UV hpair).1] at hU
  rw [hm.g3, hm.V2, (pairCharge_mean_UV hpair).2] at hV
  constructor <;> linarith

omit [DecidableEq X] [DecidableEq Y] in
/-- Expansion shared by the two orientations of the mixed shifted moment. -/
lemma pairCharge_E_shift_mixed {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F G : X × Y → ℝ) :
    E P (fun z => (F z + 1) * (G z + 1)^2) =
      E P (fun z => F z * (G z)^2) + 2 * E P (fun z => F z * G z) +
      E P F + E P (fun z => (G z)^2) + 2 * E P G + 1 := by
  calc
    _ = E P (fun z => (((((F z * (G z)^2) + 2 * (F z * G z)) + F z) +
        (G z)^2) + 2 * G z) + 1) := by
      congr 1
      funext z
      ring
    _ = _ := by
      simp only [contact_E_add, contact_q_E_scale, contact_E_const hP]

omit [DecidableEq X] [DecidableEq Y] in
/-- Expansion shared by the `U` and `V` weighted energies. -/
lemma pairCharge_E_weighted_cube (P : Law X Y) (F : X × Y → ℝ) :
    E P (fun z => (F z)^2 * (2 + F z)) =
      2 * E P (fun z => (F z)^2) + E P (fun z => (F z)^3) := by
  calc
    _ = E P (fun z => 2 * (F z)^2 + (F z)^3) := by
      congr 1
      funext z
      ring
    _ = _ := by rw [contact_E_add, contact_q_E_scale]

lemma pairCharge_mixed_UV {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    E P (fun z => U P R z.1 * (V P R z.2)^2) =
      (3 * (A0 P R - B0 P R) - J P R) / 2 ∧
    E P (fun z => (U P R z.1)^2 * V P R z.2) =
      (-3 * (A0 P R - B0 P R) - J P R) / 2 := by
  have hm := contact_moments hpair
  have hmeans := pairCharge_mean_UV hpair
  have hmix := contact_q_mixed_moments (contact_cond_g2_mul hpair) (contact_cond_f2_mul hpair)
  have hU := pairCharge_E_shift_mixed hpair.2.1.1
    (fun z => U P R z.1) (fun z => V P R z.2)
  change E P (fun z => f P R z.1 * (g P R z.2)^2) = _ at hU
  have hVraw := pairCharge_E_shift_mixed hpair.2.1.1
    (fun z => V P R z.2) (fun z => U P R z.1)
  have hV : E P (fun z => (f P R z.1)^2 * g P R z.2) =
      E P (fun z => (U P R z.1)^2 * V P R z.2) +
      2 * E P (fun z => U P R z.1 * V P R z.2) +
      E P (fun z => V P R z.2) + E P (fun z => (U P R z.1)^2) +
      2 * E P (fun z => U P R z.1) + 1 := by
    calc
      _ = E P (fun z => (V P R z.2 + 1) * (U P R z.1 + 1)^2) := by
        congr 1
        funext z
        unfold f g
        ring
      _ = _ := by simpa only [mul_comm] using hVraw
  rw [hmix.2, hm.f2, hmeans.1, hmeans.2, hm.V2] at hU
  rw [hmix.1, hm.g2, hmeans.1, hmeans.2, hm.U2] at hV
  have hEf : E P (fun z => f P R z.1) = 1 - A0 P R := by unfold A0; ring
  have hEg : E P (fun z => g P R z.2) = 1 - B0 P R := by unfold B0; ring
  rw [hEg] at hU
  rw [hEf] at hV
  have hs : s P R = A0 P R + B0 P R := rfl
  have hq := hm.quartic
  constructor <;> linarith

lemma pairCharge_UV_weighted_energy {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    E P (fun z => (U P R z.1)^2 * (2 + U P R z.1)) = s P R ∧
      E P (fun z => (V P R z.2)^2 * (2 + V P R z.2)) = s P R := by
  have hm := contact_moments hpair
  have hc := pairCharge_cubic_UV hpair
  have hU := pairCharge_E_weighted_cube P (fun z => U P R z.1)
  have hV := pairCharge_E_weighted_cube P (fun z => V P R z.2)
  rw [hm.U2, hc.1] at hU
  rw [hm.V2, hc.2] at hV
  have hs : s P R = A0 P R + B0 P R := rfl
  constructor <;> linarith

lemma pairCharge_reciprocal_roots {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a / b)^((1 : ℝ) / 3) * (b / a)^((1 : ℝ) / 3) = 1 := by
  rw [← Real.mul_rpow (div_nonneg ha.le hb.le) (div_nonneg hb.le ha.le)]
  have hid : a / b * (b / a) = 1 := by field_simp
  rw [hid, Real.one_rpow]

lemma pairCharge_f_reverse_mul {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) {x : X} (hx : x ∈ XSupport S) :
    f P R x * f R P x = 1 := by
  rw [f_eq_cubeRoot, f_eq_cubeRoot]
  exact pairCharge_reciprocal_roots
    (contact_mX_pos hpair.2.2.1 hpair.2.2.2.2.1 hx)
    (contact_mX_pos hpair.2.1 hpair.2.2.2.1 hx)

lemma pairCharge_g_reverse_mul {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) {y : Y} (hy : y ∈ YSupport S) :
    g P R y * g R P y = 1 := by
  rw [g_eq_cubeRoot, g_eq_cubeRoot]
  exact pairCharge_reciprocal_roots
    (contact_mY_pos hpair.2.2.1 hpair.2.2.2.2.1 hy)
    (contact_mY_pos hpair.2.1 hpair.2.2.2.1 hy)

lemma pairCharge_mean_losses_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    A0 R P = B0 P R ∧ B0 R P = A0 P R := by
  have hmix := contact_q_mixed_moments (contact_cond_g2_mul hpair) (contact_cond_f2_mul hpair)
  have hf : E R (fun z => f R P z.1) = E P (fun z => f P R z.1 * (g P R z.2)^2) := by
    unfold E
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : z ∈ S
    · have hroot := pairCharge_f_reverse_mul hpair (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
      calc
        _ = (P z * (g P R z.2)^2) * (f P R z.1 * f R P z.1) * f P R z.1 := by
          rw [contact_ratio_mul hpair z]
          ring
        _ = _ := by rw [hroot]; ring
    · rw [hpair.2.1.2.1 z hz, hpair.2.2.1.2.1 z hz]
      ring
  have hg : E R (fun z => g R P z.2) = E P (fun z => (f P R z.1)^2 * g P R z.2) := by
    unfold E
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : z ∈ S
    · have hroot := pairCharge_g_reverse_mul hpair (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
      calc
        _ = (P z * (f P R z.1)^2) * (g P R z.2 * g R P z.2) * g P R z.2 := by
          rw [contact_ratio_mul hpair z]
          ring
        _ = _ := by rw [hroot]; ring
    · rw [hpair.2.1.2.1 z hz, hpair.2.2.1.2.1 z hz]
      ring
  have hm := contact_moments hpair
  rw [hmix.2, hm.f2] at hf
  rw [hmix.1, hm.g2] at hg
  unfold A0 B0
  constructor <;> linarith

lemma pairCharge_s_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) : s R P = s P R := by
  rw [s, s,
    (pairCharge_mean_losses_reverse hpair).1, (pairCharge_mean_losses_reverse hpair).2]
  ring

lemma pairCharge_J_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) : J R P = J P R := by
  unfold J E
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : z ∈ S
  · have hf := pairCharge_f_reverse_mul hpair (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    have hg := pairCharge_g_reverse_mul hpair (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    have hU : f P R z.1 * U R P z.1 = -U P R z.1 := by
      unfold f at hf ⊢
      nlinarith [hf]
    have hV : g P R z.2 * V R P z.2 = -V P R z.2 := by
      unfold g at hg ⊢
      nlinarith [hg]
    calc
      _ = P z * (f P R z.1 * U R P z.1)^2 *
          (g P R z.2 * V R P z.2)^2 := by
        rw [contact_ratio_mul hpair z]
        ring
      _ = _ := by rw [hU, hV]; ring
  · rw [hpair.2.1.2.1 z hz, hpair.2.2.1.2.1 z hz]
    ring

lemma pairCharge_contactj_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) : contactj R P = contactj P R := by
  unfold contactj
  rw [pairCharge_s_reverse hpair, pairCharge_J_reverse hpair]

lemma pairCharge_v_reverse {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    A0 R P * B0 R P / (s R P)^2 = A0 P R * B0 P R / (s P R)^2 := by
  rw [pairCharge_s_reverse hpair,
    (pairCharge_mean_losses_reverse hpair).1, (pairCharge_mean_losses_reverse hpair).2]
  ring

lemma pairCharge_feasible_marginal_norm {S : Finset (X × Y)} {w P : Law X Y}
    (hw : FeasibleKernel S w) (hP : Contact S w P)
    (A : X → ℝ) (B : Y → ℝ) (hA : ∀ x, 0 ≤ A x) (hB : ∀ y, 0 ≤ B y) :
    E P (fun z => (A z.1)^2 * (B z.2)^2) ≤
      (E P (fun z => (A z.1)^3))^((2 : ℝ) / 3) *
      (E P (fun z => (B z.2)^3))^((2 : ℝ) / 3) := by
  have hApow (x : X) : ((A x)^2)^((3 : ℝ) / 2) = (A x)^3 := by
    rw [← Real.rpow_natCast_mul (hA x) 2 ((3 : ℝ) / 2)]
    norm_num
  have hBpow (y : Y) : ((B y)^2)^((3 : ℝ) / 2) = (B y)^3 := by
    rw [← Real.rpow_natCast_mul (hB y) 2 ((3 : ℝ) / 2)]
    norm_num
  have hhc := stoch_to_det.contact_hypercontractive hw hP
    (f := fun x => (A x)^2) (g := fun y => (B y)^2)
    (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
  simp only [hApow, hBpow] at hhc
  have hleft : (∑ z ∈ S, P z * (A z.1)^2 * (B z.2)^2) =
      E P (fun z => (A z.1)^2 * (B z.2)^2) := by
    unfold E
    simp only [mul_assoc]
    apply Finset.sum_subset (Finset.subset_univ S)
    intro z _ hz
    simp [hP.2.1 z hz]
  have hsumA : (∑ x, stoch_to_det.mX P x * (A x)^3) =
      E P (fun z => (A z.1)^3) :=
    stoch_to_det.sum_push_mul Prod.fst P (fun x => (A x)^3)
  have hsumB : (∑ y, stoch_to_det.mY P y * (B y)^3) =
      E P (fun z => (B z.2)^3) :=
    stoch_to_det.sum_push_mul Prod.snd P (fun y => (B y)^3)
  rw [hleft, hsumA, hsumB] at hhc
  exact hhc

/-- Independence under the product of the two marginals, including its null cells. -/
lemma pairCharge_E_product (P : Law X Y) (F : X → ℝ) (G : Y → ℝ) :
    E (productLaw P) (fun z => F z.1 * G z.2) =
      E P (fun z => F z.1) * E P (fun z => G z.2) := by
  rw [contact_E_fst, contact_E_snd]
  unfold E productLaw
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma pairCharge_E_product_fst {P : Law X Y} (hP : stoch_to_det.IsPMF P) (F : X → ℝ) :
    E (productLaw P) (fun z => F z.1) = E P (fun z => F z.1) := by
  have h := pairCharge_E_product P F (fun _ => 1)
  simpa only [mul_one, contact_E_const hP] using h

lemma pairCharge_E_product_snd {P : Law X Y} (hP : stoch_to_det.IsPMF P) (G : Y → ℝ) :
    E (productLaw P) (fun z => G z.2) = E P (fun z => G z.2) := by
  have h := pairCharge_E_product P (fun _ => 1) G
  simpa only [one_mul, contact_E_const hP] using h

lemma pairCharge_product_isPMF {P : Law X Y} (hP : stoch_to_det.IsPMF P) :
    stoch_to_det.IsPMF (productLaw P) :=
  stoch_to_det.product_isPMF_dom (stoch_to_det.isPMF_push hP) (stoch_to_det.isPMF_push hP)

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_E_div (P : Law X Y) (F : X × Y → ℝ) (c : ℝ) :
    E P (fun z => F z / c) = E P F / c := by
  simp only [E, ← mul_div_assoc, ← Finset.sum_div]

omit [DecidableEq X] [DecidableEq Y] in
lemma pairCharge_E_affine_square (P : Law X Y) (F G : X × Y → ℝ) (c : ℝ) :
    E P (fun z => (F z / c + G z / 4)^2) =
      E P (fun z => (F z)^2) / c^2 +
        E P (fun z => F z * G z) / (2*c) +
        E P (fun z => (G z)^2) / 16 := by
  have hid (z : X × Y) : (F z / c + G z / 4)^2 =
      (F z)^2 / c^2 + (F z * G z) / (2*c) + (G z)^2 / 16 := by
    ring
  simp only [hid, contact_E_add, pairCharge_E_div]


/-- The exact endpoint table for the fixed quarter correction. -/
lemma pairCharge_fixed_endpoint_table {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    let H : X × Y → ℝ := fun z => U P R z.1 * V P R z.2
    let L : X × Y → ℝ := fun z => U P R z.1 + V P R z.2 + s P R
    E P H = (s P R + J P R)/4 ∧
    E (productLaw P) H = A0 P R * B0 P R ∧
    E P L = 0 ∧ E (productLaw P) L = 0 ∧
    E P (fun z => (H z)^2) = J P R ∧
    E (productLaw P) (fun z => (H z)^2) = 9*A0 P R*B0 P R-2*(s P R)^2 ∧
    E P (fun z => (L z)^2) = 3*s P R/2-(s P R)^2+J P R/2 ∧
    E (productLaw P) (fun z => (L z)^2) = s P R-(s P R)^2+2*A0 P R*B0 P R ∧
    E P (fun z => H z*L z) = -J P R+s P R*(s P R+J P R)/4 ∧
    E (productLaw P) (fun z => H z*L z) =
      (s P R)^2-6*A0 P R*B0 P R+s P R*A0 P R*B0 P R := by
  let H : X × Y → ℝ := fun z => U P R z.1 * V P R z.2
  let L : X × Y → ℝ := fun z => U P R z.1 + V P R z.2 + s P R
  have hm := contact_moments hpair
  have hu := (pairCharge_mean_UV hpair).1
  have hv := (pairCharge_mean_UV hpair).2
  have hsum : s P R = A0 P R + B0 P R := rfl
  have hH : E P H = (s P R+J P R)/4 := by
    dsimp [H]
    linarith [hm.quartic]
  have hHQ : E (productLaw P) H = A0 P R*B0 P R := by
    dsimp [H]
    rw [pairCharge_E_product,hu,hv]
    ring
  have hL : E P L = 0 := by
    dsimp [L]
    rw [contact_E_add,contact_E_add,hu,hv,contact_E_const hpair.2.1.1]
    linarith
  have hLQ : E (productLaw P) L = 0 := by
    dsimp [L]
    rw [contact_E_add,contact_E_add,pairCharge_E_product_fst hpair.2.1.1,
      pairCharge_E_product_snd hpair.2.1.1,hu,hv,contact_E_const (pairCharge_product_isPMF hpair.2.1.1)]
    linarith
  have hH2 : E P (fun z => (H z)^2) = J P R := by
    unfold H J
    congr 1
    funext z
    ring
  have hH2Q : E (productLaw P) (fun z => (H z)^2) =
      9*A0 P R*B0 P R-2*(s P R)^2 := by
    simp only [H,mul_pow]
    rw [pairCharge_E_product P (fun x => (U P R x)^2) (fun y => (V P R y)^2),hm.U2,hm.V2,hsum]
    ring
  have hL2 (Q : Law X Y) (hQ : stoch_to_det.IsPMF Q) :
      E Q (fun z => (L z)^2) =
      E Q (fun z => (U P R z.1)^2)+E Q (fun z => (V P R z.2)^2)+
      2*E Q H+2*s P R*(E Q (fun z => U P R z.1)+E Q (fun z => V P R z.2))+(s P R)^2 := by
    dsimp [L]
    rw [contact_q_E_shift_sq hQ]
    have hid (z : X × Y) : (U P R z.1+V P R z.2)^2 =
        (U P R z.1)^2+(V P R z.2)^2+2*H z := by dsimp [H];ring
    simp only [hid,contact_E_add,contact_q_E_scale]
  have hHL (Q : Law X Y) : E Q (fun z => H z*L z) =
      E Q (fun z => (U P R z.1)^2*V P R z.2)+
      E Q (fun z => U P R z.1*(V P R z.2)^2)+s P R*E Q H := by
    have hid (z : X × Y) : H z*L z =
        (U P R z.1)^2*V P R z.2+U P R z.1*(V P R z.2)^2+s P R*H z := by dsimp [H,L];ring
    simp only [hid,contact_E_add,contact_q_E_scale]
  refine ⟨hH,hHQ,hL,hLQ,hH2,hH2Q,?_,?_,?_,?_⟩
  · rw [hL2 P hpair.2.1.1,hm.U2,hm.V2,hH,hu,hv,hsum]
    ring
  · rw [hL2 (productLaw P) (pairCharge_product_isPMF hpair.2.1.1),
      pairCharge_E_product_fst hpair.2.1.1 (fun x => (U P R x)^2),
      pairCharge_E_product_snd hpair.2.1.1 (fun y => (V P R y)^2),
      pairCharge_E_product_fst hpair.2.1.1 (U P R),
      pairCharge_E_product_snd hpair.2.1.1 (V P R),hm.U2,hm.V2,hHQ,hu,hv,hsum]
    ring
  · rw [hHL P,(pairCharge_mixed_UV hpair).1,(pairCharge_mixed_UV hpair).2,hH]
    ring
  · rw [hHL (productLaw P),
      pairCharge_E_product P (fun x => (U P R x)^2) (V P R),
      pairCharge_E_product P (U P R) (fun y => (V P R y)^2),
      hm.U2,hm.V2,hu,hv,hHQ,hsum]
    ring

/-- Exact variance for any fixed additive correction. -/
lemma pairCharge_fixed_coefficient_data {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) (c : ℝ) :
    let t := s P R
    let jj := contactj P R
    let vv := A0 P R*B0 P R/t^2
    let hh := (1+t*jj)/4
    let F : X × Y → ℝ := fun z =>
      U P R z.1*V P R z.2/t+c*(U P R z.1+V P R z.2+t)
    E P F-E (productLaw P) F = hh-t*vv ∧
    E (productLaw P) (fun z => (F z-E (productLaw P) F)^2)/3 +
      E P (fun z => (F z-E P F)^2)/6 + (E P F-E (productLaw P) F)^2/12 =
    (9*vv-2)/3+jj/6-t^2*vv^2/4-t*vv*hh/6-hh^2/12 +
      2*c*t*((3/8:ℝ)-2*vv-jj/6+t*(vv/3+jj/24)) +
      c^2*t*((7/12:ℝ)-t/2+2*t*vv/3+t*jj/12) := by
  let t := s P R
  let H : X × Y → ℝ := fun z => U P R z.1*V P R z.2
  let L : X × Y → ℝ := fun z => U P R z.1+V P R z.2+t
  let F : X × Y → ℝ := fun z => H z/t+c*L z
  change E P F-E (productLaw P) F = _ ∧ _ = _
  obtain ⟨hH,hHQ,hL,hLQ,hH2,hH2Q,hL2,hL2Q,hHL,hHLQ⟩ := pairCharge_fixed_endpoint_table hpair
  have hden : t ≠ 0 := (contact_moments hpair).s_pos.ne'
  have hFP : E P F = (t+J P R)/(4*t) := by
    dsimp [F]
    rw [contact_E_add,pairCharge_E_div,contact_q_E_scale,hH,hL]
    dsimp [t]
    ring
  have hFQ : E (productLaw P) F = A0 P R*B0 P R/t := by
    dsimp [F]
    rw [contact_E_add,pairCharge_E_div,contact_q_E_scale,hHQ,hLQ]
    ring
  have hsquare (Q : Law X Y) : E Q (fun z => (F z)^2) =
      E Q (fun z => (H z)^2)/t^2+(2*c/t)*E Q (fun z => H z*L z)+
        c^2*E Q (fun z => (L z)^2) := by
    have hid (z : X × Y) : (F z)^2 =
        (H z)^2/t^2+(2*c/t)*(H z*L z)+c^2*(L z)^2 := by
      dsimp [F]
      ring
    simp only [hid,contact_E_add,contact_q_E_scale,pairCharge_E_div]
  have hFP2 : E P (fun z => (F z)^2) =
      J P R/t^2+(2*c/t)*(-J P R+t*(t+J P R)/4)+c^2*(3*t/2-t^2+J P R/2) := by
    rw [hsquare P,hH2,hHL,hL2]
  have hFQ2 : E (productLaw P) (fun z => (F z)^2) =
      (9*A0 P R*B0 P R-2*t^2)/t^2+
      (2*c/t)*(t^2-6*A0 P R*B0 P R+t*A0 P R*B0 P R)+
      c^2*(t-t^2+2*A0 P R*B0 P R) := by
    rw [hsquare (productLaw P),hH2Q,hHLQ,hL2Q]
  constructor
  · rw [hFP,hFQ]
    dsimp only [contactj]
    change (t+J P R)/(4*t)-A0 P R*B0 P R/t =
      (1+t*(J P R/t^2))/4-t*(A0 P R*B0 P R/t^2)
    field_simp [hden]
  · rw [pairCharge_E_centered_square (pairCharge_product_isPMF hpair.2.1.1),
      pairCharge_E_centered_square hpair.2.1.1,hFP,hFQ,hFP2,hFQ2]
    dsimp only [contactj]
    change _ = (9*(A0 P R*B0 P R/t^2)-2)/3+(J P R/t^2)/6-
      t^2*(A0 P R*B0 P R/t^2)^2/4-
      t*(A0 P R*B0 P R/t^2)*((1+t*(J P R/t^2))/4)/6-
      ((1+t*(J P R/t^2))/4)^2/12+
      2*c*t*((3/8:ℝ)-2*(A0 P R*B0 P R/t^2)-(J P R/t^2)/6+
        t*((A0 P R*B0 P R/t^2)/3+(J P R/t^2)/24))+
      c^2*t*((7/12:ℝ)-t/2+2*t*(A0 P R*B0 P R/t^2)/3+t*(J P R/t^2)/12)
    field_simp [hden]
    ring

/-- The exact fixed-quarter statistic, gap and integrated variance. -/
lemma pairCharge_fixed_statistic_data {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPairs S w P R) :
    let t := s P R
    let jj := contactj P R
    let vv := A0 P R*B0 P R/t^2
    let hh := (1+t*jj)/4
    let F : X × Y → ℝ := fun z =>
      U P R z.1*V P R z.2/t+(U P R z.1+V P R z.2+t)/4
    E P F-E (productLaw P) F = hh-t*vv ∧
    E (productLaw P) (fun z => (F z-E (productLaw P) F)^2)/3 +
      E P (fun z => (F z-E P F)^2)/6 + (E P F-E (productLaw P) F)^2/12 =
    (9*vv-2)/3+jj/6-t^2*vv^2/4-t*vv*hh/6-hh^2/12 +
      t*((3/8:ℝ)-2*vv-jj/6+t*(vv/3+jj/24))/2 +
      t*((7/12:ℝ)-t/2+2*t*vv/3+t*jj/12)/16 := by
  have h := pairCharge_fixed_coefficient_data hpair (1 / 4 : ℝ)
  constructor
  · simpa [div_eq_mul_inv, mul_comm] using h.1
  · convert h.2 using 1
    all_goals simp [div_eq_mul_inv, mul_comm] <;> ring

end

end StochasticToDeterministicLatents.General
