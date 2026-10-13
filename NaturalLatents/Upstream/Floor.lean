-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/Floor.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised.
-- Source: the main branch and the shared-race/contact additions of pull request #5 by Satya Benson, as included in pull request #6 by Jeremy Gillen.
-- Local changes: Added ratio_rpow_two_thirds and mul_ratio_rpow; retained and reorganised the contact-secant helpers, with required lemmas public.
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic.NormNum
import NaturalLatents.Upstream.Prelude
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import NaturalLatents.Upstream.Duality
import NaturalLatents.Upstream.Toolkit

/-!
# The near-collision information floor

This file proves `Ixy_ge_hgr_floor`, which bounds mutual information using
maximal correlation, and `nearcollision_floor`, which gives a uniform floor for
two distinct nearby contacts of one feasible kernel. These estimates supply
the contact-separation bounds used by the race argument.
-/

namespace stoch_to_det

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

lemma mX_eq_sum (q : α × β → ℝ) (x : α) : mX q x = ∑ y, q (x, y) := by
  change push Prod.fst q x = ∑ y, q (x, y)
  unfold push
  rw [show (Finset.univ.filter fun a : α × β => a.1 = x) =
      Finset.univ.image fun y : β => (x, y) by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hz
      exact ⟨z.2, by ext <;> simp [hz]⟩
    · rintro ⟨y, rfl⟩
      rfl]
  rw [Finset.sum_image]
  intro y₁ _ y₂ _ h
  exact congrArg Prod.snd h

lemma mY_eq_sum (q : α × β → ℝ) (y : β) : mY q y = ∑ x, q (x, y) := by
  change push Prod.snd q y = ∑ x, q (x, y)
  unfold push
  rw [show (Finset.univ.filter fun a : α × β => a.2 = y) =
      Finset.univ.image fun x : α => (x, y) by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hz
      exact ⟨z.1, by ext <;> simp [hz]⟩
    · rintro ⟨x, rfl⟩
      rfl]
  rw [Finset.sum_image]
  intro x₁ _ x₂ _ h
  exact congrArg Prod.fst h

lemma mX_zero_of_support_eq {q r : α × β → ℝ}
    (hq : IsPMF q) (hs : support q = support r) {x : α}
    (hx : mX q x = 0) : mX r x = 0 := by
  rw [mX_eq_sum]
  apply Finset.sum_eq_zero
  intro y _
  have hqxy : q (x, y) = 0 := by
    apply le_antisymm
    · have hle : q (x, y) ≤ mX q x := by
        rw [mX_eq_sum]
        exact Finset.single_le_sum (fun y _ => hq.nonneg (x, y)) (Finset.mem_univ y)
      simpa [hx] using hle
    · exact hq.nonneg _
  have hnotq : (x, y) ∉ support q := by simp [support, hqxy]
  have hnotr : (x, y) ∉ support r := by simpa [hs] using hnotq
  simpa [support] using hnotr

lemma mX_zero_iff_of_support_eq {q r : α × β → ℝ}
    (hq : IsPMF q) (hr : IsPMF r) (hs : support q = support r) (x : α) :
    mX q x = 0 ↔ mX r x = 0 := by
  exact ⟨mX_zero_of_support_eq hq hs,
    mX_zero_of_support_eq hr hs.symm⟩

lemma mY_zero_of_support_eq {q r : α × β → ℝ}
    (hq : IsPMF q) (hs : support q = support r) {y : β}
    (hy : mY q y = 0) : mY r y = 0 := by
  rw [mY_eq_sum]
  apply Finset.sum_eq_zero
  intro x _
  have hqxy : q (x, y) = 0 := by
    apply le_antisymm
    · have hle : q (x, y) ≤ mY q y := by
        rw [mY_eq_sum]
        exact Finset.single_le_sum (fun x _ => hq.nonneg (x, y)) (Finset.mem_univ x)
      simpa [hy] using hle
    · exact hq.nonneg _
  have hnotq : (x, y) ∉ support q := by simp [support, hqxy]
  have hnotr : (x, y) ∉ support r := by simpa [hs] using hnotq
  simpa [support] using hnotr

lemma mY_zero_iff_of_support_eq {q r : α × β → ℝ}
    (hq : IsPMF q) (hr : IsPMF r) (hs : support q = support r) (y : β) :
    mY q y = 0 ↔ mY r y = 0 := by
  exact ⟨mY_zero_of_support_eq hq hs,
    mY_zero_of_support_eq hr hs.symm⟩

lemma mul_ratio_rpow_one_third_cube {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hzero : b = 0 ↔ a = 0) :
    b * ((a / b) ^ ((1 : ℝ) / 3)) ^ 3 = a := by
  by_cases hb0 : b = 0
  · have ha0 := hzero.mp hb0
    simp [hb0, ha0]
  · have hratio : 0 ≤ a / b := div_nonneg ha hb
    have hcube : ((a / b) ^ ((1 : ℝ) / 3)) ^ 3 = a / b := by
      (convert Real.rpow_inv_natCast_pow hratio (by norm_num : (3 : ℕ) ≠ 0) using 1;
        norm_num)
    rw [hcube]
    field_simp

private lemma ratio_rpow_two_thirds {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((a / b) ^ ((1 : ℝ) / 3)) ^ 2 = (a / b) ^ ((2 : ℝ) / 3) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg ha hb)]
  norm_num

private lemma mul_ratio_rpow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (t : ℝ) :
    b ^ t * (a / b) ^ t = a ^ t := by
  rw [← Real.mul_rpow hb.le (div_nonneg ha hb.le), mul_div_cancel₀ _ hb.ne']

lemma contact_ratio_eq {S : Finset (α × β)} {w q r : α × β → ℝ}
    (hq : IsContact S w q) (hr : IsContact S w r)
    (hqs : support q = S) (hrs : support r = S) :
    ∀ z, r z = q z *
      ((mX r z.1 / mX q z.1) ^ ((1 : ℝ) / 3)) ^ 2 *
      ((mY r z.2 / mY q z.2) ^ ((1 : ℝ) / 3)) ^ 2 := by
  intro z
  by_cases hz : z ∈ S
  · have hqmem : z ∈ support q := by simpa [hqs] using hz
    have hrmem : z ∈ support r := by simpa [hrs] using hz
    have hqne : q z ≠ 0 := by simpa [support] using hqmem
    have hrne : r z ≠ 0 := by simpa [support] using hrmem
    have hqpos : 0 < q z := lt_of_le_of_ne (hq.1.nonneg z) (Ne.symm hqne)
    have hrpos : 0 < r z := lt_of_le_of_ne (hr.1.nonneg z) (Ne.symm hrne)
    have hqxpos : 0 < mX q z.1 := by
      have hle : q z ≤ mX q z.1 := by
        rw [mX_eq_sum]
        exact Finset.single_le_sum (fun y _ => hq.1.nonneg (z.1, y)) (Finset.mem_univ z.2)
      exact lt_of_lt_of_le hqpos hle
    have hqypos : 0 < mY q z.2 := by
      have hle : q z ≤ mY q z.2 := by
        rw [mY_eq_sum]
        exact Finset.single_le_sum (fun x _ => hq.1.nonneg (x, z.2)) (Finset.mem_univ z.1)
      exact lt_of_lt_of_le hqpos hle
    have hrxpos : 0 < mX r z.1 := by
      have hle : r z ≤ mX r z.1 := by
        rw [mX_eq_sum]
        exact Finset.single_le_sum (fun y _ => hr.1.nonneg (z.1, y)) (Finset.mem_univ z.2)
      exact lt_of_lt_of_le hrpos hle
    have hrypos : 0 < mY r z.2 := by
      have hle : r z ≤ mY r z.2 := by
        rw [mY_eq_sum]
        exact Finset.single_le_sum (fun x _ => hr.1.nonneg (x, z.2)) (Finset.mem_univ z.1)
      exact lt_of_lt_of_le hrpos hle
    rw [ratio_rpow_two_thirds hrxpos.le hqxpos.le,
      ratio_rpow_two_thirds hrypos.le hqypos.le]
    calc
      r z = w z * mX r z.1 ^ ((2 : ℝ) / 3) * mY r z.2 ^ ((2 : ℝ) / 3) :=
        hr.2.2 z hz
      _ = (w z * mX q z.1 ^ ((2 : ℝ) / 3) * mY q z.2 ^ ((2 : ℝ) / 3)) *
          (mX r z.1 / mX q z.1) ^ ((2 : ℝ) / 3) *
          (mY r z.2 / mY q z.2) ^ ((2 : ℝ) / 3) := by
        rw [← mul_ratio_rpow hrxpos.le hqxpos ((2 : ℝ) / 3),
          ← mul_ratio_rpow hrypos.le hqypos ((2 : ℝ) / 3)]
        ring
      _ = q z * (mX r z.1 / mX q z.1) ^ ((2 : ℝ) / 3) *
          (mY r z.2 / mY q z.2) ^ ((2 : ℝ) / 3) := by rw [← hq.2.2 z hz]
  · rw [hq.2.1 z hz, hr.2.1 z hz]
    simp

lemma secant_equations {S : Finset (α × β)} {w q r : α × β → ℝ}
    (hq : IsContact S w q) (hr : IsContact S w r)
    (hqs : support q = S) (hrs : support r = S) :
    (∀ x, (∑ y, q (x, y) *
        ((mY r y / mY q y) ^ ((1 : ℝ) / 3)) ^ 2) =
      mX q x * (mX r x / mX q x) ^ ((1 : ℝ) / 3)) ∧
    (∀ y, (∑ x, q (x, y) *
        ((mX r x / mX q x) ^ ((1 : ℝ) / 3)) ^ 2) =
      mY q y * (mY r y / mY q y) ^ ((1 : ℝ) / 3)) := by
  have hsqr : support q = support r := hqs.trans hrs.symm
  have hratio := contact_ratio_eq hq hr hqs hrs
  constructor
  · intro x
    by_cases hqx0 : mX q x = 0
    · have hrx0 := (mX_zero_iff_of_support_eq hq.1 hr.1 hsqr x).mp hqx0
      have hrowzero : ∑ y, q (x, y) *
          ((mY r y / mY q y) ^ ((1 : ℝ) / 3)) ^ 2 = 0 := by
        apply Finset.sum_eq_zero
        intro y _
        have hqxy : q (x, y) = 0 := by
          apply le_antisymm
          · have hle : q (x, y) ≤ mX q x := by
              rw [mX_eq_sum]
              exact Finset.single_le_sum (fun y _ => hq.1.nonneg (x, y)) (Finset.mem_univ y)
            simpa [hqx0] using hle
          · exact hq.1.nonneg _
        simp [hqxy]
      rw [hrowzero, hqx0, hrx0]
      simp
    · have hqxpos : 0 < mX q x :=
        lt_of_le_of_ne ((isPMF_push hq.1).nonneg x) (Ne.symm hqx0)
      have hrx0iff := mX_zero_iff_of_support_eq hq.1 hr.1 hsqr x
      have hrxne : mX r x ≠ 0 := fun h => hqx0 (hrx0iff.mpr h)
      have hrxpos : 0 < mX r x :=
        lt_of_le_of_ne ((isPMF_push hr.1).nonneg x) (Ne.symm hrxne)
      let F : ℝ := (mX r x / mX q x) ^ ((1 : ℝ) / 3)
      have hFpos : 0 < F := Real.rpow_pos_of_pos (div_pos hrxpos hqxpos) _
      have hrow : mX r x = F ^ 2 * (∑ y, q (x, y) *
          ((mY r y / mY q y) ^ ((1 : ℝ) / 3)) ^ 2) := by
        rw [mX_eq_sum]
        calc
          ∑ y, r (x, y) = ∑ y, q (x, y) * F ^ 2 *
              ((mY r y / mY q y) ^ ((1 : ℝ) / 3)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro y _
            simpa [F] using hratio (x, y)
          _ = F ^ 2 * (∑ y, q (x, y) *
              ((mY r y / mY q y) ^ ((1 : ℝ) / 3)) ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _
            ring
      have hcube : mX q x * F ^ 3 = mX r x := by
        dsimp [F]
        exact mul_ratio_rpow_one_third_cube hrxpos.le hqxpos.le hrx0iff
      apply mul_left_cancel₀ (pow_ne_zero 2 hFpos.ne')
      calc
        F ^ 2 * (∑ y, q (x, y) *
            ((mY r y / mY q y) ^ ((1 : ℝ) / 3)) ^ 2) = mX r x := hrow.symm
        _ = mX q x * F ^ 3 := hcube.symm
        _ = F ^ 2 * (mX q x * (mX r x / mX q x) ^ ((1 : ℝ) / 3)) := by
          dsimp [F]
          ring
  · intro y
    by_cases hqy0 : mY q y = 0
    · have hry0 := (mY_zero_iff_of_support_eq hq.1 hr.1 hsqr y).mp hqy0
      have hcolzero : ∑ x, q (x, y) *
          ((mX r x / mX q x) ^ ((1 : ℝ) / 3)) ^ 2 = 0 := by
        apply Finset.sum_eq_zero
        intro x _
        have hqxy : q (x, y) = 0 := by
          apply le_antisymm
          · have hle : q (x, y) ≤ mY q y := by
              rw [mY_eq_sum]
              exact Finset.single_le_sum (fun x _ => hq.1.nonneg (x, y)) (Finset.mem_univ x)
            simpa [hqy0] using hle
          · exact hq.1.nonneg _
        simp [hqxy]
      rw [hcolzero, hqy0, hry0]
      simp
    · have hqypos : 0 < mY q y :=
        lt_of_le_of_ne ((isPMF_push hq.1).nonneg y) (Ne.symm hqy0)
      have hry0iff := mY_zero_iff_of_support_eq hq.1 hr.1 hsqr y
      have hryne : mY r y ≠ 0 := fun h => hqy0 (hry0iff.mpr h)
      have hrypos : 0 < mY r y :=
        lt_of_le_of_ne ((isPMF_push hr.1).nonneg y) (Ne.symm hryne)
      let G : ℝ := (mY r y / mY q y) ^ ((1 : ℝ) / 3)
      have hGpos : 0 < G := Real.rpow_pos_of_pos (div_pos hrypos hqypos) _
      have hcol : mY r y = G ^ 2 * (∑ x, q (x, y) *
          ((mX r x / mX q x) ^ ((1 : ℝ) / 3)) ^ 2) := by
        rw [mY_eq_sum]
        calc
          ∑ x, r (x, y) = ∑ x, q (x, y) *
              ((mX r x / mX q x) ^ ((1 : ℝ) / 3)) ^ 2 * G ^ 2 := by
            apply Finset.sum_congr rfl
            intro x _
            simpa [G] using hratio (x, y)
          _ = G ^ 2 * (∑ x, q (x, y) *
              ((mX r x / mX q x) ^ ((1 : ℝ) / 3)) ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring
      have hcube : mY q y * G ^ 3 = mY r y := by
        dsimp [G]
        exact mul_ratio_rpow_one_third_cube hrypos.le hqypos.le hry0iff
      apply mul_left_cancel₀ (pow_ne_zero 2 hGpos.ne')
      calc
        G ^ 2 * (∑ x, q (x, y) *
            ((mX r x / mX q x) ^ ((1 : ℝ) / 3)) ^ 2) = mY r y := hcol.symm
        _ = mY q y * G ^ 3 := hcube.symm
        _ = G ^ 2 * (mY q y * (mY r y / mY q y) ^ ((1 : ℝ) / 3)) := by
          dsimp [G]
          ring

/-- The `X`-marginal cube-root secant from `q` to `r`. -/
noncomputable def contactSecantX (q r : α × β → ℝ) (x : α) : ℝ :=
  (mX r x / mX q x) ^ ((1 : ℝ) / 3) - 1

/-- The `Y`-marginal cube-root secant from `q` to `r`. -/
noncomputable def contactSecantY (q r : α × β → ℝ) (y : β) : ℝ :=
  (mY r y / mY q y) ^ ((1 : ℝ) / 3) - 1

private lemma secant_expanded_equations {S : Finset (α × β)}
    {w q r : α × β → ℝ} (hq : IsContact S w q) (hr : IsContact S w r)
    (hqs : support q = S) (hrs : support r = S) :
    (∀ x, mX q x * contactSecantX q r x =
      2 * (∑ y, q (x, y) *
        contactSecantY q r y) +
      ∑ y, q (x, y) *
        contactSecantY q r y ^ 2) ∧
    (∀ y, mY q y * contactSecantY q r y =
      2 * (∑ x, q (x, y) *
        contactSecantX q r x) +
      ∑ x, q (x, y) *
        contactSecantX q r x ^ 2) := by
  unfold contactSecantX contactSecantY
  have hsec := secant_equations hq hr hqs hrs
  constructor
  · intro x
    calc
      mX q x * ((mX r x / mX q x) ^ ((1 : ℝ) / 3) - 1) =
          (∑ y, q (x, y) *
            ((mY r y / mY q y) ^ ((1 : ℝ) / 3)) ^ 2) - mX q x := by
        rw [hsec.1 x]
        ring
      _ = 2 * (∑ y, q (x, y) *
            ((mY r y / mY q y) ^ ((1 : ℝ) / 3) - 1)) +
          ∑ y, q (x, y) *
            ((mY r y / mY q y) ^ ((1 : ℝ) / 3) - 1) ^ 2 := by
        rw [mX_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
          ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro y _
        ring
  · intro y
    calc
      mY q y * ((mY r y / mY q y) ^ ((1 : ℝ) / 3) - 1) =
          (∑ x, q (x, y) *
            ((mX r x / mX q x) ^ ((1 : ℝ) / 3)) ^ 2) - mY q y := by
        rw [hsec.2 y]
        ring
      _ = 2 * (∑ x, q (x, y) *
            ((mX r x / mX q x) ^ ((1 : ℝ) / 3) - 1)) +
          ∑ x, q (x, y) *
            ((mX r x / mX q x) ^ ((1 : ℝ) / 3) - 1) ^ 2 := by
        rw [mY_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
          ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring

/-! ## Improved Hellinger floor

The historical TV/clipping argument above remains available.  The improved
proof uses squared Hellinger distance, exact secant moments, and the same HGR
singular-pair and contact-hypercontractivity API.
-/

/-! ### L² secant geometry for two contacts -/

/-- Exact marginal-mean identities forced by the two contact equations. -/
theorem contactSecant_mean_identities
    {S : Finset (α × β)} {w q r : α × β → ℝ}
    (hq : IsContact S w q) (hr : IsContact S w r)
    (hqs : support q = S) (hrs : support r = S) :
    (∑ x, mX q x * contactSecantX q r x) =
        -(2 * (∑ x, mX q x * contactSecantX q r x ^ 2) +
          (∑ y, mY q y * contactSecantY q r y ^ 2)) / 3 ∧
    (∑ y, mY q y * contactSecantY q r y) =
        -((∑ x, mX q x * contactSecantX q r x ^ 2) +
          2 * (∑ y, mY q y * contactSecantY q r y ^ 2)) / 3 := by
  let f : α → ℝ := contactSecantX q r
  let g : β → ℝ := contactSecantY q r
  let A : ℝ := ∑ x, mX q x * f x ^ 2
  let B : ℝ := ∑ y, mY q y * g y ^ 2
  let μf : ℝ := ∑ x, mX q x * f x
  let μg : ℝ := ∑ y, mY q y * g y
  have hsec := secant_expanded_equations hq hr hqs hrs
  have hmeanf : μf = 2 * μg + B := by
    calc
      μf = ∑ x, mX q x * f x := rfl
      _ = ∑ x, (2 * (∑ y, q (x, y) * g y) +
          ∑ y, q (x, y) * g y ^ 2) := by
        apply Finset.sum_congr rfl
        intro x _
        exact hsec.1 x
      _ = 2 * (∑ z, q z * g z.2) + ∑ z, q z * g z.2 ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum,
          Fintype.sum_prod_type, Fintype.sum_prod_type]
      _ = 2 * μg + B := by
        rw [← sum_push_mul Prod.snd q g,
          ← sum_push_mul Prod.snd q (fun y => g y ^ 2)]
  have hmeang : μg = 2 * μf + A := by
    have hfirst : (∑ y, ∑ x, q (x, y) * f x) =
        ∑ z, q z * f z.1 := by
      calc
        (∑ y, ∑ x, q (x, y) * f x) =
            ∑ x, ∑ y, q (x, y) * f x := Finset.sum_comm
        _ = ∑ z, q z * f z.1 := by rw [Fintype.sum_prod_type]
    have hsecond : (∑ y, ∑ x, q (x, y) * f x ^ 2) =
        ∑ z, q z * f z.1 ^ 2 := by
      calc
        (∑ y, ∑ x, q (x, y) * f x ^ 2) =
            ∑ x, ∑ y, q (x, y) * f x ^ 2 := Finset.sum_comm
        _ = ∑ z, q z * f z.1 ^ 2 := by rw [Fintype.sum_prod_type]
    calc
      μg = ∑ y, mY q y * g y := rfl
      _ = ∑ y, (2 * (∑ x, q (x, y) * f x) +
          ∑ x, q (x, y) * f x ^ 2) := by
        apply Finset.sum_congr rfl
        intro y _
        exact hsec.2 y
      _ = 2 * (∑ z, q z * f z.1) + ∑ z, q z * f z.1 ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hfirst, hsecond]
      _ = 2 * μf + A := by
        rw [← sum_push_mul Prod.fst q f,
          ← sum_push_mul Prod.fst q (fun x => f x ^ 2)]
  constructor <;>
    dsimp [f, g, A, B, μf, μg] at hmeanf hmeang ⊢ <;>
    linarith

end stoch_to_det
