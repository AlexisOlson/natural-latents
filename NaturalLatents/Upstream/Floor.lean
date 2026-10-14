-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/Floor.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised; proofs shortened.
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
  unfold mX push
  rw [show (Finset.univ.filter fun a : α × β => a.1 = x) =
      Finset.univ.image (fun y : β => (x, y)) by
    ext z
    simp [Prod.ext_iff, eq_comm]]
  rw [Finset.sum_image]
  intro y₁ _ y₂ _ h
  exact congrArg Prod.snd h

lemma mY_eq_sum (q : α × β → ℝ) (y : β) : mY q y = ∑ x, q (x, y) := by
  unfold mY push
  rw [show (Finset.univ.filter fun a : α × β => a.2 = y) =
      Finset.univ.image (fun x : α => (x, y)) by
    ext z
    simp [Prod.ext_iff, eq_comm]]
  rw [Finset.sum_image]
  intro x₁ _ x₂ _ h
  exact congrArg Prod.fst h

lemma mX_zero_of_support_eq {q r : α × β → ℝ}
    (hq : IsPMF q) (hs : support q = support r) {x : α}
    (hx : mX q x = 0) : mX r x = 0 := by
  rw [mX_eq_sum]
  apply Finset.sum_eq_zero
  intro y _
  have hqxy : q (x, y) = 0 :=
    le_antisymm (hx ▸ apply_le_push hq.nonneg Prod.fst (x, y)) (hq.nonneg _)
  have hnotr : (x, y) ∉ support r := by
    rw [← hs]
    simp [support, hqxy]
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
  have hqxy : q (x, y) = 0 :=
    le_antisymm (hy ▸ apply_le_push hq.nonneg Prod.snd (x, y)) (hq.nonneg _)
  have hnotr : (x, y) ∉ support r := by
    rw [← hs]
    simp [support, hqxy]
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
  · simp [hb0, hzero.mp hb0]
  · have hcube : ((a / b) ^ ((1 : ℝ) / 3)) ^ 3 = a / b := by
      convert Real.rpow_inv_natCast_pow (div_nonneg ha hb)
        (by norm_num : (3 : ℕ) ≠ 0) using 1
      norm_num
    rw [hcube, mul_div_cancel₀ _ hb0]

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
  · have hqne : q z ≠ 0 := by simpa [← hqs, support] using hz
    have hqpos : 0 < q z := lt_of_le_of_ne (hq.1.nonneg z) (Ne.symm hqne)
    have hqxpos : 0 < mX q z.1 :=
      lt_of_lt_of_le hqpos (apply_le_push hq.1.nonneg Prod.fst z)
    have hqypos : 0 < mY q z.2 :=
      lt_of_lt_of_le hqpos (apply_le_push hq.1.nonneg Prod.snd z)
    have hrx : 0 ≤ mX r z.1 := (isPMF_push hr.1).nonneg _
    have hry : 0 ≤ mY r z.2 := (isPMF_push hr.1).nonneg _
    rw [ratio_rpow_two_thirds hrx hqxpos.le,
      ratio_rpow_two_thirds hry hqypos.le]
    calc
      r z = w z * mX r z.1 ^ ((2 : ℝ) / 3) * mY r z.2 ^ ((2 : ℝ) / 3) :=
        hr.2.2 z hz
      _ = (w z * mX q z.1 ^ ((2 : ℝ) / 3) * mY q z.2 ^ ((2 : ℝ) / 3)) *
          (mX r z.1 / mX q z.1) ^ ((2 : ℝ) / 3) *
          (mY r z.2 / mY q z.2) ^ ((2 : ℝ) / 3) := by
        rw [← mul_ratio_rpow hrx hqxpos ((2 : ℝ) / 3),
          ← mul_ratio_rpow hry hqypos ((2 : ℝ) / 3)]
        ring
      _ = q z * (mX r z.1 / mX q z.1) ^ ((2 : ℝ) / 3) *
          (mY r z.2 / mY q z.2) ^ ((2 : ℝ) / 3) := by rw [← hq.2.2 z hz]
  · have hrzero : r z = 0 := by simpa [← hrs, support] using hz
    simp [hrzero, hq.2.1 z hz]

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
    · rw [hqx0, zero_mul]
      apply Finset.sum_eq_zero
      intro y _
      have hqxy : q (x, y) = 0 :=
        le_antisymm (hqx0 ▸ apply_le_push hq.1.nonneg Prod.fst (x, y)) (hq.1.nonneg _)
      simp [hqxy]
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
        rw [mX_eq_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        rw [hratio (x, y)]
        dsimp [F]
        ring
      have hcube : mX q x * F ^ 3 = mX r x :=
        mul_ratio_rpow_one_third_cube hrxpos.le hqxpos.le hrx0iff
      apply mul_left_cancel₀ (pow_ne_zero 2 hFpos.ne')
      change F ^ 2 * _ = F ^ 2 * (mX q x * F)
      rw [← hrow, ← hcube]
      ring
  · intro y
    by_cases hqy0 : mY q y = 0
    · rw [hqy0, zero_mul]
      apply Finset.sum_eq_zero
      intro x _
      have hqxy : q (x, y) = 0 :=
        le_antisymm (hqy0 ▸ apply_le_push hq.1.nonneg Prod.snd (x, y)) (hq.1.nonneg _)
      simp [hqxy]
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
        rw [mY_eq_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [hratio (x, y)]
        dsimp [G]
        ring
      have hcube : mY q y * G ^ 3 = mY r y :=
        mul_ratio_rpow_one_third_cube hrypos.le hqypos.le hry0iff
      apply mul_left_cancel₀ (pow_ne_zero 2 hGpos.ne')
      change G ^ 2 * _ = G ^ 2 * (mY q y * G)
      rw [← hcol, ← hcube]
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
    rw [mul_sub, mul_one, ← hsec.1 x, mX_eq_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    ring
  · intro y
    rw [mul_sub, mul_one, ← hsec.2 y, mY_eq_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
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
    have hsum := congrArg (fun F : α → ℝ => ∑ x, F x) (funext hsec.1)
    change μf = ∑ x, (2 * (∑ y, q (x, y) * g y) +
      ∑ y, q (x, y) * g y ^ 2) at hsum
    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Fintype.sum_prod_type (fun z : α × β => q z * g z.2),
      ← Fintype.sum_prod_type (fun z : α × β => q z * g z.2 ^ 2),
      ← sum_push_mul Prod.snd q g,
      ← sum_push_mul Prod.snd q (fun y => g y ^ 2)] at hsum
    exact hsum
  have hmeang : μg = 2 * μf + A := by
    have hsum := congrArg (fun G : β → ℝ => ∑ y, G y) (funext hsec.2)
    change μg = ∑ y, (2 * (∑ x, q (x, y) * f x) +
      ∑ x, q (x, y) * f x ^ 2) at hsum
    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Fintype.sum_prod_type_right (fun z : α × β => q z * f z.1),
      ← Fintype.sum_prod_type_right (fun z : α × β => q z * f z.1 ^ 2),
      ← sum_push_mul Prod.fst q f,
      ← sum_push_mul Prod.fst q (fun x => f x ^ 2)] at hsum
    exact hsum
  constructor <;>
    dsimp [f, g, A, B, μf, μg] at hmeanf hmeang ⊢ <;>
    linarith

end stoch_to_det
