-- Original work by Alexis Olson, Apache-2.0 (see NOTICE), October 2026, first written on an unpublished branch of
-- github.com/AlexisOlson/stochastic-to-deterministic-latents; reorganised for this repository
-- (namespace NaturalLatents.General, declarations renamed, unused material removed).
-- This file builds on and cites the definitions of DLorell/stoch_to_det (Apache-2.0).
import NaturalLatents.General.Definitions

/-!
# Moment relations of two contacts

For two distinct positive contacts `P` and `R` of a common feasible kernel, the cube-root
secants `f = (mX R / mX P)^(1/3)` and `g = (mY R / mY P)^(1/3)` satisfy the relations collected
in `ContactMoments`: the likelihood ratio is `f² g²`, the conditional second moments of one
secant reproduce the other, the cubes have mean one, and the energy identities, the quartic
identity and a Hessian inequality bound `quarticMoment P R` by `separation P R ^ 2 / 2`.

The module builds these from the secant equations of the contact (`stoch_to_det.secant_equations`),
the finite expectation algebra for the quartic, and a Hessian test on affine and cubic
perturbations. The headline is `contact_moments`.

All quantities are dimensionless ratios and expectations; no information units enter.

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

lemma contact_support_eq_of_positiveOn {S : Finset (X × Y)} {w P : Law X Y}
    (hP : stoch_to_det.IsContact S w P) (hpos : PositiveOn S P) :
    stoch_to_det.support P = S := by
  ext z
  simp only [stoch_to_det.support, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hz
    by_contra hnot
    exact hz (hP.2.1 z hnot)
  · intro hz
    exact (hpos z hz).ne'

lemma contact_mX_pos {S : Finset (X × Y)} {w P : Law X Y}
    (hP : stoch_to_det.IsContact S w P) (hpos : PositiveOn S P) {x : X} (hx : x ∈ xSupport S) :
    0 < stoch_to_det.mX P x := by
  obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx
  have hle : P z ≤ stoch_to_det.mX P z.1 := by
    rw [stoch_to_det.mX_eq_sum]
    exact Finset.single_le_sum (fun y _ => hP.1.nonneg (z.1, y)) (Finset.mem_univ z.2)
  simpa only [hzx] using lt_of_lt_of_le (hpos z hz) hle

lemma contact_mY_pos {S : Finset (X × Y)} {w P : Law X Y}
    (hP : stoch_to_det.IsContact S w P) (hpos : PositiveOn S P) {y : Y} (hy : y ∈ ySupport S) :
    0 < stoch_to_det.mY P y := by
  obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hy
  have hle : P z ≤ stoch_to_det.mY P z.2 := by
    rw [stoch_to_det.mY_eq_sum]
    exact Finset.single_le_sum (fun x _ => hP.1.nonneg (x, z.2)) (Finset.mem_univ z.1)
  simpa only [hzy] using lt_of_lt_of_le (hpos z hz) hle

lemma contact_mem_xSupport_of_mX_pos {S : Finset (X × Y)} {w P : Law X Y}
    (hP : stoch_to_det.IsContact S w P) {x : X} (hx : 0 < stoch_to_det.mX P x) : x ∈ xSupport S := by
  rw [stoch_to_det.mX_eq_sum] at hx
  obtain ⟨y, _, hy⟩ := (Finset.sum_pos_iff_of_nonneg (fun y _ => hP.1.nonneg (x, y))).mp hx
  exact Finset.mem_image.mpr ⟨(x, y), by contrapose! hy; exact (hP.2.1 (x, y) hy).le, rfl⟩

lemma contact_mem_ySupport_of_mY_pos {S : Finset (X × Y)} {w P : Law X Y}
    (hP : stoch_to_det.IsContact S w P) {y : Y} (hy : 0 < stoch_to_det.mY P y) : y ∈ ySupport S := by
  rw [stoch_to_det.mY_eq_sum] at hy
  obtain ⟨x, _, hx⟩ := (Finset.sum_pos_iff_of_nonneg (fun x _ => hP.1.nonneg (x, y))).mp hy
  exact Finset.mem_image.mpr ⟨(x, y), by contrapose! hx; exact (hP.2.1 (x, y) hx).le, rfl⟩

lemma contact_rootRatioX_nonneg {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (x : X) : 0 ≤ rootRatioX P R x := by
  rw [rootRatioX_eq_cbrt]
  exact Real.rpow_nonneg (div_nonneg ((stoch_to_det.isPMF_push (f := Prod.fst) hpair.2.2.1.1).nonneg x)
    ((stoch_to_det.isPMF_push (f := Prod.fst) hpair.2.1.1).nonneg x)) _

lemma contact_rootRatioY_nonneg {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (y : Y) : 0 ≤ rootRatioY P R y := by
  rw [rootRatioY_eq_cbrt]
  exact Real.rpow_nonneg (div_nonneg ((stoch_to_det.isPMF_push (f := Prod.snd) hpair.2.2.1.1).nonneg y)
    ((stoch_to_det.isPMF_push (f := Prod.snd) hpair.2.1.1).nonneg y)) _

lemma contact_rootRatioX_pos {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) {x : X} (hx : x ∈ xSupport S) : 0 < rootRatioX P R x := by
  rw [rootRatioX_eq_cbrt]
  exact Real.rpow_pos_of_pos (div_pos (contact_mX_pos hpair.2.2.1 hpair.2.2.2.2.1 hx)
    (contact_mX_pos hpair.2.1 hpair.2.2.2.1 hx)) _

lemma contact_rootRatioY_pos {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) {y : Y} (hy : y ∈ ySupport S) : 0 < rootRatioY P R y := by
  rw [rootRatioY_eq_cbrt]
  exact Real.rpow_pos_of_pos (div_pos (contact_mY_pos hpair.2.2.1 hpair.2.2.2.2.1 hy)
    (contact_mY_pos hpair.2.1 hpair.2.2.2.1 hy)) _
lemma contact_ratio_mul {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (z : X × Y) :
    R z = P z * (rootRatioX P R z.1)^2 * (rootRatioY P R z.2)^2 := by
  simpa only [rootRatioX_eq_cbrt, rootRatioY_eq_cbrt] using stoch_to_det.contact_ratio_eq hpair.2.1 hpair.2.2.1
    (contact_support_eq_of_positiveOn hpair.2.1 hpair.2.2.2.1)
    (contact_support_eq_of_positiveOn hpair.2.2.1 hpair.2.2.2.2.1) z


lemma contact_cond_rootRatioY_square_mul {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (x : X) :
    (∑ y, P (x,y) * (rootRatioY P R y)^2) = stoch_to_det.mX P x * rootRatioX P R x := by
  simpa only [rootRatioX_eq_cbrt, rootRatioY_eq_cbrt] using (stoch_to_det.secant_equations hpair.2.1 hpair.2.2.1
    (contact_support_eq_of_positiveOn hpair.2.1 hpair.2.2.2.1)
    (contact_support_eq_of_positiveOn hpair.2.2.1 hpair.2.2.2.2.1)).1 x

lemma contact_cond_rootRatioX_square_mul {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (y : Y) :
    (∑ x, P (x,y) * (rootRatioX P R x)^2) = stoch_to_det.mY P y * rootRatioY P R y := by
  simpa only [rootRatioX_eq_cbrt, rootRatioY_eq_cbrt] using (stoch_to_det.secant_equations hpair.2.1 hpair.2.2.1
    (contact_support_eq_of_positiveOn hpair.2.1 hpair.2.2.2.1)
    (contact_support_eq_of_positiveOn hpair.2.2.1 hpair.2.2.2.2.1)).2 y

lemma contact_cond_rootRatioY_square {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) {x : X} (hx : x ∈ xSupport S) :
    (∑ y, P (x,y) * (rootRatioY P R y)^2) / stoch_to_det.mX P x = rootRatioX P R x := by
  rw [contact_cond_rootRatioY_square_mul hpair x]
  field_simp [(contact_mX_pos hpair.2.1 hpair.2.2.2.1 hx).ne']

lemma contact_cond_rootRatioX_square {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) {y : Y} (hy : y ∈ ySupport S) :
    (∑ x, P (x,y) * (rootRatioX P R x)^2) / stoch_to_det.mY P y = rootRatioY P R y := by
  rw [contact_cond_rootRatioX_square_mul hpair y]
  field_simp [(contact_mY_pos hpair.2.1 hpair.2.2.2.1 hy).ne']

lemma contact_rootRatioX_cube_mul_marginal {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (x : X) :
    stoch_to_det.mX P x * (rootRatioX P R x)^3 = stoch_to_det.mX R x := by
  rw [rootRatioX_eq_cbrt]
  apply stoch_to_det.mul_ratio_rpow_one_third_cube ((stoch_to_det.isPMF_push (f := Prod.fst) hpair.2.2.1.1).nonneg _)
    ((stoch_to_det.isPMF_push (f := Prod.fst) hpair.2.1.1).nonneg _)
  exact stoch_to_det.mX_zero_iff_of_support_eq hpair.2.1.1 hpair.2.2.1.1
    ((contact_support_eq_of_positiveOn hpair.2.1 hpair.2.2.2.1).trans
      (contact_support_eq_of_positiveOn hpair.2.2.1 hpair.2.2.2.2.1).symm) x

lemma contact_rootRatioY_cube_mul_marginal {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) (y : Y) :
    stoch_to_det.mY P y * (rootRatioY P R y)^3 = stoch_to_det.mY R y := by
  rw [rootRatioY_eq_cbrt]
  apply stoch_to_det.mul_ratio_rpow_one_third_cube ((stoch_to_det.isPMF_push (f := Prod.snd) hpair.2.2.1.1).nonneg _)
    ((stoch_to_det.isPMF_push (f := Prod.snd) hpair.2.1.1).nonneg _)
  exact stoch_to_det.mY_zero_iff_of_support_eq hpair.2.1.1 hpair.2.2.1.1
    ((contact_support_eq_of_positiveOn hpair.2.1 hpair.2.2.2.1).trans
      (contact_support_eq_of_positiveOn hpair.2.2.1 hpair.2.2.2.2.1).symm) y

lemma contact_rootRatioX_cube {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) : expect P (fun z => (rootRatioX P R z.1)^3) = 1 := by
  unfold expect
  rw [← stoch_to_det.sum_push_mul Prod.fst P (fun x => (rootRatioX P R x)^3)]
  simp only [contact_rootRatioX_cube_mul_marginal hpair]
  exact (stoch_to_det.isPMF_push (f := Prod.fst) hpair.2.2.1.1).total

lemma contact_rootRatioY_cube {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) : expect P (fun z => (rootRatioY P R z.2)^3) = 1 := by
  unfold expect
  rw [← stoch_to_det.sum_push_mul Prod.snd P (fun x => (rootRatioY P R x)^3)]
  simp only [contact_rootRatioY_cube_mul_marginal hpair]
  exact (stoch_to_det.isPMF_push (f := Prod.snd) hpair.2.2.1.1).total

lemma contact_rootRatioX_square {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) :
    expect P (fun z => (rootRatioX P R z.1)^2) = expect P (fun z => rootRatioY P R z.2) := by
  calc
    expect P (fun z => (rootRatioX P R z.1)^2) = ∑ y, ∑ x, P (x,y) * (rootRatioX P R x)^2 := by
      unfold expect
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = ∑ y, stoch_to_det.mY P y * rootRatioY P R y :=
      Finset.sum_congr rfl (fun y _ => contact_cond_rootRatioX_square_mul hpair y)
    _ = expect P (fun z => rootRatioY P R z.2) := stoch_to_det.sum_push_mul Prod.snd P (rootRatioY P R)

lemma contact_rootRatioY_square {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) :
    expect P (fun z => (rootRatioY P R z.2)^2) = expect P (fun z => rootRatioX P R z.1) := by
  calc
    expect P (fun z => (rootRatioY P R z.2)^2) = ∑ x, ∑ y, P (x,y) * (rootRatioY P R y)^2 := by
      unfold expect
      rw [Fintype.sum_prod_type]
    _ = ∑ x, stoch_to_det.mX P x * rootRatioX P R x :=
      Finset.sum_congr rfl (fun x _ => contact_cond_rootRatioY_square_mul hpair x)
    _ = expect P (fun z => rootRatioX P R z.1) := stoch_to_det.sum_push_mul Prod.fst P (rootRatioX P R)

omit [DecidableEq X] [DecidableEq Y] in
lemma contact_expect_add (P : Law X Y) (F G : X × Y → ℝ) :
    expect P (fun z => F z + G z) = expect P F + expect P G := by
  simp [expect, mul_add, Finset.sum_add_distrib]

omit [DecidableEq X] [DecidableEq Y] in
lemma contact_expect_const {P : Law X Y} (hP : stoch_to_det.IsPMF P) (a : ℝ) :
    expect P (fun _ => a) = a := by
  change (∑ z, P z * a) = a
  rw [← Finset.sum_mul, hP.sum_eq_one, one_mul]

omit [DecidableEq X] [DecidableEq Y] in
lemma contact_expect_nonneg {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F : X × Y → ℝ) (hF : ∀ z, 0 ≤ F z) : 0 ≤ expect P F := by
  exact Finset.sum_nonneg (fun z _ => mul_nonneg (hP.nonneg z) (hF z))

omit [DecidableEq Y] in
lemma contact_expect_fst (P : Law X Y) (F : X → ℝ) :
    expect P (fun z => F z.1) = ∑ x, stoch_to_det.mX P x * F x := by
  exact (stoch_to_det.sum_push_mul Prod.fst P F).symm

omit [DecidableEq X] in
lemma contact_expect_snd (P : Law X Y) (G : Y → ℝ) :
    expect P (fun z => G z.2) = ∑ y, stoch_to_det.mY P y * G y := by
  exact (stoch_to_det.sum_push_mul Prod.snd P G).symm

lemma contact_energy_identities {S : Finset (X × Y)} {w P R : Law X Y}
    (hP : stoch_to_det.IsContact S w P) (hR : stoch_to_det.IsContact S w R)
    (hPs : stoch_to_det.support P = S) (hRs : stoch_to_det.support R = S) :
    expect P (fun z => (stoch_to_det.contactSecantX P R z.1)^2) = 2 * defectX P R - defectY P R ∧
    expect P (fun z => (stoch_to_det.contactSecantY P R z.2)^2) = 2 * defectY P R - defectX P R ∧
    separation P R = expect P (fun z => (stoch_to_det.contactSecantX P R z.1)^2) + expect P (fun z => (stoch_to_det.contactSecantY P R z.2)^2) := by
  have hm := stoch_to_det.contactSecant_mean_identities hP hR hPs hRs
  have hx : expect P (fun z => rootRatioX P R z.1) = expect P (fun z => stoch_to_det.contactSecantX P R z.1) + 1 := by
    change expect P (fun z => stoch_to_det.contactSecantX P R z.1 + 1) = _
    rw [contact_expect_add, contact_expect_const hP.1]
  have hy : expect P (fun z => rootRatioY P R z.2) = expect P (fun z => stoch_to_det.contactSecantY P R z.2) + 1 := by
    change expect P (fun z => stoch_to_det.contactSecantY P R z.2 + 1) = _
    rw [contact_expect_add, contact_expect_const hP.1]
  have hmx : expect P (fun z => stoch_to_det.contactSecantX P R z.1) =
      -(2 * expect P (fun z => (stoch_to_det.contactSecantX P R z.1)^2) + expect P (fun z => (stoch_to_det.contactSecantY P R z.2)^2)) / 3 := by
    rw [contact_expect_fst P (stoch_to_det.contactSecantX P R), contact_expect_fst P (fun x => (stoch_to_det.contactSecantX P R x)^2),
      contact_expect_snd P (fun y => (stoch_to_det.contactSecantY P R y)^2)]
    exact hm.1
  have hmy : expect P (fun z => stoch_to_det.contactSecantY P R z.2) =
      -(expect P (fun z => (stoch_to_det.contactSecantX P R z.1)^2) + 2 * expect P (fun z => (stoch_to_det.contactSecantY P R z.2)^2)) / 3 := by
    rw [contact_expect_snd P (stoch_to_det.contactSecantY P R), contact_expect_fst P (fun x => (stoch_to_det.contactSecantX P R x)^2),
      contact_expect_snd P (fun y => (stoch_to_det.contactSecantY P R y)^2)]
    exact hm.2
  dsimp [defectX, defectY, separation]
  constructor
  · linarith
  constructor <;> linarith

omit [DecidableEq X] [DecidableEq Y] in
lemma contact_weighted_sq_zero {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F : X × Y → ℝ) (hs : expect P (fun z => (F z)^2) = 0)
    {z : X × Y} (hz : 0 < P z) : F z = 0 := by
  have ht : P z * (F z)^2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun a _ => mul_nonneg (hP.nonneg a) (sq_nonneg (F a)))).mp hs z (Finset.mem_univ z)
  exact sq_eq_zero_iff.mp ((mul_eq_zero.mp ht).resolve_left hz.ne')

lemma contact_separation {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R)
    (hratio : ∀ z, R z = P z * (rootRatioX P R z.1)^2 * (rootRatioY P R z.2)^2)
    (he : separation P R = expect P (fun z => (stoch_to_det.contactSecantX P R z.1)^2) + expect P (fun z => (stoch_to_det.contactSecantY P R z.2)^2)) :
    0 < separation P R := by
  have hx := contact_expect_nonneg hpair.2.1.1 (fun z => (stoch_to_det.contactSecantX P R z.1)^2) (fun _ => sq_nonneg _)
  have hy := contact_expect_nonneg hpair.2.1.1 (fun z => (stoch_to_det.contactSecantY P R z.2)^2) (fun _ => sq_nonneg _)
  by_contra hn
  have hs : separation P R = 0 := by linarith
  have hx0 : expect P (fun z => (stoch_to_det.contactSecantX P R z.1)^2) = 0 := by linarith
  have hy0 : expect P (fun z => (stoch_to_det.contactSecantY P R z.2)^2) = 0 := by linarith
  apply hpair.2.2.2.2.2
  funext z
  by_cases hz : z ∈ S
  · have hPz := hpair.2.2.2.1 z hz
    have hUz := contact_weighted_sq_zero hpair.2.1.1 (fun z => stoch_to_det.contactSecantX P R z.1) hx0 hPz
    have hVz := contact_weighted_sq_zero hpair.2.1.1 (fun z => stoch_to_det.contactSecantY P R z.2) hy0 hPz
    rw [hratio z]
    simp [rootRatioX, rootRatioY, hUz, hVz]
  · rw [hpair.2.1.2.1 z hz, hpair.2.2.1.2.1 z hz]

lemma contact_upper_separation {P R : Law X Y} (hP : stoch_to_det.IsPMF P)
    (hf : ∀ x, 0 ≤ rootRatioX P R x) (hg : ∀ y, 0 ≤ rootRatioY P R y)
    (hfp : ∀ z, 0 < P z → 0 < rootRatioX P R z.1)
    (hgp : ∀ z, 0 < P z → 0 < rootRatioY P R z.2) : separation P R < 2 := by
  have ht : ∑ z, P z = 1 := hP.total
  obtain ⟨z, _, hz⟩ : ∃ z ∈ (Finset.univ : Finset (X × Y)), 0 < P z := by
    apply (Finset.sum_pos_iff_of_nonneg (fun z _ => hP.nonneg z)).mp
    rw [ht]
    norm_num
  have hxf : 0 < expect P (fun z => rootRatioX P R z.1) := by
    apply Finset.sum_pos'
    · intro z _
      exact mul_nonneg (hP.nonneg z) (hf z.1)
    · exact ⟨z, Finset.mem_univ z, mul_pos hz (hfp z hz)⟩
  have hyg : 0 < expect P (fun z => rootRatioY P R z.2) := by
    apply Finset.sum_pos'
    · intro z _
      exact mul_nonneg (hP.nonneg z) (hg z.2)
    · exact ⟨z, Finset.mem_univ z, mul_pos hz (hgp z hz)⟩
  dsimp [separation, defectX, defectY]
  linarith

/- Finite expectation algebra used only by the contact quartic. -/
omit [DecidableEq X] [DecidableEq Y] in
lemma contact_q_expect_sub (P : Law X Y) (F G : X × Y → ℝ) :
    expect P (fun z => F z - G z) = expect P F - expect P G := by
  simp only [expect, mul_sub, Finset.sum_sub_distrib]

omit [DecidableEq X] [DecidableEq Y] in
lemma contact_q_expect_scale (P : Law X Y) (a : ℝ) (F : X × Y → ℝ) :
    expect P (fun z => a * F z) = a * expect P F := by
  simp only [expect, Finset.mul_sum, mul_left_comm]

omit [DecidableEq X] [DecidableEq Y] in
lemma contact_q_expect_shift_prod {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F G : X × Y → ℝ) (a b : ℝ) :
    expect P (fun z => (F z + a) * (G z + b)) =
      expect P (fun z => F z * G z) + a * expect P G + b * expect P F + a * b := by
  conv_rhs => rw [← contact_expect_const hP (a * b)]
  simp only [expect, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  ring

omit [DecidableEq X] [DecidableEq Y] in
lemma contact_q_expect_shift_sq {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (F : X × Y → ℝ) (a : ℝ) :
    expect P (fun z => (F z + a)^2) = expect P (fun z => (F z)^2) +
      2 * a * expect P F + a^2 := by
  simp only [pow_two, contact_q_expect_shift_prod hP]
  ring

lemma contact_q_mixed_moments {P R : Law X Y}
    (hcond_g2 : ∀ x, (∑ y, P (x,y) * (rootRatioY P R y)^2) =
      stoch_to_det.mX P x * rootRatioX P R x)
    (hcond_f2 : ∀ y, (∑ x, P (x,y) * (rootRatioX P R x)^2) =
      stoch_to_det.mY P y * rootRatioY P R y) :
    expect P (fun z => (rootRatioX P R z.1)^2 * rootRatioY P R z.2) =
      expect P (fun z => (rootRatioY P R z.2)^2) ∧
    expect P (fun z => rootRatioX P R z.1 * (rootRatioY P R z.2)^2) =
      expect P (fun z => (rootRatioX P R z.1)^2) := by
  constructor
  · rw [contact_expect_snd P (fun y => (rootRatioY P R y)^2)]
    unfold expect
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, hcond_f2]
    ring
  · rw [contact_expect_fst P (fun x => (rootRatioX P R x)^2)]
    unfold expect
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    simp_rw [show ∀ y, P (x,y) * (rootRatioX P R x * (rootRatioY P R y)^2) =
      (P (x,y) * (rootRatioY P R y)^2) * rootRatioX P R x by intro y; ring]
    rw [← Finset.sum_mul, hcond_g2]
    ring

lemma contact_quartic_identity {P R : Law X Y} (hP : stoch_to_det.IsPMF P)
    (hR : stoch_to_det.IsPMF R)
    (hratio : ∀ z, R z = P z * (rootRatioX P R z.1)^2 * (rootRatioY P R z.2)^2)
    (hcond_g2 : ∀ x, (∑ y, P (x,y) * (rootRatioY P R y)^2) =
      stoch_to_det.mX P x * rootRatioX P R x)
    (hcond_f2 : ∀ y, (∑ x, P (x,y) * (rootRatioX P R x)^2) =
      stoch_to_det.mY P y * rootRatioY P R y)
    (hf2 : expect P (fun z => (rootRatioX P R z.1)^2) = expect P (fun z => rootRatioY P R z.2))
    (hg2 : expect P (fun z => (rootRatioY P R z.2)^2) = expect P (fun z => rootRatioX P R z.1)) :
    quarticMoment P R = 4 * expect P (fun z => stoch_to_det.contactSecantX P R z.1 * stoch_to_det.contactSecantY P R z.2) - separation P R := by
  have hm := contact_q_mixed_moments hcond_g2 hcond_f2
  have h22 : expect P (fun z => (rootRatioX P R z.1)^2 * (rootRatioY P R z.2)^2) = 1 := by
    unfold expect
    simp_rw [← mul_assoc, ← hratio]
    exact hR.total
  have hf : ∀ x, stoch_to_det.contactSecantX P R x = rootRatioX P R x - 1 := by intro x; simp [rootRatioX]
  have hg : ∀ y, stoch_to_det.contactSecantY P R y = rootRatioY P R y - 1 := by intro y; simp [rootRatioY]
  have hj : quarticMoment P R =
      expect P (fun z => (rootRatioX P R z.1)^2 * (rootRatioY P R z.2)^2) -
      2 * expect P (fun z => (rootRatioX P R z.1)^2 * rootRatioY P R z.2) -
      2 * expect P (fun z => rootRatioX P R z.1 * (rootRatioY P R z.2)^2) +
      expect P (fun z => (rootRatioX P R z.1)^2) + expect P (fun z => (rootRatioY P R z.2)^2) +
      4 * expect P (fun z => rootRatioX P R z.1 * rootRatioY P R z.2) -
      2 * expect P (fun z => rootRatioX P R z.1) - 2 * expect P (fun z => rootRatioY P R z.2) + 1 := by
    calc
      _ = expect P (fun z => (rootRatioX P R z.1)^2 * (rootRatioY P R z.2)^2 -
          2 * ((rootRatioX P R z.1)^2 * rootRatioY P R z.2) -
          2 * (rootRatioX P R z.1 * (rootRatioY P R z.2)^2) + (rootRatioX P R z.1)^2 +
          (rootRatioY P R z.2)^2 + 4 * (rootRatioX P R z.1 * rootRatioY P R z.2) -
          2 * rootRatioX P R z.1 - 2 * rootRatioY P R z.2 + 1) := by
        unfold quarticMoment
        congr 1
        funext z
        rw [hf, hg]
        ring
      _ = _ := by
        simp only [contact_expect_add, contact_q_expect_sub, contact_q_expect_scale, contact_expect_const hP]
  have huv := contact_q_expect_shift_prod hP
    (fun z => rootRatioX P R z.1) (fun z => rootRatioY P R z.2) (-1) (-1)
  simp only [← sub_eq_add_neg, ← hf, ← hg] at huv
  rw [hm.1, hm.2, h22, hf2, hg2] at hj
  rw [hj]
  unfold separation defectX defectY
  linarith [huv]

lemma contact_quarticMoment_bound {P R : Law X Y} (hP : stoch_to_det.IsPMF P)
    (hU2 : expect P (fun z => (stoch_to_det.contactSecantX P R z.1)^2) = 2 * defectX P R - defectY P R)
    (hV2 : expect P (fun z => (stoch_to_det.contactSecantY P R z.2)^2) = 2 * defectY P R - defectX P R)
    (hquartic : quarticMoment P R = 4 * expect P (fun z => stoch_to_det.contactSecantX P R z.1 * stoch_to_det.contactSecantY P R z.2) - separation P R)
    (hhessian : ∀ (F : X → ℝ) (G : Y → ℝ),
      expect P (fun z => F z.1) = 0 → expect P (fun z => G z.2) = 0 →
      4 * expect P (fun z => F z.1 * G z.2) ≤ expect P (fun z => (F z.1)^2) +
        expect P (fun z => (G z.2)^2)) :
    quarticMoment P R ≤ 6 * defectX P R * defectY P R - (separation P R)^2 := by
  have hU : expect P (fun z => stoch_to_det.contactSecantX P R z.1) = -defectX P R := by
    simp only [defectX, rootRatioX, contact_expect_add, contact_expect_const hP]
    ring
  have hV : expect P (fun z => stoch_to_det.contactSecantY P R z.2) = -defectY P R := by
    simp only [defectY, rootRatioY, contact_expect_add, contact_expect_const hP]
    ring
  have hF : expect P (fun z => stoch_to_det.contactSecantX P R z.1 + defectX P R) = 0 := by
    rw [contact_expect_add, contact_expect_const hP, hU]
    ring
  have hG : expect P (fun z => stoch_to_det.contactSecantY P R z.2 + defectY P R) = 0 := by
    rw [contact_expect_add, contact_expect_const hP, hV]
    ring
  have hh := hhessian (fun x => stoch_to_det.contactSecantX P R x + defectX P R) (fun y => stoch_to_det.contactSecantY P R y + defectY P R) hF hG
  rw [contact_q_expect_shift_prod hP, contact_q_expect_shift_sq hP, contact_q_expect_shift_sq hP,
    hU, hV, hU2, hV2] at hh
  have hs : separation P R = defectX P R + defectY P R := rfl
  rw [hs] at hquartic ⊢
  nlinarith [hquartic]

lemma contact_scalar_bound (P R : Law X Y) :
    6 * defectX P R * defectY P R - (separation P R)^2 ≤ (separation P R)^2 / 2 := by
  unfold separation
  nlinarith [sq_nonneg (defectX P R - defectY P R)]

lemma contact_hessian_affine_pos {ι : Type*} [Fintype ι] (F : ι → ℝ) :
    ∀ᶠ t : ℝ in nhds 0, ∀ x, 0 < 1 + t * F x := by
  rw [Filter.eventually_all]
  intro x
  have hc : ContinuousAt (fun t : ℝ => 1 + t * F x) 0 := by fun_prop
  exact hc.tendsto.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1 + 0 * F x))

omit [DecidableEq X] [DecidableEq Y] in
lemma contact_hessian_expect_cubic {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (H : X × Y → ℝ) (hH : expect P H = 0) (t : ℝ) :
    expect P (fun z => (1 + t * H z)^3) =
      1 + t^2 * (3 * expect P (fun z => (H z)^2) + t * expect P (fun z => (H z)^3)) := by
  have hmass : (∑ z, P z) = 1 := by simpa [stoch_to_det.mass] using hP.total
  calc
    expect P (fun z => (1 + t * H z)^3) =
        (∑ z, P z) + 3 * t * expect P H +
          3 * t^2 * expect P (fun z => (H z)^2) + t^3 * expect P (fun z => (H z)^3) := by
      unfold expect
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := by rw [hmass, hH]; ring

omit [DecidableEq X] [DecidableEq Y] in
lemma contact_hessian_expect_biquad {P : Law X Y} (hP : stoch_to_det.IsPMF P)
    (H K : X × Y → ℝ) (hH : expect P H = 0) (hK : expect P K = 0) (t : ℝ) :
    expect P (fun z => (1 + t * H z)^2 * (1 + t * K z)^2) =
      1 + t^2 * (expect P (fun z => (H z)^2) + expect P (fun z => (K z)^2) +
        4 * expect P (fun z => H z * K z) +
        2 * t * (expect P (fun z => (H z)^2 * K z) + expect P (fun z => H z * (K z)^2)) +
        t^2 * expect P (fun z => (H z)^2 * (K z)^2)) := by
  have hmass : (∑ z, P z) = 1 := by simpa [stoch_to_det.mass] using hP.total
  calc
    expect P (fun z => (1 + t * H z)^2 * (1 + t * K z)^2) =
        (∑ z, P z) + 2 * t * expect P H + 2 * t * expect P K +
        t^2 * expect P (fun z => (H z)^2) + t^2 * expect P (fun z => (K z)^2) +
        4 * t^2 * expect P (fun z => H z * K z) +
        2 * t^3 * expect P (fun z => (H z)^2 * K z) +
        2 * t^3 * expect P (fun z => H z * (K z)^2) +
        t^4 * expect P (fun z => (H z)^2 * (K z)^2) := by
      unfold expect
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := by rw [hmass, hH, hK]; ring

lemma contact_hessian_cube_test {S : Finset (X × Y)} {w P : Law X Y}
    (hw : stoch_to_det.Feasible S w) (hP : stoch_to_det.IsContact S w P)
    (F : X → ℝ) (G : Y → ℝ) (t : ℝ)
    (hF : ∀ x, 0 ≤ 1 + t * F x) (hG : ∀ y, 0 ≤ 1 + t * G y) :
    (expect P (fun z => (1 + t * F z.1)^2 * (1 + t * G z.2)^2))^3 ≤
      (expect P (fun z => (1 + t * F z.1)^3))^2 *
      (expect P (fun z => (1 + t * G z.2)^3))^2 := by
  have hFpow (x : X) : ((1 + t * F x)^2) ^ ((3 : ℝ) / 2) = (1 + t * F x)^3 := by
    rw [← Real.rpow_natCast_mul (hF x) 2 ((3 : ℝ) / 2)]
    norm_num
  have hGpow (y : Y) : ((1 + t * G y)^2) ^ ((3 : ℝ) / 2) = (1 + t * G y)^3 := by
    rw [← Real.rpow_natCast_mul (hG y) 2 ((3 : ℝ) / 2)]
    norm_num
  have hhc := stoch_to_det.contact_hypercontractive hw hP
    (f := fun x => (1 + t * F x)^2) (g := fun y => (1 + t * G y)^2)
    (fun x => sq_nonneg _) (fun y => sq_nonneg _)
  simp only [hFpow, hGpow] at hhc
  have hleft : (∑ z ∈ S, P z * (1 + t * F z.1)^2 * (1 + t * G z.2)^2) =
      expect P (fun z => (1 + t * F z.1)^2 * (1 + t * G z.2)^2) := by
    unfold expect
    simp only [mul_assoc]
    apply Finset.sum_subset (Finset.subset_univ S)
    intro z _ hz
    simp [hP.2.1 z hz]
  have hsumF : (∑ x, stoch_to_det.mX P x * (1 + t * F x)^3) =
      expect P (fun z => (1 + t * F z.1)^3) :=
    stoch_to_det.sum_push_mul Prod.fst P (fun x => (1 + t * F x)^3)
  have hsumG : (∑ y, stoch_to_det.mY P y * (1 + t * G y)^3) =
      expect P (fun z => (1 + t * G z.2)^3) :=
    stoch_to_det.sum_push_mul Prod.snd P (fun y => (1 + t * G y)^3)
  rw [hleft, hsumF, hsumG] at hhc
  have hA : 0 ≤ expect P (fun z => (1 + t * F z.1)^3) :=
    Finset.sum_nonneg (fun z _ => mul_nonneg (hP.1.nonneg z) (pow_nonneg (hF z.1) _))
  have hB : 0 ≤ expect P (fun z => (1 + t * G z.2)^3) :=
    Finset.sum_nonneg (fun z _ => mul_nonneg (hP.1.nonneg z) (pow_nonneg (hG z.2) _))
  have hL : 0 ≤ expect P (fun z => (1 + t * F z.1)^2 * (1 + t * G z.2)^2) :=
    Finset.sum_nonneg (fun z _ => mul_nonneg (hP.1.nonneg z) (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hApow : (expect P (fun z => (1 + t * F z.1)^3) ^ ((2 : ℝ) / 3))^3 =
      (expect P (fun z => (1 + t * F z.1)^3))^2 := by
    rw [← Real.rpow_mul_natCast hA ((2 : ℝ) / 3) 3]
    norm_num
  have hBpow : (expect P (fun z => (1 + t * G z.2)^3) ^ ((2 : ℝ) / 3))^3 =
      (expect P (fun z => (1 + t * G z.2)^3))^2 := by
    rw [← Real.rpow_mul_natCast hB ((2 : ℝ) / 3) 3]
    norm_num
  have hcube := pow_le_pow_left₀ hL hhc 3
  simpa only [mul_pow, hApow, hBpow] using hcube

lemma contact_hessian_coefficient {a b l : ℝ → ℝ}
    (ha : ContinuousAt a 0) (hb : ContinuousAt b 0) (hl : ContinuousAt l 0)
    (h : ∀ᶠ t : ℝ in nhds 0,
      (1 + t^2 * l t)^3 ≤ (1 + t^2 * a t)^2 * (1 + t^2 * b t)^2) :
    3 * l 0 ≤ 2 * (a 0 + b 0) := by
  let q : ℝ → ℝ := fun t => 2 * (a t + b t) - 3 * l t +
    t^2 * ((a t)^2 + (b t)^2 + 4 * a t * b t - 3 * (l t)^2) +
    t^4 * (2 * (a t)^2 * b t + 2 * a t * (b t)^2 - (l t)^3) +
    t^6 * (a t)^2 * (b t)^2
  have hcont : ContinuousAt q 0 := by dsimp [q]; fun_prop
  have hevent : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 ≤ q t := by
    have h' : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (1 + t^2 * l t)^3 ≤ (1 + t^2 * a t)^2 * (1 + t^2 * b t)^2 :=
      h.filter_mono nhdsWithin_le_nhds
    filter_upwards [h', self_mem_nhdsWithin] with t ht htpos
    change 0 < t at htpos
    have hfactor : (1 + t^2 * a t)^2 * (1 + t^2 * b t)^2 -
        (1 + t^2 * l t)^3 = t^2 * q t := by dsimp [q]; ring
    have hnonneg : 0 ≤ t^2 * q t := by rw [← hfactor]; linarith
    exact nonneg_of_mul_nonneg_right hnonneg (sq_pos_of_pos htpos)
  have hq : 0 ≤ q 0 := ge_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hevent
  have hq' : 0 ≤ 2 * (a 0 + b 0) - 3 * l 0 := by simpa [q] using hq
  linarith

lemma contact_hessian {S : Finset (X × Y)} {w P : Law X Y}
    (hw : stoch_to_det.Feasible S w) (hP : stoch_to_det.IsContact S w P)
    (F : X → ℝ) (G : Y → ℝ)
    (hF : expect P (fun z => F z.1) = 0) (hG : expect P (fun z => G z.2) = 0) :
    4 * expect P (fun z => F z.1 * G z.2) ≤
      expect P (fun z => (F z.1)^2) + expect P (fun z => (G z.2)^2) := by
  let a : ℝ → ℝ := fun t => 3 * expect P (fun z => (F z.1)^2) + t * expect P (fun z => (F z.1)^3)
  let b : ℝ → ℝ := fun t => 3 * expect P (fun z => (G z.2)^2) + t * expect P (fun z => (G z.2)^3)
  let l : ℝ → ℝ := fun t => expect P (fun z => (F z.1)^2) + expect P (fun z => (G z.2)^2) +
    4 * expect P (fun z => F z.1 * G z.2) +
    2 * t * (expect P (fun z => (F z.1)^2 * G z.2) + expect P (fun z => F z.1 * (G z.2)^2)) +
    t^2 * expect P (fun z => (F z.1)^2 * (G z.2)^2)
  have ha : ContinuousAt a 0 := by dsimp [a]; fun_prop
  have hb : ContinuousAt b 0 := by dsimp [b]; fun_prop
  have hl : ContinuousAt l 0 := by dsimp [l]; fun_prop
  have htest : ∀ᶠ t : ℝ in nhds 0,
      (1 + t^2 * l t)^3 ≤ (1 + t^2 * a t)^2 * (1 + t^2 * b t)^2 := by
    filter_upwards [contact_hessian_affine_pos F, contact_hessian_affine_pos G] with t htF htG
    have hc := contact_hessian_cube_test hw hP F G t (fun x => (htF x).le) (fun y => (htG y).le)
    rw [contact_hessian_expect_cubic hP.1 _ hF t, contact_hessian_expect_cubic hP.1 _ hG t,
      contact_hessian_expect_biquad hP.1 _ _ hF hG t] at hc
    exact hc
  have hc := contact_hessian_coefficient ha hb hl htest
  dsimp [a, b, l] at hc
  linarith

/-- Two distinct positive contacts `P`, `R` of a common feasible kernel satisfy the moment relations of
`ContactMoments`, in particular `quarticMoment P R ≤ separation P R ^ 2 / 2`. -/
theorem contact_moments {S : Finset (X × Y)} {w P R : Law X Y}
    (hpair : CommonSupportPair S w P R) : ContactMoments S P R := by
  have hP := hpair.2.1
  have hR := hpair.2.2.1
  have hPs := contact_support_eq_of_positiveOn hP hpair.2.2.2.1
  have hRs := contact_support_eq_of_positiveOn hR hpair.2.2.2.2.1
  have he := contact_energy_identities hP hR hPs hRs
  have hr := contact_ratio_mul hpair
  have hx := contact_cond_rootRatioY_square_mul hpair
  have hy := contact_cond_rootRatioX_square_mul hpair
  have hf2 := contact_rootRatioX_square hpair
  have hg2 := contact_rootRatioY_square hpair
  have hq := contact_quartic_identity hP.1 hR.1 hr hx hy hf2 hg2
  have hh := contact_hessian hpair.1 hP
  have hzS : ∀ z, 0 < P z → z ∈ S := by
    intro z hz
    by_contra hn
    exact hz.ne' (hP.2.1 z hn)
  refine ⟨(fun x hx => contact_cond_rootRatioY_square hpair hx),
    (fun y hy => contact_cond_rootRatioX_square hpair hy),
    contact_rootRatioX_cube hpair, contact_rootRatioY_cube hpair, hf2, hg2, contact_separation hpair hr he.2.2,
    ?_, he.1, he.2.1, hq, hh, contact_quarticMoment_bound hP.1 he.1 he.2.1 hq hh,
    contact_scalar_bound P R⟩
  apply contact_upper_separation hP.1 (contact_rootRatioX_nonneg hpair) (contact_rootRatioY_nonneg hpair)
  · intro z hz
    apply contact_rootRatioX_pos hpair
    exact Finset.mem_image.mpr ⟨z, hzS z hz, rfl⟩
  · intro z hz
    apply contact_rootRatioY_pos hpair
    exact Finset.mem_image.mpr ⟨z, hzS z hz, rfl⟩

end

end NaturalLatents.General
