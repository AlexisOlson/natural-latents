-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/Toolkit.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed.
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import NaturalLatents.Upstream.Entropy

/-!
# Lemma 0.1 — the classical toolkit


Four standard facts, none of which is available in Mathlib in the form used
here (Mathlib's `klDiv` is `ℝ≥0∞`-valued and in nats; there is no finite
bits-valued KL, no Bhattacharyya coefficient, and no differential entropy).
All four proofs are included below.

| Lean name | Label | Used by |
|---|---|---|
| `variational_le` | (T1) | Lemma 5.2 |
| `pinsker` | (T2) | Thm 6.1, Thm 9.1 |
| `bhattacharyya` | (T3) | Thm 9.1 (far part) |
| `diffEntropy_le_of_abs_le` | (T4) | Thm 8.1 (off-diagonal contexts) |

(T4) is the only item here that leaves the finite world; it is stated for a
real random variable given by a Lebesgue density, which is exactly how §8 uses
it (`X + N` with `N = ln T`, `T ~ Exp(1)`).
-/

namespace stoch_to_det

open Finset MeasureTheory
open Filter
open scoped ENNReal Topology

variable {ω : Type*} [Fintype ω] [DecidableEq ω]

/-- KL divergence in **bits** between finite laws, `D(P ‖ Q) := ∑ P lg(P/Q)`.
The junk-value convention makes `P a = 0` contribute `0`; when `Q a = 0 < P a`
the summand is `P a * lg (P a / 0) = 0`, which is **wrong** (it should be `+∞`),
so every lemma about `KL` carries an absolute-continuity hypothesis. -/
noncomputable def KL (P Q : ω → ℝ) : ℝ := ∑ a, P a * lg (P a / Q a)

/-- Absolute continuity `P ≪ Q` for finite laws. -/
def AbsCont (P Q : ω → ℝ) : Prop := ∀ a, Q a = 0 → P a = 0

/-- The Bhattacharyya coefficient `BC(P,Q) := ∑ √(P Q)`. -/
noncomputable def BC (P Q : ω → ℝ) : ℝ := ∑ a, Real.sqrt (P a * Q a)

omit [DecidableEq ω] in
private lemma absCont_pos {P Q : ω → ℝ} (hQ : IsPMF Q) (hac : AbsCont P Q)
    {a : ω} (ha : P a ≠ 0) : 0 < Q a :=
  lt_of_le_of_ne (hQ.nonneg a) (Ne.symm (fun h => ha (hac a h)))

omit [DecidableEq ω] in
/-- Finite Gibbs inequality for the bits-valued `KL`. -/
private lemma KL_nonneg {P Q : ω → ℝ} (hP : IsPMF P) (hQ : IsPMF Q)
    (hac : AbsCont P Q) : 0 ≤ KL P Q := by
<<<<<<< HEAD
  have hnats := gibbs_nonneg hP hQ (fun a hPa hQa => hPa (hac a hQa))
||||||| merged common ancestors
  have hterm : ∀ a : ω, P a - Q a ≤ P a * Real.log (P a / Q a) := by
    intro a
    by_cases hPa : P a = 0
    · simp [hPa, hQ.nonneg a]
    · have hPa_pos : 0 < P a := lt_of_le_of_ne (hP.nonneg a) (Ne.symm hPa)
      have hQa : Q a ≠ 0 := fun h ↦ hPa (hac a h)
      have hQa_pos : 0 < Q a := lt_of_le_of_ne (hQ.nonneg a) (Ne.symm hQa)
      have hlog := Real.log_le_sub_one_of_pos (div_pos hQa_pos hPa_pos)
      have hmul := mul_le_mul_of_nonneg_left hlog hPa_pos.le
      have hlog_eq : Real.log (Q a / P a) = -Real.log (P a / Q a) := by
        rw [Real.log_div hQa hPa, Real.log_div hPa hQa]
        ring
      calc
        P a - Q a = -(Q a - P a) := by ring
        _ = -(P a * (Q a / P a - 1)) := by field_simp
        _ ≤ -(P a * Real.log (Q a / P a)) := neg_le_neg hmul
        _ = P a * Real.log (P a / Q a) := by rw [hlog_eq]; ring
  have hnats : 0 ≤ ∑ a, P a * Real.log (P a / Q a) := by
    calc
      0 = ∑ a, (P a - Q a) := by
        rw [sum_sub_distrib, ← mass, ← mass, hP.total, hQ.total]
        norm_num
      _ ≤ ∑ a, P a * Real.log (P a / Q a) := sum_le_sum fun a _ ↦ hterm a
=======
  have hterm : ∀ a : ω, P a - Q a ≤ P a * Real.log (P a / Q a) := by
    intro a
    by_cases hPa : P a = 0
    · simp [hPa, hQ.nonneg a]
    · have hPa_pos : 0 < P a := lt_of_le_of_ne (hP.nonneg a) (Ne.symm hPa)
      have hQa_pos : 0 < Q a := absCont_pos hQ hac hPa
      have hlog := Real.log_le_sub_one_of_pos (div_pos hQa_pos hPa_pos)
      have hmul := mul_le_mul_of_nonneg_left hlog hPa_pos.le
      have hlog_eq : Real.log (Q a / P a) = -Real.log (P a / Q a) := by
        rw [Real.log_div hQa_pos.ne' hPa, Real.log_div hPa hQa_pos.ne']
        ring
      calc
        P a - Q a = -(Q a - P a) := by ring
        _ = -(P a * (Q a / P a - 1)) := by field_simp
        _ ≤ -(P a * Real.log (Q a / P a)) := neg_le_neg hmul
        _ = P a * Real.log (P a / Q a) := by rw [hlog_eq]; ring
  have hnats : 0 ≤ ∑ a, P a * Real.log (P a / Q a) := by
    calc
      0 = ∑ a, (P a - Q a) := by
        rw [sum_sub_distrib, ← mass, ← mass, hP.total, hQ.total]
        norm_num
      _ ≤ ∑ a, P a * Real.log (P a / Q a) := sum_le_sum fun a _ ↦ hterm a
>>>>>>> lane/cleanup-low
  rw [KL]
  change 0 ≤ ∑ a, P a * (Real.log (P a / Q a) / Real.log 2)
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  exact div_nonneg hnats (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

omit [DecidableEq ω] in
/-- **(T3)** Bhattacharyya, first half:
`min_r [D(r‖P) + D(r‖Q)] = −2 lg BC(P,Q)`. Only `≥` is used (Thm 9.1). -/
theorem bhattacharyya_le {P Q : ω → ℝ} (hP : IsPMF P) (hQ : IsPMF Q)
    {r : ω → ℝ} (hr : IsPMF r) (hacP : AbsCont r P) (hacQ : AbsCont r Q) :
    -2 * lg (BC P Q) ≤ KL r P + KL r Q := by
  let B : ℝ := BC P Q
  let S : ω → ℝ := fun a ↦ Real.sqrt (P a * Q a) / B
  obtain ⟨a₀, ha₀⟩ : ∃ a, 0 < r a := by
    have hsum : 0 < ∑ a, r a := by
      rw [← mass, hr.total]
      norm_num
    rcases (Finset.sum_pos_iff_of_nonneg (fun a _ ↦ hr.nonneg a)).mp hsum with
      ⟨a, _, ha⟩
    exact ⟨a, ha⟩
  have hPa₀ : 0 < P a₀ := absCont_pos hP hacP ha₀.ne'
  have hQa₀ : 0 < Q a₀ := absCont_pos hQ hacQ ha₀.ne'
  have hB : 0 < B := by
    dsimp [B, BC]
    apply Finset.sum_pos'
    · intro a _
      exact Real.sqrt_nonneg _
    · exact ⟨a₀, Finset.mem_univ _, Real.sqrt_pos.2 (mul_pos hPa₀ hQa₀)⟩
  have hS : IsPMF S := by
    constructor
    · intro a
      dsimp [S]
      exact div_nonneg (Real.sqrt_nonneg _) hB.le
    · dsimp [mass, S]
      rw [← sum_div]
      exact div_self hB.ne'
  have hacS : AbsCont r S := by
    intro a hSa
    by_contra hra
    have hPa_pos := absCont_pos hP hacP hra
    have hQa_pos := absCont_pos hQ hacQ hra
    exact (div_pos (Real.sqrt_pos.2 (mul_pos hPa_pos hQa_pos)) hB).ne' hSa
  have hnonneg : 0 ≤ KL r S := KL_nonneg hr hS hacS
  have hterm : ∀ a : ω,
      2 * (r a * lg (r a / S a)) =
        r a * lg (r a / P a) + r a * lg (r a / Q a) + r a * (2 * lg B) := by
    intro a
    by_cases hra : r a = 0
    · simp [hra]
    · have hra_pos : 0 < r a := lt_of_le_of_ne (hr.nonneg a) (Ne.symm hra)
      have hPa_pos : 0 < P a := absCont_pos hP hacP hra
      have hQa_pos : 0 < Q a := absCont_pos hQ hacQ hra
      have hS_pos : 0 < S a := by
        dsimp [S]
        exact div_pos (Real.sqrt_pos.2 (mul_pos hPa_pos hQa_pos)) hB
      change 2 * (r a * (Real.log (r a / S a) / Real.log 2)) =
        r a * (Real.log (r a / P a) / Real.log 2) +
          r a * (Real.log (r a / Q a) / Real.log 2) +
            r a * (2 * (Real.log B / Real.log 2))
      rw [Real.log_div hra hS_pos.ne', Real.log_div hra hPa_pos.ne', Real.log_div hra hQa_pos.ne',
        show Real.log (S a) =
            (Real.log (P a) + Real.log (Q a)) / 2 - Real.log B by
          dsimp [S]
          rw [Real.log_div (Real.sqrt_pos.2 (mul_pos hPa_pos hQa_pos)).ne' hB.ne',
            Real.log_sqrt (mul_nonneg (hP.nonneg a) (hQ.nonneg a)),
            Real.log_mul hPa_pos.ne' hQa_pos.ne']]
      field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2)
        (by norm_num : (2 : ℝ) ≠ 1)]
      ring
  have hid : 2 * KL r S = KL r P + KL r Q + 2 * lg B := by
    rw [KL, KL, KL, mul_sum]
    calc
      (∑ a, 2 * (r a * lg (r a / S a))) =
          ∑ a, (r a * lg (r a / P a) + r a * lg (r a / Q a) +
            r a * (2 * lg B)) := by
              apply sum_congr rfl
              intro a _
              exact hterm a
      _ = (∑ a, r a * lg (r a / P a)) + (∑ a, r a * lg (r a / Q a)) +
          (∑ a, r a) * (2 * lg B) := by
            rw [sum_add_distrib, sum_add_distrib, ← sum_mul]
      _ = (∑ a, r a * lg (r a / P a)) + (∑ a, r a * lg (r a / Q a)) +
          2 * lg B := by
            have hsumr : ∑ a, r a = 1 := by simpa [mass] using hr.total
            rw [hsumr, one_mul]
  have htwice : 0 ≤ 2 * KL r S := mul_nonneg (by norm_num) hnonneg
  rw [hid] at htwice
  change -2 * lg B ≤ KL r P + KL r Q
  linarith

/-! ### Analytic preparation for (T4) -/

end stoch_to_det
