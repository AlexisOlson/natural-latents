-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/DomFloorCore.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed.
import NaturalLatents.Upstream.PhiBounds
import NaturalLatents.Upstream.Duality

/-!
# Entropy control of contact correlations

The natural-log mutual information budget is split into bulk cells, where a
quadratic estimate and Cauchy--Schwarz apply, and tail cells, where feasibility
controls a quartic moment.
-/

namespace stoch_to_det

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Mutual information in nats, written with the scalar entropy integrand and
product marginals. -/
noncomputable def Knat (q : α × β → ℝ) : ℝ :=
  ∑ z, (mX q z.1 * mY q z.2) *
    ((q z / (mX q z.1 * mY q z.2)) *
      Real.log (q z / (mX q z.1 * mY q z.2)) -
      q z / (mX q z.1 * mY q z.2) + 1)

private lemma sum_negMulLog {ι : Type*} [Fintype ι] (m : ι → ℝ) :
    (∑ i, Real.negMulLog (m i)) = ∑ i, m i * (-Real.log (m i)) := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [Real.negMulLog]
  ring

/-- The scalar-integrand formula for mutual information, in natural-log units. -/
theorem Knat_eq_log_two_mul_Ixy {q : α × β → ℝ} (hq : IsPMF q) :
    Knat q = Real.log 2 * Ixy q := by
  let Q : α × β → ℝ := fun z => mX q z.1 * mY q z.2
  have hqX : IsPMF (mX q) := isPMF_push hq
  have hqY : IsPMF (mY q) := isPMF_push hq
  have hQ : IsPMF Q := product_isPMF_dom hqX hqY
  have hac : ∀ z, Q z = 0 → q z = 0 := by
    intro z hQz
    by_contra hqz
    have hqpos : 0 < q z := lt_of_le_of_ne (hq.nonneg z) (Ne.symm hqz)
    have hxle : q z ≤ mX q z.1 := apply_le_push hq.nonneg Prod.fst z
    have hyle : q z ≤ mY q z.2 := apply_le_push hq.nonneg Prod.snd z
    have hxpos : 0 < mX q z.1 := lt_of_lt_of_le hqpos hxle
    have hypos : 0 < mY q z.2 := lt_of_lt_of_le hqpos hyle
    exact (mul_ne_zero hxpos.ne' hypos.ne') hQz
  have hliftX : (∑ x, Real.negMulLog (mX q x)) =
      ∑ z, q z * (-Real.log (mX q z.1)) :=
    (sum_negMulLog (mX q)).trans (sum_push_mul Prod.fst q _)
  have hliftY : (∑ y, Real.negMulLog (mY q y)) =
      ∑ z, q z * (-Real.log (mY q z.2)) :=
    (sum_negMulLog (mY q)).trans (sum_push_mul Prod.snd q _)
  have hliftq := sum_negMulLog q
  have hEntropyKL :
      (∑ x, Real.negMulLog (mX q x)) + (∑ y, Real.negMulLog (mY q y)) -
          ∑ z, Real.negMulLog (q z) =
        ∑ z, q z * Real.log (q z / Q z) := by
    rw [hliftX, hliftY, hliftq, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hqz : q z = 0
    · simp [hqz]
    · have hQz : Q z ≠ 0 := fun h => hqz (hac z h)
      have hxy : mX q z.1 * mY q z.2 ≠ 0 := by simpa [Q] using hQz
      have hx0 : mX q z.1 ≠ 0 := (mul_ne_zero_iff.mp hxy).1
      have hy0 : mY q z.2 ≠ 0 := (mul_ne_zero_iff.mp hxy).2
      rw [Real.log_div hqz hQz]
      dsimp [Q]
      rw [Real.log_mul hx0 hy0]
      ring
  have hEq_q := H_eq_negMulLog hq.nonneg
  have hEq_X := H_eq_negMulLog hqX.nonneg
  have hEq_Y := H_eq_negMulLog hqY.nonneg
  have hI_nats : Real.log 2 * Ixy q = ∑ z, q z * Real.log (q z / Q z) := by
    calc
      Real.log 2 * Ixy q =
          Real.log 2 * H (mX q) + Real.log 2 * H (mY q) - Real.log 2 * H q := by
            unfold Ixy
            ring
      _ = (∑ x, Real.negMulLog (mX q x)) + (∑ y, Real.negMulLog (mY q y)) -
          ∑ z, Real.negMulLog (q z) := by rw [hEq_X, hEq_Y, hEq_q]
      _ = ∑ z, q z * Real.log (q z / Q z) := hEntropyKL
  have hterm : ∀ z,
      Q z * ((q z / Q z) * Real.log (q z / Q z) - q z / Q z + 1) =
        q z * Real.log (q z / Q z) - q z + Q z := by
    intro z
    by_cases hQz : Q z = 0
    · have hqz := hac z hQz
      simp [hQz, hqz]
    · field_simp [hQz]
  have hsumq : ∑ z, q z = 1 := by simpa [mass] using hq.total
  have hsumQ : ∑ z, Q z = 1 := by simpa [mass] using hQ.total
  calc
    Knat q = ∑ z, Q z *
        ((q z / Q z) * Real.log (q z / Q z) - q z / Q z + 1) := by rfl
    _ = ∑ z, (q z * Real.log (q z / Q z) - q z + Q z) :=
      Finset.sum_congr rfl (fun z _ => hterm z)
    _ = ∑ z, q z * Real.log (q z / Q z) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsumq, hsumQ]
      ring
    _ = Real.log 2 * Ixy q := hI_nats.symm


lemma joint_pos_marginals {q : α × β → ℝ} (hq : IsPMF q)
    {z : α × β} (hz : 0 < q z) :
    0 < mX q z.1 ∧ 0 < mY q z.2 := by
  have hxle : q z ≤ mX q z.1 := apply_le_push hq.nonneg Prod.fst z
  have hyle : q z ≤ mY q z.2 := apply_le_push hq.nonneg Prod.snd z
  exact ⟨hz.trans_le hxle, hz.trans_le hyle⟩

end stoch_to_det
