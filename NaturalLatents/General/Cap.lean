-- Adapted from the author's earlier repository (StochasticToDeterministicLatents);
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised; namespace renamed to NaturalLatents.General.
import NaturalLatents.General.RaceLaplace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.ZetaValues

/-!
# Caps on the race price

A closed-form upper bound on the race price, from a series for `log Γ (1 - 1/a)`:
`racePrice_lt_capC3b` proves `j a < C3b a` for `a > 1`.

The proofs use the partial-fraction identity for `log Γ`, a telescoping bound with midpoint and
tail estimates for the three remainders, and the zeta values at two, three, four and five
bracketed by rational bounds.

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

lemma gamma_sum_log_factorial (n : ℕ) :
    ∑ m ∈ Finset.range n, Real.log (m + 1 : ℝ) = Real.log (n.factorial : ℝ) := by
  have hc : (n.factorial : ℝ) = ∏ m ∈ Finset.range n, ((m : ℝ) + 1) := by
    rw [← Finset.prod_range_add_one_eq_factorial]
    push_cast
    rfl
  rw [hc, Real.log_prod]
  intro m _
  positivity

lemma gamma_factor_pos {y : ℝ} (hy : y < 1) (m : ℕ) :
    0 < 1 - y / (m + 1) := by
  have hd : 0 < (m + 1 : ℝ) := by positivity
  apply sub_pos.mpr
  rw [div_lt_one hd]
  linarith [Nat.cast_nonneg m (α := ℝ)]

lemma gamma_log_factor {y : ℝ} (hy : y < 1) (m : ℕ) :
    Real.log (1 - y + m) = Real.log (m + 1 : ℝ) + Real.log (1 - y / (m + 1)) := by
  have hd : 0 < (m + 1 : ℝ) := by positivity
  rw [← Real.log_mul hd.ne' (gamma_factor_pos hy m).ne']
  congr 1
  field_simp
  ring_nf

lemma gamma_partial_identity {y : ℝ} (hy : y < 1) (n : ℕ) :
    (∑ m ∈ Finset.range n, (-Real.log (1 - y / (m + 1)) - y / (m + 1))) =
      Real.BohrMollerup.logGammaSeq (1 - y) n +
        (Real.log (n + (1 - y)) - Real.log n) -
        y * ((harmonic n : ℝ) - Real.log n) := by
  unfold Real.BohrMollerup.logGammaSeq harmonic
  rw [Finset.sum_range_succ]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_add, Rat.cast_one, Rat.cast_natCast, Nat.cast_add, Nat.cast_one]
  have hlogs :
      (∑ m ∈ Finset.range n, Real.log (1 - y + m)) =
        (∑ m ∈ Finset.range n, Real.log (m + 1 : ℝ)) +
        (∑ m ∈ Finset.range n, Real.log (1 - y / (m + 1))) := by
    simp_rw [gamma_log_factor hy, Finset.sum_add_distrib]
  rw [hlogs, gamma_sum_log_factorial]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, div_eq_mul_inv, ← Finset.mul_sum]
  rw [show (1 - y + n : ℝ) = n + (1 - y) by ring_nf]
  ring_nf

lemma gamma_term_nonneg {y : ℝ} (hy : y < 1) (m : ℕ) :
    0 ≤ -Real.log (1 - y / (m + 1)) - y / (m + 1) := by
  have h := Real.log_le_sub_one_of_pos (gamma_factor_pos hy m)
  linarith

lemma gamma_hasSum_product_remainder {y : ℝ} (hy : y < 1) :
    HasSum (fun m : ℕ => -Real.log (1 - y / (m + 1)) - y / (m + 1))
      (Real.log (Real.Gamma (1 - y)) - Real.eulerMascheroniConstant * y) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (gamma_term_nonneg hy)]
  have hg := Real.BohrMollerup.tendsto_log_gamma (sub_pos.mpr hy)
  have hb := (Real.tendsto_log_comp_add_sub_log (1 - y)).comp tendsto_natCast_atTop_atTop
  have he := Real.tendsto_harmonic_sub_log.const_mul y
  convert (hg.add hb).sub he using 1
  · ext n
    exact gamma_partial_identity hy n
  · ring_nf

lemma cap_telescope_bound {f q : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hq : ∀ n, 0 ≤ q n)
    (hstep : ∀ n, f n ≤ q n - q (n + 1)) :
    Summable f ∧ (∑' n, f n) ≤ q 0 := by
  have hrange : ∀ n, (∑ i ∈ Finset.range n, f i) ≤ q 0 - q n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hs := hstep n
      linarith
  have hb : ∀ n, (∑ i ∈ Finset.range n, f i) ≤ q 0 := by
    intro n
    exact (hrange n).trans (sub_le_self _ (hq n))
  exact ⟨summable_of_sum_range_le hf hb, Real.tsum_le_of_sum_range_le hf hb⟩

lemma cap_telescope_strict {f q : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hq : ∀ n, 0 ≤ q n)
    (hstep : ∀ n, f n ≤ q n - q (n + 1))
    (hstrict : f 0 < q 0 - q 1) :
    Summable f ∧ (∑' n, f n) < q 0 := by
  have hb := cap_telescope_bound hf hq hstep
  have ht := cap_telescope_bound (fun n => hf (n + 1))
    (fun n => hq (n + 1)) (fun n => by simpa [Nat.add_assoc] using hstep (n + 1))
  refine ⟨hb.1, ?_⟩
  have hs := hb.1.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hs
  linarith [ht.2]

lemma cap_midpoint_three {x : ℝ} (hx : 1 ≤ x) :
    1 / x ^ 3 < (1 / 2) / (x - 1 / 2) ^ 2 - (1 / 2) / (x + 1 / 2) ^ 2 := by
  have hxp : 0 < x := by linarith
  have hq : 0 < x ^ 2 - 1 / 4 := by nlinarith
  have hn : 0 < x ^ 2 / 2 - 1 / 16 := by nlinarith
  have heq : (1 / 2) / (x - 1 / 2) ^ 2 - (1 / 2) / (x + 1 / 2) ^ 2 - 1 / x ^ 3 =
      (x ^ 2 / 2 - 1 / 16) / (x ^ 3 * (x ^ 2 - 1 / 4) ^ 2) := by
    have h2m : x * 2 - 1 ≠ 0 := by linarith
    have h2p : x * 2 + 1 ≠ 0 := by linarith
    have h4q : x ^ 2 * 4 - 1 ≠ 0 := by nlinarith
    have h2m' : 2 * x - 1 ≠ 0 := by linarith
    have h2p' : 2 * x + 1 ≠ 0 := by linarith
    field_simp [h2m, h2p, h2m', h2p', h4q, ne_of_gt hxp]
    ring
  apply sub_pos.mp
  rw [heq]
  positivity

lemma cap_tail_three :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 3) ^ 3) ∧
      (∑' n : ℕ, 1 / ((n : ℝ) + 3) ^ 3) < 2 / 25 := by
  have hs := cap_telescope_strict
    (f := fun n : ℕ => 1 / ((n : ℝ) + 3) ^ 3)
    (q := fun n : ℕ => (1 / 2) / ((n : ℝ) + 5 / 2) ^ 2)
    (fun n => by positivity) (fun n => by positivity)
    (fun n => by
      have hn : (1 : ℝ) ≤ (n : ℝ) + 3 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have h1 : (n : ℝ) + 3 - 1 / 2 = (n : ℝ) + 5 / 2 := by ring
      have h2 : (n : ℝ) + 3 + 1 / 2 = ((n + 1 : ℕ) : ℝ) + 5 / 2 := by
        rw [Nat.cast_add, Nat.cast_one]
        ring
      simpa only [h1, h2] using (cap_midpoint_three hn).le)
    (by norm_num)
  norm_num at hs ⊢
  exact hs

lemma cap_zeta_two :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) ∧ (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) < 533 / 324 := by
  have h : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa [Finset.sum_range_one] using this
  refine ⟨h.summable, ?_⟩
  rw [h.tsum_eq]
  nlinarith [Real.pi_lt_d4, Real.pi_pos]

lemma cap_zeta_three :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 3) ∧ (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3) < 241 / 200 := by
  have ht : Summable (fun n : ℕ => 1 / (((n + 2 : ℕ) : ℝ) + 1) ^ 3) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat, add_assoc, show (2 : ℝ) + 1 = 3 by norm_num] using cap_tail_three.1
  have hs := (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 3) 2).1 ht
  refine ⟨hs, ?_⟩
  rw [← hs.sum_add_tsum_nat_add 2]
  have hb := cap_tail_three.2
  have he : (∑' n : ℕ, 1 / (((n + 2 : ℕ) : ℝ) + 1) ^ 3) =
      ∑' n : ℕ, 1 / ((n : ℝ) + 3) ^ 3 := by
    congr 1
    funext n
    simp only [Nat.cast_add, Nat.cast_ofNat]
    congr 2
    ring
  rw [he]
  have hfin : (∑ i ∈ Finset.range 2, 1 / ((i : ℝ) + 1) ^ 3) = 9 / 8 := by
    norm_num [Finset.sum_range_succ]
  rw [hfin]
  linarith

lemma cap_zeta_four :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 4) ∧ (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 4) < 6503 / 6000 := by
  have h : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 4) (Real.pi ^ 4 / 90) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_four
    simpa [Finset.sum_range_one] using this
  refine ⟨h.summable, ?_⟩
  rw [h.tsum_eq]
  have hpi2 : Real.pi ^ 2 < 9.87 := by nlinarith [Real.pi_lt_d4, Real.pi_pos]
  nlinarith [sq_nonneg (Real.pi ^ 2)]

/-- The part of the logarithm's power series after its linear term. -/
lemma c3b_log_remainder_hasSum {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => x ^ (n + 2) / ((n : ℝ) + 2))
      (-Real.log (1 - x) - x) := by
  have hx : |x| < 1 := by simpa only [abs_of_nonneg hx0] using hx1
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one hx
  have ht := (hasSum_nat_add_iff' 1).mpr hs
  norm_num [add_assoc] at ht
  exact ht

/-- Keep the quadratic and cubic terms, then dominate the tail by a geometric series. -/
lemma c3b_log_remainder_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -Real.log (1 - x) - x ≤ x ^ 2 / 2 + x ^ 3 / 3 + x ^ 4 / (4 * (1 - x)) := by
  have hx : |x| < 1 := by simpa only [abs_of_nonneg hx0] using hx1
  have hs := c3b_log_remainder_hasSum hx0 hx1
  have htail : Summable (fun n : ℕ => x ^ (n + 4) / ((n : ℝ) + 4)) := by
    have ht := (summable_nat_add_iff 2).mpr hs.summable
    norm_num [add_assoc] at ht
    exact ht
  have hgeom : Summable (fun n : ℕ => (x ^ 4 / 4) * x ^ n) :=
    (summable_geometric_of_abs_lt_one hx).mul_left _
  have hle : (∑' n : ℕ, x ^ (n + 4) / ((n : ℝ) + 4)) ≤
      ∑' n : ℕ, (x ^ 4 / 4) * x ^ n := by
    apply htail.tsum_le_tsum _ hgeom
    intro n
    have hn : (4 : ℝ) ≤ (n : ℝ) + 4 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    calc
      x ^ (n + 4) / ((n : ℝ) + 4) ≤ x ^ (n + 4) / 4 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hn
      _ = (x ^ 4 / 4) * x ^ n := by rw [pow_add]; ring
  have hsplit := hs.summable.sum_add_tsum_nat_add 2
  have hsplit' : x ^ 2 / 2 + x ^ 3 / 3 +
      (∑' n : ℕ, x ^ (n + 4) / ((n : ℝ) + 4)) =
      -Real.log (1 - x) - x := by
    norm_num [Finset.sum_range_succ, add_assoc, hs.tsum_eq] at hsplit
    simpa only [add_assoc] using hsplit
  have hgeom_eq : (∑' n : ℕ, (x ^ 4 / 4) * x ^ n) = x ^ 4 / (4 * (1 - x)) := by
    rw [tsum_mul_left, tsum_geometric_of_abs_lt_one hx]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hgeom_eq] at hle
  linarith

lemma c3b_assemble_remainders {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1)
    (hs : HasSum (fun n : ℕ => -Real.log (1 - y / (n + 1)) - y / (n + 1))
      (Real.log (Real.Gamma (1 - y)) - Real.eulerMascheroniConstant * y)) :
    Real.log (Real.Gamma (1 - y)) - Real.eulerMascheroniConstant * y <
      533 / 648 * y ^ 2 + 241 / 600 * y ^ 3 + 6503 / 24000 * y ^ 4 / (1 - y) := by
  let f : ℕ → ℝ := fun n =>
    (y ^ 2 / 2) * (1 / (n + 1 : ℝ) ^ 2) +
    (y ^ 3 / 3) * (1 / (n + 1 : ℝ) ^ 3) +
    (y ^ 4 / (4 * (1 - y))) * (1 / (n + 1 : ℝ) ^ 4)
  have h2s := cap_zeta_two.1
  have h3s := cap_zeta_three.1
  have h4s := cap_zeta_four.1
  have hfs : Summable f := ((h2s.mul_left _).add (h3s.mul_left _)).add (h4s.mul_left _)
  have hterm : ∀ n : ℕ,
      -Real.log (1 - y / (n + 1)) - y / (n + 1) ≤ f n := by
    intro n
    have hd : 0 < (n + 1 : ℝ) := by positivity
    have hd1 : 1 ≤ (n + 1 : ℝ) := by linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
    have hxy : y / (n + 1 : ℝ) ≤ y := div_le_self hy0.le hd1
    have h := c3b_log_remainder_le (x := y / (n + 1)) (by positivity)
      (hxy.trans_lt hy1)
    have hdenom :
        (y / (n + 1 : ℝ)) ^ 4 / (4 * (1 - y / (n + 1))) ≤
          (y / (n + 1 : ℝ)) ^ 4 / (4 * (1 - y)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have h := h.trans (add_le_add le_rfl hdenom)
    refine h.trans_eq ?_
    dsimp [f]
    field_simp [hd.ne']
  have hbound := hs.summable.tsum_le_tsum hterm hfs
  rw [hs.tsum_eq] at hbound
  have hsum : (∑' n : ℕ, f n) =
      y ^ 2 / 2 * (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ 2) +
      y ^ 3 / 3 * (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ 3) +
      y ^ 4 / (4 * (1 - y)) * (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ 4) := by
    dsimp [f]
    rw [(((h2s.mul_left _).add (h3s.mul_left _)).tsum_add (h4s.mul_left _)),
      ((h2s.mul_left _).tsum_add (h3s.mul_left _)), tsum_mul_left, tsum_mul_left,
      tsum_mul_left]
  rw [hsum] at hbound
  have h2' := mul_lt_mul_of_pos_left cap_zeta_two.2 (show 0 < y ^ 2 / 2 by positivity)
  have h3' := mul_le_mul_of_nonneg_left cap_zeta_three.2.le
    (show 0 ≤ y ^ 3 / 3 by positivity)
  have h4' := mul_le_mul_of_nonneg_left cap_zeta_four.2.le
    (show 0 ≤ y ^ 4 / (4 * (1 - y)) by positivity)
  calc
    _ ≤ _ := hbound
    _ < y ^ 2 / 2 * (533 / 324) + y ^ 3 / 3 * (241 / 200) +
      y ^ 4 / (4 * (1 - y)) * (6503 / 6000) := by linarith
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

lemma c3b_reciprocal_conversion (a : ℝ) (ha : 1 < a)
    (h : Real.log (Real.Gamma (1 - 1 / a)) - Real.eulerMascheroniConstant * (1 / a) <
      533 / 648 * (1 / a) ^ 2 + 241 / 600 * (1 / a) ^ 3 +
        6503 / 24000 * (1 / a) ^ 4 / (1 - 1 / a)) :
    a * Real.log (Real.Gamma (1 - 1 / a)) - Real.eulerMascheroniConstant <
      533 / (648 * a) + 241 / (600 * a ^ 2) + 6503 / (24000 * a ^ 2 * (a - 1)) := by
  have ha0 : 0 < a := by linarith
  have hane : a ≠ 0 := ha0.ne'
  have ham : a - 1 ≠ 0 := by linarith
  have hsub : 1 - 1 / a ≠ 0 := by
    apply ne_of_gt
    exact sub_pos.mpr ((div_lt_one ha0).mpr ha)
  have hm := mul_lt_mul_of_pos_left h ha0
  have hl : a * Real.log (Real.Gamma (1 - 1 / a)) - Real.eulerMascheroniConstant =
      a * (Real.log (Real.Gamma (1 - 1 / a)) - Real.eulerMascheroniConstant * (1 / a)) := by
    rw [mul_sub]
    congr 1
    field_simp
  have hr : 533 / (648 * a) + 241 / (600 * a ^ 2) +
      6503 / (24000 * a ^ 2 * (a - 1)) =
      a * (533 / 648 * (1 / a) ^ 2 + 241 / 600 * (1 / a) ^ 3 +
        6503 / 24000 * (1 / a) ^ 4 / (1 - 1 / a)) := by
    field_simp [hane, ham, hsub]
  rw [hl, hr]
  exact hm

/-- The Gamma-form race price lies below its three-term cap: `j a < C3b a` for `a > 1`. -/
theorem racePrice_lt_capC3b (a : ℝ) (ha : 1 < a) : j a < C3b a := by
  have ha0 : 0 < a := by linarith
  have hy0 : 0 < 1 / a := by positivity
  have hy1 : 1 / a < 1 := (div_lt_one ha0).mpr ha
  have h := c3b_assemble_remainders hy0 hy1
    (gamma_hasSum_product_remainder hy1)
  simpa only [j, C3b] using c3b_reciprocal_conversion a ha h

end

end NaturalLatents.General
