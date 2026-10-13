-- Adapted from the author's earlier repository (StochasticToDeterministicLatents);
-- modified: module paths renamed; declarations unused by the main theorems removed.
import NaturalLatents.General.Setup
import NaturalLatents.General.Ledger
import NaturalLatents.General.Race
import NaturalLatents.General.Cap
import NaturalLatents.General.Affinity
import NaturalLatents.General.Payment
import NaturalLatents.General.PairCharge

/-!
# The bound for positive, connected and general laws

Assembling the results of the earlier modules at the exponent `a = 93/20`, with
`beta = 1/10` and `gamma = 3/25`, gives in nats

    T p ≤ (2789/400) * tau p.

Three routes:

* `T_le_of_pos` for a positive law, through `exists_setup_of_pos`, the race with the Gamma-form
  price and the three-term cap;
* `T_le_of_connected` for a law with connected support, through `exists_setup_of_connected`;
* `T_le` for every probability law, through `exists_setup`, the zero-rate race
  with the exponential-time price and the four-term cap; this route does not use
  `racePriceE_eq`.

`constants_arithmetic` records the exact arithmetic: both caps at `93/20` lie below `199/1000`,
the coefficient of `M` is `697/100`, and the coefficient of `B` is
`(3 * (93/20) - 1) / 2 + 3 * (199/1000) * (1/10) / (3/25) = 2789/400`.

## Attribution

The upstream ancestor is
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
The upstream definitions and lemmas used here come from that project, including
its open pull request #6 (`jezgillen`, head `7b41957d`) at the pinned revision.
The rest is adapted from unpublished working material with public names and
module boundaries; that material supplies attribution only, not verification evidence.
-/

namespace StochasticToDeterministicLatents.General

noncomputable section

open scoped BigOperators
open MeasureTheory ProbabilityTheory

variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- Exact pricing arithmetic at `a = 93/20`: both caps lie below `199/1000`, the coefficient of `M` is
`697/100` and the coefficient of `B` is `2789/400`. This is arithmetic, not an analytic cap proof. -/
lemma constants_arithmetic :
    C3a (93/20) = 3015167/15153048 ∧
    (199/1000 : ℝ) - C3a (93/20) = 18097/947065500 ∧
    C4b (93/20) = 2334323707/11743612200 ∧
    (199/1000 : ℝ) - C4b (93/20) = 3318901/14679515250 ∧
    C3a (93/20) < 199/1000 ∧ C4b (93/20) < 199/1000 ∧
    (1 + 3*(199/1000)*(1+2*(1/10))/(3/25) : ℝ) = 697/100 ∧
    (((3*(93/20)-1)/2) + 3*(199/1000)*(1/10)/(3/25) : ℝ) = 2789/400 ∧
    (697/100 : ℝ) ≤ 2789/400 ∧ (2789/400 : ℝ) < 7 := by
  norm_num [C3a, C4b]

/-- `T p ≤ (2789/400) * tau p`, in nats, for a law with connected support. -/
theorem T_le_of_connected {p : Law X Y} (hp : stoch_to_det.IsPMF p)
    (hconn : stoch_to_det.IsConnected (stoch_to_det.support p)) :
    T p ≤ (2789/400 : ℝ)*tau p := by
  obtain ⟨D⟩ := exists_setup_of_connected hp hconn
  obtain ⟨F, hF⟩ := exists_race hp D.L D.rows_pos (93/20) (by norm_num)
  have hT := T_le_ledger hp D.L F
  have hj : j (93/20) < (199/1000 : ℝ) :=
    lt_trans (racePrice_lt_capC3a (93/20) (by norm_num)) constants_arithmetic.2.2.2.2.1
  have hd : 0 ≤ d D.L :=
    stoch_to_det.SharedRace.categoricalMismatch_nonneg_of_support hp
      (fun z hz => race_post_isPMF hp D.L z hz)
  have hjd := mul_le_mul_of_nonneg_right hj.le hd
  have hh : h F ≤ (93/20 : ℝ) * B D.L + 2 * (199/1000 : ℝ) * d D.L := by
    linarith only [hF, hjd]
  have haffinity : ∀ i j : D.L.ι, i ≠ j → AffinityBound (D.L.comp i) (D.L.comp j) := by
    intro i j hij
    have hpair : CommonSupportPairs (stoch_to_det.support p) D.w
        (D.L.comp i) (D.L.comp j) :=
      ⟨D.feasible, D.contact i, D.contact j, D.positive i, D.positive j,
        fun heq => hij (D.distinct heq)⟩
    exact affinity_bound hpair (contact_moments hpair)
  have hcharge := mismatch_payment hp D (1/10) (3/25) (by norm_num) (by norm_num)
    haffinity (replica_budget hp D.L) pairCharge_A
  have hM : 0 ≤ M D.L :=
    mul_nonneg (Real.log_pos one_lt_two).le
      (stoch_to_det.condMI_nonneg D.L.joint_isPMF
        (fun w => w.2.1) (fun w => w.2.2) (fun w => w.1))
  have hprice : T p ≤ (697/100 : ℝ) * M D.L + (2789/400 : ℝ) * B D.L := by
    linarith only [hT, hh, hcharge]
  have hdom := mul_le_mul_of_nonneg_right
    constants_arithmetic.2.2.2.2.2.2.2.2.1 hM
  calc
    T p ≤ (697/100 : ℝ) * M D.L + (2789/400 : ℝ) * B D.L := hprice
    _ ≤ (2789/400 : ℝ) * (M D.L + B D.L) := by linarith only [hdom]
    _ = (2789/400 : ℝ) * tau p := by rw [D.attained]

end

end StochasticToDeterministicLatents.General
