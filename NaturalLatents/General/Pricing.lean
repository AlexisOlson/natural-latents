-- Adapted from the author's earlier repository (StochasticToDeterministicLatents);
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised.
import NaturalLatents.General.Setup
import NaturalLatents.General.Ledger
import NaturalLatents.General.Race
import NaturalLatents.General.Cap
import NaturalLatents.General.Affinity
import NaturalLatents.General.Payment
import NaturalLatents.General.PairCharge

/-!
# The bound for connected laws

Assembling the results of the earlier modules at the exponent `a = 93/20`, with
`beta = 1/10` and `gamma = 3/25`, gives in nats

    T p ≤ (2789/400) * tau p.

The theorem `T_le_of_connected` combines `exists_setup_of_connected`, the exponential race,
the cap on its Gamma-form price, the pair charge, the mismatch payment, and the ledger inequality.

The cap at `93/20` lies below `199/1000`, the coefficient of `M` is `697/100`, and the coefficient of `B` is
`(3 * (93/20) - 1) / 2 + 3 * (199/1000) * (1/10) / (3/25) = 2789/400`.

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

/-- `T p ≤ (2789/400) * tau p`, in nats, for a law with connected support. -/
theorem T_le_of_connected {p : Law X Y} (hp : stoch_to_det.IsPMF p)
    (hconn : stoch_to_det.IsConnected (stoch_to_det.support p)) :
    T p ≤ (2789/400 : ℝ)*tau p := by
  obtain ⟨D⟩ := exists_setup_of_connected hp hconn
  obtain ⟨F, hF⟩ := exists_race hp D.L D.rows_pos (93/20) (by norm_num)
  have hT := T_le_ledger hp D.L F
  have hj : j (93/20) < (199/1000 : ℝ) :=
    lt_trans (racePrice_lt_capC3a (93/20) (by norm_num)) (by norm_num [C3a])
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
  rw [← D.attained]
  linarith only [hT, hh, hcharge, hM]

end

end StochasticToDeterministicLatents.General
