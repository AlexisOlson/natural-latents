-- Original work by Alexis Olson, Apache-2.0 (see NOTICE), first developed in
-- github.com/AlexisOlson/stochastic-to-deterministic-latents; reorganised for this repository
-- (namespace NaturalLatents.General, declarations renamed, unused material removed).
-- This file builds on and cites the definitions of DLorell/stoch_to_det (Apache-2.0).
import NaturalLatents.General.Setup
import NaturalLatents.General.Ledger
import NaturalLatents.General.ExponentialRace
import NaturalLatents.General.Cap
import NaturalLatents.General.Affinity
import NaturalLatents.General.Payment
import NaturalLatents.General.PairCharge

/-!
# The bound for connected laws

Assembling the results of the earlier modules at the exponent `a = 211/45`, with
`beta = 23 / 250` and `gamma = 7/60`, gives in nats

    TNat p ≤ (13999/2000) * tauNat p.

The theorem `T_le_of_connected` combines `exists_setup_of_connected`, the exponential race,
the cap on its Gamma-form price, the pair charge, the mismatch payment, and the ledger inequality.

The cap at `211/45` lies below `u = 3941/20000`. The budget coefficients are
`C_M = 1 + 3u(1 + 2β)/γ = 218729/31250` and
`C_B = (3a - 1)/2 + 3uβ/γ = 5249623/750000`, both at most `13999/2000`.

## Attribution

Original work by Alexis Olson, first developed in
github.com/AlexisOlson/stochastic-to-deterministic-latents.
This file builds on and cites the definitions of
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.

The method is powered-reference race coding with a coordinate ledger, from
[pull request #6](https://github.com/DLorell/stoch_to_det/pull/6) by Jeremy Gillen.
-/

namespace NaturalLatents.General

noncomputable section

open scoped BigOperators
open MeasureTheory ProbabilityTheory

variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- `TNat p ≤ (13999/2000) * tauNat p`, in nats, for a law with connected support. -/
theorem T_le_of_connected {p : Law X Y} (hp : stoch_to_det.IsPMF p)
    (hconn : stoch_to_det.IsConnected (stoch_to_det.support p)) :
    TNat p ≤ (13999/2000 : ℝ)*tauNat p := by
  obtain ⟨D⟩ := exists_setup_of_connected hp hconn
  obtain ⟨F, hF⟩ := exists_race hp D.L D.rows_pos (211/45) (by norm_num)
  have hT := T_le_ledger hp D.L F
  have hj : gammaPrice (211/45) < (3941/20000 : ℝ) :=
    lt_trans (racePrice_lt_capC3b (211/45) (by norm_num)) (by norm_num [gammaPriceCap])
  have hd : 0 ≤ mismatch D.L :=
    stoch_to_det.SharedRace.categoricalMismatch_nonneg_of_support hp
      (fun z hz => race_posterior_isPMF hp D.L z hz)
  have hjd := mul_le_mul_of_nonneg_right hj.le hd
  have hh : seedEntropy F ≤ (211/45 : ℝ) * redundancy D.L + 2 * (3941/20000 : ℝ) * mismatch D.L := by
    linarith only [hF, hjd]
  have haffinity : ∀ i j : D.L.ι, i ≠ j → AffinityBound (D.L.comp i) (D.L.comp j) := by
    intro i j hij
    have hpair : CommonSupportPair (stoch_to_det.support p) D.w
        (D.L.comp i) (D.L.comp j) :=
      ⟨D.feasible, D.contact i, D.contact j, D.positive i, D.positive j,
        fun heq => hij (D.distinct heq)⟩
    exact affinity_bound hpair (contact_moments hpair)
  have hcharge := mismatch_payment hp D (23/250) (7/60) (by norm_num) (by norm_num)
    haffinity (replica_budget hp D.L) pairCharge_C
  have hM : 0 ≤ mediation D.L :=
    nats_nonneg_iff.mpr
      (stoch_to_det.condMI_nonneg D.L.joint_isPMF
        (fun w => w.2.1) (fun w => w.2.2) (fun w => w.1))
  have hB : 0 ≤ redundancy D.L :=
    nats_nonneg_iff.mpr
      (add_nonneg
        (stoch_to_det.condMI_nonneg D.L.joint_isPMF
          (fun w => w.1) (fun w => w.2.1) (fun w => w.2.2))
        (stoch_to_det.condMI_nonneg D.L.joint_isPMF
          (fun w => w.1) (fun w => w.2.2) (fun w => w.2.1)))
  rw [← D.attained]
  linarith only [hT, hh, hcharge, hM, hB]

end

end NaturalLatents.General
