-- Original work by Alexis Olson, Apache-2.0 (see NOTICE), October 2026, written for this repository
-- (namespace NaturalLatents.General); not part of the earlier repository
-- github.com/AlexisOlson/stochastic-to-deterministic-latents.
-- This file builds on and cites the definitions of DLorell/stoch_to_det (Apache-2.0).
import NaturalLatents.Upstream.Functionals
import NaturalLatents.Upstream.SharedRace.Definitions

/-!
# Natural-log units

`nats` is the conversion from the upstream bit-valued information quantities.
The arithmetic and order lemmas let the General development use natural-log units,
with `bits_of_nats` converting the connected optimum bound once at its boundary.

## Attribution

Original work by Alexis Olson, October 2026, written for this repository; not part of the
earlier repository github.com/AlexisOlson/stochastic-to-deterministic-latents.
This file builds on and cites the definitions of
[`DLorell/stoch_to_det`](https://github.com/DLorell/stoch_to_det), Apache-2.0.
-/

namespace NaturalLatents.General

noncomputable section

/-- Convert a bit-valued quantity to natural-log units. -/
def nats (x : ℝ) : ℝ := Real.log 2 * x

lemma nats_add (x y : ℝ) : nats (x + y) = nats x + nats y := mul_add _ _ _

lemma nats_mul_left (c x : ℝ) : nats (c * x) = c * nats x := mul_left_comm _ _ _

lemma nats_le_nats_iff {x y : ℝ} : nats x ≤ nats y ↔ x ≤ y :=
  mul_le_mul_iff_of_pos_left (Real.log_pos one_lt_two)

lemma nats_nonneg_iff {x : ℝ} : 0 ≤ nats x ↔ 0 ≤ x :=
  mul_nonneg_iff_of_pos_left (Real.log_pos one_lt_two)

lemma bits_of_nats {x y c : ℝ} (h : nats x ≤ c * nats y) : x ≤ c * y :=
  nats_le_nats_iff.mp (by simpa only [nats_mul_left] using h)

variable {α β γ δ : Type*} [Fintype α]

def HNat (m : α → ℝ) : ℝ := nats (stoch_to_det.H m)
lemma HNat_eq (m : α → ℝ) : HNat m = nats (stoch_to_det.H m) := rfl

variable [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

def condHNat (f : α → β) (g : α → γ) (m : α → ℝ) : ℝ :=
  nats (stoch_to_det.condH f g m)
lemma condHNat_eq (f : α → β) (g : α → γ) (m : α → ℝ) :
    condHNat f g m = nats (stoch_to_det.condH f g m) := rfl

def MINat (f : α → β) (g : α → γ) (m : α → ℝ) : ℝ := nats (stoch_to_det.MI f g m)
lemma MINat_eq (f : α → β) (g : α → γ) (m : α → ℝ) :
    MINat f g m = nats (stoch_to_det.MI f g m) := rfl

variable [Fintype δ] [DecidableEq δ]

def condMINat (f : α → β) (g : α → γ) (h : α → δ) (m : α → ℝ) : ℝ :=
  nats (stoch_to_det.condMI f g h m)
lemma condMINat_eq (f : α → β) (g : α → γ) (h : α → δ) (m : α → ℝ) :
    condMINat f g h m = nats (stoch_to_det.condMI f g h m) := rfl

variable [DecidableEq α]

def IxyNat (p : α × β → ℝ) : ℝ := nats (stoch_to_det.Ixy p)
lemma IxyNat_eq (p : α × β → ℝ) : IxyNat p = nats (stoch_to_det.Ixy p) := rfl

def detScoreNat (p : α × β → ℝ) (A : α × β → γ) : ℝ := nats (stoch_to_det.detScore p A)
lemma detScoreNat_eq (p : α × β → ℝ) (A : α × β → γ) :
    detScoreNat p A = nats (stoch_to_det.detScore p A) := rfl

def sharedRaceEntropyNat {Ω : Type*} {κ : Type} [Fintype Ω] [Fintype κ]
    [DecidableEq κ] [Nonempty κ] (μ : Ω → ℝ) (r : Ω → κ → ℝ) : ℝ :=
  nats (stoch_to_det.SharedRace.sharedRaceEntropy μ r)
lemma sharedRaceEntropyNat_eq {Ω : Type*} {κ : Type} [Fintype Ω] [Fintype κ]
    [DecidableEq κ] [Nonempty κ] (μ : Ω → ℝ) (r : Ω → κ → ℝ) :
    sharedRaceEntropyNat μ r = nats (stoch_to_det.SharedRace.sharedRaceEntropy μ r) := rfl

end

end NaturalLatents.General
