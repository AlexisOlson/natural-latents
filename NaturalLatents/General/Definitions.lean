-- Original work by Alexis Olson, Apache-2.0 (see NOTICE), October 2026, first written on an unpublished branch of
-- github.com/AlexisOlson/stochastic-to-deterministic-latents; reorganised for this repository
-- (namespace NaturalLatents.General, declarations renamed, unused material removed).
-- This file builds on and cites the definitions of DLorell/stoch_to_det (Apache-2.0).
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Probability.Independence.InfinitePi
import NaturalLatents.General.Nats
import NaturalLatents.Upstream.Connected
import NaturalLatents.Upstream.ContactInformation
import NaturalLatents.Upstream.Floor
import NaturalLatents.Upstream.Quotient
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import NaturalLatents.Upstream.CoordinateRace
import NaturalLatents.Upstream.TableBoundProof

/-!
# Laws, budgets, contact data and race prices in nats

This module fixes the vocabulary of the bound `TNat p ≤ (13999/2000) tauNat p` for an arbitrary finite
law `p` on `X × Y`. The budgets, contact estimates and race prices use nats: `TNat` and `tauNat` are the
corresponding bit-valued `stoch_to_det` functionals converted by `nats`. The connected bound
returns to bits once before `extension_of_connected`.

* **Budgets of a latent `L`.** `mediation L = I(X;Y | Λ)` and
  `redundancy L = I(Λ;X | Y) + I(Λ;Y | X)`, with mutual information in nats, so that
  `mediation L + redundancy L` is the stochastic score in nats (`mediation_add_redundancy_eq_score`). `posterior L i z` is the
  posterior of component `i` at the cell `z`, `mismatch L` is its categorical mismatch, and `replicaBudget L`
  is the replica budget of two posterior draws. `score_nats` proves the score identity
  `mediation L + redundancy L = psiNat p + ∑ prior i * negPhiNat (comp i)`. Here `negPhiNat` is the negation of
  `stoch_to_det.Phi`, while `psiNat` is `stoch_to_det.Psi`, both converted to nats.
* **Contact data.** For two contacts `P`, `R` of a common feasible kernel, `rootRatioX` and `rootRatioY` are the
  cube-root secants shifted by one, `expect` is the expectation under `P`, and `defectX`, `defectY`, `separation`, `quarticMoment`
  and `quarticRatio` are the moments that the contact relations constrain. `separationPrice t = -2 log (affinityPoly t)` is
  the separation price, `AffinityBound` compares it with the marginal Bhattacharyya
  affinities, and `HasPairCharge` is the pair-charge statement on a domain of pairs.
* **Setups.** `CommonSetup` is an attaining latent with a feasible kernel, distinct positive
  contacts of full common support, and positive posterior rows.
* **Seeded families.** `CalibratedSeededFamily` is a law on complete maps `X × Y → ι` whose
  one-cell marginals are the posteriors, and `seedEntropy` is the seed-averaged conditional entropy of
  the fixed maps.
* **Race prices.** `gammaPrice a` is the Gamma form of the exponential-race price, `gammaPriceET a` its
  exponential-time form `∫ logGain a t dt` with `logGain a t = expect log (1 + tailSum a t)`, and `gammaPriceCap` is
  the explicit three-term cap on `gammaPrice a`.

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

abbrev Law (X Y : Type) := X × Y → ℝ

/-- Upstream functionals converted to nats; their optimization domains are unchanged. -/
def tauNat (p : Law X Y) : ℝ := nats (stoch_to_det.tau p)
def TNat (p : Law X Y) : ℝ := nats (stoch_to_det.T p)

/-- The two conditional-mutual-information budgets for a finite latent. -/
def mediation {p : Law X Y} (L : stoch_to_det.Latent p) : ℝ :=
  condMINat (fun w => w.2.1) (fun w => w.2.2)
    (fun w => w.1) L.joint

def redundancy {p : Law X Y} (L : stoch_to_det.Latent p) : ℝ :=
  nats (stoch_to_det.condMI (fun w => w.1) (fun w => w.2.1)
    (fun w => w.2.2) L.joint + stoch_to_det.condMI (fun w => w.1)
    (fun w => w.2.2) (fun w => w.2.1) L.joint)

def posterior {p : Law X Y} (L : stoch_to_det.Latent p) (i : L.ι) (z : X × Y) : ℝ :=
  L.prior i * L.comp i z / p z

omit [DecidableEq X] [DecidableEq Y] in
lemma mul_posterior_eq_joint {p : Law X Y} (L : stoch_to_det.Latent p) (i : L.ι) (z : X × Y) :
    p z * posterior L i z = L.joint (i, z) := by
  unfold posterior stoch_to_det.Latent.joint
  by_cases hz : p z = 0
  · have hle : L.prior i * L.comp i z ≤ ∑ v, L.prior v * L.comp v z :=
      Finset.single_le_sum
        (fun v _ => mul_nonneg (L.prior_isPMF.nonneg v) ((L.comp_isPMF v).nonneg z))
        (Finset.mem_univ i)
    rw [L.mixture z, hz] at hle
    have hzero : L.prior i * L.comp i z = 0 :=
      le_antisymm hle
        (mul_nonneg (L.prior_isPMF.nonneg i) ((L.comp_isPMF i).nonneg z))
    simp [hz, hzero]
  · field_simp

lemma mediation_add_redundancy_eq_score {p : Law X Y} (L : stoch_to_det.Latent p) :
    mediation L + redundancy L = nats L.score := by
  unfold mediation redundancy condMINat nats stoch_to_det.Latent.score
  ring

/-- `negPhiNat` negates `stoch_to_det.Phi`; `psiNat` converts the law functional `stoch_to_det.Psi` to nats. -/
def negPhiNat (q : Law X Y) : ℝ := -(nats (stoch_to_det.Phi q))
def psiNat (p : Law X Y) : ℝ := nats (stoch_to_det.Psi p)
/-- The score identity in nats: `mediation L + redundancy L = psiNat p + ∑ i, prior i * negPhiNat (comp i)` for every latent `L` of a
probability law `p`; this is the corresponding bit-valued identity converted by `nats`. -/
lemma score_nats (p : Law X Y) (hp : stoch_to_det.IsPMF p) (L : stoch_to_det.Latent p) :
    mediation L + redundancy L = psiNat p + ∑ i, L.prior i * negPhiNat (L.comp i) := by
  rw [mediation_add_redundancy_eq_score, L.score_eq hp]
  simp only [psiNat, negPhiNat, nats, mul_sub, Finset.mul_sum, mul_neg, Finset.sum_neg_distrib]
  rw [sub_eq_add_neg]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Positive exactly on S when combined with the supported condition of `stoch_to_det.IsContact` condition. -/
def PositiveOn (S : Finset (X × Y)) (q : Law X Y) : Prop := ∀ z ∈ S, 0 < q z

def xSupport (S : Finset (X × Y)) : Finset X := S.image Prod.fst
def ySupport (S : Finset (X × Y)) : Finset Y := S.image Prod.snd
def marginalProduct (P : Law X Y) (z : X × Y) : ℝ := stoch_to_det.mX P z.1 * stoch_to_det.mY P z.2


def CommonSupportPair (S : Finset (X × Y)) (w P R : Law X Y) : Prop :=
  stoch_to_det.Feasible S w ∧ stoch_to_det.IsContact S w P ∧ stoch_to_det.IsContact S w R ∧
    PositiveOn S P ∧ PositiveOn S R ∧ P ≠ R

/-- Cube-root secants, retaining the arbitrary convention at null marginals. -/
def rootRatioX (P R : Law X Y) (x : X) : ℝ := stoch_to_det.contactSecantX P R x + 1
def rootRatioY (P R : Law X Y) (y : Y) : ℝ := stoch_to_det.contactSecantY P R y + 1
omit [DecidableEq Y] in
lemma rootRatioX_eq_cbrt (P R : Law X Y) (x : X) :
    rootRatioX P R x = (stoch_to_det.mX R x / stoch_to_det.mX P x) ^ ((1 : ℝ) / 3) := by
  simp only [rootRatioX, stoch_to_det.contactSecantX, sub_add_cancel]
omit [DecidableEq X] in
lemma rootRatioY_eq_cbrt (P R : Law X Y) (y : Y) :
    rootRatioY P R y = (stoch_to_det.mY R y / stoch_to_det.mY P y) ^ ((1 : ℝ) / 3) := by
  simp only [rootRatioY, stoch_to_det.contactSecantY, sub_add_cancel]

def expect (P : Law X Y) (F : X × Y → ℝ) : ℝ := ∑ z, P z * F z

def defectX (P R : Law X Y) : ℝ := 1 - expect P (fun z => rootRatioX P R z.1)
def defectY (P R : Law X Y) : ℝ := 1 - expect P (fun z => rootRatioY P R z.2)
def separation (P R : Law X Y) : ℝ := defectX P R + defectY P R
def quarticMoment (P R : Law X Y) : ℝ := expect P (fun z => (stoch_to_det.contactSecantX P R z.1)^2 * (stoch_to_det.contactSecantY P R z.2)^2)
def quarticRatio (P R : Law X Y) : ℝ := quarticMoment P R / (separation P R)^2

def affinityPoly (t : ℝ) : ℝ := 1 - 9 * t / 16 + 3 * t^2 / 64
lemma affinityPoly_pos (t : ℝ) (ht : t ≤ 2) : 0 < affinityPoly t := by
  have hp : 0 ≤ (2 - t) * (10 - t) :=
    mul_nonneg (by linarith) (by linarith)
  unfold affinityPoly
  nlinarith
/-- stoch_to_det.IsContact separation price, distinct from the law functional `stoch_to_det.Psi`. -/
def separationPrice (t : ℝ) : ℝ := -2 * Real.log (affinityPoly t)
def HasPairCharge (domain : Finset (X × Y) → Law X Y → Law X Y → Law X Y → Prop) (beta gamma : ℝ) : Prop :=
  ∀ S w P R, domain S w P R → gamma ≤ (stoch_to_det.Knat P + stoch_to_det.Knat R) / 2 + beta * separationPrice (separation P R)

/-- The moment relations of two contacts, with conditional equalities only on used marginal symbols. -/
structure ContactMoments (S : Finset (X × Y)) (P R : Law X Y) : Prop where
  cond_rootRatioY_square : ∀ x ∈ xSupport S,
    (∑ y, P (x,y) * (rootRatioY P R y)^2) / stoch_to_det.mX P x = rootRatioX P R x
  cond_rootRatioX_square : ∀ y ∈ ySupport S,
    (∑ x, P (x,y) * (rootRatioX P R x)^2) / stoch_to_det.mY P y = rootRatioY P R y
  rootRatioX_cube : expect P (fun z => (rootRatioX P R z.1)^3) = 1
  rootRatioY_cube : expect P (fun z => (rootRatioY P R z.2)^3) = 1
  rootRatioX_square : expect P (fun z => (rootRatioX P R z.1)^2) = expect P (fun z => rootRatioY P R z.2)
  rootRatioY_square : expect P (fun z => (rootRatioY P R z.2)^2) = expect P (fun z => rootRatioX P R z.1)
  separation_pos : 0 < separation P R
  separation_lt_two : separation P R < 2
  secantX_square : expect P (fun z => (stoch_to_det.contactSecantX P R z.1)^2) = 2 * defectX P R - defectY P R
  secantY_square : expect P (fun z => (stoch_to_det.contactSecantY P R z.2)^2) = 2 * defectY P R - defectX P R
  quartic_identity : quarticMoment P R = 4 * expect P (fun z => stoch_to_det.contactSecantX P R z.1 * stoch_to_det.contactSecantY P R z.2) - separation P R
  hessian : ∀ (F : X → ℝ) (G : Y → ℝ),
    expect P (fun z => F z.1) = 0 → expect P (fun z => G z.2) = 0 →
    4 * expect P (fun z => F z.1 * G z.2) ≤ expect P (fun z => (F z.1)^2) + expect P (fun z => (G z.2)^2)
  quarticMoment_bound : quarticMoment P R ≤ 6 * defectX P R * defectY P R - (separation P R)^2
  scalar_bound : 6 * defectX P R * defectY P R - (separation P R)^2 ≤ (separation P R)^2 / 2

structure CommonSetup (p : Law X Y) where
  L : stoch_to_det.Latent p
  w : Law X Y
  feasible : stoch_to_det.Feasible (stoch_to_det.support p) w
  attained : mediation L + redundancy L = tauNat p
  prior_pos : ∀ i, 0 < L.prior i
  distinct : Function.Injective L.comp
  contact : ∀ i, stoch_to_det.IsContact (stoch_to_det.support p) w (L.comp i)
  positive : ∀ i, PositiveOn (stoch_to_det.support p) (L.comp i)
  rows_pos : ∀ z ∈ stoch_to_det.support p, ∀ i, 0 < posterior L i z

/-- A law on complete maps is the finite-valued seed F. Continuous seeds push forward to maps.
Calibration is support-local. seedSourceJoint is explicitly the independent product law. -/
structure CalibratedSeededFamily {p : Law X Y} (L : stoch_to_det.Latent p) where
  seedLaw : (X × Y → L.ι) → ℝ
  seed_isPMF : stoch_to_det.IsPMF seedLaw
  calibrated : ∀ z ∈ stoch_to_det.support p, ∀ i,
    (∑ F, if F z = i then seedLaw F else 0) = posterior L i z

def seedSourceJoint {p : Law X Y} {L : stoch_to_det.Latent p} (F : CalibratedSeededFamily L)
    (w : (X × Y → L.ι) × (X × Y)) : ℝ := F.seedLaw w.1 * p w.2

/-- Fixed-map conditional entropies averaged over the seed, never H of an averaged label. -/
def seedEntropy {p : Law X Y} {L : stoch_to_det.Latent p} (F : CalibratedSeededFamily L) : ℝ :=
  ∑ A, F.seedLaw A * (condHNat A Prod.fst p +
    condHNat A Prod.snd p)

def mismatch {p : Law X Y} (L : stoch_to_det.Latent p) : ℝ :=
  stoch_to_det.SharedRace.categoricalMismatch p (fun z i => posterior L i z)
/-- Two posterior draws independent given Z. Upstream Seed.replicaLaw instead has three draws. -/
def replicaJoint {p : Law X Y} (L : stoch_to_det.Latent p) : L.ι × L.ι × (X × Y) → ℝ :=
  fun w => p w.2.2 * posterior L w.1 w.2.2 * posterior L w.2.1 w.2.2

def pairMass {p : Law X Y} (L : stoch_to_det.Latent p) (i j : L.ι) : ℝ :=
  ∑ z, p z * posterior L i z * posterior L j z

/-- Total replica budget including diagonal pairs, in nats. -/
def replicaBudget {p : Law X Y} (L : stoch_to_det.Latent p) : ℝ :=
  nats (stoch_to_det.condMI (fun w => w.2.1) (fun w => w.2.2.1)
    (fun w => w.1) (replicaJoint L) + stoch_to_det.condMI (fun w => w.2.1)
    (fun w => w.2.2.2) (fun w => w.1) (replicaJoint L))

def AffinityBound (P R : Law X Y) : Prop :=
  separationPrice (separation P R) ≤ -Real.log (stoch_to_det.BC (stoch_to_det.mX P) (stoch_to_det.mX R)) - Real.log (stoch_to_det.BC (stoch_to_det.mY P) (stoch_to_det.mY R))

/-- Gamma-form race price, distinct from quarticRatio. -/
def gammaPrice (a : ℝ) : ℝ := a * Real.log (Real.Gamma (1 - 1/a)) - Real.eulerMascheroniConstant

def expOne : Measure ℝ := expMeasure 1
def arrivalLaw : Measure (ℕ → ℝ) := by
  letI : IsProbabilityMeasure expOne := isProbabilityMeasure_expMeasure (by norm_num)
  exact Measure.infinitePi (fun _ : ℕ => expOne)

/-- n=1 is the first arrivalTime, the first positive partial sum. -/
def arrivalTime (increments : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, increments k

/-- The tail sum `t^a * ∑ (t + T_{n+1})^(-a)`. The real `tsum` is totalized on exceptional sequences;
finiteness and log-integrability for `a > 1` are proved where used, not assumed here. -/
def tailSum (a t : ℝ) (increments : ℕ → ℝ) : ℝ :=
  t^a * ∑' n : ℕ, (t + arrivalTime increments (n+1)) ^ (-a)

def logGain (a t : ℝ) : ℝ := ∫ increments, Real.log (1 + tailSum a t increments) ∂arrivalLaw
/-- The outer T~Exp(1) is independent of the increments whose partial sums are T_n. -/
def gammaPriceET (a : ℝ) : ℝ := ∫ t, logGain a t ∂expOne

/-- The three-term cap on the Gamma-form race price `gammaPrice a`. -/
def gammaPriceCap (a : ℝ) : ℝ := 533/(648*a) + 241/(600*a^2) + 6503/(24000*a^2*(a-1))
end

end NaturalLatents.General
