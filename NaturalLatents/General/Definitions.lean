-- Adapted from the author's earlier repository (StochasticToDeterministicLatents);
-- modified: module paths renamed; declarations unused by the main theorems removed.
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Probability.Independence.InfinitePi
import NaturalLatents.Upstream.Connected
import NaturalLatents.Upstream.ContactInformation
import NaturalLatents.Upstream.ContinuousMismatch
import NaturalLatents.Upstream.CoordinateRace
import NaturalLatents.Upstream.TableBoundProof

/-!
# Laws, budgets, contact data and race prices in nats

This module fixes the vocabulary of the bound `T p ≤ (2789/400) tau p` for an arbitrary finite
law `p` on `X × Y`. Everything inside the `General` tree is measured in nats: `T`, `tau` and
`Hnat` are the upstream bit-valued functionals multiplied by `Real.log 2`, and the factor
cancels at the endpoint in `General.lean`.

* **Budgets of a latent `L`.** `M L = I(X;Y | Λ)` and `B L = I(Λ;X | Y) + I(Λ;Y | X)`, so that
  `M L + B L` is the stochastic score in nats (`budgets_eq_score`). `post L i z` is the
  posterior of component `i` at the cell `z`, `d L` is its categorical mismatch, and `K L`
  is the replica budget of two posterior draws. `CostIdentity` states the score identity
  `M L + B L = c p + ∑ prior i * phi (comp i)`, with `phi` minus upstream's `Φ` and `c`
  upstream's `Ψ`, both in nats.
* **Contact data.** For two contacts `P`, `R` of a common feasible kernel, `f` and `g` are the
  cube-root secants shifted by one, `E` is the expectation under `P`, and `A0`, `B0`, `s`, `J`
  and `contactj` are the moments that the contact relations constrain. `Psi t = -2 log (b t)` is
  the separation price, `AffinityBound` compares it with the marginal Bhattacharyya
  affinities, and `PC` is the pair-charge statement on a domain of pairs.
* **Setups.** `CommonSetup` is an attaining latent with a feasible kernel, distinct positive
  contacts of full common support and positive posterior rows; `GeneralSetup` replaces the
  common support by localization on graph components of the support.
* **Seeded families.** `CalibratedSeededFamily` is a law on complete maps `X × Y → ι` whose
  one-cell marginals are the posteriors, and `h` is the seed-averaged conditional entropy of
  the fixed maps.
* **Race prices.** `j a` is the Gamma form of the exponential-race price, `jET a` its
  exponential-time form `∫ m a t dt` with `m a t = E log (1 + Vtail a t)`, and `C3a`, `C4b` are
  the three-term and four-term caps on them.

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

abbrev Law (X Y : Type) := X × Y → ℝ
abbrev FiniteLatent (p : Law X Y) := stoch_to_det.Latent p
abbrev FeasibleKernel (S : Finset (X × Y)) (w : Law X Y) : Prop := stoch_to_det.Feasible S w
abbrev Contact (S : Finset (X × Y)) (w q : Law X Y) : Prop := stoch_to_det.IsContact S w q

/-- Upstream functionals converted to nats; their optimization domains are unchanged. -/
def tau (p : Law X Y) : ℝ := Real.log 2 * stoch_to_det.tau p
def T (p : Law X Y) : ℝ := Real.log 2 * stoch_to_det.T p
lemma tau_eq_upstream (p : Law X Y) : tau p = Real.log 2 * stoch_to_det.tau p := rfl
lemma T_eq_upstream (p : Law X Y) : T p = Real.log 2 * stoch_to_det.T p := rfl

/-- The two CMI budgets for an arbitrary upstream latent. -/
def M {p : Law X Y} (L : FiniteLatent p) : ℝ :=
  Real.log 2 * stoch_to_det.condMI (fun w => w.2.1) (fun w => w.2.2)
    (fun w => w.1) L.joint

def B {p : Law X Y} (L : FiniteLatent p) : ℝ :=
  Real.log 2 * (stoch_to_det.condMI (fun w => w.1) (fun w => w.2.1)
    (fun w => w.2.2) L.joint + stoch_to_det.condMI (fun w => w.1)
    (fun w => w.2.2) (fun w => w.2.1) L.joint)

def post {p : Law X Y} (L : FiniteLatent p) (i : L.ι) (z : X × Y) : ℝ :=
  L.prior i * L.comp i z / p z

lemma budgets_eq_score {p : Law X Y} (L : FiniteLatent p) :
    M L + B L = Real.log 2 * L.score := by
  unfold M B stoch_to_det.Latent.score
  ring

/-- phi is minus upstream Phi; c is upstream's law-only Psi. -/
def phi (q : Law X Y) : ℝ := -(Real.log 2 * stoch_to_det.Phi q)
def c (p : Law X Y) : ℝ := Real.log 2 * stoch_to_det.Psi p
/-- The score identity in nats: `M L + B L = c p + ∑ i, prior i * phi (comp i)` for every latent `L` of a
probability law `p`; the upstream identity multiplied by `Real.log 2`. -/
def CostIdentity : Prop := ∀ (p : Law X Y), stoch_to_det.IsPMF p →
  ∀ L : FiniteLatent p, M L + B L = c p + ∑ i, L.prior i * phi (L.comp i)

lemma cost_identity : CostIdentity (X := X) (Y := Y) := by
  intro p hp L
  rw [budgets_eq_score, L.score_eq hp]
  simp only [c, phi, mul_sub, Finset.mul_sum, mul_neg, Finset.sum_neg_distrib]
  rw [sub_eq_add_neg]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Positive exactly on S when combined with Contact's Supported condition. -/
def PositiveOn (S : Finset (X × Y)) (q : Law X Y) : Prop := ∀ z ∈ S, 0 < q z

def XSupport (S : Finset (X × Y)) : Finset X := S.image Prod.fst
def YSupport (S : Finset (X × Y)) : Finset Y := S.image Prod.snd
/-- Q and mixture/chi-square sums use this rectangle, including its holes. -/
def MarginalRectangle (S : Finset (X × Y)) : Finset (X × Y) := XSupport S ×ˢ YSupport S

def productLaw (P : Law X Y) (z : X × Y) : ℝ := stoch_to_det.mX P z.1 * stoch_to_det.mY P z.2

abbrev PairDomain := Finset (X × Y) → Law X Y → Law X Y → Law X Y → Prop

def CommonSupportPairs (S : Finset (X × Y)) (w P R : Law X Y) : Prop :=
  FeasibleKernel S w ∧ Contact S w P ∧ Contact S w R ∧
    PositiveOn S P ∧ PositiveOn S R ∧ P ≠ R

/-- Reuse upstream cube-root secants, including its irrelevant null-marginal convention. -/
abbrev U (P R : Law X Y) := stoch_to_det.contactSecantX P R
abbrev V (P R : Law X Y) := stoch_to_det.contactSecantY P R
def f (P R : Law X Y) (x : X) : ℝ := U P R x + 1
def g (P R : Law X Y) (y : Y) : ℝ := V P R y + 1
omit [DecidableEq Y] in
lemma f_eq_cubeRoot (P R : Law X Y) (x : X) :
    f P R x = (stoch_to_det.mX R x / stoch_to_det.mX P x) ^ ((1 : ℝ) / 3) := by
  simp only [f, U, stoch_to_det.contactSecantX, sub_add_cancel]
omit [DecidableEq X] in
lemma g_eq_cubeRoot (P R : Law X Y) (y : Y) :
    g P R y = (stoch_to_det.mY R y / stoch_to_det.mY P y) ^ ((1 : ℝ) / 3) := by
  simp only [g, V, stoch_to_det.contactSecantY, sub_add_cancel]

def E (P : Law X Y) (F : X × Y → ℝ) : ℝ := ∑ z, P z * F z

def A0 (P R : Law X Y) : ℝ := 1 - E P (fun z => f P R z.1)
def B0 (P R : Law X Y) : ℝ := 1 - E P (fun z => g P R z.2)
def s (P R : Law X Y) : ℝ := 2 - E P (fun z => f P R z.1) - E P (fun z => g P R z.2)
def J (P R : Law X Y) : ℝ := E P (fun z => (U P R z.1)^2 * (V P R z.2)^2)
def contactj (P R : Law X Y) : ℝ := J P R / (s P R)^2

def b (t : ℝ) : ℝ := 1 - 9 * t / 16 + 3 * t^2 / 64
/-- Contact separation price, distinct from upstream's law-only Psi. -/
def Psi (t : ℝ) : ℝ := -2 * Real.log (b t)
abbrev BC_X (P R : Law X Y) := stoch_to_det.BC (stoch_to_det.mX P) (stoch_to_det.mX R)
abbrev BC_Y (P R : Law X Y) := stoch_to_det.BC (stoch_to_det.mY P) (stoch_to_det.mY R)
abbrev I (P : Law X Y) := stoch_to_det.Knat P
lemma I_eq_upstream_bits {P : Law X Y} (hP : stoch_to_det.IsPMF P) :
    I P = Real.log 2 * stoch_to_det.Ixy P := stoch_to_det.Knat_eq_log_two_mul_Ixy hP

def PC (domain : PairDomain (X := X) (Y := Y)) (beta gamma : ℝ) : Prop :=
  ∀ S w P R, domain S w P R → gamma ≤ (I P + I R) / 2 + beta * Psi (s P R)

/-- The moment relations of two contacts, with conditional equalities only on used marginal symbols. -/
structure ContactMoments (S : Finset (X × Y)) (P R : Law X Y) : Prop where
  ratio : ∀ z ∈ S, R z / P z = (f P R z.1)^2 * (g P R z.2)^2
  cond_g2 : ∀ x ∈ XSupport S,
    (∑ y, P (x,y) * (g P R y)^2) / stoch_to_det.mX P x = f P R x
  cond_f2 : ∀ y ∈ YSupport S,
    (∑ x, P (x,y) * (f P R x)^2) / stoch_to_det.mY P y = g P R y
  f3 : E P (fun z => (f P R z.1)^3) = 1
  g3 : E P (fun z => (g P R z.2)^3) = 1
  f2 : E P (fun z => (f P R z.1)^2) = E P (fun z => g P R z.2)
  g2 : E P (fun z => (g P R z.2)^2) = E P (fun z => f P R z.1)
  s_pos : 0 < s P R
  s_lt_two : s P R < 2
  U2 : E P (fun z => (U P R z.1)^2) = 2 * A0 P R - B0 P R
  V2 : E P (fun z => (V P R z.2)^2) = 2 * B0 P R - A0 P R
  quartic : J P R = 4 * E P (fun z => U P R z.1 * V P R z.2) - s P R
  hessian : ∀ (F : X → ℝ) (G : Y → ℝ),
    E P (fun z => F z.1) = 0 → E P (fun z => G z.2) = 0 →
    4 * E P (fun z => F z.1 * G z.2) ≤ E P (fun z => (F z.1)^2) + E P (fun z => (G z.2)^2)
  J_bound : J P R ≤ 6 * A0 P R * B0 P R - (s P R)^2
  scalar_bound : 6 * A0 P R * B0 P R - (s P R)^2 ≤ (s P R)^2 / 2

structure CommonSetup (p : Law X Y) where
  L : FiniteLatent p
  w : Law X Y
  feasible : FeasibleKernel (stoch_to_det.support p) w
  kernel_zero : stoch_to_det.Supported (stoch_to_det.support p) w
  attained : M L + B L = tau p
  prior_pos : ∀ i, 0 < L.prior i
  distinct : Function.Injective L.comp
  contact : ∀ i, Contact (stoch_to_det.support p) w (L.comp i)
  positive : ∀ i, PositiveOn (stoch_to_det.support p) (L.comp i)
  rows_pos : ∀ z ∈ stoch_to_det.support p, ∀ i, 0 < post L i z

/-- A law on complete maps is the finite-valued seed F. Continuous seeds push forward to maps.
Calibration is support-local. seedSourceJoint is explicitly the independent product law. -/
structure CalibratedSeededFamily {p : Law X Y} (L : FiniteLatent p) where
  seedLaw : (X × Y → L.ι) → ℝ
  seed_isPMF : stoch_to_det.IsPMF seedLaw
  calibrated : ∀ z ∈ stoch_to_det.support p, ∀ i,
    (∑ F, if F z = i then seedLaw F else 0) = post L i z

def seedSourceJoint {p : Law X Y} {L : FiniteLatent p} (F : CalibratedSeededFamily L)
    (w : (X × Y → L.ι) × (X × Y)) : ℝ := F.seedLaw w.1 * p w.2

/-- Fixed-map conditional entropies averaged over the seed, never H of an averaged label. -/
def h {p : Law X Y} {L : FiniteLatent p} (F : CalibratedSeededFamily L) : ℝ :=
  ∑ A, F.seedLaw A * (Real.log 2 * (stoch_to_det.condH A Prod.fst p +
    stoch_to_det.condH A Prod.snd p))

def d {p : Law X Y} (L : FiniteLatent p) : ℝ :=
  stoch_to_det.SharedRace.categoricalMismatch p (fun z i => post L i z)
/-- Two posterior draws independent given Z. Upstream Seed.replicaLaw instead has three draws. -/
def replicaJoint {p : Law X Y} (L : FiniteLatent p) : L.ι × L.ι × (X × Y) → ℝ :=
  fun w => p w.2.2 * post L w.1 w.2.2 * post L w.2.1 w.2.2

def mu {p : Law X Y} (L : FiniteLatent p) (i j : L.ι) : ℝ :=
  ∑ z, p z * post L i z * post L j z

/-- Total replica budget including diagonal pairs, in nats. -/
def K {p : Law X Y} (L : FiniteLatent p) : ℝ :=
  Real.log 2 * (stoch_to_det.condMI (fun w => w.2.1) (fun w => w.2.2.1)
    (fun w => w.1) (replicaJoint L) + stoch_to_det.condMI (fun w => w.2.1)
    (fun w => w.2.2.2) (fun w => w.1) (replicaJoint L))

def AffinityBound (P R : Law X Y) : Prop :=
  Psi (s P R) ≤ -Real.log (BC_X P R) - Real.log (BC_Y P R)

/-- Gamma-form race price, distinct from contactj. -/
def j (a : ℝ) : ℝ := a * Real.log (Real.Gamma (1 - 1/a)) - Real.eulerMascheroniConstant

def expOne : Measure ℝ := expMeasure 1
def arrivalLaw : Measure (ℕ → ℝ) := by
  letI : IsProbabilityMeasure expOne := isProbabilityMeasure_expMeasure (by norm_num)
  exact Measure.infinitePi (fun _ : ℕ => expOne)

/-- n=1 is the first arrival, the first positive partial sum. -/
def arrival (increments : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, increments k

/-- The tail sum `t^a * ∑ (t + T_{n+1})^(-a)`. The real `tsum` is totalized on exceptional sequences;
finiteness and log-integrability for `a > 1` are proved where used, not assumed here. -/
def Vtail (a t : ℝ) (increments : ℕ → ℝ) : ℝ :=
  t^a * ∑' n : ℕ, (t + arrival increments (n+1)) ^ (-a)

def m (a t : ℝ) : ℝ := ∫ increments, Real.log (1 + Vtail a t increments) ∂arrivalLaw
/-- The outer T~Exp(1) is independent of the increments whose partial sums are T_n. -/
def jET (a : ℝ) : ℝ := ∫ t, m a t ∂expOne

/-- The three-term cap on the Gamma-form race price `j a`. -/
def C3a (a : ℝ) : ℝ := 79/(96*a) + 241/(600*a^2) + 6503/(24000*a^2*(a-1))
/-- The four-term cap on the exponential-time race price `jET a`. -/
def C4b (a : ℝ) : ℝ :=
  3291/(4000*a) + 241/(600*a^2) + 271/(1000*a^3) + 26/(125*a^3*(a-1))

end

end StochasticToDeterministicLatents.General
