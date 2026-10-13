-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/Entropy.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised.
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import NaturalLatents.Upstream.Prelude

/-!
# Finite entropy and mutual information

This file defines finite nonnegative measures, homogeneous entropy, deterministic
pushforwards, conditional entropy, mutual information, and the product-law
functionals `Psi`, `Phi`, and `Ixy`. These finite-sum definitions support the
latent-variable functionals used throughout the repository.
-/

namespace stoch_to_det

open Finset

variable {α β γ δ ε : Type*}

/-! ### Nonnegative finite measures -/

section Meas
variable [Fintype α]

/-- Total mass `|m|` of a finite measure. -/
noncomputable def mass (m : α → ℝ) : ℝ := ∑ a, m a

/-- `m` is a nonnegative finite measure. -/
def IsFinMeas (m : α → ℝ) : Prop := ∀ a, 0 ≤ m a

/-- `m` is a probability law: nonnegative with total mass `1`. -/
structure IsPMF (m : α → ℝ) : Prop where
  nonneg : ∀ a, 0 ≤ m a
  total : mass m = 1

/-- The total-mass field of a PMF, projected to the underlying finite sum. -/
lemma IsPMF.sum_eq_one {m : α → ℝ} (hm : IsPMF m) : ∑ a, m a = 1 := by
  simpa only [mass] using hm.total

/-- `𝖧(m) := ∑ m · lg(|m|/m)`, the 1-homogeneous entropy in bits.

The convention `0 log 0 := 0` is automatic here: at `m a = 0` the
summand is `0 * lg (mass m / 0) = 0 * lg 0 = 0`. -/
noncomputable def H (m : α → ℝ) : ℝ := ∑ a, m a * lg (mass m / m a)

lemma apply_le_mass {m : α → ℝ} (hm : IsFinMeas m) (a : α) : m a ≤ mass m :=
  Finset.single_le_sum (fun b _ => hm b) (Finset.mem_univ a)

/-- `𝖧` in nats splits into a mass term and a sum of `Real.negMulLog`s:
`(ln 2) · 𝖧(m) = |m| · ln|m| + ∑ₐ negMulLog (m a)`.

-/
lemma H_eq_negMulLog {m : α → ℝ} (hm : IsFinMeas m) :
    Real.log 2 * H m = mass m * Real.log (mass m) + ∑ a, Real.negMulLog (m a) := by
  by_cases hmass : mass m = 0
  · have hm_zero : ∀ a, m a = 0 := by
      intro a
      apply le_antisymm
      · have ha_le : m a ≤ mass m := apply_le_mass hm a
        simpa [hmass] using ha_le
      · exact hm a
    simp [H, hmass, hm_zero]
  · have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    calc
      Real.log 2 * H m
          = ∑ a, Real.log 2 * (m a * lg (mass m / m a)) := by
              simp [H, Finset.mul_sum]
      _ = ∑ a, (m a * Real.log (mass m) + Real.negMulLog (m a)) := by
            apply Finset.sum_congr rfl
            intro a _
            by_cases ha : m a = 0
            · simp [ha]
            · rw [lg_eq_log_div, Real.log_div hmass ha]
              simp only [Real.negMulLog]
              (field_simp [hlog2]; ring)
      _ = mass m * Real.log (mass m) + ∑ a, Real.negMulLog (m a) := by
            unfold mass
            rw [Finset.sum_add_distrib, Finset.sum_mul]

/-- `𝖧` is 1-homogeneous: `𝖧(c · m) = c · 𝖧(m)` for `c ≥ 0`. -/
lemma H_smul {m : α → ℝ} {c : ℝ} (hc : 0 ≤ c) :
    H (fun a => c * m a) = c * H m := by
  rcases hc.eq_or_lt with rfl | hc
  · simp [H, mass]
  · have hc0 : c ≠ 0 := ne_of_gt hc
    unfold H
    rw [show mass (fun a => c * m a) = c * mass m by simp [mass, Finset.mul_sum]]
    simp_rw [mul_div_mul_left _ _ hc0]
    rw [Finset.mul_sum]
    congr 1
    funext a
    ring

lemma H_eq_negMulLog_of_isPMF {m : α → ℝ} (hm : IsPMF m) :
    Real.log 2 * H m = ∑ a, Real.negMulLog (m a) := by
  simpa [hm.total] using H_eq_negMulLog hm.nonneg

/-- Entropy of a probability law is nonnegative. -/
lemma H_nonneg_of_isPMF {m : α → ℝ} (hm : IsPMF m) : 0 ≤ H m := by
  have hsum : 0 ≤ ∑ a, Real.negMulLog (m a) := by
    apply Finset.sum_nonneg
    intro a _
    apply Real.negMulLog_nonneg (hm.nonneg a)
    have ha_mass : m a ≤ mass m := apply_le_mass hm.nonneg a
    simpa [hm.total] using ha_mass
  have hEq := H_eq_negMulLog_of_isPMF hm
  apply (mul_nonneg_iff_of_pos_left (Real.log_pos one_lt_two)).mp
  rw [hEq]
  exact hsum

/-- Finite Gibbs inequality, with the support condition made explicit to avoid
Lean's junk value for division and logarithm at zero. -/
lemma gibbs_nonneg {p q : α → ℝ} (hp : IsPMF p) (hq : IsPMF q)
    (hsupp : ∀ a, p a ≠ 0 → q a ≠ 0) :
    0 ≤ ∑ a, p a * Real.log (p a / q a) := by
  have hterm : ∀ a, p a - q a ≤ p a * Real.log (p a / q a) := by
    intro a
    by_cases hpa : p a = 0
    · simp [hpa, hq.nonneg a]
    · have hqa := hsupp a hpa
      have hratio : 0 ≤ p a / q a := div_nonneg (hp.nonneg a) (hq.nonneg a)
      have h := mul_le_mul_of_nonneg_left
        (Real.self_sub_one_le_mul_log hratio) (hq.nonneg a)
      calc
        p a - q a = q a * (p a / q a - 1) := by field_simp
        _ ≤ q a * ((p a / q a) * Real.log (p a / q a)) := h
        _ = p a * Real.log (p a / q a) := by field_simp
  have hp_sum : ∑ a, p a = 1 := by simpa [mass] using hp.total
  have hq_sum : ∑ a, q a = 1 := by simpa [mass] using hq.total
  calc
    0 = ∑ a, (p a - q a) := by rw [Finset.sum_sub_distrib, hp_sum, hq_sum, sub_self]
    _ ≤ ∑ a, p a * Real.log (p a / q a) := Finset.sum_le_sum fun a _ => hterm a

end Meas

/-! ### Pushforwards: the single mechanism for "random variables" -/

section Push
variable [Fintype α] [DecidableEq γ]

/-- The law of the random variable `f` under `m`: `(push f m) c = m (f⁻¹ c)`. -/
noncomputable def push (f : α → γ) (m : α → ℝ) : γ → ℝ :=
  fun c => ∑ a ∈ univ.filter (fun a => f a = c), m a

lemma isFinMeas_push {f : α → γ} {m : α → ℝ} (hm : IsFinMeas m) :
    IsFinMeas (push f m) := by
  intro c
  exact sum_nonneg fun a _ => hm a

@[simp] lemma mass_push [Fintype γ] (f : α → γ) (m : α → ℝ) :
    mass (push f m) = mass m := by
  unfold mass push
  exact Finset.sum_fiberwise univ f m

lemma isPMF_push [Fintype γ] {f : α → γ} {m : α → ℝ} (hm : IsPMF m) :
    IsPMF (push f m) :=
  ⟨isFinMeas_push hm.nonneg, by simpa using hm.total⟩

/-- Entropy cannot increase under a deterministic pushforward. -/
lemma apply_le_push {m : α → ℝ} (hm : IsFinMeas m) (f : α → γ) (a : α) :
    m a ≤ push f m (f a) := by
  unfold push
  exact Finset.single_le_sum (fun b _ => hm b) (by simp)

lemma H_push_le [Fintype γ] {f : α → γ} {m : α → ℝ} (hm : IsPMF m) :
    H (push f m) ≤ H m := by
  have hfiber : ∀ c, Real.negMulLog (push f m c) ≤
      ∑ a ∈ univ.filter (fun a => f a = c), Real.negMulLog (m a) := by
    intro c
    unfold push
    rw [Real.negMulLog]
    calc
      (-∑ a ∈ univ.filter (fun a => f a = c), m a) *
            Real.log (∑ a ∈ univ.filter (fun a => f a = c), m a)
          = ∑ a ∈ univ.filter (fun a => f a = c),
              (-m a * Real.log (∑ a ∈ univ.filter (fun a => f a = c), m a)) := by
              rw [← Finset.sum_mul, Finset.sum_neg_distrib]
      _ ≤ ∑ a ∈ univ.filter (fun a => f a = c), Real.negMulLog (m a) := by
            apply Finset.sum_le_sum
            intro a ha
            rw [Real.negMulLog]
            by_cases hma : m a = 0
            · simp [hma]
            · have hma_pos : 0 < m a := lt_of_le_of_ne (hm.nonneg a) (Ne.symm hma)
              have hma_le : m a ≤ ∑ b ∈ univ.filter (fun b => f b = c), m b := by
                simpa only [push, (Finset.mem_filter.mp ha).2] using apply_le_push hm.nonneg f a
              have hlog := Real.log_le_log hma_pos hma_le
              nlinarith
  have hsum : ∑ c, Real.negMulLog (push f m c) ≤ ∑ a, Real.negMulLog (m a) := by
    calc
      ∑ c, Real.negMulLog (push f m c)
          ≤ ∑ c, ∑ a ∈ univ.filter (fun a => f a = c), Real.negMulLog (m a) :=
            Finset.sum_le_sum fun c _ => hfiber c
      _ = ∑ a, Real.negMulLog (m a) := Finset.sum_fiberwise univ f _
  have hp : IsPMF (push f m) := isPMF_push hm
  have hEqPush := H_eq_negMulLog_of_isPMF hp
  have hEq := H_eq_negMulLog_of_isPMF hm
  exact (mul_le_mul_iff_of_pos_left (Real.log_pos one_lt_two)).mp
    (hEqPush.trans_le (hsum.trans_eq hEq.symm))

/-- Pushing forward twice is pushing forward along the composite. -/
lemma push_push [Fintype γ] [DecidableEq δ] (f : α → γ) (g : γ → δ) (m : α → ℝ) :
    push g (push f m) = push (g ∘ f) m := by
  funext d
  unfold push
  rw [Finset.sum_fiberwise_eq_sum_filter]
  simp

/-- Pushing along the identity function leaves a finite measure unchanged. -/
@[simp] lemma push_id [DecidableEq α] (m : α → ℝ) : push id m = m := by
  funext a
  unfold push
  rw [Finset.sum_eq_single a]
  · simp
  · simp

/-- Pushforward is linear under scalar multiplication. -/
lemma push_smul (f : α → γ) (m : α → ℝ) (c : ℝ) :
    push f (fun a => c * m a) = fun x => c * push f m x := by
  funext x
  simp [push, Finset.mul_sum]

/-- Integrating a function against a pushforward is the corresponding fibrewise sum. -/
lemma sum_push_mul [Fintype γ] (f : α → γ) (m : α → ℝ) (k : γ → ℝ) :
    ∑ c, push f m c * k c = ∑ a, m a * k (f a) := by
  calc
    ∑ c, push f m c * k c
        = ∑ c, ∑ a ∈ univ.filter (fun a => f a = c), m a * k c := by
            unfold push
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.sum_mul]
    _ = ∑ c, ∑ a ∈ univ.filter (fun a => f a = c), m a * k (f a) := by
          apply Finset.sum_congr rfl
          intro c _
          apply Finset.sum_congr rfl
          intro a ha
          rw [(Finset.mem_filter.mp ha).2]
    _ = ∑ a, m a * k (f a) := Finset.sum_fiberwise univ f _

/-- The negative-log summand commutes with pushforward after integration. -/
lemma sum_negMulLog_push [Fintype γ] (f : α → γ) (m : α → ℝ) :
    ∑ c, Real.negMulLog (push f m c) = ∑ a, m a * (-Real.log (push f m (f a))) := by
  calc
    ∑ c, Real.negMulLog (push f m c) =
        ∑ c, push f m c * (-Real.log (push f m c)) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Real.negMulLog]
      ring
    _ = ∑ a, m a * (-Real.log (push f m (f a))) := sum_push_mul f m _

end Push

/-! ### Entropy decomposition over product fibres -/

section FiberEntropy
variable [Fintype α] [Fintype β] [DecidableEq β]

/-- Chain rule for a PMF on a product, with unnormalized conditional fibres. -/
lemma H_prod_eq_snd_add_fibers {r : α × β → ℝ} (hr : IsPMF r) :
    H r = H (push Prod.snd r) + ∑ y, H (fun x => r (x, y)) := by
  let ry : β → ℝ := push Prod.snd r
  have hry : IsPMF ry := isPMF_push hr
  have hmass_fiber : ∀ y, mass (fun x => r (x, y)) = ry y := by
    intro y
    simp [ry, push, mass, Finset.sum_filter, Fintype.sum_prod_type]
  have hFibEq : ∀ y, Real.log 2 * H (fun x => r (x, y)) =
      ry y * Real.log (ry y) + ∑ x, Real.negMulLog (r (x, y)) := by
    intro y
    have h := H_eq_negMulLog (fun x => hr.nonneg (x, y))
    rw [hmass_fiber y] at h
    exact h
  have hprod : ∑ y, ∑ x, Real.negMulLog (r (x, y)) =
      ∑ z, Real.negMulLog (r z) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hsumFib : Real.log 2 * (∑ y, H (fun x => r (x, y))) =
      (∑ y, ry y * Real.log (ry y)) + ∑ z, Real.negMulLog (r z) := by
    calc
      Real.log 2 * (∑ y, H (fun x => r (x, y))) =
          ∑ y, Real.log 2 * H (fun x => r (x, y)) := Finset.mul_sum _ _ _
      _ = ∑ y, (ry y * Real.log (ry y) + ∑ x, Real.negMulLog (r (x, y))) := by
        apply Finset.sum_congr rfl
        intro y _
        exact hFibEq y
      _ = (∑ y, ry y * Real.log (ry y)) +
          ∑ y, ∑ x, Real.negMulLog (r (x, y)) := Finset.sum_add_distrib
      _ = (∑ y, ry y * Real.log (ry y)) + ∑ z, Real.negMulLog (r z) := by
        rw [hprod]
  have hcancel : (∑ y, Real.negMulLog (ry y)) +
      ∑ y, ry y * Real.log (ry y) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro y _
    rw [Real.negMulLog]
    ring
  have hEr := H_eq_negMulLog_of_isPMF hr
  have hEry := H_eq_negMulLog_of_isPMF hry
  have hmult : Real.log 2 * H r =
      Real.log 2 * (H ry + ∑ y, H (fun x => r (x, y))) := by
    rw [mul_add, hEr, hEry, hsumFib]
    linarith
  nlinarith [Real.log_pos one_lt_two]

end FiberEntropy

/-! ### Entropy, conditional entropy, mutual information

All four are defined from `H ∘ push`, so every identity below reduces to
`Finset.sum` manipulation plus the marginalization lemma `push_push`. -/

section Info
variable [Fintype α]
  [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ] [Fintype ε] [DecidableEq ε]

/-- `H(f)` under the law `m`. -/
noncomputable def Hvar (f : α → γ) (m : α → ℝ) : ℝ := H (push f m)

/-- `H(f ∣ g)` under the law `m`. -/
noncomputable def condH (f : α → γ) (g : α → δ) (m : α → ℝ) : ℝ :=
  Hvar (fun a => (f a, g a)) m - Hvar g m

/-- `I(f ; g)` under the law `m`. -/
noncomputable def MI (f : α → γ) (g : α → δ) (m : α → ℝ) : ℝ :=
  Hvar f m + Hvar g m - Hvar (fun a => (f a, g a)) m

/-- `I(f ; g ∣ h)` under the law `m`. -/
noncomputable def condMI (f : α → γ) (g : α → δ) (h : α → ε) (m : α → ℝ) : ℝ :=
  Hvar (fun a => (f a, h a)) m + Hvar (fun a => (g a, h a)) m
    - Hvar (fun a => (f a, g a, h a)) m - Hvar h m

/-! #### Basic properties -/

theorem condMI_push_source
    {Ω Ω' K D E : Type*} [Fintype Ω] [Fintype Ω'] [DecidableEq Ω']
    [Fintype K] [DecidableEq K] [Fintype D] [DecidableEq D]
    [Fintype E] [DecidableEq E]
    (e : Ω → Ω') (a : Ω' → K) (b : Ω' → D) (c : Ω' → E)
    (m : Ω → ℝ) :
    condMI a b c (push e m) = condMI (a ∘ e) (b ∘ e) (c ∘ e) m := by
  simp only [condMI, Hvar, push_push, Function.comp_def]

/-- Entropy cannot increase after applying a deterministic function. -/
lemma Hvar_comp_le {m : α → ℝ} (hm : IsPMF m) (f : α → γ) (u : γ → δ) :
    Hvar (u ∘ f) m ≤ Hvar f m := by
  unfold Hvar
  rw [← push_push f u m]
  exact H_push_le (isPMF_push hm)

/-- A deterministic re-encoding with a left inverse preserves entropy. -/
lemma Hvar_eq_of_leftInverse {m : α → ℝ} (hm : IsPMF m) (f : α → γ)
    (u : γ → δ) (v : δ → γ) (huv : Function.LeftInverse v u) :
    Hvar (u ∘ f) m = Hvar f m := by
  apply le_antisymm
  · exact Hvar_comp_le hm f u
  · have hback := Hvar_comp_le hm (u ∘ f) v
    have hfun : v ∘ u ∘ f = f := by
      funext a
      exact huv (f a)
    rw [hfun] at hback
    exact hback

/-- Re-encoding a random variable by an equivalence preserves its entropy. -/
lemma Hvar_equiv {m : α → ℝ} (hm : IsPMF m) (f : α → γ) (e : γ ≃ δ) :
    Hvar (fun a => e (f a)) m = Hvar f m :=
  Hvar_eq_of_leftInverse hm f e e.symm e.left_inv

/-- Entropy is invariant under an equivalence of the output alphabet. -/
lemma H_push_equiv [DecidableEq α] (e : α ≃ γ) (m : α → ℝ)
    (hm : IsPMF m) : H (push e m) = H m := by
  simpa [Hvar, Function.comp_def] using Hvar_equiv hm id e

/-- Conditional-entropy chain rule written as a sum of unnormalized fibres. -/
lemma Hvar_pair_eq_sum_fibers {m : α → ℝ} (hm : IsPMF m) (f : α → γ) (h : α → δ) :
    Hvar (fun a => (f a, h a)) m = Hvar h m +
      ∑ y, H (push f (fun a => if h a = y then m a else 0)) := by
  let r : γ × δ → ℝ := push (fun a => (f a, h a)) m
  have hr : IsPMF r := isPMF_push hm
  have hsnd : push Prod.snd r = push h m := by
    dsimp [r]
    simpa [Function.comp_def] using
      (push_push (fun a => (f a, h a)) Prod.snd m)
  have hfib : ∀ y, (fun x => r (x, y)) =
      push f (fun a => if h a = y then m a else 0) := by
    intro y
    funext x
    dsimp [r]
    unfold push
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hx : f a = x <;> by_cases hy : h a = y <;> simp [hx, hy]
  have hdecomp := H_prod_eq_snd_add_fibers hr
  rw [hsnd] at hdecomp
  simp_rw [hfib] at hdecomp
  unfold Hvar
  exact hdecomp

/-- Mutual information is homogeneous on nonnegative finite measures. -/
lemma MI_smul {m : α → ℝ} (_hm : IsFinMeas m) (f : α → γ) (g : α → δ)
    {c : ℝ} (hc : 0 ≤ c) : MI f g (fun a => c * m a) = c * MI f g m := by
  unfold MI Hvar
  rw [push_smul f m c, H_smul hc,
    push_smul g m c, H_smul hc,
    push_smul (fun a => (f a, g a)) m c, H_smul hc]
  ring

lemma product_isPMF_dom {ι κ : Type*} [Fintype ι] [Fintype κ]
    {u : ι → ℝ} {v : κ → ℝ} (hu : IsPMF u) (hv : IsPMF v) :
    IsPMF (fun z : ι × κ => u z.1 * v z.2) := by
  refine ⟨fun z => mul_nonneg (hu.nonneg z.1) (hv.nonneg z.2), ?_⟩
  have hu_sum : ∑ i, u i = 1 := by simpa [mass] using hu.total
  have hv_sum : ∑ k, v k = 1 := by simpa [mass] using hv.total
  rw [mass, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [hv_sum]
  simpa using hu_sum

/-- Mutual information is nonnegative. -/
lemma MI_nonneg {m : α → ℝ} (hm : IsPMF m) (f : α → γ) (g : α → δ) :
    0 ≤ MI f g m := by
  let r : γ × δ → ℝ := push (fun a => (f a, g a)) m
  let rx : γ → ℝ := push Prod.fst r
  let ry : δ → ℝ := push Prod.snd r
  let s : γ × δ → ℝ := fun z => rx z.1 * ry z.2
  have hr : IsPMF r := isPMF_push hm
  have hrx : IsPMF rx := isPMF_push hr
  have hry : IsPMF ry := isPMF_push hr
  have hs : IsPMF s := product_isPMF_dom hrx hry
  have hsupp : ∀ z, r z ≠ 0 → s z ≠ 0 := by
    intro z hz
    have hrpos : 0 < r z := lt_of_le_of_ne (hr.nonneg z) (Ne.symm hz)
    have hxle : r z ≤ rx z.1 := apply_le_push hr.nonneg Prod.fst z
    have hyle : r z ≤ ry z.2 := apply_le_push hr.nonneg Prod.snd z
    dsimp [s]
    exact mul_ne_zero (lt_of_lt_of_le hrpos hxle).ne' (lt_of_lt_of_le hrpos hyle).ne'
  have hKL : 0 ≤ ∑ z, r z * Real.log (r z / s z) := gibbs_nonneg hr hs hsupp
  have hrx_eq : rx = push f m := by
    dsimp [rx, r]
    simpa [Function.comp_def] using
      (push_push (fun a => (f a, g a)) Prod.fst m)
  have hry_eq : ry = push g m := by
    dsimp [ry, r]
    simpa [Function.comp_def] using
      (push_push (fun a => (f a, g a)) Prod.snd m)
  have hMIent : MI f g m = H rx + H ry - H r := by
    unfold MI Hvar
    rw [hrx_eq, hry_eq]
  have hliftx : ∑ x, Real.negMulLog (rx x) =
      ∑ z, r z * (-Real.log (rx z.1)) := by
    simpa [rx] using sum_negMulLog_push Prod.fst r
  have hlifty : ∑ y, Real.negMulLog (ry y) =
      ∑ z, r z * (-Real.log (ry z.2)) := by
    simpa [ry] using sum_negMulLog_push Prod.snd r
  have hliftr : ∑ z, Real.negMulLog (r z) =
      ∑ z, r z * (-Real.log (r z)) := by
    simpa using sum_negMulLog_push id r
  have hEntropyKL :
      (∑ x, Real.negMulLog (rx x)) + (∑ y, Real.negMulLog (ry y))
          - ∑ z, Real.negMulLog (r z) =
        ∑ z, r z * Real.log (r z / s z) := by
    rw [hliftx, hlifty, hliftr, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : r z = 0
    · simp [hz]
    · have hsz := hsupp z hz
      dsimp [s] at hsz ⊢
      have hx0 : rx z.1 ≠ 0 := (mul_ne_zero_iff.mp hsz).1
      have hy0 : ry z.2 ≠ 0 := (mul_ne_zero_iff.mp hsz).2
      rw [Real.log_div hz hsz, Real.log_mul hx0 hy0]
      ring
  have hEr := H_eq_negMulLog_of_isPMF hr
  have hErx := H_eq_negMulLog_of_isPMF hrx
  have hEry := H_eq_negMulLog_of_isPMF hry
  have hMIKL : Real.log 2 * MI f g m = ∑ z, r z * Real.log (r z / s z) := by
    calc
      Real.log 2 * MI f g m = Real.log 2 * (H rx + H ry - H r) := by rw [hMIent]
      _ = Real.log 2 * H rx + Real.log 2 * H ry - Real.log 2 * H r := by ring
      _ = (∑ x, Real.negMulLog (rx x)) + (∑ y, Real.negMulLog (ry y))
          - ∑ z, Real.negMulLog (r z) := by rw [hErx, hEry, hEr]
      _ = ∑ z, r z * Real.log (r z / s z) := hEntropyKL
  apply (mul_nonneg_iff_of_pos_left (Real.log_pos one_lt_two)).mp
  rw [hMIKL]
  exact hKL

/-- Mutual information is nonnegative for every nonnegative finite measure. -/
lemma MI_nonneg_of_isFinMeas {m : α → ℝ} (hm : IsFinMeas m)
    (f : α → γ) (g : α → δ) : 0 ≤ MI f g m := by
  have hmass_nonneg : 0 ≤ mass m := Finset.sum_nonneg fun a _ => hm a
  by_cases hmass : mass m = 0
  · have hm_zero : m = fun _ => 0 := by
      funext a
      apply le_antisymm
      · have ha_le : m a ≤ mass m := apply_le_mass hm a
        simpa [hmass] using ha_le
      · exact hm a
    rw [hm_zero]
    simp [MI, Hvar, H, push, mass]
  · have hmass_pos : 0 < mass m := lt_of_le_of_ne hmass_nonneg (Ne.symm hmass)
    let q : α → ℝ := fun a => (mass m)⁻¹ * m a
    have hq : IsPMF q := by
      constructor
      · intro a
        exact mul_nonneg (inv_nonneg.mpr hmass_nonneg) (hm a)
      · unfold mass q
        rw [← Finset.mul_sum]
        exact inv_mul_cancel₀ hmass
    have hnonneg := MI_nonneg hq f g
    have hscale := MI_smul hm f g (inv_nonneg.mpr hmass_nonneg)
    change MI f g q = (mass m)⁻¹ * MI f g m at hscale
    rw [hscale] at hnonneg
    exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hmass_pos)).mp hnonneg

/-- Conditional mutual information is nonnegative. -/
lemma condMI_nonneg {m : α → ℝ} (hm : IsPMF m) (f : α → γ) (g : α → δ) (h : α → ε) :
    0 ≤ condMI f g h m := by
  let mh : ε → α → ℝ := fun z a => if h a = z then m a else 0
  have hmh : ∀ z, IsFinMeas (mh z) := by
    intro z a
    dsimp [mh]
    split <;> simp_all [hm.nonneg a]
  have hF := Hvar_pair_eq_sum_fibers hm f h
  have hG := Hvar_pair_eq_sum_fibers hm g h
  have hFG := Hvar_pair_eq_sum_fibers hm (fun a => (f a, g a)) h
  change Hvar (fun a => (f a, h a)) m = Hvar h m + ∑ z, H (push f (mh z)) at hF
  change Hvar (fun a => (g a, h a)) m = Hvar h m + ∑ z, H (push g (mh z)) at hG
  change Hvar (fun a => ((f a, g a), h a)) m = Hvar h m +
    ∑ z, H (push (fun a => (f a, g a)) (mh z)) at hFG
  have hAssoc : Hvar (fun a => (f a, g a, h a)) m =
      Hvar (fun a => ((f a, g a), h a)) m := by
    simpa using Hvar_equiv hm (fun a => ((f a, g a), h a))
      (Equiv.prodAssoc γ δ ε)
  have hEq : condMI f g h m = ∑ z, MI f g (mh z) := by
    unfold condMI
    rw [hF, hG, hAssoc, hFG]
    simp only [MI, Hvar, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [hEq]
  exact Finset.sum_nonneg fun z _ => MI_nonneg_of_isFinMeas (hmh z) f g

lemma Hvar_pair_swap {m : α → ℝ} (hm : IsPMF m) (f : α → γ) (g : α → δ) :
    Hvar (fun a => (g a, f a)) m = Hvar (fun a => (f a, g a)) m := by
  simpa using Hvar_equiv hm (fun a => (f a, g a)) (Equiv.prodComm γ δ)

/-- Chain rule: `I(f, g ; k) = I(f ; k) + I(g ; k ∣ f)`. -/
lemma MI_pair_left {m : α → ℝ} (hm : IsPMF m) (f : α → γ) (g : α → δ) (k : α → ε) :
    MI (fun a => (f a, g a)) k m = MI f k m + condMI g k f m := by
  have hgf : Hvar (fun a => (g a, f a)) m = Hvar (fun a => (f a, g a)) m := Hvar_pair_swap hm _ _
  have hkf : Hvar (fun a => (k a, f a)) m = Hvar (fun a => (f a, k a)) m := Hvar_pair_swap hm _ _
  let e : δ × (ε × γ) ≃ (γ × δ) × ε :=
    (Equiv.prodAssoc δ ε γ).symm |>.trans
      ((Equiv.prodComm (δ × ε) γ).trans (Equiv.prodAssoc γ δ ε).symm)
  have htrip : Hvar (fun a => (g a, k a, f a)) m =
      Hvar (fun a => ((f a, g a), k a)) m := by
    symm
    simpa [e] using Hvar_equiv hm (fun a => (g a, k a, f a)) e
  unfold MI condMI
  rw [hgf, hkf, htrip]
  ring

/-- Mutual information is symmetric. -/
lemma MI_comm {m : α → ℝ} (hm : IsPMF m) (f : α → γ) (g : α → δ) :
    MI f g m = MI g f m := by
  have hpair : Hvar (fun a => (g a, f a)) m = Hvar (fun a => (f a, g a)) m := Hvar_pair_swap hm _ _
  unfold MI
  rw [hpair]
  ring

end Info

/-! ### Marginals on a product

`mX`/`mY` are literally pushforwards along the projections, so all the lemmas
above apply to them unchanged. -/

section Product
variable [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The `X`-marginal `m_X`. -/
noncomputable abbrev mX (m : α × β → ℝ) : α → ℝ := push Prod.fst m

/-- The `Y`-marginal `m_Y`. -/
noncomputable abbrev mY (m : α × β → ℝ) : β → ℝ := push Prod.snd m

/-- `Ψ(m) := 2𝖧(m) − 𝖧(m_X) − 𝖧(m_Y)` -/
noncomputable def Psi (m : α × β → ℝ) : ℝ := 2 * H m - H (mX m) - H (mY m)

/-- `Φ(m) := 3𝖧(m) − 2𝖧(m_X) − 2𝖧(m_Y)` -/
noncomputable def Phi (m : α × β → ℝ) : ℝ := 3 * H m - 2 * H (mX m) - 2 * H (mY m)

/-- `I_q(X;Y)` for a law `q` on the product. -/
noncomputable def Ixy (q : α × β → ℝ) : ℝ := H (mX q) + H (mY q) - H q

end Product

end stoch_to_det
