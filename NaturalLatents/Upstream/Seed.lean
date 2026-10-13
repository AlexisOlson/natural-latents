-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/Seed.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed; documentation revised.
-- Source: the DLorell/stoch_to_det main branch, taken from the head of pull request #6 by Jeremy Gillen at the revision above.
-- Local changes: Added or moved local conditional-information and cross-entropy helpers; retained the seed and exponential-clock lemmas required by the race.
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.InformationTheory.KullbackLeibler.Basic
import NaturalLatents.Upstream.Duality
import NaturalLatents.Upstream.Toolkit

/-!
# Seed setup, shared races, and posterior replicas

This file packages an attained optimal latent and feasible contact kernel in
`SeedSetup`. It defines the exponential-clock and Gumbel seed laws, the
fixed-seed winner, continuous-versus-finite conditional information, averaged
defect, and the finite posterior-replica identities used by the race proof.
-/

namespace stoch_to_det

open Finset MeasureTheory ProbabilityTheory InformationTheory

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-! ### Standing data for the race construction -/

/-- The optimal latent and contact-kernel data used by the race construction
: a law with connected support together with an attained
`τ`-optimal common-contact pair `(L, w)`. -/
structure SeedSetup (p : α × β → ℝ) where
  /-- `p` is a probability law. -/
  isPMF : IsPMF p
  /-- The joint law has connected support. -/
  conn : IsConnected (support p)
  /-- A latent attaining `tau p`. -/
  L : Latent p
  /-- A feasible kernel attaining the dual optimum. -/
  w : α × β → ℝ
  /-- `w` is feasible. -/
  feasible : Feasible (support p) w
  /-- `L` attains `τ`. -/
  optimal : L.score = tau p
  /-- Every component of positive prior mass is a contact of `w`. -/
  contact : ∀ v, L.prior v ≠ 0 → IsContact (support p) w (L.comp v)
  /-- All prior weights are strictly positive: zero-mass labels are pruned
  when `exists_seedSetup` constructs the setup. Clustering uses this positivity. -/
  prior_pos : ∀ v, 0 < L.prior v

namespace SeedSetup

variable {p : α × β → ℝ} (D : SeedSetup p)

/-- The posterior `t_ℓ(z) := λ_ℓ q^ℓ(z) / p(z)`. -/
noncomputable def post (ℓ : D.L.ι) (z : α × β) : ℝ := D.L.prior ℓ * D.L.comp ℓ z / p z

/-- `M := I(X;Y ∣ L)`. -/
noncomputable def M : ℝ :=
  condMI (fun q => q.2.1) (fun q => q.2.2) (fun q => q.1) D.L.joint

end SeedSetup

private lemma sum_ne_zero_subtype_eq {κ : Type*} [Fintype κ]
    (a f : κ → ℝ) (hf : ∀ i, a i = 0 → f i = 0) :
    (∑ i : {i : κ // a i ≠ 0}, f i.1) = ∑ i, f i := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter fun i => a i ≠ 0) (by simp) f]
  exact Finset.sum_filter_of_ne (fun i _ hi h => hi (hf i h))

/-- Construction of a `SeedSetup`: prune the zero-prior labels
of `exists_common_contact_pair`'s latent (pruning to the subtype
`{v // L.prior v ≠ 0}` preserves the score and the mixture). -/
theorem exists_seedSetup {p : α × β → ℝ} (hp : IsPMF p)
    (hconn : IsConnected (support p)) :
    Nonempty (SeedSetup p) := by
  rcases exists_common_contact_pair hp with ⟨L, w, hw, hoptimal, hcontact⟩
  let L' : Latent p := {
    ι := {v : L.ι // L.prior v ≠ 0}
    fin := inferInstance
    dec := inferInstance
    prior := fun v => L.prior v.1
    comp := fun v => L.comp v.1
    prior_isPMF := by
      refine ⟨fun v => L.prior_isPMF.nonneg v.1, ?_⟩
      rw [mass, sum_ne_zero_subtype_eq L.prior L.prior (fun _ h => h)]
      simpa [mass] using L.prior_isPMF.total
    comp_isPMF := fun v => L.comp_isPMF v.1
    mixture := by
      intro z
      rw [sum_ne_zero_subtype_eq L.prior
        (fun v => L.prior v * L.comp v z) (fun _ h => by simp [h])]
      exact L.mixture z
  }
  have hpayoff :
      (∑ v, L'.prior v * Phi (L'.comp v)) =
        ∑ v, L.prior v * Phi (L.comp v) := by
    change (∑ v : {v : L.ι // L.prior v ≠ 0},
      L.prior v.1 * Phi (L.comp v.1)) = ∑ v, L.prior v * Phi (L.comp v)
    exact sum_ne_zero_subtype_eq L.prior
      (fun v => L.prior v * Phi (L.comp v)) (fun _ h => by simp [h])
  have hscore : L'.score = L.score := by
    rw [Latent.score_eq hp L', Latent.score_eq hp L, hpayoff]
  refine ⟨{
    isPMF := hp
    conn := hconn
    L := L'
    w := w
    feasible := hw
    optimal := hscore.trans hoptimal
    contact := ?_
    prior_pos := ?_
  }⟩
  · intro v _
    change IsContact (support p) w (L.comp v.1)
    exact hcontact v.1 v.2
  · intro v
    change 0 < L.prior v.1
    exact lt_of_le_of_ne (L.prior_isPMF.nonneg v.1) (Ne.symm v.2)

/-! ### The race at a fixed seed -/

section FixedSeed

variable {p : α × β → ℝ} (D : SeedSetup p)

end FixedSeed

/-! ### The seed law -/

/-- The clock law: iid `Exp(1)` coordinates, `E_ℓ = e^{−ε_ℓ}`.
Taken as primitive so the clock arguments can use exponential memorylessness. -/
noncomputable def clockLaw (ι : Type) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι => expMeasure 1

instance (ι : Type) [Fintype ι] : IsProbabilityMeasure (clockLaw ι) := by
  unfold clockLaw
  let : ∀ _ : ι, IsProbabilityMeasure (expMeasure 1) :=
    fun _ => isProbabilityMeasure_expMeasure zero_lt_one
  infer_instance

/-- The seed law on `ι → ℝ`: iid standard Gumbel, the pushforward of `clockLaw`
under `E ↦ −log E`. -/
noncomputable def seedLaw (ι : Type) [Fintype ι] : Measure (ι → ℝ) :=
  (clockLaw ι).map fun E i => -Real.log (E i)

instance (ι : Type) [Fintype ι] : IsProbabilityMeasure (seedLaw ι) := by
  unfold seedLaw
  infer_instance

/- The one-coordinate seed law is atomless.  The only junk-value issue is at
nonpositive clocks: `-log E = 0` there, but `Exp(1)` assigns that half-line
measure zero. -/
lemma expMeasure_one_Iic_zero : expMeasure 1 (Set.Iic 0) = 0 := by
  let := isProbabilityMeasure_expMeasure (r := (1 : ℝ)) zero_lt_one
  have hreal : (expMeasure 1).real (Set.Iic 0) = 0 := by
    rw [← cdf_eq_real]
    simpa using cdf_expMeasure_eq (r := (1 : ℝ)) zero_lt_one 0
  exact (measureReal_eq_zero_iff).mp hreal

lemma expMeasure_one_Ioi (x : ℝ) (hx : 0 ≤ x) :
    expMeasure 1 (Set.Ioi x) = ENNReal.ofReal (Real.exp (-x)) := by
  let := isProbabilityMeasure_expMeasure (r := (1 : ℝ)) zero_lt_one
  have hsub : 0 ≤ 1 - Real.exp (-x) := by
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hreal : (expMeasure 1).real (Set.Iic x) = 1 - Real.exp (-x) := by
    rw [← cdf_eq_real, cdf_expMeasure_eq (r := (1 : ℝ)) zero_lt_one x,
      ite_eq_left hx]
    ring
  have hIic : expMeasure 1 (Set.Iic x) =
      ENNReal.ofReal (1 - Real.exp (-x)) := by
    rw [← ENNReal.toReal_eq_toReal_iff'
      (measure_ne_top (expMeasure 1) (Set.Iic x)) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hsub]
    simpa [measureReal_def] using hreal
  rw [show Set.Ioi x = (Set.Iic x)ᶜ by ext y; simp, measure_compl measurableSet_Iic
    (measure_ne_top (expMeasure 1) (Set.Iic x)), measure_univ, hIic,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hsub]
  congr 1
  ring

lemma expMeasure_one_laplace (c : ℝ) (hc : 0 ≤ c) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-(c * x))) ∂(expMeasure 1)) =
      ENNReal.ofReal (1 / (1 + c)) := by
  have hr : 0 < 1 + c := by linarith
  have hmeasPDF : Measurable (gammaPDF 1 1) :=
    (measurable_gammaPDFReal 1 1).ennreal_ofReal
  have hmeasExp : Measurable (fun x : ℝ =>
      ENNReal.ofReal (Real.exp (-(c * x)))) := by fun_prop
  unfold expMeasure gammaMeasure
  rw [lintegral_withDensity_eq_lintegral_mul volume hmeasPDF hmeasExp]
  have hpoint :
      (fun x : ℝ => gammaPDF 1 1 x * ENNReal.ofReal (Real.exp (-(c * x)))) =ᵐ[volume]
        Set.indicator (Set.Ioi 0)
          (fun x => ENNReal.ofReal (Real.exp (-((1 + c) * x)))) := by
    have hne : ∀ᵐ x : ℝ ∂volume, x ∉ ({0} : Set ℝ) :=
      measure_eq_zero_iff_ae_notMem.mp (measure_singleton 0)
    filter_upwards [hne] with x hx0
    by_cases hx : 0 < x
    · have hxmem : x ∈ Set.Ioi (0 : ℝ) := hx
      rw [Set.indicator_of_mem hxmem]
      simp only [gammaPDF_eq, ite_eq_left hx.le, Real.one_rpow, Real.Gamma_one, div_one,
        sub_self, Real.rpow_zero, mul_one, one_mul]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg (-x)), ← Real.exp_add]
      congr 2
      ring
    · have hxne : x ≠ 0 := by simpa using hx0
      have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hxne
      have hxmem : x ∉ Set.Ioi (0 : ℝ) := not_lt.mpr hxneg.le
      rw [Set.indicator_of_notMem hxmem]
      simp [gammaPDF_of_neg hxneg]
  change (∫⁻ x, gammaPDF 1 1 x * ENNReal.ofReal (Real.exp (-(c * x))) ∂volume) = _
  rw [lintegral_congr_ae hpoint, lintegral_indicator measurableSet_Ioi]
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-((1 + c) * x))) (Set.Ioi 0) :=
    by
      convert exp_neg_integrableOn_Ioi 0 hr using 1
      funext x
      congr 2
      ring
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => Real.exp_nonneg _)]
  have hvalue := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (1 : ℝ)) (r := 1 + c) zero_lt_one hr
  apply congrArg ENNReal.ofReal
  simpa using hvalue

def strictClockWin {κ : Type*} (t : κ → ℝ) (a : κ)
    (E : κ → ℝ) : Prop :=
  ∀ b, b ≠ a → E a / t a < E b / t b

lemma pi_exp_strictClockWin {κ : Type*} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ a, 0 < t a) (htotal : ∑ a, t a = 1) (a : κ) :
    Measure.pi (fun _ : κ => expMeasure 1) {E | strictClockWin t a E} =
      ENNReal.ofReal (t a) := by
  let : ∀ _ : κ, IsProbabilityMeasure (expMeasure 1) :=
    fun _ => isProbabilityMeasure_expMeasure zero_lt_one
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let e : Option {i : κ // i ≠ a} ≃ κ := Equiv.optionSubtypeNe a
  let f := (MeasurableEquiv.piOptionEquivProd
    (fun _ : Option {i : κ // i ≠ a} => ℝ)).symm
  let g := MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e
  let q := (Measure.pi (fun _ : {i : κ // i ≠ a} => expMeasure 1)).prod
    (expMeasure 1)
  have hfirst :
      Measure.map f q =
        Measure.pi (fun _ : Option {i : κ // i ≠ a} => expMeasure 1) := by
    dsimp [f, q]
    exact Measure.pi_map_piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => expMeasure 1)
  have hsecond :
      Measure.map g
          (Measure.pi (fun _ : Option {i : κ // i ≠ a} => expMeasure 1)) =
        Measure.pi (fun _ : κ => expMeasure 1) := by
    dsimp [g]
    simpa [e] using Measure.pi_map_piCongrLeft e
      (fun _ : κ => expMeasure 1)
  have hmap : Measure.map (g ∘ f) q =
      Measure.pi (fun _ : κ => expMeasure 1) := by
    calc
      Measure.map (g ∘ f) q = Measure.map g (Measure.map f q) :=
        (Measure.map_map g.measurable f.measurable).symm
      _ = _ := by rw [hfirst, hsecond]
  have hset : MeasurableSet {E : κ → ℝ | strictClockWin t a E} := by
    unfold strictClockWin
    measurability
  rw [← hmap, Measure.map_apply (g.measurable.comp f.measurable) hset]
  have hpre : MeasurableSet ((g ∘ f) ⁻¹' {E : κ → ℝ | strictClockWin t a E}) :=
    hset.preimage (g.measurable.comp f.measurable)
  rw [Measure.prod_apply_symm hpre]
  have hsection (y : ℝ) :
      (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹'
          ((g ∘ f) ⁻¹' {E : κ → ℝ | strictClockWin t a E}) =
        Set.pi Set.univ
          (fun i : {i : κ // i ≠ a} => Set.Ioi (t i.1 / t a * y)) := by
    ext x
    have hf_pair := (MeasurableEquiv.piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => ℝ)).apply_symm_apply (x, y)
    have hf_some (i : {i : κ // i ≠ a}) : f (x, y) (some i) = x i :=
      congrFun (congrArg Prod.fst hf_pair) i
    have hf_none : f (x, y) none = y := congrArg Prod.snd hf_pair
    have he_i (i : {i : κ // i ≠ a}) : (g (f (x, y))) i.1 = x i := by
      dsimp [g]
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
      simp [e, Equiv.optionSubtypeNe_symm_of_ne i.2, hf_some]
    have he_a : (g (f (x, y))) a = y := by
      dsimp [g]
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
      simp [e, hf_none]
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_Ioi]
    constructor
    · intro h i
      have hrel := h i.1 i.2
      change g (f (x, y)) a / t a < g (f (x, y)) i.1 / t i.1 at hrel
      rw [he_a, he_i] at hrel
      have hcross : y * t i.1 < x i * t a :=
        (div_lt_div_iff₀ (ht a) (ht i.1)).1 hrel
      have hdiv : t i.1 * y / t a < x i :=
        (div_lt_iff₀ (ht a)).2 (by nlinarith)
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv
    · intro h b hba
      let i : {i : κ // i ≠ a} := ⟨b, hba⟩
      have hdiv := h i
      change t b / t a * y < x i at hdiv
      have hdiv' : t b * y / t a < x i := by
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv
      have hcross : y * t b < x i * t a := by
        have := (div_lt_iff₀ (ht a)).1 hdiv'
        nlinarith
      change g (f (x, y)) a / t a < g (f (x, y)) b / t b
      have hib := he_i i
      change g (f (x, y)) b = x i at hib
      rw [he_a, hib]
      exact (div_lt_div_iff₀ (ht a) (ht b)).2 hcross
  simp_rw [hsection, Measure.pi_pi]
  let c : ℝ := ∑ i : {i : κ // i ≠ a}, t i.1 / t a
  have hsplit := Fintype.sum_eq_add_sum_subtype_ne t a
  have hsubsum : (∑ i : {i : κ // i ≠ a}, t i.1) = 1 - t a := by
    linarith
  have hc : c = (1 - t a) / t a := by
    dsimp [c]
    rw [← Finset.sum_div, hsubsum]
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact Finset.sum_nonneg fun i _ => div_nonneg (ht i.1).le (ht a).le
  have hypos : ∀ᵐ y : ℝ ∂(expMeasure 1), 0 < y := by
    have hnot := measure_eq_zero_iff_ae_notMem.mp expMeasure_one_Iic_zero
    filter_upwards [hnot] with y hy
    simpa only [Set.mem_Iic, not_le] using hy
  have hprod : ∀ᵐ y : ℝ ∂(expMeasure 1),
      (∏ i : {i : κ // i ≠ a},
          expMeasure 1 (Set.Ioi (t i.1 / t a * y))) =
        ENNReal.ofReal (Real.exp (-(c * y))) := by
    filter_upwards [hypos] with y hy
    simp_rw [expMeasure_one_Ioi _
      (mul_nonneg (div_nonneg (ht _).le (ht a).le) hy.le)]
    rw [← ENNReal.ofReal_prod_of_nonneg
      (fun i _ => Real.exp_nonneg (-(t i.1 / t a * y))), ← Real.exp_sum]
    congr 2
    dsimp [c]
    rw [Finset.sum_neg_distrib, Finset.sum_mul]
  calc
    (∫⁻ y, ∏ i : {i : κ // i ≠ a},
        expMeasure 1 (Set.Ioi (t i.1 / t a * y)) ∂(expMeasure 1)) =
        ∫⁻ y, ENNReal.ofReal (Real.exp (-(c * y))) ∂(expMeasure 1) :=
      lintegral_congr_ae hprod
    _ = ENNReal.ofReal (1 / (1 + c)) := expMeasure_one_laplace c hc_nonneg
    _ = ENNReal.ofReal (t a) := by
      congr 1
      rw [hc]
      field_simp [(ht a).ne']
      ring

/- An affine equality between two distinct coordinates has measure zero under
a finite product of any atomless sigma-finite law.  Splitting off the second
coordinate turns every section into a singleton. -/
/- A fixed list order supplies a measurable tie-breaking version of argmax. -/
noncomputable def lexMax {Ω ι : Type*} [Fintype ι]
    [Nonempty ι] (F : Ω → ι → ℝ) (ω : Ω) : ι :=
  (List.argmax (F ω) Finset.univ.toList).get (by
    rw [Option.isSome_iff_ne_none, Ne, List.argmax_eq_none]
    simpa using (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty).ne_empty)

lemma lexMax_eq_iff {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (F : Ω → ι → ℝ) (ω : Ω) (a : ι) :
    lexMax F ω = a ↔ List.argmax (F ω) Finset.univ.toList = some a := by
  unfold lexMax
  let hsome : (List.argmax (F ω) Finset.univ.toList).isSome := by
    rw [Option.isSome_iff_ne_none, Ne, List.argmax_eq_none]
    simpa using (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty).ne_empty
  constructor
  · intro h
    exact (Option.some_get hsome).symm.trans (congrArg some h)
  · intro h
    exact Option.get_of_eq_some hsome h

lemma measurable_lexMax {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (F : Ω → ι → ℝ) (hF : ∀ a, Measurable fun ω => F ω a) :
    Measurable (lexMax F) := by
  have hlevel (a : ι) : MeasurableSet {ω | lexMax F ω = a} := by
    have hchar : {ω | lexMax F ω = a} =
        {ω | (∀ b, F ω b ≤ F ω a) ∧
          ∀ b, F ω a ≤ F ω b →
            List.idxOf a Finset.univ.toList ≤ List.idxOf b Finset.univ.toList} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      rw [lexMax_eq_iff, List.argmax_eq_some_iff]
      simp
    rw [hchar]
    have hleft₀ := MeasurableSet.iInter fun b => measurableSet_le (hF b) (hF a)
    have heqleft : (⋂ b, {ω | F ω b ≤ F ω a}) = {ω | ∀ b, F ω b ≤ F ω a} := by
      ext ω
      simp
    have hleft : MeasurableSet {ω | ∀ b, F ω b ≤ F ω a} := by
      rw [← heqleft]
      exact hleft₀
    have hright₀ := MeasurableSet.iInter fun b =>
      (measurableSet_le (hF a) (hF b)).imp
        (MeasurableSet.const (List.idxOf a Finset.univ.toList ≤
          List.idxOf b Finset.univ.toList))
    have heqright : (⋂ b, {ω | F ω a ≤ F ω b →
        List.idxOf a Finset.univ.toList ≤ List.idxOf b Finset.univ.toList}) =
        {ω | ∀ b, F ω a ≤ F ω b →
          List.idxOf a Finset.univ.toList ≤ List.idxOf b Finset.univ.toList} := by
      ext ω
      simp
    have hright : MeasurableSet {ω | ∀ b, F ω a ≤ F ω b →
        List.idxOf a Finset.univ.toList ≤ List.idxOf b Finset.univ.toList} := by
      rw [← heqright]
      exact hright₀
    change MeasurableSet ({ω | ∀ b, F ω b ≤ F ω a} ∩
      {ω | ∀ b, F ω a ≤ F ω b →
        List.idxOf a Finset.univ.toList ≤ List.idxOf b Finset.univ.toList})
    exact hleft.inter hright
  apply measurable_to_countable
  intro ω
  exact hlevel (lexMax F ω)

lemma lexMax_max {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (F : Ω → ι → ℝ) (ω : Ω) (a : ι) :
    F ω a ≤ F ω (lexMax F ω) := by
  have hmem : lexMax F ω ∈ List.argmax (F ω) Finset.univ.toList := by
    unfold lexMax
    exact Option.get_mem _
  exact List.le_of_mem_argmax (by simp) hmem

lemma ae_forall_fintype {Ω κ : Type*} [Finite κ]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {R : κ → Ω → Prop}
    (hR : ∀ k, ∀ᵐ ω ∂P, R k ω) : ∀ᵐ ω ∂P, ∀ k, R k ω := ae_all_iff.2 hR

/-! ### Conditional mutual information against a continuous variable

When `Z` and the conditioning variable are finite and only the observed
variable `W` is continuous, `I(W;Z ∣ C)` is a weighted sum of KL divergences
between measures on the observation space. -/

/-! ### The averaged defect and a good fixed seed -/

section Average

variable {p : α × β → ℝ} (D : SeedSetup p)

end Average

/-! ### Posterior replicas

`L₀, L₁, L₂` are conditionally iid finite draws from the posterior given `Z`
, so the replica space is a finite product and Lemmas
The initial replica identities are finite; the final comparison also involves the seed.

The replica joint law on `ι × ι × ι × (α × β)` is
`P(ℓ₀,ℓ₁,ℓ₂,z) = p(z) t_{ℓ₀}(z) t_{ℓ₁}(z) t_{ℓ₂}(z)`; exchangeability of the
three coordinates is then a `Finset.sum` symmetry, not a probabilistic
argument. -/

section Replica

variable {p : α × β → ℝ} (D : SeedSetup p)

lemma MI_equiv_left_local
    {A Γ Γ' Δ : Type*} [Fintype A] [Fintype Γ] [Fintype Γ'] [Fintype Δ]
    [DecidableEq Γ] [DecidableEq Γ'] [DecidableEq Δ]
    {m : A → ℝ} (hm : IsPMF m) (f : A → Γ) (e : Γ ≃ Γ') (g : A → Δ) :
    MI (fun a => e (f a)) g m = MI f g m := by
  have hf := Hvar_equiv hm f e
  have hfg := Hvar_equiv hm (fun a => (f a, g a))
    (Equiv.prodCongr e (Equiv.refl Δ))
  change Hvar (fun a => (e (f a), g a)) m = Hvar (fun a => (f a, g a)) m at hfg
  unfold MI
  rw [hf, hfg]

lemma condMI_comm_local
    {A Γ Δ K : Type*} [Fintype A] [Fintype Γ] [Fintype Δ] [Fintype K]
    [DecidableEq Γ] [DecidableEq Δ] [DecidableEq K]
    {m : A → ℝ} (hm : IsPMF m) (f : A → Γ) (g : A → Δ) (h : A → K) :
    condMI f g h m = condMI g f h m := by
  let e : Γ × Δ × K ≃ Δ × Γ × K :=
    { toFun := fun t => (t.2.1, t.1, t.2.2)
      invFun := fun t => (t.2.1, t.1, t.2.2)
      left_inv := by rintro ⟨x, y, k⟩; rfl
      right_inv := by rintro ⟨y, x, k⟩; rfl }
  have htrip : Hvar (fun a => (g a, f a, h a)) m = Hvar (fun a => (f a, g a, h a)) m := by
    simpa [e] using Hvar_equiv hm (fun a => (f a, g a, h a)) e
  unfold condMI
  rw [htrip]
  ring

private lemma condMI_eq_MI_pair_sub_local
    {A Γ Δ K : Type*} [Fintype A] [Fintype Γ] [Fintype Δ] [Fintype K]
    [DecidableEq Γ] [DecidableEq Δ] [DecidableEq K]
    {m : A → ℝ} (hm : IsPMF m) (f : A → Γ) (g : A → Δ) (h : A → K) :
    condMI f g h m = MI (fun a => (h a, f a)) g m - MI h g m := by
  have hchain := MI_pair_left hm h f g
  linarith

lemma condMI_pair_left_local
    {A Γ Δ E K : Type*} [Fintype A] [Fintype Γ] [Fintype Δ] [Fintype E]
    [Fintype K] [DecidableEq Γ] [DecidableEq Δ] [DecidableEq E] [DecidableEq K]
    {m : A → ℝ} (hm : IsPMF m) (f : A → Γ) (g : A → Δ) (k : A → E)
    (h : A → K) :
    condMI (fun a => (f a, g a)) k h m =
      condMI f k h m + condMI g k (fun a => (h a, f a)) m := by
  have hleft := condMI_eq_MI_pair_sub_local hm (fun a => (f a, g a)) k h
  have hfirst := condMI_eq_MI_pair_sub_local hm f k h
  have hsecond := condMI_eq_MI_pair_sub_local hm g k (fun a => (h a, f a))
  have hassoc := MI_equiv_left_local hm (fun a => ((h a, f a), g a))
    (Equiv.prodAssoc K Γ Δ) k
  change MI (fun a => (h a, f a, g a)) k m = MI (fun a => ((h a, f a), g a)) k m at hassoc
  linarith

lemma condMI_equiv_cond_local
    {A Γ Δ K K' : Type*} [Fintype A] [Fintype Γ] [Fintype Δ]
    [Fintype K] [Fintype K'] [DecidableEq Γ] [DecidableEq Δ]
    [DecidableEq K] [DecidableEq K']
    {m : A → ℝ} (hm : IsPMF m) (f : A → Γ) (g : A → Δ) (h : A → K)
    (e : K ≃ K') :
    condMI f g (fun a => e (h a)) m = condMI f g h m := by
  have hfh := Hvar_equiv hm (fun a => (f a, h a))
    (Equiv.prodCongr (Equiv.refl Γ) e)
  have hgh := Hvar_equiv hm (fun a => (g a, h a))
    (Equiv.prodCongr (Equiv.refl Δ) e)
  have htrip := Hvar_equiv hm (fun a => (f a, g a, h a))
    (Equiv.prodCongr (Equiv.refl Γ) (Equiv.prodCongr (Equiv.refl Δ) e))
  have hh := Hvar_equiv hm h e
  change Hvar (fun a => (f a, e (h a))) m = Hvar (fun a => (f a, h a)) m at hfh
  change Hvar (fun a => (g a, e (h a))) m = Hvar (fun a => (g a, h a)) m at hgh
  change Hvar (fun a => (f a, g a, e (h a))) m = Hvar (fun a => (f a, g a, h a)) m at htrip
  unfold condMI
  rw [hfh, hgh, htrip, hh]

lemma condMI_equiv_left_local
    {A Γ Γ' Δ K : Type*} [Fintype A] [Fintype Γ] [Fintype Γ'] [Fintype Δ]
    [Fintype K] [DecidableEq Γ] [DecidableEq Γ'] [DecidableEq Δ] [DecidableEq K]
    {m : A → ℝ} (hm : IsPMF m) (f : A → Γ) (e : Γ ≃ Γ') (g : A → Δ) (h : A → K) :
    condMI (fun a => e (f a)) g h m = condMI f g h m := by
  have hfh := Hvar_equiv hm (fun a => (f a, h a))
    (Equiv.prodCongr e (Equiv.refl K))
  have htrip := Hvar_equiv hm (fun a => (f a, g a, h a))
    (Equiv.prodCongr e (Equiv.refl (Δ × K)))
  change Hvar (fun a => (e (f a), h a)) m = Hvar (fun a => (f a, h a)) m at hfh
  change Hvar (fun a => (e (f a), g a, h a)) m = Hvar (fun a => (f a, g a, h a)) m at htrip
  unfold condMI
  rw [hfh, htrip]

/-! #### Calibration of the finite winner law -/

/- Any real-valued expression which depends on the seed only through the
finite winner map is integrable.  We use the measurable lexicographic winner
as an a.e. version of the arbitrary maximizer in `winner`. -/
/-! #### The cellwise source latent -/

/- The finite cross-entropy inequality used for conditional-entropy
concavity.  It is just Gibbs' inequality, with all quantities in bits. -/
lemma H_le_crossEntropy
    {κ : Type*} [Fintype κ]
    {r q : κ → ℝ} (hr : IsPMF r) (hq : IsPMF q)
    (hsupp : ∀ i, r i ≠ 0 → q i ≠ 0) :
    H r ≤ ∑ i, r i * lg (1 / q i) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hH := H_eq_negMulLog hr.nonneg
  rw [hr.total, Real.log_one, mul_zero, zero_add] at hH
  have hcross :
      Real.log 2 * (∑ i, r i * lg (1 / q i)) =
        ∑ i, r i * Real.log (1 / q i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [lg_eq_log_div]
    field_simp [hlog2.ne']
  have hdiff :
      (∑ i, r i * Real.log (1 / q i)) -
          ∑ i, Real.negMulLog (r i) =
        ∑ i, r i * Real.log (r i / q i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hri : r i = 0
    · simp [hri, Real.negMulLog]
    · have hqi : q i ≠ 0 := hsupp i hri
      rw [Real.negMulLog, Real.log_div one_ne_zero hqi,
        Real.log_one, Real.log_div hri hqi]
      ring
  have hgibbs := gibbs_nonneg hr hq hsupp
  apply (mul_le_mul_iff_of_pos_left hlog2).mp
  rw [hH, hcross]
  linarith

lemma condH_eq_sum_H_fibers
    {A Γ K : Type*} [Fintype A] [Fintype Γ] [Fintype K]
    [DecidableEq Γ] [DecidableEq K]
    {m : A → ℝ} (hm : IsPMF m) (f : A → Γ) (h : A → K) :
    condH f h m =
      ∑ k, H (push f (fun x => if h x = k then m x else 0)) := by
  have hdecomp := Hvar_pair_eq_sum_fibers hm f h
  unfold condH
  rw [hdecomp]
  ring

end Replica

end stoch_to_det
