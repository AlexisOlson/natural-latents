import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
The finite natural-latent theorem, stated from probability tables in bits.
This file contains definitions and two propositions, with no theorem proofs.
The information formulas have their probability meaning on normalized,
nonnegative tables. Both claims require `Probability p`; `TableClaim` and `tau`
require `Probability q` for stochastic joint laws. All derived marginal and
deterministic tables are then laws.

Notation: `H` is entropy, `Hcond` conditions the first coordinate on the second,
and `CMI` conditions its first two coordinates on the third.
Lean writes a triple as `A × B × C = A × (B × C)`; its slots are `(a, b, c)`.
-/

open scoped BigOperators
namespace NaturalLatents

section Defs

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

/-- A probability law on a finite alphabet: every entry is nonnegative and
all entries sum to one. Zero-probability entries are allowed. -/
def Probability (p : A → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

/-- Shannon entropy in bits when `Probability p` holds:
`H(p) = -∑ a, p(a) log₂ p(a)`. Zero entries contribute zero.
The formula is defined on all real tables; its probability interpretation
requires normalization and nonnegativity. -/
noncomputable def H (p : A → ℝ) : ℝ :=
  -∑ a, p a * (Real.log (p a) / Real.log 2)

/-- For a probability table on pairs `(x, y)`, the conditional entropy
`H(X | Y) = H(X,Y) - H(Y)`: the first coordinate given the second. -/
noncomputable def Hcond (pXY : A × B → ℝ) : ℝ :=
  H pXY - H (fun y => ∑ x, pXY (x, y))

/-- For a probability table on triples `(x, y, z)`,
`I(X;Y | Z) = H(X,Z) + H(Y,Z) - H(X,Y,Z) - H(Z)`. -/
noncomputable def CMI (pXYZ : A × B × C → ℝ) : ℝ :=
  H (fun (x, z) => ∑ y, pXYZ (x, y, z))     -- H(X,Z)
    + H (fun (y, z) => ∑ x, pXYZ (x, y, z)) -- H(Y,Z)
    - H pXYZ                               -- H(X,Y,Z)
    - H (fun z => ∑ x, ∑ y, pXYZ (x, y, z)) -- H(Z)

/-- Stochastic natural-latent error of a probability table on `(X, Y, V)`:
`I(X;Y | V) + I(V;X | Y) + I(V;Y | X)`. -/
noncomputable def StochasticError (pXYV : A × B × C → ℝ) : ℝ :=
  CMI pXYV                                  -- slots (X,Y,V): I(X;Y | V)
    + CMI (fun (v, x, y) => pXYV (x, y, v)) -- slots (V,X,Y): I(V;X | Y)
    + CMI (fun (v, y, x) => pXYV (x, y, v)) -- slots (V,Y,X): I(V;Y | X)

/-- The deterministic-side expression on a probability table `(X, Y, Γ)`:
`I(X;Y | Γ) + H(Γ | X) + H(Γ | Y)`.
This formula itself does not impose determinism. `T` and `TableClaim` apply
it to `deterministicTable p g`, where `Γ = g(X,Y)` is deterministic. -/
noncomputable def DeterministicError (pXYΓ : A × B × C → ℝ) : ℝ :=
  CMI pXYΓ
    + Hcond (fun (g, x) => ∑ y, pXYΓ (x, y, g)) -- slots (Γ,X): H(Γ | X)
    + Hcond (fun (g, y) => ∑ x, pXYΓ (x, y, g)) -- slots (Γ,Y): H(Γ | Y)

/-- The joint law of `(X, Y, g(X,Y))` when `Probability pXY` holds.
For each `(x,y)`, its mass is placed at the single label `g (x,y)`.
Summing over that label recovers `pXY`. -/
def deterministicTable (pXY : A × B → ℝ) (g : A × B → C) : A × B × C → ℝ :=
  fun (x, y, c) => if g (x, y) = c then pXY (x, y) else 0

/-- Minimum deterministic error for the law `p`. The code uses at most
`card (A × B)` labels; it need not use every label in this codomain.
Every deterministic finite latent can be relabeled into this codomain.
The code space is finite and nonempty, so this infimum is attained. -/
noncomputable def T (p : A × B → ℝ) : ℝ :=
  ⨅ g : A × B → Fin (Fintype.card (A × B)),
    DeterministicError (deterministicTable p g)

/-- Infimum stochastic error over all finite joint laws `(X,Y,V)` whose
`(X,Y)` marginal is `p`; `Fin k` represents any finite latent alphabet.
When `Probability p` holds, the feasible set is nonempty (a constant latent)
and bounded below by zero (each conditional mutual information is nonnegative).
Thus this is a genuine real infimum; no minimizing stochastic latent is assumed.
Outside probability laws, this definition has no asserted optimum meaning. -/
noncomputable def tau (p : A × B → ℝ) : ℝ :=
  sInf {s : ℝ | ∃ (k : ℕ) (q : A × B × Fin k → ℝ),
    Probability q ∧ (∀ x y, ∑ v, q (x, y, v) = p (x, y)) ∧ StochasticError q = s}

end Defs

/-- There is one universal real constant `c` with `0 ≤ c < 7`. For every
finite-alphabet probability law `p`, one deterministic code `g`, chosen before the
stochastic latent, satisfies the bound for every finite joint law `q` with marginal `p`.
No independence or strict-positivity assumption is imposed on either law. -/
def TableClaim : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ c < 7 ∧
    ∀ (A B : Type) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
      (p : A × B → ℝ), Probability p →
        ∃ g : A × B → Fin (Fintype.card (A × B)),
          ∀ (k : ℕ) (q : A × B × Fin k → ℝ),
            Probability q → (∀ x y, ∑ v, q (x, y, v) = p (x, y)) →
              DeterministicError (deterministicTable p g) ≤ c * StochasticError q

/-- The equivalent optimum form with one universal real constant `c` with
`0 ≤ c < 7`: `T p ≤ c * tau p` for every finite-alphabet probability law.
Equivalence uses attainment of `T` and nonemptiness and a lower bound for the
stochastic feasible set. It does not require attainment of `tau`. -/
def ScoreClaim : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ c < 7 ∧
    ∀ (A B : Type) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
      (p : A × B → ℝ), Probability p → T p ≤ c * tau p

end NaturalLatents