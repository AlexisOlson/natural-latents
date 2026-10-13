import Mathlib.Util.AssertNoSorry
import NaturalLatents

/-!
Kernel audit of the two headline theorems. A successful run exits with code 0 and prints nothing.
`#print axioms` reports each theorem's whole dependency cone, so these pins cover every lemma the
proofs use. The propositions themselves are fixed in `NaturalLatents/Statement.lean`, whose SHA-256
is checked separately (`scripts/check_statement.py`).
-/

/-- info: NaturalLatents.table : NaturalLatents.TableClaim -/
#guard_msgs in
#check NaturalLatents.table

/-- info: NaturalLatents.score : NaturalLatents.ScoreClaim -/
#guard_msgs in
#check NaturalLatents.score

assert_no_sorry NaturalLatents.table
/-- info: 'NaturalLatents.table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NaturalLatents.table

assert_no_sorry NaturalLatents.score
/-- info: 'NaturalLatents.score' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NaturalLatents.score

-- Exact optimum bound.
example (A B : Type) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (p : A × B → ℝ) (hp : NaturalLatents.Probability p) :
    NaturalLatents.T p ≤ (2789 / 400) * NaturalLatents.tau p :=
  NaturalLatents.T_le_mul_tau A B p hp

assert_no_sorry NaturalLatents.T_le_mul_tau
/-- info: 'NaturalLatents.T_le_mul_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NaturalLatents.T_le_mul_tau

-- Setup: attain a latent on connected support.
assert_no_sorry NaturalLatents.General.exists_setup_of_connected
/-- info: 'NaturalLatents.General.exists_setup_of_connected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NaturalLatents.General.exists_setup_of_connected

-- Ledger: bound the deterministic score.
assert_no_sorry NaturalLatents.General.T_le_ledger
/-- info: 'NaturalLatents.General.T_le_ledger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NaturalLatents.General.T_le_ledger

-- Race: construct the exponential race.
assert_no_sorry NaturalLatents.General.exists_race
/-- info: 'NaturalLatents.General.exists_race' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NaturalLatents.General.exists_race

-- Cap: bound the race price.
assert_no_sorry NaturalLatents.General.racePrice_lt_capC3a
/-- info: 'NaturalLatents.General.racePrice_lt_capC3a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NaturalLatents.General.racePrice_lt_capC3a

-- Payment: pay for mismatches.
assert_no_sorry NaturalLatents.General.mismatch_payment
/-- info: 'NaturalLatents.General.mismatch_payment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NaturalLatents.General.mismatch_payment

-- Extension: pass from connected support to every law.
assert_no_sorry NaturalLatents.General.extension_of_connected
/-- info: 'NaturalLatents.General.extension_of_connected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NaturalLatents.General.extension_of_connected

-- Assembly: combine the connected estimates.
assert_no_sorry NaturalLatents.General.T_le_of_connected
/-- info: 'NaturalLatents.General.T_le_of_connected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NaturalLatents.General.T_le_of_connected

-- Assembly: the optimum bound in bits.
assert_no_sorry NaturalLatents.T_le_c_mul_tau
/-- info: 'NaturalLatents.T_le_c_mul_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NaturalLatents.T_le_c_mul_tau
