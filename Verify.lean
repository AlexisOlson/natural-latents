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
