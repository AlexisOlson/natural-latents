-- Adapted from DLorell/stoch_to_det (Apache-2.0), file stoch_to_det/SharedRace/Scalar.lean at 7b41957da9500716102cba323b3a48af0f23751c;
-- modified: module paths renamed; declarations unused by the main theorems removed.
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Scalar core of the all-label shared-race bound

This file formalizes the elementary one-variable end of the direct
C less than 96 argument. The probability-law and simplex
change-of-variables layers are intentionally kept separate.
-/

namespace stoch_to_det
namespace SharedRace

open Set
open scoped Interval Real



end SharedRace
end stoch_to_det
