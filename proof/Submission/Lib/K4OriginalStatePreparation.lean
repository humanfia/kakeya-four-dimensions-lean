/- Adapted from: here:o247 (session x0870). -/
import Submission.Lib.K4OriginalStatePreparation.Consensus
import Submission.Lib.K4OriginalStatePreparation.Measured
import Submission.Lib.K4OriginalStatePreparation.Smoothing
import Submission.Lib.K4OriginalStatePreparation.Copies
import Submission.Lib.K4OriginalStatePreparation.Numerics

/-!
# Original-state consensus, smoothing, and reference preparation

Finite and measurable coefficient consensus with original conditional-pair
loss, factor-two palette transfer, cell smoothing that preserves the entire
original law, uniform label copies with exact reference budgets, and the
wide-comparison exponent estimates. Every result is Mathlib-only.
-/
