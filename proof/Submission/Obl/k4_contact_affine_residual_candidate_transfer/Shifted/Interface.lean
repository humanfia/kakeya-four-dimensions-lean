/- Adapted from this LOT tree, obligation o260, session x0919, commit 57638ddd7c07709143f61bbedd02efd72974929b,
   Submission/Obl/k4_contact_shifted_quadratic_candidates/Shifted/Interface.lean. Original attribution comments are retained below. -/
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.GoodFrames
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.FrameGood
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.Shifted.Statement

/-!
# What the per-index frames must supply

For a fixed parent depth `s₀`, residual horizon `U'` and residual contact
exponent `e₀'`, a `GoodFrames` value gives a frame of `Transfer.Frame` at every
index (`none` at finitely many), each good in the sense of `Transfer.FrameGood`
with the stated constants, with a floor of the original residual law `ρ` on the
core, and with subpower asymptotics of all constants:

* `θ` (core floors) is at least every negative power of `N` eventually;
* `K₂` (centering), the palette fit `H` and the number of grid levels are at
  most every positive power of `N` eventually;
* the grid gap `U' / m` tends to zero and the velocity mesh range `Rk` to
  infinity.

`FrameExistence` is the statement the frame construction proves for the
original contact data: frames exist for every small parent depth and residual
horizon inside the palette range and the centering range.
-/

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open MeasureTheory Set Filter
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Obl.k4_contact_affine_residual_candidate_transfer

noncomputable section

/-- Frames exist below the palette range, inside the centering range, with
residual contact exponent half of what the parent depth leaves. -/
def FrameExistence {α : Type} [MeasurableSpace α] (D : Data α) : Prop :=
  ∃ U₁ : ℝ, 0 < U₁ ∧ ∀ s₀ U' : ℝ, 0 < s₀ → 0 < U' → s₀ + U' ≤ U₁ →
    D.κ * (s₀ + U') ≤ D.e₀ / 2 →
    Nonempty (GoodFrames D s₀ U' ((D.e₀ - D.κ * s₀) / 2))

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
