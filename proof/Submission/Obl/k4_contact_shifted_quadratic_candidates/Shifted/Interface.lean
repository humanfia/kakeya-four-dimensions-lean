import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.FrameGood
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Shifted.Statement

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

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates

open MeasureTheory Set Filter
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

noncomputable section

/-- Frames for one residual model. -/
structure GoodFrames {α : Type} [MeasurableSpace α] (D : Data α) (s₀ U' e₀' : ℝ) where
  /-- the frame at each index -/
  fr : (k : ℕ) → Option (Frame D k s₀ U')
  /-- velocity mesh range of the joint caps -/
  Rk : ℕ → ℝ
  /-- core floor fraction -/
  θ : ℕ → ℝ
  /-- centering constant -/
  K₂ : ℕ → ℝ
  good : ∀ k f, fr k = some f → FrameGood f (Rk k) (θ k) (K₂ k) e₀'
  rho_floor : ∀ k f, fr k = some f →
    ENNReal.ofReal (θ k * f.ql 0) * D.ν k (D.A k (f.depth 0) f.i₀) ≤ D.ρ k f.core
  eventually_some : ∀ᶠ k in atTop, ∃ f, fr k = some f
  Rk_large : ∀ R : ℝ, ∀ᶠ k in atTop, R ≤ Rk k
  θ_large : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, D.N k ^ (-ε) ≤ θ k
  K₂_small : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K₂ k ≤ D.N k ^ ε
  H_small : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ f, fr k = some f → f.H ≤ D.N k ^ ε
  gap_small : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ f, fr k = some f → U' / f.m ≤ ε
  steps_small : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ f, fr k = some f →
    (f.m : ℝ) + 1 ≤ D.N k ^ ε

/-- Frames exist below the palette range, inside the centering range, with
residual contact exponent half of what the parent depth leaves. -/
def FrameExistence {α : Type} [MeasurableSpace α] (D : Data α) : Prop :=
  ∃ U₁ : ℝ, 0 < U₁ ∧ ∀ s₀ U' : ℝ, 0 < s₀ → 0 < U' → s₀ + U' ≤ U₁ →
    D.κ * (s₀ + U') ≤ D.e₀ / 2 →
    Nonempty (GoodFrames D s₀ U' ((D.e₀ - D.κ * s₀) / 2))

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates
