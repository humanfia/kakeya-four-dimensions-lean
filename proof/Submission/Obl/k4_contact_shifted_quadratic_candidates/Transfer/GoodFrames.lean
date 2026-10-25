/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/GoodFrames.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.ResidualAtlas
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.Subpower

/-!
# Good frame sequences and their constants

`GoodFrames` is the interface of o260 (session x0921, `Shifted/Interface.lean`,
structure `GoodFrames`), restated here over this obligation's `Frame`: a frame
at every index (`none` at finitely many), each good, with subpower asymptotics
of its constants. The per-index constants of the residual atlas are read off
the frame at each index.
-/

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open MeasureTheory Set Filter
open Submission.Obl.k4_critical_switching_state_preparation

noncomputable section

/-- Frames for one residual model. Adapted from o260 (x0921),
`Shifted/Interface.lean`, `GoodFrames`. -/
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

variable {α : Type} [MeasurableSpace α] {D : Data α} {s₀ U' e₀' : ℝ}

namespace GoodFrames

variable (gf : GoodFrames D s₀ U' e₀')

/-- The palette fit constant of the frame at an index. -/
def Hk (k : ℕ) : ℝ :=
  match gf.fr k with
  | some f => f.H
  | none => 1

/-- The number of grid steps at an index. -/
def steps (k : ℕ) : ℝ := residualSteps D s₀ U' gf.fr k

/-- The grid gap at an index. -/
def gap (k : ℕ) : ℝ := U' / residualSteps D s₀ U' gf.fr k

variable {gf}

theorem Hk_eq {k : ℕ} {f : Frame D k s₀ U'} (h : gf.fr k = some f) : gf.Hk k = f.H := by
  simp [Hk, h]

theorem steps_eq {k : ℕ} {f : Frame D k s₀ U'} (h : gf.fr k = some f) : gf.steps k = f.m := by
  simp [steps, residualSteps_some h]

theorem gap_eq {k : ℕ} {f : Frame D k s₀ U'} (h : gf.fr k = some f) :
    gf.gap k = U' / f.m := by
  simp [gap, residualSteps_some h]

variable (gf)

/-- The cap constant of the residual caps at an index. -/
def capC (k : ℕ) : ℝ := 27 * (6 * D.K k + 5) * D.K k * (D.K k ^ 3 / gf.θ k)

/-- The slope constant at an index. -/
def slopeK (A₀ : ℝ) (k : ℕ) : ℝ :=
  max (20 * D.K k ^ 3 * gf.K₂ k * gf.Hk k / gf.θ k)
    ((3 + 13 * D.K k ^ 4 * gf.K₂ k ^ 2) *
      (passA A₀ (boxK (D.K k) (gf.K₂ k)) (gf.capC k) (4 * gf.Hk k + 2) (D.K k) (gf.θ k) 1 *
          (2 * gf.Hk k) +
        gf.steps k * (passA A₀ (boxK (D.K k) (gf.K₂ k)) (gf.capC k) (4 * gf.Hk k + 6) (D.K k)
          (gf.θ k) (D.N k ^ (D.d * gf.gap k)) * (2 * gf.Hk k) *
            (D.N k ^ gf.gap k * D.K k ^ 8))))

/-- The atlas constant at an index, with the depth rounding cost. -/
def atlasK (A₀ : ℝ) (k : ℕ) : ℝ :=
  max 1 (gf.slopeK A₀ k) * D.N k ^ ((1 + D.d + D.κ + D.κ) * gf.gap k)

end GoodFrames

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
