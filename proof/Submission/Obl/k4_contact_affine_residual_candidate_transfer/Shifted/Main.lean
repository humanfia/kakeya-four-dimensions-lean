/- Adapted from this LOT tree, obligation o260, session x0919, commit 57638ddd7c07709143f61bbedd02efd72974929b,
   Submission/Obl/k4_contact_shifted_quadratic_candidates/Shifted/Main.lean. Original attribution comments are retained below. -/
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.Shifted.Assembly

/-!
# The obligation from frames and a ready residual model

`ResidualReady` is what the residual-model verification supplies: for good
frames at a small parent depth and residual horizon, some subpower constant
`K'` makes the residual model satisfy every hypothesis of the horizontal
principle. The coefficient budget follows from the horizontal atlas at the
candidate depths.

`shiftedTransfer_of` proves the field-named obligation `ShiftedTransfer` from
frame existence and `ResidualReady`: for a horizon `V`, choose a parent depth
`s₀` and a residual horizon `U'` small enough, apply the horizontal principle
to the residual model and return its candidates (`shifted_of_residual`).
-/

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer.Shifted

open MeasureTheory Set Filter MvPolynomial
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Obl.k4_contact_affine_residual_candidate_transfer
open Submission.Lib.K4ContactNormalization

noncomputable section

/-- The residual model on good frames meets the horizontal hypotheses. -/
def ResidualReady : Prop :=
  ∀ (α : Type) [MeasurableSpace α] (D : Data α), MeshCalibration → ContactProblem D →
    ∀ s₀ U' : ℝ, 0 < s₀ → 0 < U' → U' ≤ 1 / 4 → D.κ * (s₀ + U') ≤ D.e₀ / 2 →
    ∀ gf : GoodFrames D s₀ U' ((D.e₀ - D.κ * s₀) / 2),
    ∃ K' : ℕ → ℝ,
      Parameters (residualData D s₀ U' ((D.e₀ - D.κ * s₀) / 2) K' gf.fr) ∧
      (residualData D s₀ U' ((D.e₀ - D.κ * s₀) / 2) K' gf.fr).Basic ∧
      (residualData D s₀ U' ((D.e₀ - D.κ * s₀) / 2) K' gf.fr).Caps ∧
      (residualData D s₀ U' ((D.e₀ - D.κ * s₀) / 2) K' gf.fr).Atlas ∧
      (residualData D s₀ U' ((D.e₀ - D.κ * s₀) / 2) K' gf.fr).Nested

/-- The obligation, from frame existence and a ready residual model. -/
theorem shiftedTransfer_of
    (hFE : ∀ (α : Type) [MeasurableSpace α] (D : Data α), ContactProblem D → FrameExistence D)
    (hRR : ResidualReady) : ShiftedTransfer := by
  intro hcal hH α _ D hD V hV hVU
  obtain ⟨U₁, hU₁, hframes⟩ := hFE α D hD
  have p := hD.parameters
  have hκ := p.rate_pos
  have he₀ := p.defect_pos
  -- a parent depth and a residual horizon below every constraint
  set w : ℝ := min (min V U₁) (min (1 / 4) (D.e₀ / (2 * D.κ))) with hw
  have hw0 : 0 < w := by
    refine lt_min (lt_min hV hU₁) (lt_min (by norm_num) ?_)
    positivity
  set s₀ : ℝ := w / 2 with hs₀
  set U' : ℝ := w / 2 with hU'
  have hs₀0 : 0 < s₀ := by positivity
  have hU'0 : 0 < U' := by positivity
  have hsum : s₀ + U' = w := by simp only [hs₀, hU']; ring
  have hwV : w ≤ V := (min_le_left _ _).trans (min_le_left _ _)
  have hwU : w ≤ U₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hw4 : w ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hwe : w ≤ D.e₀ / (2 * D.κ) := (min_le_right _ _).trans (min_le_right _ _)
  have hU'4 : U' ≤ 1 / 4 := by linarith
  have hκw : D.κ * (s₀ + U') ≤ D.e₀ / 2 := by
    rw [hsum]
    have := mul_le_mul_of_nonneg_left hwe hκ.le
    calc
      D.κ * w ≤ D.κ * (D.e₀ / (2 * D.κ)) := this
      _ = D.e₀ / 2 := by field_simp
  obtain ⟨gf⟩ := hframes s₀ U' hs₀0 hU'0 (by rw [hsum]; exact hwU) hκw
  obtain ⟨K', hpar, hbasic, hcaps, hatlas, hnested⟩ :=
    hRR α D hcal hD s₀ U' hs₀0 hU'0 hU'4 hκw gf
  have hcand := hH α (residualData D s₀ U' ((D.e₀ - D.κ * s₀) / 2) K' gf.fr) hpar rfl
    hbasic hcaps hatlas hnested
  exact shifted_of_residual hD hs₀0 hU'0 (by rw [hsum]; exact hwV) gf K' hpar hbasic hatlas hcand

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer.Shifted
