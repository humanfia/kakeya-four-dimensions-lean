import Submission.Obl.k4_true_forest_own_depth_preparation.Model
import Submission.Lib.K4XInterface.Charts

namespace Submission.Obl.k4_true_forest_own_depth_preparation

open MeasureTheory Set
open Submission.Obl.k4_coarsened_outer_horizon_composition

/-- Restrict selected incidences while leaving every full trajectory
assignment and every geometric datum unchanged. -/
theorem chart_restrict {N κ j r B : ℝ} {M D T : ℕ}
    {E : Set Inc} {c u : E2} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set Line} {F H : Set Inc} {ex ex' : Prop}
    (h : chart N M D κ T j r B E c u Q R A F ex)
    (hsub : H ⊆ F) (hHm : MeasurableSet H)
    (hfmt : ∀ i, fmt 7 (N ^ M) D
      {z : Fin 7 → ℝ | ((i, fun e : Fin 6 => z e.castSucc), z 6) ∈ H})
    (hex : ex') : chart N M D κ T j r B E c u Q R A H ex' := by
  have h₀ := h
  rcases h with ⟨_, _, _, _, _, _, hAm, _, hfmt₀, _, hsel, _⟩
  exact Submission.Lib.K4XInterface.gchart_restrict h₀ (Subset.refl A) hsub
    (fun p hp => (hsel p (hsub hp)).2.1) hAm hHm
    (fun i => ⟨(hfmt₀ i).1, hfmt i⟩) hex

end Submission.Obl.k4_true_forest_own_depth_preparation
