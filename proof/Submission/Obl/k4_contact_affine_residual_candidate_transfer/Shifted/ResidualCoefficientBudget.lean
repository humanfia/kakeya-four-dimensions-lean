/- Adapted from this LOT tree, obligation o260, session x0919, commit 57638ddd7c07709143f61bbedd02efd72974929b,
   Submission/Obl/k4_contact_shifted_quadratic_candidates/Shifted/ResidualCoefficientBudget.lean. Original attribution comments are retained below. -/
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.Shifted.HorizontalCoefficients
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.ResidualFields

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer.Shifted

open MeasureTheory Set Filter MvPolynomial
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Obl.k4_contact_affine_residual_candidate_transfer

noncomputable section

/-- The horizontal model bounds the tests of its actual serving frame levels
at every fixed positive candidate depth. -/
theorem eventually_residual_coefficient_budget {α : Type} [MeasurableSpace α]
    (D : Data α) (s₀ U' e₀' : ℝ) (K' : ℕ → ℝ)
    (frames : (k : ℕ) → Option (Frame D k s₀ U'))
    (hpar : Parameters (residualData D s₀ U' e₀' K' frames))
    (hbasic : (residualData D s₀ U' e₀' K' frames).Basic)
    (hatlas : (residualData D s₀ U' e₀' K' frames).Atlas)
    {R : ℝ} (hR : 1 < R) :
    ∀ᶠ k in atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ U' →
      ∀ f, frames k = some f →
      ∀ i : Fin (f.level (gridLevel (U' / f.m) f.m s)).n,
        (1 + ∑ e ∈ ((f.level (gridLevel (U' / f.m) f.m s)).F i).support,
          |((f.level (gridLevel (U' / f.m) f.m s)).F i).coeff e|) +
          ∑ e ∈ (X 3 : MvPolynomial (Fin 4) ℝ).support,
            |(X 3 : MvPolynomial (Fin 4) ℝ).coeff e| ≤ D.N k ^ (2 * U' + 13) := by
  filter_upwards [eventually_horizontal_coefficient_budget
    (residualData D s₀ U' e₀' K' frames) hpar hbasic hatlas hR] with k hk
  intro s hs hsU f hfr i
  have hk' := hk s hs hsU
  simp only [residualData, withLevels, residualBase, residualLevels, residualSteps] at hk'
  rw [hfr] at hk'
  dsimp only at hk'
  exact hk' i

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer.Shifted
