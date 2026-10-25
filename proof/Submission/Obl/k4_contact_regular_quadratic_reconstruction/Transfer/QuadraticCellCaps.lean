/- Adapted from this LOT tree, obligation o243 (k4_contact_affine_residual_candidate_transfer),
   session x0835, branch x0835, commit c4aab87f,
   Submission/Obl/k4_contact_affine_residual_candidate_transfer/QuadraticCellCaps.lean.
   Namespace and module paths renamed into o261's Transfer namespace;
   the accepted Data record is the same o238 one (k4_critical_switching_state_preparation). -/
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer.QuadraticCandidateCaps
import Submission.Lib.K4HiddenQuadratic

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4HiddenQuadratic

/-- A regular four-variable quadratic candidate inherits each original
hidden-bin ceiling after freezing its base coordinates. The ceiling may
already include an original velocity-palette factor. -/
theorem quadratic_candidate_cell_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E T : Set Ω) (hET : E ⊆ T) (x : Ω → Fin 4 → ℝ)
    (Q : MvPolynomial (Fin 4) ℝ) (hQ : Q.totalDegree ≤ 2) (z : Fin 4 → ℝ)
    {H c β : ℝ} (hH : 0 ≤ H) (hc : 0 < c) (hβ : 0 < β)
    (hgood : ∀ᵐ p ∂μ, p ∈ E →
      |eval (x p) Q| ≤ H * c ∧ β ≤ |eval (x p) (pderiv 3 Q)| ∧
      |eval (Function.update z 3 (x p 3)) Q - eval (x p) Q| ≤ H * c ∧
      |eval (Function.update z 3 (x p 3)) (pderiv 3 Q) -
        eval (x p) (pderiv 3 Q)| ≤ β / 2)
    (cap : ENNReal)
    (hcap : ∀ a : ℤ, μ {p | p ∈ T ∧ ⌊x p 3 / c⌋ = a} ≤ cap) :
    μ E ≤ ENNReal.ofReal (8 * (1 + 4 * H / β)) * cap := by
  apply frozen_candidate_original_bin_cap μ E T hET (fun p => x p 3)
    (fun p => eval (x p) Q) (fun p => eval (x p) (pderiv 3 Q))
    (coordPoly z 3 Q) ((natDegree_coordPoly_le z 3 Q).trans hQ) hH hc hβ
  · simpa only [eval_coordPoly, derivative_coordPoly] using hgood
  · exact hcap

end Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer
