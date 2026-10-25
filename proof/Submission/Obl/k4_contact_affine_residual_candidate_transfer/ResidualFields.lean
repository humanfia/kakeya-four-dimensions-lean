import Submission.Obl.k4_contact_affine_residual_candidate_transfer.FrameAlgebra

/-!
# Fields of the residual model at an index with a frame
-/

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open MeasureTheory Set MvPolynomial ProbabilityTheory
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Lib.K4ContactNormalization

noncomputable section

variable {α : Type} [MeasurableSpace α] {D : Data α} {s₀ U' e₀' : ℝ} {K' : ℕ → ℝ}
  {fr : (k : ℕ) → Option (Frame D k s₀ U')} {k : ℕ} {f : Frame D k s₀ U'}

theorem residual_N : (residualData D s₀ U' e₀' K' fr).N = D.N := rfl
theorem residual_K : (residualData D s₀ U' e₀' K' fr).K = K' := rfl
theorem residual_d : (residualData D s₀ U' e₀' K' fr).d = D.d := rfl
theorem residual_κ : (residualData D s₀ U' e₀' K' fr).κ = D.κ := rfl
theorem residual_ℓ : (residualData D s₀ U' e₀' K' fr).ℓ = D.κ := rfl
theorem residual_S : (residualData D s₀ U' e₀' K' fr).S = D.S := rfl
theorem residual_U : (residualData D s₀ U' e₀' K' fr).U = U' := rfl
theorem residual_e₀ : (residualData D s₀ U' e₀' K' fr).e₀ = e₀' := rfl
theorem residual_π : (residualData D s₀ U' e₀' K' fr).π = D.π := rfl
theorem residual_P : (residualData D s₀ U' e₀' K' fr).P k = X 3 := rfl

theorem residual_ν (h : fr k = some f) :
    (residualData D s₀ U' e₀' K' fr).ν k = cond (D.ν k) f.parentSet := by
  simp [residualData, withLevels, residualBase, h]

theorem residual_μ (h : fr k = some f) :
    (residualData D s₀ U' e₀' K' fr).μ k = f.resμ := by
  simp [residualData, withLevels, residualBase, h]

theorem residual_ρ (h : fr k = some f) :
    (residualData D s₀ U' e₀' K' fr).ρ k = f.resρ := by
  simp [residualData, withLevels, residualBase, h]

theorem residual_b (h : fr k = some f) :
    (residualData D s₀ U' e₀' K' fr).b k = f.coeff := by
  funext l
  simp [residualData, withLevels, residualBase, h]

theorem residual_x (h : fr k = some f) (l : α) (t : ℝ) :
    (residualData D s₀ U' e₀' K' fr).x k l t = point (f.coeff l) t := by
  simp only [Data.x, residual_b h, point]

theorem residualLevels_some (h : fr k = some f) (lev : ℕ) :
    residualLevels D s₀ U' fr k lev = f.level lev := by
  simp [residualLevels, h]

theorem residualSteps_some (h : fr k = some f) :
    residualSteps D s₀ U' fr k = f.m := by
  simp [residualSteps, h]

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
