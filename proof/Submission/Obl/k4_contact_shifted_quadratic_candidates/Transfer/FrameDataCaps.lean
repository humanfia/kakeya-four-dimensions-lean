/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/FrameDataCaps.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.GoodFrameCaps
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.ResidualFields

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open Set MeasureTheory Filter MvPolynomial
open Submission.Obl.k4_critical_switching_state_preparation

noncomputable section

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' e₀' : ℝ}
variable {K' : ℕ → ℝ} {frames : (k : ℕ) → Option (Frame D k s₀ U')}
variable {f : Frame D k s₀ U'}

theorem residual_z_frame (hf : frames k = some f) (r : ℝ) (p : α × ℝ) :
    (residualData D s₀ U' e₀' K' frames).z k (D.N k) r p = f.baseCode r p := by
  funext i
  fin_cases i <;>
    simp [Data.z, Frame.baseCode, Submission.Lib.K4AffineMeshCaps.baseMesh,
      Submission.Lib.K4MovingMeshBoxes.baseMesh, residual_x hf,
      Submission.Lib.K4ContactNormalization.point]

theorem residual_native_frame (hf : frames k = some f) (angular : Bool) (s : ℝ)
    (p : α × ℝ) :
    ⌊(if angular then
      eval ((residualData D s₀ U' e₀' K' frames).x k p.1 p.2)
        ((residualData D s₀ U' e₀' K' frames).P k)
      else (residualData D s₀ U' e₀' K' frames).x k p.1 p.2 3) / D.N k ^ (-s)⌋ =
      f.hiddenCode s p := by
  cases angular <;> simp [Frame.hiddenCode, residual_x hf, residual_P, eval_X]

theorem residual_velocity_frame (hf : frames k = some f) (v : ℝ) (p : α × ℝ) :
    ⌊(residualData D s₀ U' e₀' K' frames).b k p.1 3 / D.N k ^ (-v)⌋ =
      f.velocityCode v p := by
  rw [residual_b hf]
  rfl

/-- Good frames with a common subpower loss allowance install the exact
frozen mesh-cap hypothesis of the residual data. Both native flags become
the same hidden coordinate, and the velocity palette is the original one. -/
theorem residualData_caps (D : Data α) (p : Parameters D) (h1 : D.Basic) (h2 : D.Caps)
    {s₀ U' e₀' : ℝ} (hs₀ : 0 ≤ s₀) (K' Rk θ K₂ : ℕ → ℝ)
    (frames : (k : ℕ) → Option (Frame D k s₀ U'))
    (hK' : ∀ᶠ k in atTop, D.K k ≤ K' k)
    (hframes : ∀ᶠ k in atTop, ∃ f : Frame D k s₀ U', frames k = some f ∧
      FrameGood f (Rk k) (θ k) (K₂ k) e₀' ∧
      D.N k ^ (-1 : ℝ) ≤ θ k ∧ f.H * f.a₀ ≤ 1 / 4 ∧
      27 * (6 * D.K k + 5) * D.K k * (D.K k ^ 3 / θ k) ≤ K' k) :
    (residualData D s₀ U' e₀' K' frames).Caps := by
  intro R hR
  filter_upwards [eventual_good_frame_caps D p h1 h2 (U' := U') hR hs₀,
    h2 R hR, hframes, hK'] with k hcap₀ horig hframe hK
  obtain ⟨f, hf, hg, hθ, hquarter, hconstant⟩ := hframe
  intro r s v hrl hru hs hsu hvl hvu
  have hc := hcap₀ f (Rk k) (θ k) (K₂ k) e₀' hg hθ hquarter r s v hrl hru hs hsu hvl hvu
  dsimp only at hc
  have hπ := (horig r s v hrl hru hs hsu hvl hvu).1
  have hN : 0 < D.N k := lt_of_lt_of_le (by norm_num) (p.scale k)
  have hscalar : ENNReal.ofReal
      (27 * (6 * D.K k + 5) * D.K k * (D.K k ^ 3 / θ k) * D.N k ^ (-3 * r - D.d * s)) ≤
      ENNReal.ofReal (K' k * D.N k ^ (-3 * r - D.d * s)) :=
    ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hN.le _))
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact (hπ a).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hN.le _)))
  · intro angular q j
    have hh := (hc.1 q j).trans hscalar
    simpa only [residual_N, residual_K, residual_d, residual_μ hf, residual_z_frame hf,
      residual_native_frame hf] using hh
  · intro angular q j v₀
    have hh := (hc.2 q j v₀).trans (mul_le_mul' hscalar
      (le_refl (D.π k {w : ℝ | ⌊w / D.N k ^ (-v)⌋ = v₀})))
    simpa only [residual_N, residual_K, residual_d, residual_μ hf, residual_π,
      residual_z_frame hf, residual_native_frame hf, residual_velocity_frame hf] using hh

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
