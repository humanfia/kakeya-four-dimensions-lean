import Submission.Obl.k4_contact_affine_residual_candidate_transfer.FrameSlopeBounds
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.FrameNested

/-!
# Atlas and nesting of the residual model

The residual model installs its labels at the grid depths of its frames. Good
frames with slope bounds at every grid level give the atlas (after rounding
depths to the grid), and good frames give the nesting.
-/

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open MeasureTheory Set Filter
open Submission.Obl.k4_critical_switching_state_preparation

noncomputable section

variable {α : Type} [MeasurableSpace α] {D : Data α} {s₀ U' e₀' : ℝ} {K' : ℕ → ℝ}
  {fr : (k : ℕ) → Option (Frame D k s₀ U')}

theorem FrameSlopes.mono {k : ℕ} {f : Frame D k s₀ U'} {h : ℕ} {K₁ K₁' : ℝ}
    (hN0 : 0 ≤ D.N k) (hs : FrameSlopes f h K₁) (hK : K₁ ≤ K₁') : FrameSlopes f h K₁' := by
  intro i
  obtain ⟨h3, h1⟩ := hs i
  have hN : 0 ≤ D.N k ^ (-((h : ℝ) * (U' / f.m))) := Real.rpow_nonneg hN0 _
  refine ⟨h3.trans ?_, fun l hl t ht => (h1 l hl t ht).trans ?_⟩
  · apply mul_le_mul_of_nonneg_right hK
    have : (0 : ℝ) < ((2 : ℝ) ^ (-(f.resT h : ℤ))) ^ 2 := by positivity
    positivity
  · apply mul_le_mul_of_nonneg_right hK
    have : (0 : ℝ) < (2 : ℝ) ^ (-(f.resT h : ℤ)) := by positivity
    positivity

theorem residualSteps_pos (hm : ∀ k (f : Frame D k s₀ U'), fr k = some f → 1 ≤ f.m)
    (k : ℕ) : 0 < residualSteps D s₀ U' fr k := by
  cases hfr : fr k with
  | none => simp [residualSteps, hfr]
  | some f =>
    have := hm k f hfr
    simp only [residualSteps, hfr]
    omega

/-- The residual atlas from good frames with slope bounds at every grid level. -/
theorem residualData_atlas (hN : ∀ k, 1 ≤ D.N k) (hd : 0 ≤ D.d) (hκ : 0 ≤ D.κ)
    (hU' : 0 < U')
    (hm : ∀ k (f : Frame D k s₀ U'), fr k = some f → 1 ≤ f.m)
    (K₁ : ℕ → ℝ) (hK₁ : ∀ k, 0 < K₁ k)
    (hcost : ∀ᶠ k in atTop, K₁ k * roundCost (residualBase D s₀ U' e₀' K' fr) k
      (U' / residualSteps D s₀ U' fr k) ≤ K' k)
    (hgood : ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∃ f : Frame D k s₀ U', fr k = some f ∧
      ∃ Rk θ K₂ : ℝ, FrameGood f Rk θ K₂ e₀' ∧ R ≤ Rk ∧
        20 * D.K k ^ 3 * K₂ * f.H / θ ≤ K₁ k ∧ ∀ h ≤ f.m, FrameSlopes f h (K₁ k)) :
    (residualData D s₀ U' e₀' K' fr).Atlas := by
  have hsteps := residualSteps_pos hm
  refine atlas_withLevels (residualBase D s₀ U' e₀' K' fr) (residualLevels D s₀ U' fr)
    (fun k => U' / residualSteps D s₀ U' fr k) (residualSteps D s₀ U' fr)
    hN hd hκ hκ (fun k => div_pos hU' (by exact_mod_cast hsteps k)) ?_ K₁ hK₁ hcost ?_
  · intro k
    have h0 : (residualSteps D s₀ U' fr k : ℝ) ≠ 0 := by exact_mod_cast (hsteps k).ne'
    show (residualSteps D s₀ U' fr k : ℝ) * (U' / residualSteps D s₀ U' fr k) = U'
    field_simp
  · intro R hR
    filter_upwards [hgood R hR] with k hk
    obtain ⟨f, hf, Rk, θ, K₂, hg, hRk, hK, hsl⟩ := hk
    intro h hh
    rw [residualSteps_some hf] at hh
    show AtlasBody (residualData D s₀ U' e₀' K' fr) k R
      ((h : ℝ) * (U' / residualSteps D s₀ U' fr k)) (residualLevels D s₀ U' fr k h) (K₁ k)
    rw [residualSteps_some hf, residualLevels_some hf]
    exact hg.atlasBody hf hh (by linarith) hRk hK (hsl h hh)

/-- The residual nesting from good frames. -/
theorem residualData_nested (hU' : 0 < U')
    (hm : ∀ k (f : Frame D k s₀ U'), fr k = some f → 1 ≤ f.m)
    (hgood : ∀ᶠ k in atTop, ∃ f : Frame D k s₀ U', fr k = some f ∧
      ∃ Rk θ K₂ : ℝ, FrameGood f Rk θ K₂ e₀') :
    (residualData D s₀ U' e₀' K' fr).Nested := by
  have hsteps := residualSteps_pos hm
  refine nested_withLevels (residualBase D s₀ U' e₀' K' fr) (residualLevels D s₀ U' fr)
    (fun k => U' / residualSteps D s₀ U' fr k) (residualSteps D s₀ U' fr)
    (fun k => div_pos hU' (by exact_mod_cast hsteps k)) ?_
  filter_upwards [hgood] with k hk
  obtain ⟨f, hf, Rk, θ, K₂, hg⟩ := hk
  intro h hh
  rw [residualSteps_some hf] at hh
  rw [residualLevels_some hf, residualLevels_some hf]
  intro i
  exact hg.res_nested hh i

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
