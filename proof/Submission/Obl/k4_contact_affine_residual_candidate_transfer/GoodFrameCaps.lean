import Submission.Obl.k4_contact_affine_residual_candidate_transfer.FrameCaps
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.FrameNativeBounds

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open Set MeasureTheory Filter MvPolynomial
open Submission.Lib.K4ContactNormalization
open Submission.Obl.k4_critical_switching_state_preparation

noncomputable section

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable {f : Frame D k s₀ U'} {Rk θ K₂ e₀' : ℝ}

/-- The source already lies on the parent's successful full-block affine
entry. This uses the original restricted law, before any normalization. -/
theorem FrameGood.native_core_residual_bound (hg : FrameGood f Rk θ K₂ e₀') :
    ∀ᵐ p ∂(D.μ k).restrict f.core,
      |eval (D.x k p.1 p.2) (affineBase (f.pal 0 f.i₀ f.u₀)) - (D.x k p.1 p.2) 3| ≤
        f.H * f.a₀ := by
  filter_upwards [ae_restrict_mem hg.core_meas] with p hp
  obtain ⟨hl, ht⟩ := hg.core_parent_event hp
  have hentry : p.1 ∈ f.entry 0 f.i₀ f.u₀ := f.hist_subset_entry 0 f.i₀ f.u₀ hl
  have hfit : p.1 ∈ affineFitSet (D.b k) (f.pal 0 f.i₀ f.u₀)
      (f.left 0 f.i₀) (f.right 0 f.i₀) (f.H * f.a₀) := hentry.1.2
  exact hfit p.2 ht

/-- Actual normalized pure and angular caps of every good frame, after
one common original sample tail. Only the subpower history loss and the
small parent affine error remain as inputs to frame construction. -/
theorem eventual_good_frame_caps (D : Data α) (p : Parameters D) (h1 : D.Basic) (h2 : D.Caps)
    {R s₀ U' : ℝ} (hR : 1 < R) (hs₀ : 0 ≤ s₀) :
    ∀ᶠ k in atTop, ∀ (f : Frame D k s₀ U') (Rk θ K₂ e₀' : ℝ),
      FrameGood f Rk θ K₂ e₀' → D.N k ^ (-1 : ℝ) ≤ θ → f.H * f.a₀ ≤ 1 / 4 →
      ∀ r s v : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R →
      let C := 27 * (6 * D.K k + 5) * D.K k * (D.K k ^ 3 / θ) *
        D.N k ^ (-3 * r - D.d * s)
      (∀ (q : Fin 3 → ℤ) (j : ℤ),
        f.resμ {x | f.baseCode r x = q ∧ f.hiddenCode s x = j} ≤ ENNReal.ofReal C) ∧
      (∀ (q : Fin 3 → ℤ) (j v₀ : ℤ),
        f.resμ {x | f.baseCode r x = q ∧ f.hiddenCode s x = j ∧ f.velocityCode v x = v₀} ≤
          ENNReal.ofReal C * D.π k {w : ℝ | ⌊w / D.N k ^ (-v)⌋ = v₀}) := by
  have hB : 0 ≤ 5 * s₀ + 7 := by linarith
  have hA : 0 ≤ 2 * s₀ + 5 := by linarith
  filter_upwards [eventual_frame_caps D p h1 h2 (U' := U') hB hA hR hs₀,
    p.subpower.2 1 (by norm_num)] with k hk hKN
  rw [Real.rpow_one] at hKN
  intro f Rk θ K₂ e₀' hg hθ hquarter r s v hrl hru hs hsu hvl hvu
  have hmass : ENNReal.ofReal (D.N k ^ (-(5 * s₀ + 7))) ≤
      ((D.μ k).restrict f.core) univ := by
    simpa only [Measure.restrict_apply_univ] using
      hg.native_core_fixed_power hs₀ p.dimension_lt_one.le p.rate_le_one hKN hθ
  have hfit : ∀ᵐ x ∂(D.μ k).restrict f.core,
      |eval (D.x k x.1 x.2) (affineBase (f.pal 0 f.i₀ f.u₀)) - (D.x k x.1 x.2) 3| ≤ 1 / 4 := by
    filter_upwards [hg.native_core_residual_bound] with x hx
    exact hx.trans hquarter
  have hJ : 0 ≤ D.K k ^ 3 / θ := by have := hg.K_ge; have := hg.θ_pos; positivity
  exact hk f hg.parent_pos.ne' hmass hfit
    (hg.native_matrix_rows hs₀ p.rate_le_one hKN) (D.K k ^ 3 / θ) hJ
    hg.native_reference_bound r s v hrl hru hs hsu hvl hvu

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
