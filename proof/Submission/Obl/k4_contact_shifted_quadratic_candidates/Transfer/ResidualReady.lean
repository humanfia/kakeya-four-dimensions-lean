/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/ResidualReady.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.GoodFramesResidual
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.GoodFrameBasic
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.FrameDataCaps
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.FrameParameters
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.MeshCalibration

/-!
# The residual model on good frames meets every horizontal hypothesis

One common subpower loss `K'` dominates, at every index with a frame, the
original density, the palette fit constant, the conditional prior envelope and
the inverse core fraction (basic bounds), and eventually the residual cap
constant and the atlas constant. With it the residual model has the frozen
parameters, basic bounds, mesh caps, atlas and nesting. This is the
`ResidualReady` interface of o260 (`Shifted/Main.lean`), restated over this
obligation's frames.
-/

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open MeasureTheory Set Filter
open Submission.Obl.k4_critical_switching_state_preparation

noncomputable section

variable {α : Type} [MeasurableSpace α] {D : Data α} {s₀ U' e₀' : ℝ}

namespace GoodFrames

variable (gf : GoodFrames D s₀ U' e₀')

/-- The conditional prior envelope at an index. -/
def priorK (k : ℕ) : ℝ :=
  2 * D.K k + 2 * D.K k ^ 2 + 2 * (gf.K₂ k + D.K k + 1) * D.K k + (gf.K₂ k + D.K k + 1)

/-- The common loss of the residual model. -/
def lossK (A₀ : ℝ) (k : ℕ) : ℝ :=
  max (max (max 1 (D.K k)) (max (gf.Hk k) (gf.priorK k)))
    (max (max (gf.θ k)⁻¹ (gf.capC k)) (gf.atlasK A₀ k))

theorem one_le_lossK (A₀ : ℝ) (k : ℕ) : 1 ≤ gf.lossK A₀ k :=
  (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))

variable (p : Parameters D)
include p

theorem small_priorK : Small D.N gf.priorK := by
  have hN1 := N_one p
  have hN0 : ∀ k, 0 ≤ D.N k := fun k => by linarith [hN1 k]
  have hNt := p.scale_limit
  have hK := small_K p
  have hK₂ := gf.small_K₂ p
  have hs : Small D.N (fun k => gf.K₂ k + D.K k + 1) :=
    (hK₂.add hNt hK).add hNt (Small.const hNt zero_le_one)
  have h2 := Small.const hNt (N := D.N) (by norm_num : (0 : ℝ) ≤ 2)
  exact ((((h2.mul hN0 hK).add hNt (h2.mul hN0 (hK.pow hN0 hNt 2))).add hNt
    ((h2.mul hN0 hs).mul hN0 hK)).add hNt hs).congr fun k => rfl

theorem small_lossK {A₀ : ℝ} (hA₀ : 0 ≤ A₀) : Small D.N (gf.lossK A₀) := by
  have hNt := p.scale_limit
  exact ((((Small.const hNt zero_le_one).max hNt (small_K p)).max hNt
    ((gf.small_Hk p).max hNt (gf.small_priorK p))).max hNt
    (((gf.small_θinv p).max hNt (gf.small_capC p)).max hNt
      (gf.small_atlasK p hA₀))).congr fun k => rfl

end GoodFrames

/-- The residual model on good frames meets every horizontal hypothesis. -/
theorem GoodFrames.residualReady (gf : GoodFrames D s₀ U' e₀') (p : Parameters D)
    (h1 : D.Basic) (h2 : D.Caps) (hcal : MeshCalibration) (hs₀ : 0 < s₀) (hU' : 0 < U')
    (he₀' : 0 < e₀') :
    ∃ K' : ℕ → ℝ,
      Parameters (residualData D s₀ U' e₀' K' gf.fr) ∧
      (residualData D s₀ U' e₀' K' gf.fr).Basic ∧
      (residualData D s₀ U' e₀' K' gf.fr).Caps ∧
      (residualData D s₀ U' e₀' K' gf.fr).Atlas ∧
      (residualData D s₀ U' e₀' K' gf.fr).Nested := by
  obtain ⟨A₀, hA₀, hA⟩ := affine_box_slopes hcal
  have hA₀0 : 0 ≤ A₀ := by linarith
  set K' := gf.lossK A₀ with hK'def
  have hsmall := gf.small_lossK p hA₀0
  have hK'1 : ∀ k, 1 ≤ K' k := gf.one_le_lossK A₀
  have hKle : ∀ k, D.K k ≤ K' k := fun k =>
    (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨K', residualData_parameters D p gf.fr hU' he₀' ⟨hK'1, hsmall.2⟩, ?_, ?_, ?_,
    gf.residual_nested p hU' K'⟩
  · -- basic bounds at every index with a frame
    refine residualData_basic D p h1 s₀ U' e₀' K' gf.fr hK'1 fun k f hf => ?_
    have hg := gf.good k f hf
    have hHf := GoodFrames.Hk_eq hf
    have hθ := hg.θ_pos
    have hθle : (gf.θ k)⁻¹ ≤ K' k :=
      (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
    refine hg.basic_bounds h1 (hKle k) ?_ ?_ ?_
    · rw [← hHf]
      exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
    · -- the original rho floor of the core
      have hK'pos : 0 < K' k := lt_of_lt_of_le one_pos (hK'1 k)
      have hinv : (K' k)⁻¹ ≤ gf.θ k := by
        rw [inv_le_comm₀ hK'pos hθ]
        exact hθle
      have hsub : f.parentSet ⊆ D.A k (f.depth 0) f.i₀ := f.hist_subset_A 0 f.i₀ f.u₀
      have hq := f.q₀_pos
      calc ENNReal.ofReal (K' k)⁻¹ * f.scale
          = ENNReal.ofReal ((K' k)⁻¹ * f.q₀) * D.ν k f.parentSet := by
            rw [Frame.scale, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hK'pos.le)]
        _ ≤ ENNReal.ofReal (gf.θ k * f.ql 0) * D.ν k (D.A k (f.depth 0) f.i₀) := by
            gcongr
            exact f.q₀_eq.le
        _ ≤ D.ρ k f.core := gf.rho_floor k f hf
  · -- residual mesh caps
    have hK₂ := gf.small_Hk p
    have evH := hK₂.le_mul_rpow p.scale_limit (by norm_num : (0 : ℝ) < 1 / 4) hs₀
    refine residualData_caps D p h1 h2 hs₀.le K' gf.Rk gf.θ gf.K₂ gf.fr
      (Eventually.of_forall hKle) ?_
    filter_upwards [gf.eventually_some, gf.θ_large 1 one_pos, evH] with k ⟨f, hf⟩ hθk hHk
    have hg := gf.good k f hf
    have hHf := GoodFrames.Hk_eq hf
    have hNpos : 0 < D.N k := by linarith [p.scale k]
    refine ⟨f, hf, hg, hθk, ?_, ?_⟩
    · have ha : f.a₀ = D.N k ^ (-s₀) := by rw [Frame.a₀, hg.depth_zero]
      rw [ha, ← hHf]
      have h4 : D.N k ^ s₀ * D.N k ^ (-s₀) = 1 := by rw [← Real.rpow_add hNpos]; simp
      calc gf.Hk k * D.N k ^ (-s₀) ≤ 1 / 4 * D.N k ^ s₀ * D.N k ^ (-s₀) :=
            mul_le_mul_of_nonneg_right hHk (Real.rpow_nonneg hNpos.le _)
        _ = 1 / 4 := by rw [mul_assoc, h4, mul_one]
    · exact (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  · -- residual atlas
    exact gf.residual_atlas_of_model p h1 h2 hs₀ hU' hA₀ hA K'
      (Eventually.of_forall fun k => (le_max_right _ _).trans (le_max_right _ _))

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
