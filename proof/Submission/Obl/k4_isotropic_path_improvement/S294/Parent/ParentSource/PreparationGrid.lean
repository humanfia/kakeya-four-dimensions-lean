-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.PreparationGrid, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/PreparationGrid.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1046 (branch x0943), commit 40b071c3e1be70138434c7f18ff663f9c27a6dfa,
Submission/Obl/k4_staged_weak_breadth_discovery/PreparationGrid.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.StagedInterface
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.TransferGrid
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.WindowGridNumerics

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

/-- Numerical data for one fixed middle-quarter window. No source problem,
path, output tolerance or atlas slack occurs in these choices. -/
structure PreparationGrid (κ₁ ρ S η χ : ℝ) where
  m : ℕ
  C : ℕ
  levels : Finset ℕ
  gain : ℝ
  δ₀ : ℝ
  valid : grid κ₁ ρ m (transferScale m) gain δ₀ (χ * gain / 8)
  gain_small : gain ≤ 1 / 32
  gain_angular : gain ≤ S / 67108864
  gain_horizon : gain ≤ 16 * η
  tolerance : δ₀ ≤ χ * gain / 1000
  window_pos : 1 ≤ C
  window_low : 2 * gain ≤ (C : ℝ) / m
  window_high : (C : ℝ) / m ≤ 3 * gain
  middle : ∀ i ∈ levels, i < m ∧ i + C < m ∧
    1 / 4 ≤ transferScale m i ∧ transferScale m i ≤ 1 / 2
  entropy_gap : ∀ z : ℝ, 0 < z →
    2 * (C : ℝ) * (4 * z + 4 * z) <
      (levels.card : ℝ) * ((65536 * gain * z) * (1 / 128))

/-- Every requested gain bound allows this window, with arbitrarily small
positive breadth-to-gain ratio. -/
theorem exists_preparationGrid {κ₁ ρ S η χ e0 : ℝ}
    (hκ₁ : 0 < κ₁) (hρ : 0 < ρ) (hS : 0 < S) (hη : 0 < η)
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) (he0 : 0 < e0) :
    ∃ q : PreparationGrid κ₁ ρ S η χ, q.gain ≤ e0 := by
  let gain : ℝ := min e0 (min (1 / 32) (min (S / 67108864) (16 * η)))
  have hg : 0 < gain := by dsimp [gain]; positivity
  have hge : gain ≤ e0 := min_le_left _ _
  have hg32 : gain ≤ 1 / 32 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hgS : gain ≤ S / 67108864 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hgη : gain ≤ 16 * η :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let δ₀ : ℝ := min (χ * gain) (ρ * gain) / 1000
  have hδ : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hδχ : δ₀ ≤ χ * gain / 1000 :=
    div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hδρ : δ₀ ≤ ρ * gain / 1000 :=
    div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hχg : χ * gain ≤ gain := mul_le_of_le_one_left hg.le hχ1
  obtain ⟨m, C, levels, hm, heven, hm2, _, hmesh, hC,
      hClow, hChigh, _, hmiddle, hgap⟩ :=
    Native.exists_native_window_grid hg hg32 (div_pos hg hκ₁)
  have hgrid : grid κ₁ ρ m (transferScale m) gain δ₀ (χ * gain / 8) := by
    refine ⟨transferScale_valid hm, hg, by linarith, hδ, ?_, heven, hm2,
      (fun _ => rfl), hmesh, ?_, ?_, ?_, by positivity, ?_⟩ <;> nlinarith
  refine ⟨{
    m := m
    C := C
    levels := levels
    gain := gain
    δ₀ := δ₀
    valid := hgrid
    gain_small := hg32
    gain_angular := hgS
    gain_horizon := hgη
    tolerance := hδχ
    window_pos := hC
    window_low := hClow
    window_high := hChigh
    middle := hmiddle
    entropy_gap := hgap
  }, hge⟩

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
