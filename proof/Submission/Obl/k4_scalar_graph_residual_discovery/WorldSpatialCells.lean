/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file WorldSpatialCells.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.ZoomScalar
import Submission.Obl.k4_scalar_graph_residual_discovery.SpatialCaps

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice

namespace Zoom

noncomputable section

theorem physical_position_near_center {ρ : ℝ} (hρ : 0 < ρ) {q : Fin 5 → ℤ}
    {l : ScalarLine} (hl : cell ρ l.2 = q) {t : ℝ} (ht : |t| ≤ 1) :
    ‖scalarPosition (l, t) - scalarPosition (center ρ q, t)‖ ≤ 3 * ρ := by
  have hy := abs_y_le_two hρ hl ht
  rw [y_eq, abs_div, abs_of_pos hρ] at hy
  have hx := abs_x_le_three hρ hl ht
  rw [x_eq, abs_div, abs_of_pos hρ] at hx
  have hyρ := (div_le_iff₀ hρ).mp hy
  have hxρ := (div_le_iff₀ hρ).mp hx
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 3 * ρ)).mpr
  intro e
  fin_cases e
  · change |t - t| ≤ 3 * ρ
    simp only [sub_self, abs_zero]
    positivity
  · change |scalarY l t - scalarY (center ρ q) t| ≤ 3 * ρ
    linarith
  · change |scalarX l t - scalarX (center ρ q) t| ≤ 3 * ρ
    exact hxρ

/-- At any fixed time a full coefficient world meets only an absolute
number of assigned coarse physical cells. The original fine-state
assignment is retained. -/
theorem world_assigned_coarse_cell_list {ρ b : ℝ} (hρ : 0 < ρ) (hb : 0 < b) (hbρ : b ≤ ρ)
    (q : Fin 5 → ℤ) {t : ℝ} (ht : |t| ≤ 1) :
    ∃ L : Finset (Fin 3 → ℤ), (L.card : ℝ) ≤ 1331 ∧
      ∀ l : ScalarLine, cell ρ l.2 = q →
        cell ρ (leftCorner b (cell b (scalarPosition (l, t)))) ∈ L := by
  let c := scalarPosition (center ρ q, t)
  let a : Fin 3 → ℝ := fun e => c e - 4 * ρ
  let L := cubeIndices ρ (9 * ρ) a
  refine ⟨L, ?_, ?_⟩
  · have hc := card_cubeIndices hρ (by positivity : 0 ≤ 9 * ρ) a
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc
    rw [ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)] at hreal
    exact hreal.trans_eq (by field_simp; norm_num)
  · intro l hl
    let p := scalarPosition (l, t)
    let z := leftCorner b (cell b p)
    have hround : ‖z - p‖ ≤ b := by simpa only [norm_sub_rev] using norm_sub_leftCorner_le hb p
    have hactual : ‖p - c‖ ≤ 3 * ρ := physical_position_near_center hρ hl ht
    have hdist : ‖z - c‖ ≤ 4 * ρ := by
      have hh : ‖z - c‖ ≤ ‖z - p‖ + ‖p - c‖ := by
        simpa only [dist_eq_norm] using dist_triangle z p c
      exact hh.trans ((add_le_add hround hactual).trans (by linarith))
    apply cell_mem_cubeIndices hρ a z
    intro e
    have he : |z e - c e| ≤ 4 * ρ := (norm_le_pi_norm (z - c) e).trans hdist
    have he' := abs_le.mp he
    dsimp only [a]
    constructor <;> linarith only [he'.1, he'.2, hρ]

end

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
