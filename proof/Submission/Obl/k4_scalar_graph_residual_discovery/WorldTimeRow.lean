/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file WorldTimeRow.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.TimeRow
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldSpatialCells
import Submission.Obl.k4_scalar_graph_residual_discovery.CurveCells

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice

namespace Zoom

noncomputable section

def worldRowConstant (Hc Krow : ℝ) : ℝ := Krow + 3 * Hc + 3

/-- A coefficient world supplies the geometric hypotheses of the time-row
construction internally. The same original incidences are retained; only a
measurable time function is selected. No residual comparison is assumed. -/
theorem exists_world_time_row {E : Set ScalarIncidence} {ρ b Hc Krow Hrow : ℝ}
    (hρ : 0 < ρ) (hHc : 1 ≤ Hc) (hKrow : 0 ≤ Krow) (hHrow : 0 ≤ Hrow)
    (q : Fin 5 → ℤ) (G : (Fin 3 → ℤ) → Fin 2 → ℝ)
    (hworld : ∀ p ∈ E, cell ρ p.1.2 = q)
    (htime : ∀ p ∈ E, p.2 ∈ Icc (0 : ℝ) 1)
    (hcenter : ∀ e, |(center ρ q).2 e| ≤ Hc)
    (hbound : ∀ p ∈ E, |G (cell b (scalarPosition p)) 1| ≤ Hrow)
    (hcompare : ∀ p ∈ E, ∀ p' ∈ E,
      |G (cell b (scalarPosition p)) 1 - G (cell b (scalarPosition p')) 1| ≤
        Krow * (‖scalarPosition p - scalarPosition p'‖ + ρ)) :
    ∃ F : ℝ → ℝ, Measurable F ∧ (∀ t, |F t| ≤ Hrow) ∧
      (∀ p ∈ E, |G (cell b (scalarPosition p)) 1 - F p.2| ≤
        4 * worldRowConstant Hc Krow ^ 2 * ρ) ∧
      ∀ p ∈ E, ∀ p' ∈ E,
        |F p.2 - F p'.2| ≤ 12 * worldRowConstant Hc Krow ^ 2 * (|p.2 - p'.2| + ρ) := by
  have hK : 1 ≤ worldRowConstant Hc Krow := by dsimp only [worldRowConstant]; linarith
  have hthree : 3 ≤ worldRowConstant Hc Krow := by dsimp only [worldRowConstant]; linarith
  have hcentral : 3 * Hc ≤ worldRowConstant Hc Krow := by
    dsimp only [worldRowConstant]
    linarith
  have hrowle : Krow ≤ worldRowConstant Hc Krow := by
    dsimp only [worldRowConstant]
    linarith
  obtain ⟨F, hF, hFbound, happrox, hcmp⟩ := exists_time_only_row E scalarPosition
    (fun t => scalarPosition (center ρ q, t)) (fun p => G (cell b (scalarPosition p)) 1)
    hK hHrow hρ hbound
    (by
      intro p hp
      have ht : |p.2| ≤ 1 := by
        rw [abs_of_nonneg (htime p hp).1]
        exact (htime p hp).2
      exact (physical_position_near_center hρ (hworld p hp) ht).trans
        (mul_le_mul_of_nonneg_right hthree hρ.le))
    (by
      intro p hp p' hp'
      exact (scalarPosition_time_lipschitz hHc (center ρ q) hcenter
        (htime p hp) (htime p' hp')).trans
          (mul_le_mul_of_nonneg_right hcentral (abs_nonneg _)))
    (by
      intro p hp p' hp'
      exact (hcompare p hp p' hp').trans
        (mul_le_mul_of_nonneg_right hrowle (by positivity)))
  refine ⟨F, hF, hFbound, ?_, hcmp⟩
  intro p hp
  simpa only [abs_sub_comm] using happrox p hp

end

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
