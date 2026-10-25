-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_iteration.Base.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_iteration.Basic
import Submission.WZ.Obl.wz_normalized_projection_iteration.Iteration

namespace WangZahlLot.Obl.wz_normalized_projection_iteration

open MeasureTheory

/-- A single coarse/fine comparison supplies a uniform initial exponent. -/
theorem estimate_two (h : CoarseFine) : Estimate 2 := by
  obtain ⟨η, hη, d0, hd0, h⟩ := h (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨η, hη, d0, hd0, ?_⟩
  intro δ hδ hd hδ1 n x v Y hY hv hF f hf hf0
  obtain ⟨ρ, hρδ, hρ1, Z, hZm, hZY, hmass, harea⟩ :=
    h δ hδ hd hδ1 n x v Y hY hv hF f hf hf0
  have hρ : 0 < ρ := (Real.rpow_pos_of_pos hδ _).trans hρδ
  have hZ := projection_nonempty f (shading_nonempty hδ hY.1 hmass)
  have hb := terminal_area_bound hδ hρ hρ1.le (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    hρδ.le hZ
  norm_num at hb
  rw [Real.rpow_two]
  apply hb.trans (harea.trans _)
  apply measure_mono
  exact projection_mono f (Set.iUnion_mono hZY)

end WangZahlLot.Obl.wz_normalized_projection_iteration
