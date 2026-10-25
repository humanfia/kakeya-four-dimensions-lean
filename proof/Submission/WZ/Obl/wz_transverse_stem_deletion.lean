-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_transverse_stem_deletion.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_transverse_stem_deletion.Geometry
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_transverse_stem_deletion`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_transverse_stem_deletion`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_transverse_stem_deletion/`
belong to this obligation.
-/

theorem WangZahlLot.wz_transverse_stem_deletion : ∀ b : ℝ, 0 < b → b ≤ 1 → ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ∀ δ rho : ℝ, 0 < δ → 0 < rho → rho ≤ 1 → δ ≤ a * rho → ∀ (x v y w : LeanEval.Analysis.WangZahlKakeya.Space) (Y : Set LeanEval.Analysis.WangZahlKakeya.Space), ‖v‖ = 1 → ‖w‖ = 1 → b ≤ min ‖v - w‖ ‖v + w‖ → MeasurableSet Y → Y ⊆ Metric.thickening δ (segment ℝ x (x + v)) → ENNReal.ofReal (rho * δ ^ 2) ≤ MeasureTheory.volume Y → ENNReal.ofReal ((rho / 2) * δ ^ 2) ≤ MeasureTheory.volume (Y \ Metric.thickening (a * rho) (Set.range (fun t : ℝ => y + t • w))) := by
  intro b hb hb1
  refine ⟨b / 32768, by positivity, by linarith, ?_⟩
  intro δ rho hδ hrho hrho1 hδsmall x v y w Y hv hw hsep hY hYtube hdensity
  have hr : 0 < b / 32768 * rho := by positivity
  have hbound := WangZahlLot.Obl.wz_transverse_stem_deletion.tube_line_intersection_volume_le
    (x := x) (y := y) hδ hr hb hv hw hsep
  have hcoef : 128 * (8 * (δ + b / 32768 * rho) / b + δ) ≤ rho / 2 := by
    have hd : δ ≤ rho / 32768 := by
      calc
        δ ≤ b / 32768 * rho := hδsmall
        _ ≤ 1 / 32768 * rho := by gcongr
        _ = rho / 32768 := by ring
    have hddiv : 8 * (δ + b / 32768 * rho) / b ≤ rho / 2048 := by
      apply (div_le_iff₀ hb).mpr
      nlinarith
    linarith
  have hremoved : MeasureTheory.volume
      (Y ∩ Metric.thickening (b / 32768 * rho) (Set.range (fun t : ℝ => y + t • w))) ≤
      ENNReal.ofReal ((rho / 2) * δ ^ 2) := by
    refine (MeasureTheory.measure_mono (Set.inter_subset_inter_left _ hYtube)).trans
      (hbound.trans ?_)
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcoef (sq_nonneg δ))
  calc
    ENNReal.ofReal ((rho / 2) * δ ^ 2) =
        ENNReal.ofReal (rho * δ ^ 2) - ENNReal.ofReal ((rho / 2) * δ ^ 2) := by
      rw [← ENNReal.ofReal_sub _ (by positivity : 0 ≤ (rho / 2) * δ ^ 2)]
      congr 1
      ring
    _ ≤ MeasureTheory.volume Y - MeasureTheory.volume
        (Y ∩ Metric.thickening (b / 32768 * rho) (Set.range (fun t : ℝ => y + t • w))) :=
      tsub_le_tsub hdensity hremoved
    _ ≤ MeasureTheory.volume (Y \ (Y ∩ Metric.thickening (b / 32768 * rho)
        (Set.range (fun t : ℝ => y + t • w)))) := MeasureTheory.le_measure_sdiff
    _ = _ := by congr 1; ext p; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto
