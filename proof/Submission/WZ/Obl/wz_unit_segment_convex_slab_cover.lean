-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_unit_segment_convex_slab_cover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_unit_segment_convex_slab_cover.Geometry
set_option linter.unusedVariables false

/-!
A convex set containing a unit segment and of volume at most `s > 0` lies in a slab
of width `8 * sqrt s`. The determinant of three displacements is at most `64 * s`,
since the translated quarter-parallelepiped lies in the set. A transverse normal
then gives the slab, whose volume inside the unit ball is at most `64 * sqrt s`.
-/

theorem WangZahlLot.wz_unit_segment_convex_slab_cover : (fun (B : Set LeanEval.Analysis.WangZahlKakeya.Space) => ∃ C : ℝ, 1 ≤ C ∧ ∀ (s : ℝ) (W : Set LeanEval.Analysis.WangZahlKakeya.Space), 0 < s → Convex ℝ W → W ⊆ B → MeasureTheory.volume W ≤ ENNReal.ofReal s → (∃ x v : LeanEval.Analysis.WangZahlKakeya.Space, ‖v‖ = 1 ∧ segment ℝ x (x + v) ⊆ W) → ∃ (u : LeanEval.Analysis.WangZahlKakeya.Space) (a r : ℝ), ‖u‖ = 1 ∧ 0 < r ∧ W ⊆ (B ∩ {p | |inner ℝ u p - a| ≤ r}) ∧ MeasureTheory.volume (B ∩ {p | |inner ℝ u p - a| ≤ r}) ≤ ENNReal.ofReal (C * s ^ (1/2 : ℝ))) (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) := by
  refine ⟨64, by norm_num, ?_⟩
  intro s W hs hW hWB hvol hseg
  obtain ⟨x, v, hv, hseg⟩ := hseg
  obtain ⟨u, hu, hthin⟩ :=
    WangZahlLot.Obl.wz_unit_segment_convex_slab_cover.exists_thin_slab hs hW hvol hv hseg
  refine ⟨u, inner ℝ u x, 8 * Real.sqrt s, hu,
    mul_pos (by norm_num) (Real.sqrt_pos.mpr hs), ?_, ?_⟩
  · exact fun p hp => ⟨hWB hp, hthin p hp⟩
  · have h := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.slab_volume_le hu
      (inner ℝ u x) (8 * Real.sqrt s) (by positivity)
    convert h using 1
    rw [Real.sqrt_eq_rpow]
    congr 1
    ring
