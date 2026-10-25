-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.CubeBudget.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.SeparatedCubes
import Submission.WZ.Obl.wz_tower_depth_step.GridShading

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open wz_nonflat_factored_improvement (gridCell gridUnion gridUnion_volume)

lemma mem_tube_apply_isometry {δ : ℝ} {x v p : Space}
    (e : Space ≃ₗᵢ[ℝ] Space) (hp : p ∈ Metric.thickening δ (segment ℝ x (x + v))) :
    e p ∈ Metric.thickening δ (segment ℝ (e x) (e x + e v)) := by
  obtain ⟨s, hs, hps⟩ := wz_balanced_cluster_cover.exists_param_of_mem_tube hp
  apply Metric.mem_thickening_iff.mpr
  refine ⟨e x + s • e v, ?_, ?_⟩
  · rw [segment_eq_image']
    exact ⟨s, hs, by simp⟩
  · rw [dist_eq_norm, ← map_smul, ← map_add, ← map_sub, e.norm_map]
    exact hps

/-- The total volume of grain cubes whose cores meet one fine tube is at most
an absolute multiple of the squared grid mesh. -/
theorem cube_cell_tube_budget {δ b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hδb : δ ≤ b)
    (e : Space ≃ₗᵢ[ℝ] Space) (x v : Space) (hv : ‖v‖ = 1)
    (F : Finset (Fin 3 → ℤ))
    (hF : ∀ j ∈ F, (Metric.thickening δ (segment ℝ x (x + v)) ∩ cubeCell b e j).Nonempty) :
    (F.card : ℝ) * (20 * b) ^ 3 ≤ 82944000 * b ^ 2 := by
  have hv' : ‖e v‖ = 1 := by simpa using hv
  have hmeet (j) (hj : j ∈ F) :
      (Metric.thickening b (segment ℝ (e x) (e x + e v)) ∩ gridCell b j).Nonempty := by
    obtain ⟨p, hpT, hpC⟩ := hF j hj
    exact ⟨e p, (Metric.thickening_mono hδb _) (mem_tube_apply_isometry e hpT), hpC⟩
  have hm := wz_tower_depth_step.gridUnion_tube_volume hb hb1 hb le_rfl hv' F hmeet
  rw [gridUnion_volume hb] at hm
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 10368 * b ^ 2)).mp hm
  have hh := mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 8000)
  nlinarith only [hh]

end WangZahlLot.Obl.wz_broad_grains_initialization
