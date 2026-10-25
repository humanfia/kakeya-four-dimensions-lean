-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.FlatBodies.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.FlatMap
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyTransport

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_regular_transverse_affine_cells
  (closedTube closedTube_convex closedTube_compact closedTube_endpoints
    closedTube_volume_bounds tube_subset_closedTube ball_subset_tube)

theorem flat_body_geometry {δ d a b : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a)
    (hab : a ≤ b) (haSmall : a ≤ 1 / 100) (hb2 : b ≤ 2) (hd : d ≤ δ / 8)
    (e : AffineIsometryEquiv ℝ Space Space) {n : ℕ} (x v : Fin n → Space)
    (hv : ∀ i, ‖v i‖ = 1) (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball (0 : Space) 1)
    (hT : ∀ i, Tube δ (x i) (v i) ⊆ e '' StandardPrism a b) :
    let f := flatMap e a b (hδ.trans_le hδa) (hδ.trans_le (hδa.trans hab))
    BodyGeometry (fun i => f '' closedTube δ (x i) (v i)) (fun i => f (x i)) d
      (δ / (1024 * a)) ((1 / (128 * a * b)) * δ ^ 2) := by
  let ha := hδ.trans_le hδa
  let hb := hδ.trans_le (hδa.trans hab)
  let f := flatMap e a b ha hb
  change BodyGeometry (fun i => f '' closedTube δ (x i) (v i)) (fun i => f (x i)) d _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (closedTube_compact (hball i)).image f.toContinuousAffineEquiv.continuous
  · intro i
    exact (closedTube_convex δ (x i) (v i)).affine_image f.toAffineMap
  · intro i p hp
    obtain ⟨p, hp, rfl⟩ := hp
    have hh := flatMap_prism_norm e ha hb
      (closedTube_subset_prism e (hT i) hp)
    exact mem_closedBall_zero_iff.mpr (hh.trans (by norm_num))
  · intro i p hp
    refine ⟨f.symm p, ?_, f.apply_symm_apply p⟩
    apply tube_subset_closedTube
    apply ball_subset_tube
    have hh := flatMap_dist_lower e ha hb hab hb2 (f.symm p) (x i)
    change dist (f.symm p) (x i) / 8 ≤ dist (f (f.symm p)) (f (x i)) at hh
    rw [f.apply_symm_apply] at hh
    have hpd := (mem_ball.mp hp).trans_le hd
    exact mem_ball.mpr (by linarith)
  · intro i
    have hends := closedTube_endpoints hδ (x i) (v i)
    refine ⟨f (x i), ⟨_, hends.1, rfl⟩, f (x i + v i), ⟨_, hends.2, rfl⟩, ?_⟩
    have hh := flatMap_dist_lower e ha hb hab hb2 (x i) (x i + v i)
    have he : dist (x i) (x i + v i) = 1 := by simp [dist_eq_norm, hv i]
    rw [he] at hh
    exact (by norm_num : (1 / 16 : ℝ) ≤ 1 / 8).trans hh
  · intro i
    exact flatMap_tube_width hδ hδa hab haSmall hb2 e (x i) (v i) (hv i) (hT i)
  · intro i
    have hδ1 : δ ≤ 1 := hδa.trans (haSmall.trans (by norm_num))
    obtain ⟨hl, hu⟩ := closedTube_volume_bounds hδ hδ1 (x i) (v i) (hv i)
    change ENNReal.ofReal _ ≤ volume (flatMap e a b ha hb '' _) ∧ _
    rw [flatMap_volume]
    constructor
    · rw [ENNReal.ofReal_mul (by positivity)]
      exact mul_le_mul' le_rfl hl
    · calc
        _ ≤ ENNReal.ofReal (1 / (128 * a * b)) * ENNReal.ofReal (384 * δ ^ 2) :=
          mul_le_mul' le_rfl hu
        _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

end WangZahlLot.Obl.wz_flat_factored_improvement
