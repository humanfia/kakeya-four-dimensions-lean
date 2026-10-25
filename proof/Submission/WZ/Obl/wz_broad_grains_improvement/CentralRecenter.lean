-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.CentralRecenter.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.Core
import Submission.WZ.Obl.wz_multiscale_finite_tower.AxisShift

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Metric Set
open WangZahlLot.Obl.wz_multiscale_finite_tower (axisMidpoint inward_axis_shift)

noncomputable section

/-- The unit segment on the same line with scalar midpoint zero. -/
def recenterStart (x v : V) : V := x - (inner ℝ v (axisMidpoint x v)) • v

theorem recenter_midpoint (x v : V) :
    axisMidpoint (recenterStart x v) v =
      axisMidpoint x v - (inner ℝ v (axisMidpoint x v)) • v := by
  dsimp [recenterStart, axisMidpoint]
  module

theorem recenter_aligned {x v : V} (hv : ‖v‖ = 1) :
    inner ℝ v (axisMidpoint (recenterStart x v) v) = 0 := by
  rw [recenter_midpoint, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq, hv]
  ring

theorem orthogonal_component_norm_le {v : V} (hv : ‖v‖ = 1) (p : V) :
    ‖p-(inner ℝ v p)•v‖ ≤ ‖p‖ := by
  have hh := norm_sub_sq_real p ((inner ℝ v p)•v)
  rw [norm_smul, Real.norm_eq_abs, hv, mul_one, sq_abs,
    inner_smul_right, real_inner_comm v p] at hh
  nlinarith [norm_nonneg (p-(inner ℝ v p)•v), norm_nonneg p,
    sq_nonneg (inner ℝ v p)]

theorem recenter_midpoint_norm {x v : V} (hv : ‖v‖ = 1) :
    ‖axisMidpoint (recenterStart x v) v‖ ≤ ‖axisMidpoint x v‖ := by
  rw [recenter_midpoint]
  exact orthogonal_component_norm_le hv _

/-- Recentring preserves the entire part of a tube in the central axial slab.
In particular no normalized shading mass is lost near the origin. -/
theorem tube_central_subset_recenter {d : ℝ} {x v p : V} (hv : ‖v‖ = 1)
    (hp : p ∈ T d x v) (hcentral : |inner ℝ v p| ≤ 1/2) :
    p ∈ T d (recenterStart x v) v := by
  obtain ⟨t, ht, hpt⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hp
  let a : ℝ := 1/2 + inner ℝ v p
  have ha : a ∈ Icc (0:ℝ) 1 := by
    obtain ⟨hlo,hhi⟩ := abs_le.mp hcentral
    constructor <;> dsimp [a] <;> linarith
  have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  let err := p-(x+t•v)
  have he : p-(recenterStart x v+a•v) = err-(inner ℝ v err)•v := by
    dsimp [recenterStart, axisMidpoint, a, err]
    simp only [inner_sub_right, inner_add_right, inner_smul_right, hvv, mul_one]
    module
  apply mem_thickening_iff.mpr
  refine ⟨recenterStart x v+a•v, ?_, ?_⟩
  · rw [segment_eq_image']
    exact ⟨a, ha, by simp⟩
  · rw [dist_eq_norm, he]
    exact (orthogonal_component_norm_le hv err).trans_lt hpt

theorem central_shading_subset_recenter {d : ℝ} {x v : V} {Y : Set V}
    (hv : ‖v‖ = 1) (hY : Y ⊆ T d x v) (hball : Y ⊆ closedBall 0 (1/2)) :
    Y ⊆ T d (recenterStart x v) v := by
  intro p hp
  apply tube_central_subset_recenter hv (hY hp)
  have hh := abs_real_inner_le_norm v p
  rw [hv, one_mul] at hh
  exact hh.trans (by simpa [mem_closedBall, dist_zero_right] using hball hp)

theorem recenter_tube_in_ball {d : ℝ} {x v : V} (hv : ‖v‖ = 1)
    (hT : T d x v ⊆ I) : T d (recenterStart x v) v ⊆ I := by
  simpa only [zero_sub, neg_smul, ← sub_eq_add_neg, recenterStart] using
    inward_axis_shift (h := 0) hv (by simp) hT

end
end WangZahlLot.Obl.wz_broad_grains_improvement
