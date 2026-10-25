-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.BaseCapChange, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/BaseCapChange.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/BaseCapChange.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/BaseCapChange.lean.
-- Existing source attributions are preserved below.

import Submission.Lib.K4ChartLifting.NormDensity

/-! # Original continuous caps under a fixed old chart change -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory
open scoped ENNReal

theorem map_chart_base_volume (F : Submission.Lib.K4ChartLifting.Frame)
    (hq : 0 < F.q) (hD : F.D.det ≠ 0) :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).map F.obsBase =
      ENNReal.ofReal (F.q * |F.D.det|) • volume := by
  rw [F.map_obsBase_volume hq.ne' (isUnit_iff_ne_zero.mpr hD), F.det_obsMatrix,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  simp only [abs_mul, abs_inv, abs_of_pos hq, mul_inv_rev, inv_inv, mul_comm]

/-- An original-law base cap transports through the fixed old frame with
the actual Jacobian `q * |det D|`. -/
theorem base_cap_under_chart_change {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (base : Ω → EuclideanSpace ℝ (Fin 3)) (hbase : Measurable base)
    (F : Submission.Lib.K4ChartLifting.Frame) (hq : 0 < F.q) (hD : F.D.det ≠ 0)
    (C : ENNReal) (hcap : μ.map base ≤ C • volume) :
    μ.map (F.obsBase ∘ base) ≤ (C * ENNReal.ofReal (F.q * |F.D.det|)) • volume := by
  calc
    _ = (μ.map base).map F.obsBase := (Measure.map_map F.measurable_obsBase hbase).symm
    _ ≤ (C • volume).map F.obsBase := Measure.map_mono hcap F.measurable_obsBase
    _ = C • (volume.map F.obsBase) := Measure.map_smul C F.measurable_obsBase.aemeasurable
    _ = _ := by rw [map_chart_base_volume F hq hD, smul_smul]

/-- The lower floor of the FULL old line assignment cancels both the time
Jacobian and the old spatial determinant, in original reference units. -/
theorem old_packet_budget_cancels_jacobian {N κ q d : ℝ}
    (hN : 0 < N) (hκ : 0 < κ) (hq : 0 < q) (hd : 0 < d) (f₀ : ℝ)
    {m : ENNReal} (hfloor : ENNReal.ofReal (N ^ (-f₀) * d / κ) ≤ m) :
    (m * ENNReal.ofReal q)⁻¹ * ENNReal.ofReal (q * d) ≤
      ENNReal.ofReal (κ * N ^ f₀) := by
  have hscaled : ENNReal.ofReal (N ^ (-f₀) * d / κ * q) ≤ m * ENNReal.ofReal q := by
    rw [ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul' hfloor le_rfl
  calc
    _ ≤ (ENNReal.ofReal (N ^ (-f₀) * d / κ * q))⁻¹ * ENNReal.ofReal (q * d) :=
      mul_le_mul' (ENNReal.inv_le_inv.mpr hscaled) le_rfl
    _ = ENNReal.ofReal ((N ^ (-f₀) * d / κ * q)⁻¹ * (q * d)) := by
      rw [ENNReal.ofReal_mul (show 0 ≤ (N ^ (-f₀) * d / κ * q)⁻¹ by positivity),
        ENNReal.ofReal_inv_of_pos (show 0 < N ^ (-f₀) * d / κ * q by positivity)]
    _ = _ := by
      congr 1
      rw [Real.rpow_neg hN.le]
      field_simp [hκ.ne', hq.ne', hd.ne', ne_of_gt (Real.rpow_pos_of_pos hN f₀)]

/-- Scale a capped original incidence law by its fixed old packet budget.
The bound retains the fine density cap and only the old profile power. -/
theorem base_cap_in_old_packet_units {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (base : Ω → EuclideanSpace ℝ (Fin 3)) (hbase : Measurable base)
    (F : Submission.Lib.K4ChartLifting.Frame) (hq : 0 < F.q) (hD : F.D.det ≠ 0)
    {N κ : ℝ} (hN : 0 < N) (hκ : 0 < κ) (f₀ : ℝ) (m C : ENNReal)
    (hfloor : ENNReal.ofReal (N ^ (-f₀) * |F.D.det| / κ) ≤ m)
    (hcap : μ.map base ≤ C • volume) :
    (m * ENNReal.ofReal F.q)⁻¹ • μ.map (F.obsBase ∘ base) ≤
      (C * ENNReal.ofReal (κ * N ^ f₀)) • volume := by
  have hj := old_packet_budget_cancels_jacobian hN hκ hq (abs_pos.mpr hD) f₀ hfloor
  have ht := base_cap_under_chart_change μ base hbase F hq hD C hcap
  calc
    _ ≤ (m * ENNReal.ofReal F.q)⁻¹ •
        ((C * ENNReal.ofReal (F.q * |F.D.det|)) • volume) := smul_le_smul_left _ ht
    _ = (C * ((m * ENNReal.ofReal F.q)⁻¹ *
        ENNReal.ofReal (F.q * |F.D.det|))) • volume := by rw [smul_smul]; congr 1; ring
    _ ≤ _ := by gcongr

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
