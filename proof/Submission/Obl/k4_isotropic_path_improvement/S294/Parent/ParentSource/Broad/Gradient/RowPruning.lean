-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.RowPruning, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/RowPruning.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/RowPruning.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.CoreLipschitz

/-!
# Short rows cost little

For a measurable set `U` of incidences, the time set `{τ | (l, t + h τ) ∈ U}` of an incidence
`(l, t) ∈ U` has volume `h⁻¹ · |U_l|` (`U_l` the time section of `U` at `l`), the same for
every incidence on the line. Incidences whose row is short (volume `< θ`) therefore fill at
most time `θ h` on each line, and `(ν ⊗ dt)` of them is at most `θ h ν(A)` when the lines of
`U` lie in `A`.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set

noncomputable section

/-- The row volume of an incidence. -/
def rowVolume (U : Set Event) (h : ℝ) (q : Event) : ENNReal :=
  volume {τ : ℝ | (q.1, q.2 + h * τ) ∈ U}

theorem measurable_rowVolume {U : Set Event} (hU : MeasurableSet U) (h : ℝ) :
    Measurable (rowVolume U h) := by
  let S : Set (Event × ℝ) := {x | (x.1.1, x.1.2 + h * x.2) ∈ U}
  have hS : MeasurableSet S := by
    have hm : Measurable (fun x : Event × ℝ => ((x.1.1, x.1.2 + h * x.2) : Event)) :=
      (measurable_fst.fst).prodMk (measurable_fst.snd.add (measurable_const.mul measurable_snd))
    exact hm hU
  have hmeas := measurable_measure_prodMk_left (ν := (volume : Measure ℝ)) hS
  have heq : rowVolume U h = fun x => volume (Prod.mk x ⁻¹' S) := by
    funext q
    rfl
  rw [heq]
  exact hmeas

/-- On a line, the row volume is the time volume of the section, rescaled. -/
theorem rowVolume_eq (U : Set Event) {h : ℝ} (hh : 0 < h) (q : Event) :
    rowVolume U h q = ENNReal.ofReal h⁻¹ * volume {t : ℝ | (q.1, t) ∈ U} := by
  unfold rowVolume
  have hset : {τ : ℝ | (q.1, q.2 + h * τ) ∈ U} =
      (fun τ : ℝ => h * τ) ⁻¹' ((fun x : ℝ => q.2 + x) ⁻¹' {t : ℝ | (q.1, t) ∈ U}) := by
    ext τ
    simp
  rw [hset, Real.volume_preimage_mul_left hh.ne', measure_preimage_add, abs_of_pos (inv_pos.mpr hh)]

/-- **Short rows.** -/
theorem short_rows_mass_le (ν : Measure Line) [SFinite ν] {A : Set Line} (hA : MeasurableSet A)
    {U : Set Event} (hU : MeasurableSet U) (hUA : ∀ q ∈ U, q.1 ∈ A)
    {h θ : ℝ} (hh : 0 < h) :
    (ν.prod volume) (U ∩ {q | rowVolume U h q < ENNReal.ofReal θ}) ≤
      ENNReal.ofReal (θ * h) * ν A := by
  have hmeas : MeasurableSet (U ∩ {q | rowVolume U h q < ENNReal.ofReal θ}) :=
    hU.inter (measurableSet_lt (measurable_rowVolume hU h) measurable_const)
  rw [Measure.prod_apply hmeas]
  have hsection (l : Line) :
      volume (Prod.mk l ⁻¹' (U ∩ {q | rowVolume U h q < ENNReal.ofReal θ})) ≤
        A.indicator (fun _ => ENNReal.ofReal (θ * h)) l := by
    by_cases hl : l ∈ A
    · rw [Set.indicator_of_mem hl]
      by_cases hshort : ENNReal.ofReal h⁻¹ * volume {t : ℝ | (l, t) ∈ U} < ENNReal.ofReal θ
      · calc
          _ ≤ volume {t : ℝ | (l, t) ∈ U} := measure_mono (fun t ht => ht.1)
          _ ≤ ENNReal.ofReal (θ * h) := by
            have hh' : ENNReal.ofReal h⁻¹ ≠ 0 := by
              rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
            have hfin : ENNReal.ofReal h⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
            have hle := hshort.le
            calc
              volume {t : ℝ | (l, t) ∈ U} =
                  ENNReal.ofReal h * (ENNReal.ofReal h⁻¹ * volume {t : ℝ | (l, t) ∈ U}) := by
                rw [← mul_assoc, ← ENNReal.ofReal_mul hh.le, mul_inv_cancel₀ hh.ne',
                  ENNReal.ofReal_one, one_mul]
              _ ≤ ENNReal.ofReal h * ENNReal.ofReal θ := mul_le_mul' le_rfl hle
              _ = ENNReal.ofReal (θ * h) := by
                rw [← ENNReal.ofReal_mul hh.le, mul_comm]
      · have hempty : Prod.mk l ⁻¹' (U ∩ {q | rowVolume U h q < ENNReal.ofReal θ}) = ∅ := by
          ext t
          simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false,
            not_and]
          intro _ hrow
          rw [rowVolume_eq U hh] at hrow
          exact hshort hrow
        rw [hempty, measure_empty]
        exact zero_le
    · rw [Set.indicator_of_notMem hl]
      have hempty : Prod.mk l ⁻¹' (U ∩ {q | rowVolume U h q < ENNReal.ofReal θ}) = ∅ := by
        ext t
        simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false,
          not_and]
        intro htU
        exact absurd (hUA _ htU) hl
      rw [hempty, measure_empty]
  calc
    _ ≤ ∫⁻ l, A.indicator (fun _ => ENNReal.ofReal (θ * h)) l ∂ν := lintegral_mono hsection
    _ = ENNReal.ofReal (θ * h) * ν A := lintegral_indicator_const hA _

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
