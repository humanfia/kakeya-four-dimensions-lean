-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.CoreCoordinatesCap, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/CoreCoordinatesCap.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/CoreCoordinatesCap.lean.
All earlier source attributions below are retained. -/
import Mathlib

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Expanding local core coordinates can only lower a continuous base cap. -/
theorem core_coordinates_volume_le {K : ℝ} (hK : 1 ≤ K) (R : ℕ)
    (c : EuclideanSpace ℝ (Fin 3)) :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).map
        (fun x => (K ^ R) • (x - c)) ≤ volume := by
  have hKR : 1 ≤ K ^ R := one_le_pow₀ hK
  have hp : 0 < K ^ R := zero_lt_one.trans_le hKR
  have heq : (fun x : EuclideanSpace ℝ (Fin 3) => (K ^ R) • (x - c)) =
      (fun x => (K ^ R) • x) ∘ (fun x => x + -c) := by
    funext x
    simp only [Function.comp_apply, sub_eq_add_neg]
  rw [heq, ← Measure.map_map
      (show Measurable (fun x : EuclideanSpace ℝ (Fin 3) => (K ^ R) • x) by fun_prop)
      (show Measurable (fun x : EuclideanSpace ℝ (Fin 3) => x + -c) by fun_prop),
    Measure.IsAddRightInvariant.map_add_right_eq_self,
    Measure.map_addHaar_smul volume hp.ne']
  have hfactor : ENNReal.ofReal |((K ^ R) ^ Module.finrank ℝ
      (EuclideanSpace ℝ (Fin 3)))⁻¹| ≤ 1 := by
    apply ENNReal.ofReal_le_one.mpr
    rw [abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hKR)
  apply Measure.le_iff.mpr
  intro U _
  simpa only [Measure.smul_apply, smul_eq_mul, one_mul] using
    (mul_le_mul' hfactor (le_refl (volume U)))

theorem core_coordinates_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (base : Ω → EuclideanSpace ℝ (Fin 3)) (hbase : Measurable base)
    {K : ℝ} (hK : 1 ≤ K) (R : ℕ) (c : EuclideanSpace ℝ (Fin 3))
    (C : ENNReal) (hcap : μ.map base ≤ C • volume) :
    μ.map (fun z => (K ^ R) • (base z - c)) ≤ C • volume := by
  have hlocal : Measurable (fun x : EuclideanSpace ℝ (Fin 3) => (K ^ R) • (x - c)) := by
    fun_prop
  calc
    _ = (μ.map base).map (fun x => (K ^ R) • (x - c)) :=
      (Measure.map_map hlocal hbase).symm
    _ ≤ (C • volume).map (fun x => (K ^ R) • (x - c)) :=
      Measure.map_mono hcap hlocal
    _ = C • (volume.map (fun x => (K ^ R) • (x - c))) :=
      Measure.map_smul C hlocal.aemeasurable
    _ ≤ C • volume := smul_le_smul_left C (core_coordinates_volume_le hK R c)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
