/- Adapted from this LOT tree, o092, session x0317, commit d881f97f20e4.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/PaletteScaledCellCount.lean -/
import Submission.Lib.K4FinitePlankAtlases.DensityFloors

/-! Cancel the same original palette mass in old cell floors and a region ceiling. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

open Set MeasureTheory
open scoped ENNReal

theorem palette_scaled_old_cell_count {Ω C : Type*} [MeasurableSpace Ω] [DecidableEq C]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Finset C) (cells : C → Set Ω)
    (hdisj : (↑F : Set C).PairwiseDisjoint cells) (hmeas : ∀ c ∈ F, MeasurableSet (cells c))
    (A : Set Ω) (hcover : ∀ c ∈ F, cells c ⊆ A)
    (τ U : ℝ) (hτ : 0 < τ) (hU : 0 ≤ U) (p : ℝ≥0∞) (hp₀ : p ≠ 0) (hpt : p ≠ ∞)
    (hfloor : ∀ c ∈ F, ENNReal.ofReal τ * p ≤ μ (cells c))
    (hcap : μ A ≤ ENNReal.ofReal U * p) : (F.card : ℝ) ≤ U / τ := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp₀ hpt
  have hcell (c : C) (hc : c ∈ F) : (μ.restrict A) (cells c) = μ (cells c) := by
    rw [Measure.restrict_apply (hmeas c hc),Set.inter_eq_left.mpr (hcover c hc)]
  have hlo (c : C) (hc : c ∈ F) : τ * p.toReal ≤ (μ.restrict A).real (cells c) := by
    have hh := ENNReal.toReal_mono (measure_ne_top μ (cells c)) (hfloor c hc)
    simpa only [measureReal_def,hcell c hc,ENNReal.toReal_mul,ENNReal.toReal_ofReal hτ.le] using hh
  have ht := Submission.Lib.K4FinitePlankAtlases.old_cell_count (μ.restrict A) F cells
    hdisj hmeas (mul_pos hτ hp) hlo
  have hm : (μ.restrict A).real Set.univ ≤ U * p.toReal := by
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpt) hcap
    simpa only [measureReal_def,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,
      ENNReal.toReal_mul,ENNReal.toReal_ofReal hU] using hh
  calc
    _ ≤ (U * p.toReal) / (τ * p.toReal) := ht.trans
      (div_le_div_of_nonneg_right hm (mul_pos hτ hp).le)
    _ = _ := by field_simp

end Submission.Obl.k4_scalar_grid_parameter_preparation
