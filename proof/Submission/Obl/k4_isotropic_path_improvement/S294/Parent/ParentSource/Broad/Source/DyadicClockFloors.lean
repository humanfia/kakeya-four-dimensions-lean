-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.DyadicClockFloors, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/DyadicClockFloors.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 83ada3e49b5540f6b00606ae3df6268df68021ab,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/DyadicClockFloors.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o265/x1027, commit a108a9efd;
-- source Broad/Source/DyadicClockFloors.lean. Existing attributions are preserved.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CalibratedClockFloors
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ClockStateCoarsening
import Submission.Lib.K4DyadicRowScales.Basic

/-! # Calibrated clock floors with exact MK4 mesh nesting

Two additional dyadic coarsenings make the remaining fine exponent a
multiple of three. The calibrated height factor and the original law
are preserved. Only universal numerical constants change.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.ClockCalibration
open MeasureTheory Set
open Submission.Lib.K4ParentSignalPreparation.Census
open scoped ENNReal
noncomputable section

namespace RowScale
open Submission.Lib.K4DyadicRowScales

/-- An arbitrary dyadic precision can be coarsened by a polynomial
factor so that the final fine and coarse meshes are exactly `2^(-3n)`
and `2^(-2n)`. -/
theorem exists_calibrated_steps {ε θ K ζ : ℝ} (e : ℕ)
    (hεeq : ε=unit e) (hθ : 0 < θ) (hK : 1 ≤ K)
    (hεζ : ε ≤ θ*ζ) (hεζplain : ε ≤ ζ) (hmargin : 8*K^(100:ℕ)*ζ ≤ 1) :
    ∃ steps n : ℕ, e=steps+3*n ∧
      K^(100:ℕ) ≤ (2:ℝ)^steps ∧ (2:ℝ)^steps ≤ 8*K^(100:ℕ) ∧
      ε ≤ ε*(2:ℝ)^steps ∧ ε*(2:ℝ)^steps=mesh n ∧
      mesh n ≤ θ ∧ mesh n ≤ 1 ∧
      coarse n=mesh n^((2:ℝ)/3) ∧ coarse n=mesh n*(2:ℝ)^n := by
  have hε : 0 < ε := hεeq ▸ unit_pos e
  have hζ : 0 < ζ := hε.trans_le hεζplain
  have hKpow : 0 ≤ K^(100:ℕ) := by positivity
  have hmargin2 : 2*K^(100:ℕ)*ζ ≤ 1 := by nlinarith
  obtain ⟨s,hlo,hhi,-⟩ := exists_clock_coarsening_steps hε hθ hK hεζ hmargin2
  have hsmesh : ε*(2:ℝ)^s ≤ 1 := by
    calc
      _ ≤ ζ*(2*K^(100:ℕ)) := mul_le_mul hεζplain hhi (by positivity) hζ.le
      _ ≤ 1 := by nlinarith
  have hse : s ≤ e := by
    apply (pow_le_pow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp
    apply (mul_le_mul_iff_right₀ hε).mp
    calc
      _ ≤ 1 := hsmesh
      _ = ε*(2:ℝ)^e := by rw [hεeq,Submission.Lib.K4DyadicRowScales.unit]; field_simp
  let steps := s+(e-s)%3
  let n := (e-s)/3
  have heq : e=steps+3*n := by dsimp [steps,n]; omega
  have hsteps : s ≤ steps := by dsimp [steps]; omega
  have hsteps2 : steps ≤ s+2 := by dsimp [steps]; omega
  have hlow : K^(100:ℕ) ≤ (2:ℝ)^steps :=
    hlo.trans (pow_le_pow_right₀ (by norm_num) hsteps)
  have hhigh : (2:ℝ)^steps ≤ 8*K^(100:ℕ) := by
    calc
      _ ≤ (2:ℝ)^(s+2) := pow_le_pow_right₀ (by norm_num) hsteps2
      _ = (2:ℝ)^s*4 := by rw [pow_add]; norm_num
      _ ≤ (2*K^(100:ℕ))*4 := mul_le_mul_of_nonneg_right hhi (by norm_num)
      _ = _ := by ring
  have hmesh : ε*(2:ℝ)^steps=mesh n := by
    rw [hεeq]
    have heq' : e=steps+n*3 := by omega
    rw [heq']
    change ((2:ℝ)^(steps+n*3))⁻¹*(2:ℝ)^steps=(((2:ℝ)^n)⁻¹)^3
    rw [pow_add,pow_mul]
    field_simp
  have hres : mesh n ≤ θ := by
    rw [←hmesh]
    calc
      _ ≤ (θ*ζ)*(8*K^(100:ℕ)) := mul_le_mul hεζ hhigh (by positivity) (by positivity)
      _ = θ*(8*K^(100:ℕ)*ζ) := by ring
      _ ≤ θ*1 := mul_le_mul_of_nonneg_left hmargin hθ.le
      _ = θ := mul_one _
  refine ⟨steps,n,heq,hlow,hhigh,?_,hmesh,hres,?_,
    coarse_eq_mesh_rpow n,coarse_eq_mesh_mul_pow n⟩
  · exact le_mul_of_one_le_right hε.le ((one_le_pow₀ hK).trans hlow)
  · rw [←hmesh]
    calc
      _ ≤ ζ*(8*K^(100:ℕ)) := mul_le_mul hεζplain hhigh (by positivity) hζ.le
      _ = 8*K^(100:ℕ)*ζ := by ring
      _ ≤ 1 := hmargin

end RowScale

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.ClockCalibration
