-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.NativeCubeCap, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/NativeCubeCap.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/NativeCubeCap.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/NativeCubeCap.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/NativeCubeCap.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.NativeCube
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.BaseCapChange

/-! # The original base cap in unit-cube native coordinates -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

open MeasureTheory
open scoped ENNReal

noncomputable section

def nativeCubeBase (κ : ℝ) (z : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![z 0, (z 1 + κ) / (2 * κ), (z 2 + κ) / (2 * κ)]

def nativeCubeBaseFrame (κ : ℝ) : Submission.Lib.K4ChartLifting.Frame where
  t₀ := 0
  q := 1
  c := WithLp.toLp 2 ![-κ, -κ]
  u := 0
  D := Matrix.diagonal (fun _ => 2 * κ)

theorem nativeCubeBase_eq_obsBase {κ : ℝ} (hκ : κ ≠ 0) :
    nativeCubeBase κ = (nativeCubeBaseFrame κ).obsBase := by
  funext z
  ext j
  fin_cases j <;>
    simp [nativeCubeBase, nativeCubeBaseFrame,
      Submission.Lib.K4ChartLifting.Frame.obsBase, Matrix.inv_def,
      Matrix.adjugate_fin_two, Matrix.det_fin_two, Ring.inverse_eq_inv', Matrix.diagonal]
  all_goals field_simp [hκ] <;> ring

theorem measurable_nativeCubeBase (κ : ℝ) : Measurable (nativeCubeBase κ) := by
  unfold nativeCubeBase
  apply (PiLp.volume_preserving_toLp (Fin 3)).measurable.comp
  apply measurable_pi_iff.mpr
  intro j
  fin_cases j <;> simp <;> fun_prop

/-- Sending the native bounded base to the unit cube costs exactly the
planar Jacobian4*kappa^2. The measure remains the original unnormalized
entry law. -/
theorem original_native_cube_base_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → EuclideanSpace ℝ (Fin 3)) (hZ : Measurable Z)
    {κ : ℝ} (hκ : 0 < κ) (C : ENNReal) (hcap : μ.map Z ≤ C • volume) :
    μ.map (nativeCubeBase κ ∘ Z) ≤ (C * ENNReal.ofReal (4 * κ ^ 2)) • volume := by
  have hdet : (nativeCubeBaseFrame κ).D.det = 4 * κ ^ 2 := by
    simp [nativeCubeBaseFrame, Matrix.det_fin_two]
    ring
  have hc := base_cap_under_chart_change μ Z hZ (nativeCubeBaseFrame κ)
    (by change (0 : ℝ) < 1; norm_num) (by rw [hdet]; positivity) C hcap
  simpa only [← nativeCubeBase_eq_obsBase hκ.ne', hdet,
    show (nativeCubeBaseFrame κ).q = 1 from rfl,
    one_mul, abs_of_pos (show 0 < 4 * κ ^ 2 by positivity)] using hc

/-- The Euclidean base cap is the dominated-preimage condition used by
the accepted original-law polynomial coefficient theorem. -/
theorem original_base_cap_coordinate_preimages {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → EuclideanSpace ℝ (Fin 3)) (hZ : Measurable Z)
    (C : ENNReal) (hcap : μ.map Z ≤ C • volume)
    (U : Set (Fin 3 → ℝ)) (hU : MeasurableSet U) :
    μ ((fun x => WithLp.ofLp (Z x)) ⁻¹' U) ≤ C * volume U := by
  have hpre : MeasurableSet (WithLp.ofLp ⁻¹' U : Set (EuclideanSpace ℝ (Fin 3))) :=
    (PiLp.volume_preserving_ofLp (Fin 3)).measurable hU
  have hh := hcap (WithLp.ofLp ⁻¹' U)
  rw [Measure.map_apply hZ hpre, Measure.smul_apply,
    (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage hU.nullMeasurableSet] at hh
  exact hh

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
