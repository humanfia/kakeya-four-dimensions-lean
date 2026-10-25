-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.ZoomScalarStrips, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/ZoomScalarStrips.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/ZoomScalarStrips.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/ZoomScalarStrips.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ZoomTimeRow
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Basic


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set
open scoped BigOperators

noncomputable section

def normalBase (c : Fin 7 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  ![t, zy c t 0, zy c t 1]

def normalScalar (G : Fin 3 → ℝ) (c : Fin 7 → ℝ) (t : ℝ) : ℝ :=
  zx c t - ∑ j, G j * normalBase c t j

/-- At fixed time this translation is common to the entire parameter
world inside one coarse physical cube. -/
def coarseScalarTranslation (G : Fin 3 → ℝ) (center : Fin 7 → ℝ) (t : ℝ) : ℝ :=
  G 0 * t + (∑ i : Fin 2, G i.succ * zy center t i) - zx center t

/-- Exact scalar identity relating the parameter zoom to the ORIGINAL
normal-strip coordinate. The only remaining error is a product of row
and position differences. -/
theorem zoom_scalar_decomposition (ρ : ℝ) (hρ : ρ ≠ 0)
    (center c : Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ) (G : Fin 3 → ℝ) (t : ℝ) :
    ρ * zS F (zoomCoefficients ρ center c) t =
      normalScalar G c t + coarseScalarTranslation G center t +
        ∑ i : Fin 2, (G i.succ - F t i) * (zy c t i - zy center t i) := by
  simp [zS, zoomCoefficients, normalScalar, normalBase, coarseScalarTranslation,
    zx, zy, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three]
  field_simp
  ring

theorem zoom_scalar_near_normal (ρ : ℝ) (hρ : ρ ≠ 0)
    (center c : Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ) (G : Fin 3 → ℝ) (t η V : ℝ)
    (hη : 0 ≤ η) (_hV : 0 ≤ V) (hrow : ∀ i : Fin 2, |G i.succ - F t i| ≤ η)
    (hposition : ∀ i : Fin 2, |zy c t i - zy center t i| ≤ V) :
    |ρ * zS F (zoomCoefficients ρ center c) t -
      (normalScalar G c t + coarseScalarTranslation G center t)| ≤ 2 * η * V := by
  have hterm (i : Fin 2) : |(G i.succ - F t i) * (zy c t i - zy center t i)| ≤ η * V := by
    rw [abs_mul]
    exact mul_le_mul (hrow i) (hposition i) (abs_nonneg _) hη
  rw [zoom_scalar_decomposition ρ hρ, add_sub_cancel_left]
  exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => hterm i).trans_eq
    (by simp; ring))

/-- At a common time, a full coefficient diameter controls position
without any bound on the central intercepts. -/
theorem original_parameter_world_same_time_comparison (c center : Fin 7 → ℝ)
    {ρ t : ℝ} (hρ : 0 ≤ ρ) (ht : t ∈ Icc (0:ℝ) 1)
    (hdiam : ∀ i, |c i-center i| ≤ ρ) :
    ‖zpos c t-zpos center t‖ ≤ 3*ρ := by
  have hc : ‖c-center‖ ≤ ρ := norm_le_of_abs_le hρ hdiam
  apply norm_le_of_abs_le (by positivity)
  intro i
  fin_cases i
  · change |t-t| ≤ 3*ρ
    simp only [sub_self,abs_zero]
    positivity
  · exact abs_zx_sub_le hc ht
  · exact (abs_zy_sub_le hc ht 0).trans (by linarith)
  · exact (abs_zy_sub_le hc ht 1).trans (by linarith)

/-- Full ORIGINAL coefficient-bin diameter gives the scalar/normal
comparison error without any bound on central intercepts or jets. -/
theorem zoom_scalar_original_world_error (ρ : ℝ) (hρ : 0 < ρ)
    (center c : Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ) (G : Fin 3 → ℝ) (t η : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (hη : 0 ≤ η)
    (hdiam : ∀ i, |c i - center i| ≤ ρ)
    (hrow : ∀ i : Fin 2, |G i.succ - F t i| ≤ η) :
    |ρ * zS F (zoomCoefficients ρ center c) t -
      (normalScalar G c t + coarseScalarTranslation G center t)| ≤ 4 * η * ρ := by
  have hc : ‖c-center‖ ≤ ρ := norm_le_of_abs_le hρ.le hdiam
  have h := zoom_scalar_near_normal ρ hρ.ne' center c F G t η (2*ρ)
    hη (by positivity) hrow (abs_zy_sub_le hc ht)
  exact h.trans_eq (by ring)

/-- A fine normal-strip bin gives a radius-r cover of the actual zoomed
scalar, once the derived normal-coordinate error is below half a bin. -/
theorem scalar_in_ball_of_normal_strip {ρ width r error : ℝ}
    (hρ : 0 < ρ) (hw : 0 < width) (hscale : width = ρ * r) (herror : error ≤ width / 2)
    (scalar normal translation : ℝ) (n : ℤ)
    (hfit : |ρ * scalar - (normal + translation)| ≤ error) (hbin : ⌊normal / width⌋ = n) :
    scalar ∈ Metric.closedBall (((n : ℝ) + 1 / 2) * width / ρ + translation / ρ) r := by
  have hf := Int.floor_eq_iff.mp hbin
  rw [le_div_iff₀ hw, div_lt_iff₀ hw] at hf
  have hmiddle : |normal - ((n : ℝ) + 1 / 2) * width| ≤ width / 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [hf.1, hf.2]
  have htri := abs_sub_le (ρ * scalar) (normal + translation)
    (((n : ℝ) + 1 / 2) * width + translation)
  have hnorm : |ρ * scalar - (((n : ℝ) + 1 / 2) * width + translation)| ≤ width := by
    rw [add_sub_add_right_eq_sub] at htri
    linarith
  rw [Metric.mem_closedBall, Real.dist_eq]
  have heq : scalar - (((n : ℝ) + 1 / 2) * width / ρ + translation / ρ) =
      (ρ * scalar - (((n : ℝ) + 1 / 2) * width + translation)) / ρ := by field_simp
  rw [heq, abs_div, abs_of_pos hρ, div_le_iff₀ hρ]
  simpa only [hscale, mul_comm] using hnorm

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
