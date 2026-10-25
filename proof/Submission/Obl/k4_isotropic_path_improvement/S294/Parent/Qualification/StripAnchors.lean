-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.StripAnchors, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/StripAnchors.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/StripAnchors.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/StripAnchors.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.NativeStripStates


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set

noncomputable section

/-- An actual occurrence in a coarse cube lies within two coarse
widths of its corner, including the original fine-rounding error. -/
theorem physical_corner_bound {b ρ : ℝ} (hb : 0 < b) (hρ : 0 < ρ) (hbρ : b ≤ ρ)
    (x : Fin 4 → ℝ) (C : Fin 4 → ℤ) (hcode : roundedPhysicalCode b ρ x = C)
    (j : Fin 4) : |x j - ρ * (C j : ℝ)| ≤ 2 * ρ := by
  have hc := Int.floor_eq_iff.mp (congrFun hcode j)
  change (C j : ℝ) ≤ b * (⌊x j / b⌋ : ℝ) / ρ ∧
    b * (⌊x j / b⌋ : ℝ) / ρ < (C j : ℝ) + 1 at hc
  rw [le_div_iff₀ hρ, div_lt_iff₀ hρ] at hc
  have hlo := Int.floor_le (x j / b)
  have hhi := Int.lt_floor_add_one (x j / b)
  rw [le_div_iff₀ hb] at hlo
  rw [div_lt_iff₀ hb] at hhi
  apply abs_le.mpr
  constructor <;> nlinarith [hc.1, hc.2]

def normalizedStripAnchor (a v : Fin 3 → ℝ) (ρ : ℝ) (C : Fin 4 → ℤ) : Fin 3 → ℝ :=
  fun j => (a j + (ρ * (C 0 : ℝ)) * v j - ρ * (C j.castSucc : ℝ)) / ρ

theorem normalizedStripAnchor_time (a v : Fin 3 → ℝ) (ρ : ℝ) (C : Fin 4 → ℤ)
    (ha0 : a 0 = 0) (hv0 : v 0 = 1) : normalizedStripAnchor a v ρ C 0 = 0 := by
  simp [normalizedStripAnchor, ha0, hv0]

/-- A single ACTUAL coarse-cube occurrence bounds the anchor of its
entire affine base line in the cube's normalized frame. -/
theorem normalizedStripAnchor_bound {b ρ K : ℝ}
    (hb : 0 < b) (hρ : 0 < ρ) (hbρ : b ≤ ρ) (hK : 0 ≤ K)
    (signal : Polynomial ℝ) (a v : Fin 3 → ℝ) (ha0 : a 0 = 0) (hv0 : v 0 = 1)
    (hvel : ∀ j, |v j| ≤ K) (C : Fin 4 → ℤ) (t : ℝ)
    (hcode : roundedPhysicalCode b ρ (originalPhysicalCoordinates signal a v t) = C)
    (j : Fin 3) : |normalizedStripAnchor a v ρ C j| ≤ 2 + 2 * K := by
  have hbase := physical_corner_bound hb hρ hbρ _ C hcode j.castSucc
  simp only [originalPhysicalCoordinates, Fin.snoc_castSucc] at hbase
  have ht := physical_corner_bound hb hρ hbρ _ C hcode 0
  rw [originalPhysicalCoordinates_time signal a v ha0 hv0] at ht
  have hprod : |(t - ρ * (C 0 : ℝ)) * v j| ≤ 2 * ρ * K := by
    rw [abs_mul]
    exact mul_le_mul ht (hvel j) (abs_nonneg _) (by positivity)
  rw [normalizedStripAnchor, abs_div, abs_of_pos hρ]
  apply (div_le_iff₀ hρ).mpr
  have hid : a j + (ρ * (C 0 : ℝ)) * v j - ρ * (C j.castSucc : ℝ) =
      (a j + v j * t - ρ * (C j.castSucc : ℝ)) - (t - ρ * (C 0 : ℝ)) * v j := by ring
  rw [hid]
  exact (abs_sub _ _).trans ((add_le_add hbase hprod).trans_eq (by ring))

/-- This is the exact affine normalization consumed by native base
filling; original time is retained in the incidence measure. -/
theorem normalizedStripAnchor_motion (a v : Fin 3 → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (C : Fin 4 → ℤ) (t : ℝ) (j : Fin 3) :
    normalizedStripAnchor a v ρ C j + ((t - ρ * (C 0 : ℝ)) / ρ) * v j =
      (a j + v j * t - ρ * (C j.castSucc : ℝ)) / ρ := by
  unfold normalizedStripAnchor
  field_simp
  <;> ring

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
