-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.RoundedCurveCover, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/RoundedCurveCover.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/RoundedCurveCover.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/RoundedCurveCover.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_scalar_grid_parameter_preparation.CurveCells
import Submission.Lib.K4QuadraticSheets.JetBins
import Submission.Lib.K4VelocityStrips.StripBins


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set

noncomputable section

/-- Coarse physical cells are read from the ORIGINAL fine state. -/
def roundedPhysicalCode {n : ℕ} (b ρ : ℝ) (x : Fin n → ℝ) : Fin n → ℤ :=
  fun j => ⌊b * (⌊x j / b⌋ : ℝ) / ρ⌋

/-- Enlarge the accepted true-curve cover by one integer step in each
coordinate. The same finite table covers every actual fine-state corner. -/
theorem exists_rounded_curve_cover {n : ℕ} (F : ℝ → Fin n → ℝ)
    {L b ρ : ℝ} (hL : 0 ≤ L) (hb : 0 < b) (hρ : 0 < ρ) (hbρ : b ≤ ρ)
    (D : ℕ) (hD : 1 ≤ D) (hscale : L ≤ (D : ℝ) * ρ)
    (hLip : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ j,
      |F t j - F s j| ≤ L * |t - s|) :
    ∃ Q : Finset (Fin n → ℤ),
      (Q.card : ℝ) ≤ ((D : ℝ) + 1) * (7 : ℝ) ^ n * 7 ^ n ∧
      ∀ t ∈ Icc (0 : ℝ) 1, roundedPhysicalCode b ρ (F t) ∈ Q := by
  classical
  obtain ⟨Q₀, hQ₀, hcover⟩ :=
    Submission.Obl.k4_scalar_grid_parameter_preparation.exists_curve_grid_cover
      F hL hρ D hD hscale hLip
  let near : (Fin n → ℤ) → Finset (Fin n → ℤ) := fun q =>
    Fintype.piFinset fun j => Finset.Icc (q j - 1) (q j + 1)
  let Q := Q₀.biUnion near
  have hnear (q : Fin n → ℤ) : ((near q).card : ℝ) ≤ 7 ^ n := by
    have h := Submission.Lib.K4IncidenceWitnesses.card_pi_grid_of_diameter
      (near q) (R := 2) (by norm_num) (by
        intro u hu v hv j
        have hu' := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hu j)
        have hv' := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hv j)
        have hdiff : |u j - v j| ≤ (2 : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
        exact_mod_cast hdiff)
    simpa only [Fintype.card_fin, show (2 : ℝ) * 2 + 3 = 7 by norm_num] using h
  refine ⟨Q, ?_, ?_⟩
  · calc
      (Q.card : ℝ) ≤ ∑ q ∈ Q₀, ((near q).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _q ∈ Q₀, (7 : ℝ) ^ n := Finset.sum_le_sum fun q _ => hnear q
      _ = (Q₀.card : ℝ) * 7 ^ n := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hQ₀ (by positivity)
  · intro t ht
    apply Finset.mem_biUnion.mpr
    refine ⟨fun j => ⌊F t j / ρ⌋, hcover t ht, Fintype.mem_piFinset.mpr ?_⟩
    intro j
    have herr := Submission.Lib.K4VelocityStrips.midpoint_floor_center_bound hb (F t j)
    have hclose : |b * (⌊F t j / b⌋ : ℝ) - F t j| ≤ ρ := by
      rw [mul_comm, abs_sub_comm]
      exact herr.trans hbρ
    have hfloor := Submission.Lib.K4QuadraticSheets.floor_sub_le_one_of_abs_le hρ hclose
    change roundedPhysicalCode b ρ (F t) j ∈ Finset.Icc (⌊F t j / ρ⌋ - 1) (⌊F t j / ρ⌋ + 1)
    exact Finset.mem_Icc.mpr ⟨by have := (abs_le.mp hfloor).1; dsimp [roundedPhysicalCode]; omega,
      by have := (abs_le.mp hfloor).2; dsimp [roundedPhysicalCode]; omega⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
