-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.WorldCells, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/WorldCells.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Generalized from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FrozenWorldCells.lean.
The bounded quadratic physical model replaces the old chart signal.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FrozenWorldCells.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.ZoomScalar
import Submission.Lib.K4IncidenceWitnesses


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set

noncomputable section

/-- At one time, an ORIGINAL coefficient world meets only a fixed
polynomial number of coarse physical cells. Their actual fine-state
corners, rather than successful-incidence marginals, define the codes. -/
theorem exists_parameter_world_coarse_cover (p : PhysicalModel) (A : Set Ln)
    (center : Fin 7 → ℝ) (ρ b t : ℝ) (hρ : 0 < ρ)
    (hb : 0 < b) (hbρ : b ≤ ρ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hdiam : ∀ l ∈ A, ∀ i, |p.scalarCoefficients l i - center i| ≤ ρ) :
    ∃ Q : Finset (Fin 4 → ℤ), (Q.card : ℝ) ≤ (27:ℝ)^4 ∧
      ∀ l ∈ A, roundedPhysicalCode b ρ
        (originalPhysicalCoordinates (p.signal l) (p.position l) (p.velocity l) t) ∈ Q := by
  classical
  let y : Fin 4 → ℝ := fun j => Jets2.zpos center t (physicalIndex j)
  let R : ℤ := ⌈(5:ℝ)⌉
  let q₀ : Fin 4 → ℤ := fun j => ⌊y j / ρ⌋
  let Q := Fintype.piFinset fun j => Finset.Icc (q₀ j - R) (q₀ j + R)
  have hR : (R : ℝ) ≤ (6:ℝ) := by
    have hh := Int.ceil_lt_add_one ((5:ℝ))
    dsimp only [R]
    linarith
  refine ⟨Q, ?_, ?_⟩
  · have hc := Submission.Lib.K4IncidenceWitnesses.card_pi_grid_of_diameter Q
      (R := (12:ℝ)) (by linarith) (by
        intro q hq q' hq' j
        have hqj := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hq j)
        have hqj' := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hq' j)
        have hlo : (q₀ j : ℝ) - R ≤ q j := by exact_mod_cast hqj.1
        have hhi : (q j : ℝ) ≤ (q₀ j : ℝ) + R := by exact_mod_cast hqj.2
        have hlo' : (q₀ j : ℝ) - R ≤ q' j := by exact_mod_cast hqj'.1
        have hhi' : (q' j : ℝ) ≤ (q₀ j : ℝ) + R := by exact_mod_cast hqj'.2
        exact abs_le.mpr ⟨by linarith, by linarith⟩)
    simpa only [Fintype.card_fin, show 2 * ((12:ℝ)) + 3 = (27:ℝ) by ring] using hc
  · intro l hl
    apply Fintype.mem_piFinset.mpr
    intro j
    let x := originalPhysicalCoordinates (p.signal l) (p.position l) (p.velocity l) t
    let u := b * (⌊x j / b⌋ : ℝ)
    have hpos := Jets2.original_parameter_world_same_time_comparison (p.scalarCoefficients l)
      center hρ.le ht (hdiam l hl)
    have hj := norm_le_pi_norm
      (Jets2.zpos (p.scalarCoefficients l) t - Jets2.zpos center t) (physicalIndex j)
    have hxy : |x j - y j| ≤ 3 * ρ := by
      dsimp only [x, y]
      rw [p.physical_scalar_coord]
      exact hj.trans hpos
    have hround : |u - x j| ≤ b := by
      simpa only [u, mul_comm, abs_sub_comm] using
        Submission.Lib.K4VelocityStrips.midpoint_floor_center_bound hb (x j)
    have hnear : |u - y j| ≤ 4 * ρ := by
      have hh := (abs_sub_le u (x j) (y j)).trans (add_le_add hround hxy)
      nlinarith
    have hdiv : |u / ρ - y j / ρ| ≤ (4:ℝ) := by
      rw [← sub_div, abs_div, abs_of_pos hρ, div_le_iff₀ hρ]
      exact hnear
    have hfloor : |((⌊u / ρ⌋ - ⌊y j / ρ⌋ : ℤ) : ℝ)| ≤ (R : ℝ) := by
      rw [Int.cast_sub, abs_le]
      have hh := abs_le.mp hdiv
      have hceil := Int.le_ceil ((5:ℝ))
      have hu₀ := Int.floor_le (u / ρ)
      have hu₁ := Int.lt_floor_add_one (u / ρ)
      have hy₀ := Int.floor_le (y j / ρ)
      have hy₁ := Int.lt_floor_add_one (y j / ρ)
      constructor <;> dsimp only [R] <;> linarith
    have hint : |⌊u / ρ⌋ - ⌊y j / ρ⌋| ≤ R := by exact_mod_cast hfloor
    change ⌊u / ρ⌋ ∈ Finset.Icc (⌊y j / ρ⌋ - R) (⌊y j / ρ⌋ + R)
    exact Finset.mem_Icc.mpr ⟨by have := (abs_le.mp hint).1; omega,
      by have := (abs_le.mp hint).2; omega⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
