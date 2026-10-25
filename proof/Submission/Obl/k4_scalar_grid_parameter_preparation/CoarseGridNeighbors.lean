/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/CoarseGridNeighbors.lean -/
import Submission.Obl.k4_scalar_grid_density_extension.GridRelation
import Submission.Lib.K4ListedExceptions.FrameCodes
import Submission.Obl.k4_scalar_grid_parameter_preparation.PhysicalSupportCover

/-! Coarse neighbors of a fine floor cell, without nested-grid assumptions. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped Classical BigOperators ENNReal

theorem coarse_grid_neighbor_of_fine_equal {n : ℕ} (ξ ζ : ℝ) (hξ : 0 < ξ) (hξζ : ξ ≤ ζ)
    (x y : Fin n → ℝ) (hxy : (fun i => (⌊x i / ξ⌋ : ℤ)) = fun i => ⌊y i / ξ⌋) :
    (fun i => (⌊x i / ζ⌋ : ℤ)) ∈
      Submission.Lib.K4ListedExceptions.integerCodeBox 1 (fun i => ⌊y i / ζ⌋) := by
  rw [Submission.Lib.K4ListedExceptions.mem_integerCodeBox]
  intro i
  have hx := Submission.Obl.k4_scalar_grid_density_extension.floorCompatible_coarse_mem
    hξ hξζ (⌊y i / ξ⌋ : ℤ) (⌊x i / ζ⌋ : ℤ) ⟨x i, rfl, congrFun hxy i⟩
  have hy := Submission.Obl.k4_scalar_grid_density_extension.floorCompatible_coarse_mem
    hξ hξζ (⌊y i / ξ⌋ : ℤ) (⌊y i / ζ⌋ : ℤ) ⟨y i, rfl, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  norm_num only [Nat.cast_one]
  omega

theorem physical_grid_neighbor_mass_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → Fin 3 → ℝ) (ζ U : ℝ) (q₀ : Fin 3 → ℤ)
    (hcap : ∀ q, μ {p | physicalScalarGridTag ζ (f p) = q} ≤ ENNReal.ofReal U) :
    μ {p | physicalScalarGridTag ζ (f p) ∈
      Submission.Lib.K4ListedExceptions.integerCodeBox 1 q₀} ≤ ENNReal.ofReal (27 * U) := by
  let D := Submission.Lib.K4ListedExceptions.integerCodeBox 1 q₀
  have he : {p | physicalScalarGridTag ζ (f p) ∈ D} =
      ⋃ q ∈ D, {p | physicalScalarGridTag ζ (f p) = q} := by ext p; simp
  change μ {p | physicalScalarGridTag ζ (f p) ∈ D} ≤ _
  rw [he]
  calc
    _ ≤ ∑ q ∈ D, μ {p | physicalScalarGridTag ζ (f p) = q} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ D, ENNReal.ofReal U := Finset.sum_le_sum fun q _ => hcap q
    _ = ENNReal.ofReal (27 * U) := by
      simp only [Finset.sum_const, nsmul_eq_mul, D,
        Submission.Lib.K4ListedExceptions.card_integerCodeBox]
      norm_num

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
