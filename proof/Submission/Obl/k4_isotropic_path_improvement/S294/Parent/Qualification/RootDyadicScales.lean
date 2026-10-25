-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.RootDyadicScales, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.SparseSnapshotBudgets
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.WorldSupportDyadicScales

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set

/-- Every coarser snapshot is an exact dyadic multiple of the fixed
original graph mesh. -/
theorem dyadic_width_eq_fine_mul {fine coarse : ℕ} (h : coarse ≤ fine) :
    dyadicParameterWidth coarse=dyadicParameterWidth fine*(2:ℝ)^(fine-coarse) := by
  have hpow : (2:ℝ)^fine=(2:ℝ)^coarse*(2:ℝ)^(fine-coarse) := by
    rw [←pow_add,Nat.add_sub_of_le h]
  change ((2:ℝ)^coarse)⁻¹=((2:ℝ)^fine)⁻¹*(2:ℝ)^(fine-coarse)
  rw [hpow,mul_inv_rev,mul_right_comm,inv_mul_cancel₀ (by positivity),one_mul]

/-- The finite support grid can be constructed at the actual fixed
original graph mesh, with a uniform lower width and exact columns. -/
theorem exists_world_support_at_dyadic_mesh {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (fine world : ℕ) (hindex : world+parameterLevel ζ ≤ fine) :
    ∃ (W : Finset ℝ) (fineSteps columnSteps : ℝ → ℕ),
      W.card ≤ parameterLevel ζ+1 ∧
      (∀ w∈W, w=dyadicParameterWidth fine*(2:ℝ)^(fineSteps w)) ∧
      (∀ w∈W, dyadicParameterWidth world=w*(2:ℝ)^(columnSteps w)) ∧
      (∀ w∈W, dyadicParameterWidth fine ≤ w) ∧
      (∀ w∈W, w ≤ dyadicParameterWidth world) ∧
      (∀ w∈W, dyadicParameterWidth world*ζ/2 ≤ w) ∧
      ∀ r : ℝ, ζ ≤ r → r ≤ 1 → ∃ w∈W,
        w ≤ dyadicParameterWidth world*r ∧ dyadicParameterWidth world*r ≤ 2*w := by
  have hworld : world ≤ fine := by omega
  have hdepth : parameterLevel ζ ≤ fine-world := by omega
  have heq : dyadicParameterWidth world*dyadicParameterWidth (fine-world)=
      dyadicParameterWidth fine := by
    rw [←dyadicParameterWidth_add,Nat.add_sub_of_le hworld]
  simpa only [heq] using exists_world_support_dyadic_scales
    (dyadicParameterWidth_pos world) hζ hζ1 (fine-world) hdepth

/-- The sparse regularity grid fits the fixed fine mesh as soon as
its last width does. -/
theorem sparse_regular_grid_at_mesh (fine count step : ℕ)
    (hindex : count*step ≤ fine) :
    (∀ i < count+1, dyadicParameterWidth (i*step)=
      dyadicParameterWidth fine*(2:ℝ)^(fine-i*step)) ∧
    ∀ i < count+1, dyadicParameterWidth fine ≤ dyadicParameterWidth (i*step) := by
  have hi (i : ℕ) (h : i<count+1) : i*step ≤ fine :=
    (Nat.mul_le_mul_right step (by omega)).trans hindex
  exact ⟨fun i h => dyadic_width_eq_fine_mul (hi i h),
    fun i h => dyadicParameterWidth_antitone (hi i h)⟩

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
