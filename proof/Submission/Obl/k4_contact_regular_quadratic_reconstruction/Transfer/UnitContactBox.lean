/- Adapted from this LOT tree, obligation o243 (k4_contact_affine_residual_candidate_transfer),
   session x0835, branch x0835, commit c4aab87f,
   Submission/Obl/k4_contact_affine_residual_candidate_transfer/UnitContactBox.lean.
   Namespace and module paths renamed into o261's Transfer namespace;
   the accepted Data record is the same o238 one (k4_critical_switching_state_preparation). -/
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer.ContactMatrix
import Mathlib.Tactic.Linarith

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer

noncomputable section

/-- Put a bounded contact base in the unit cube while keeping its unit time
parameter. Both spatial coordinates use the same scale. -/
def unitContactBase (K : ℝ) (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![z 0, z 1 / (8 * K) + 1 / 4, z 2 / (8 * K) + 1 / 2 - z 0 / 4]

def unitContactCoeff (K : ℝ) (b : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![b 0 / (8 * K) + 1 / 4, b 1 / (8 * K) + 1 / 2, b 2,
    b 3 / (8 * K), b 4 / (8 * K) - 1 / 4, b 5]

theorem unitContactCoeff_defect (K : ℝ) (b : Fin 6 → ℝ) :
    unitContactCoeff K b 4 + unitContactCoeff K b 0 = (b 4 + b 0) / (8 * K) := by
  simp [unitContactCoeff]
  ring

theorem unitContactCoeff_velocity (K : ℝ) (b : Fin 6 → ℝ) :
    unitContactCoeff K b 3 = b 3 / (8 * K) := rfl

theorem unitContactBase_trajectory (K : ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    unitContactBase K ![t, b 0 + t * b 3, b 1 + t * b 4] =
      ![t, unitContactCoeff K b 0 + t * unitContactCoeff K b 3,
        unitContactCoeff K b 1 + t * unitContactCoeff K b 4] := by
  funext i
  fin_cases i <;> simp [unitContactBase, unitContactCoeff, div_eq_mul_inv] <;> ring

/-- Spatial coordinates have a fixed interior margin, so only the time
endpoints require trimming before taking occupied mesh cells. -/
theorem unitContactBase_interior {K : ℝ} (hK : 0 < K) (z : Fin 3 → ℝ)
    (ht : 0 ≤ z 0 ∧ z 0 ≤ 1) (hZ : |z 1| ≤ K) (hY : |z 2| ≤ K) :
    1 / 8 ≤ unitContactBase K z 1 ∧ unitContactBase K z 1 ≤ 3 / 8 ∧
      1 / 8 ≤ unitContactBase K z 2 ∧ unitContactBase K z 2 ≤ 5 / 8 := by
  have hden : 0 < 8 * K := by positivity
  have hsmall (a : ℝ) (ha : |a| ≤ K) : |a / (8 * K)| ≤ 1 / 8 := by
    rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
    nlinarith
  have hz := abs_le.mp (hsmall (z 1) hZ)
  have hy := abs_le.mp (hsmall (z 2) hY)
  simp [unitContactBase]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem unitContactBase_mem_cube {K : ℝ} (hK : 0 < K) (z : Fin 3 → ℝ)
    (ht : 0 ≤ z 0 ∧ z 0 ≤ 1) (hZ : |z 1| ≤ K) (hY : |z 2| ≤ K) :
    unitContactBase K z ∈ Set.Icc (0 : Fin 3 → ℝ) 1 := by
  obtain ⟨hz₀, hz₁, hy₀, hy₁⟩ := unitContactBase_interior hK z ht hZ hY
  constructor
  · intro i
    fin_cases i
    · exact ht.1
    · exact (by norm_num : (0 : ℝ) ≤ 1 / 8).trans hz₀
    · exact (by norm_num : (0 : ℝ) ≤ 1 / 8).trans hy₀
  · intro i
    fin_cases i
    · exact ht.2
    · exact hz₁.trans (by norm_num : (3 / 8 : ℝ) ≤ 1)
    · exact hy₁.trans (by norm_num : (5 / 8 : ℝ) ≤ 1)

def unitContactMatrix (K : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, (8 * K)⁻¹, 0; -1 / 4, 0, (8 * K)⁻¹]

theorem unitContactBase_eq_affine (K : ℝ) (z : Fin 3 → ℝ) :
    unitContactBase K z = (unitContactMatrix K).mulVec z + ![0, 1 / 4, 1 / 2] := by
  funext i
  fin_cases i <;> simp [unitContactBase, unitContactMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, div_eq_mul_inv] <;> ring

theorem det_unitContactMatrix (K : ℝ) : (unitContactMatrix K).det = ((8 * K) ^ 2)⁻¹ := by
  simp [unitContactMatrix, Matrix.det_fin_three, ← inv_pow] <;> ring

end

end Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer
