import Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep.Chart
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer.ContactBaseBounds

/-!
# Normalized lines of a centered label stay in the unit cube

A line of a label whose rows hold at the block start, with a centered label, has bounded zoomed
coefficients (`contact_base_coefficient_bound`); the unit-box map then places its whole block in
the unit cube, with fixed spatial margins.
-/

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep

open Set
open Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer

noncomputable section

namespace ChartData

variable (D : ChartData)

/-- The zoomed base point of an original line, at normalized time `σ`. -/
theorem contactBaseFrame_basePt (hq : D.q ≠ 0) (b : Fin 6 → ℝ) (σ : ℝ) :
    contactBaseFrame D.t₀ D.q D.Z₀ D.Y₀ (basePt b (D.t₀ + D.q * σ)) =
      ![σ, (b 0 + D.t₀ * b 3 - D.Z₀) / D.q + σ * b 3,
        (b 1 + D.t₀ * b 4 - D.Y₀ + D.Z₀ * D.t₀ - D.t₀ * (b 0 + D.t₀ * b 3)) / D.q ^ 2 +
          σ * ((b 4 + D.Z₀ - D.t₀ * b 3) / D.q)] := by
  funext i
  fin_cases i <;> simp [contactBaseFrame, basePt] <;> field_simp <;> ring

/-- Lines of a centered label: the normalized line is in the unit cube for all normalized times,
with the spatial coordinates in `[1/8, 3/8] × [1/8, 5/8]`. -/
theorem normLine_mem_cube {K q g J : ℝ} (hK : 1 ≤ K) (hq : 0 < q) (hg : g ≤ K * q)
    (hJ : 0 ≤ J) (hDq : D.q = q) (hDB : D.B = 2 * K + 2 * K ^ 2 + 2 * J * K + J)
    (cl : Fin 5 → ℝ) (hY₀ : D.Y₀ = cl 2 + D.t₀ * cl 3 + cl 4 * D.Z₀)
    (hcenter : |cl 3 + D.Z₀| ≤ J * q) (hpivot : |cl 4 - D.t₀| ≤ J * q)
    (b : Fin 6 → ℝ) (hv : |b 3| ≤ K)
    (hrow1 : |b 0 + D.t₀ * b 3 - D.Z₀| ≤ K * q)
    (hrow2 : |(b 1 + D.t₀ * b 4) - cl 2 - D.t₀ * cl 3 - cl 4 * (b 0 + D.t₀ * b 3)| ≤ K * q * g)
    (hrow3 : |b 4 - cl 3 - cl 4 * b 3| ≤ K * g) (σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) 1) :
    Submission.Lib.K4QuadraticSheetCore.lineP (D.normLine b) σ ∈ Icc (0 : Fin 3 → ℝ) 1 ∧
      1 / 8 ≤ Submission.Lib.K4QuadraticSheetCore.lineP (D.normLine b) σ 1 ∧
      Submission.Lib.K4QuadraticSheetCore.lineP (D.normLine b) σ 1 ≤ 3 / 8 ∧
      1 / 8 ≤ Submission.Lib.K4QuadraticSheetCore.lineP (D.normLine b) σ 2 ∧
      Submission.Lib.K4QuadraticSheetCore.lineP (D.normLine b) σ 2 ≤ 5 / 8 := by
  have hK0 : 0 ≤ K := by linarith
  have hBpos : 0 < D.B := by rw [hDB]; positivity
  have hq0 : D.q ≠ 0 := by rw [hDq]; exact hq.ne'
  have hrow2' : |b 1 + D.t₀ * b 4 - D.Y₀ - cl 4 * (b 0 + D.t₀ * b 3 - D.Z₀)| ≤ K * q * g := by
    have e : b 1 + D.t₀ * b 4 - D.Y₀ - cl 4 * (b 0 + D.t₀ * b 3 - D.Z₀) =
        (b 1 + D.t₀ * b 4) - cl 2 - D.t₀ * cl 3 - cl 4 * (b 0 + D.t₀ * b 3) := by
      rw [hY₀]; ring
    rw [e]; exact hrow2
  have hsum := contact_base_coefficient_bound hK0 hJ hq hg b hv hrow1 hrow2' hrow3
    (by simpa [abs_sub_comm] using hcenter) hpivot
  rw [← hDq] at hsum
  have hz := D.contactBaseFrame_basePt hq0 b σ
  have hσ0 : 0 ≤ σ := hσ.1
  have hσ1 : σ ≤ 1 := hσ.2
  set z := contactBaseFrame D.t₀ D.q D.Z₀ D.Y₀ (basePt b (D.t₀ + D.q * σ)) with hzdef
  have hz0 : z 0 = σ := by rw [hz]; rfl
  have hz1 : |z 1| ≤ D.B := by
    have e1 : z 1 = (b 0 + D.t₀ * b 3 - D.Z₀) / D.q + σ * b 3 := by rw [hz]; rfl
    rw [e1]
    have h1 := abs_add_le ((b 0 + D.t₀ * b 3 - D.Z₀) / D.q) (σ * b 3)
    have h2 : |σ * b 3| ≤ |b 3| := by
      rw [abs_mul, abs_of_nonneg hσ0]; exact mul_le_of_le_one_left (abs_nonneg _) hσ1
    have := abs_nonneg ((b 1 + D.t₀ * b 4 - D.Y₀ + D.Z₀ * D.t₀ - D.t₀ * (b 0 + D.t₀ * b 3)) / D.q ^ 2)
    have := abs_nonneg ((b 4 + D.Z₀ - D.t₀ * b 3) / D.q)
    rw [hDB]
    linarith
  have hz2 : |z 2| ≤ D.B := by
    have e2 : z 2 = (b 1 + D.t₀ * b 4 - D.Y₀ + D.Z₀ * D.t₀ - D.t₀ * (b 0 + D.t₀ * b 3)) /
        D.q ^ 2 + σ * ((b 4 + D.Z₀ - D.t₀ * b 3) / D.q) := by rw [hz]; rfl
    rw [e2]
    have h1 := abs_add_le ((b 1 + D.t₀ * b 4 - D.Y₀ + D.Z₀ * D.t₀ - D.t₀ * (b 0 + D.t₀ * b 3)) /
      D.q ^ 2) (σ * ((b 4 + D.Z₀ - D.t₀ * b 3) / D.q))
    have h2 : |σ * ((b 4 + D.Z₀ - D.t₀ * b 3) / D.q)| ≤ |(b 4 + D.Z₀ - D.t₀ * b 3) / D.q| := by
      rw [abs_mul, abs_of_nonneg hσ0]; exact mul_le_of_le_one_left (abs_nonneg _) hσ1
    have := abs_nonneg ((b 0 + D.t₀ * b 3 - D.Z₀) / D.q)
    have := abs_nonneg (b 3)
    rw [hDB]
    linarith
  have hP : Submission.Lib.K4QuadraticSheetCore.lineP (D.normLine b) σ = unitContactBase D.B z := by
    rw [D.normLine_lineP hq0 hBpos.ne' b σ]
    rfl
  rw [hP]
  have hmem := unitContactBase_mem_cube hBpos z ⟨by rw [hz0]; exact hσ0, by rw [hz0]; exact hσ1⟩
    hz1 hz2
  obtain ⟨a1, a2, a3, a4⟩ := unitContactBase_interior hBpos z
    ⟨by rw [hz0]; exact hσ0, by rw [hz0]; exact hσ1⟩ hz1 hz2
  exact ⟨hmem, a1, a2, a3, a4⟩

end ChartData

end

end Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep
