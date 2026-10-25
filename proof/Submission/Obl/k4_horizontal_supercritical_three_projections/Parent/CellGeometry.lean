/-
Adapted from this LOT tree o203, session x0699, commit 4341160d,
Submission/Obl/k4_horizontal_supercritical_rate_candidates/CellGeometry.lean (namespace
Submission.Obl.k4_horizontal_supercritical_rate_candidates renamed to
Submission.Obl.k4_horizontal_supercritical_three_projections.Parent).
-/
import Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.Geometry

namespace Submission.Obl.k4_horizontal_supercritical_three_projections.Parent

open Set

noncomputable section

/-- A scalar parameter cell and an angular intercept slice determine an
ordinary sheared box. The transverse width stays independent of the slice. -/
theorem scalar_cell_physical_box (b : Fin 6 → ℝ)
    {pc qc pa D r₀ v t τ χ E σ β : ℝ} (hD : 0 < D)
    (ht : t ∈ Icc (0 : ℝ) 1) (hτ : τ ∈ Icc (0 : ℝ) 1)
    (htτ : |t - τ| ≤ σ) (hp : |b 0 - pa| ≤ D * β)
    (hv : |b 3 - v| ≤ χ) (he : |b 4 + b 0| ≤ E)
    (hR : |scalarParameter t ((b 0 - pc) / D) ((b 1 - qc) / D) - r₀| ≤ σ) :
    |b 0 + t * b 3 - (pa + t * v)| ≤ D * β + χ ∧
      |b 1 + t * b 4 - (qc + D * r₀ - t * (2 * pc - pa)) -
        τ * (b 0 + t * b 3 - (pa + t * v))| ≤
          D * σ + σ * (D * β) + E + χ := by
  have ht₁ : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hτ₁ : |τ| ≤ 1 := by rw [abs_of_nonneg hτ.1]; exact hτ.2
  have hχ : 0 ≤ χ := (abs_nonneg _).trans hv
  have hE : 0 ≤ E := (abs_nonneg _).trans he
  have hσ : 0 ≤ σ := (abs_nonneg _).trans htτ
  have hDβ : 0 ≤ D * β := (abs_nonneg _).trans hp
  have hvel : |t * (b 3 - v)| ≤ χ := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul ht₁ hv (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  constructor
  · calc
      _ = |(b 0 - pa) + t * (b 3 - v)| := by congr 1; ring
      _ ≤ |b 0 - pa| + |t * (b 3 - v)| := abs_add_le _ _
      _ ≤ D * β + χ := add_le_add hp hvel
  · have hscale : D * scalarParameter t ((b 0 - pc) / D) ((b 1 - qc) / D) =
        b 1 - qc - 2 * t * (b 0 - pc) := by
      unfold scalarParameter
      field_simp
    have heq :
        b 1 + t * b 4 - (qc + D * r₀ - t * (2 * pc - pa)) -
          τ * (b 0 + t * b 3 - (pa + t * v)) =
        D * (scalarParameter t ((b 0 - pc) / D) ((b 1 - qc) / D) - r₀) +
          (t - τ) * (b 0 - pa) + t * (b 4 + b 0) - τ * (t * (b 3 - v)) := by
      simp only [mul_sub]
      rw [hscale]
      ring
    rw [heq]
    have h₁ : |D * (scalarParameter t ((b 0 - pc) / D) ((b 1 - qc) / D) - r₀)| ≤ D * σ := by
      rw [abs_mul, abs_of_pos hD]
      exact mul_le_mul_of_nonneg_left hR hD.le
    have h₂ : |(t - τ) * (b 0 - pa)| ≤ σ * (D * β) := by
      rw [abs_mul]
      exact mul_le_mul htτ hp (abs_nonneg _) hσ
    have h₃ : |t * (b 4 + b 0)| ≤ E := by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul ht₁ he (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have h₄ : |τ * (t * (b 3 - v))| ≤ χ := by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul hτ₁ hvel (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    calc
      _ ≤ (|D * (scalarParameter t ((b 0 - pc) / D) ((b 1 - qc) / D) - r₀)| +
          |(t - τ) * (b 0 - pa)|) + |t * (b 4 + b 0)| + |τ * (t * (b 3 - v))| := by
        exact (abs_sub _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ ≤ _ := add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄

/-- When rounding is below the transverse mesh, the sheared volume retains
exactly one factor of the angular slice width. -/
theorem scalar_cell_box_volume {D σ β χ ζ : ℝ} (hD : 0 ≤ D) (hσ : 0 ≤ σ)
    (hβ : σ ≤ β) (hβ₁ : β ≤ 1) (hχ₀ : 0 ≤ χ) (hχ : χ ≤ D * σ)
    (hζ₀ : 0 ≤ ζ) (hζ : ζ ≤ D * σ) :
    σ * (D * β + χ) * (D * σ + σ * (D * β) + ζ + χ) ≤
      8 * D ^ 2 * σ ^ 2 * β := by
  have hβ₀ : 0 ≤ β := hσ.trans hβ
  have hB : D * β + χ ≤ 2 * D * β := by
    have h := mul_le_mul_of_nonneg_left hβ hD
    linarith only [hχ, h]
  have hC : D * σ + σ * (D * β) + ζ + χ ≤ 4 * D * σ := by
    have h := mul_le_mul_of_nonneg_left hβ₁ (mul_nonneg hD hσ)
    nlinarith only [h, hχ, hζ]
  calc
    _ ≤ σ * (2 * D * β) * (4 * D * σ) := by gcongr
    _ = _ := by ring

end

end Submission.Obl.k4_horizontal_supercritical_three_projections.Parent
