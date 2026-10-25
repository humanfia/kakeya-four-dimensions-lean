/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/ScalarCellGeometry.lean`. Original attributions are retained below. -/
/- Adapted from this LOT tree, o218, session x0760, commit ce93c8df6e603b8044f968da8a9087dc728f3bb6,
   `Submission/Obl/k4_horizontal_endpoint_wide_return/ScalarCellGeometry.lean`. -/
import Submission.Obl.k4_scalar_coefficient_clustering.Evaluation

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set

/-- Freezing the shear at the time-cell representative preserves the second
sigma gain in the scalar parameter cell. A narrower intercept interval gives
the angular gain without changing its transverse width. -/
theorem scalar_parameter_cell_box (b : Fin 6 → ℝ)
    {D σ p₀ pc qc vc R τ t P χ δ : ℝ} (hD : 0 < D)
    (ht : t ∈ Icc (0 : ℝ) 1) (hτ : τ ∈ Icc (0 : ℝ) 1)
    (htcell : |t - τ| ≤ σ) (hp : |b 0 - pc| ≤ P)
    (hv : |b 3 - vc| ≤ χ) (hdefect : |b 4 + b 0| ≤ δ)
    (hRcell : |(b 1 - qc) / D - 2 * t * ((b 0 - p₀) / D) - R| ≤ σ) :
    |b 0 + t * b 3 - (pc + t * vc)| ≤ P + χ ∧
    |b 1 + t * b 4 - (qc + D * R - t * (2 * p₀ - pc)) -
      τ * (b 0 + t * b 3 - (pc + t * vc))| ≤ D * σ + σ * P + δ + χ := by
  have ht1 : |t| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  have hτ1 : |τ| ≤ 1 := by simpa only [abs_of_nonneg hτ.1] using hτ.2
  have hχ : 0 ≤ χ := (abs_nonneg _).trans hv
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hdefect
  have hP : 0 ≤ P := (abs_nonneg _).trans hp
  have hσ : 0 ≤ σ := (abs_nonneg _).trans htcell
  have hvel : |t * (b 3 - vc)| ≤ χ := by
    rw [abs_mul]
    exact (mul_le_mul ht1 hv (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  constructor
  · have hid : b 0 + t * b 3 - (pc + t * vc) = (b 0 - pc) + t * (b 3 - vc) := by ring
    rw [hid]
    exact (abs_add_le _ _).trans (add_le_add hp hvel)
  · have hid : b 1 + t * b 4 - (qc + D * R - t * (2 * p₀ - pc)) -
        τ * (b 0 + t * b 3 - (pc + t * vc)) =
        D * ((b 1 - qc) / D - 2 * t * ((b 0 - p₀) / D) - R) +
          (t - τ) * (b 0 - pc) + t * (b 4 + b 0) - τ * (t * (b 3 - vc)) := by
      field_simp
      <;> ring
    have hR : |D * ((b 1 - qc) / D - 2 * t * ((b 0 - p₀) / D) - R)| ≤ D * σ := by
      rw [abs_mul, abs_of_pos hD]
      exact mul_le_mul_of_nonneg_left hRcell hD.le
    have hpt : |(t - τ) * (b 0 - pc)| ≤ σ * P := by
      rw [abs_mul]
      exact mul_le_mul htcell hp (abs_nonneg _) hσ
    have hd : |t * (b 4 + b 0)| ≤ δ := by
      rw [abs_mul]
      exact (mul_le_mul ht1 hdefect (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    have hv' : |τ * (t * (b 3 - vc))| ≤ χ := by
      rw [abs_mul]
      exact (mul_le_mul hτ1 hvel (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    rw [hid]
    calc
      _ ≤ (|D * ((b 1 - qc) / D - 2 * t * ((b 0 - p₀) / D) - R) +
          (t - τ) * (b 0 - pc) + t * (b 4 + b 0)|) + |τ * (t * (b 3 - vc))| := abs_sub _ _
      _ ≤ (|D * ((b 1 - qc) / D - 2 * t * ((b 0 - p₀) / D) - R)| +
          |(t - τ) * (b 0 - pc)| + |t * (b 4 + b 0)|) + |τ * (t * (b 3 - vc))| := by
        exact add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl
      _ ≤ _ := add_le_add (add_le_add (add_le_add hR hpt) hd) hv'

/-- The actual floor-cell representatives satisfy the bounds needed to freeze
the time shear. This wrapper uses the accepted scaled-floor error. -/
theorem scalar_parameter_floor_cell_box (b : Fin 6 → ℝ)
    {D σ p₀ pc qc vc t P χ δ : ℝ} (hD : 0 < D) (hσ : 0 < σ)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : |b 0 - pc| ≤ P)
    (hv : |b 3 - vc| ≤ χ) (hdefect : |b 4 + b 0| ≤ δ) :
    let τ := σ * (⌊t / σ⌋ : ℝ)
    let R := σ * (⌊((b 1 - qc) / D - 2 * t * ((b 0 - p₀) / D)) / σ⌋ : ℝ)
    τ ∈ Icc (0 : ℝ) 1 ∧ |t - τ| ≤ σ ∧
      |b 0 + t * b 3 - (pc + t * vc)| ≤ P + χ ∧
      |b 1 + t * b 4 - (qc + D * R - t * (2 * p₀ - pc)) -
        τ * (b 0 + t * b 3 - (pc + t * vc))| ≤ D * σ + σ * P + δ + χ := by
  dsimp only
  have hτ0 : 0 ≤ σ * (⌊t / σ⌋ : ℝ) := mul_nonneg hσ.le
    (by exact_mod_cast (Int.floor_nonneg.mpr (div_nonneg ht.1 hσ.le)))
  have hτle : σ * (⌊t / σ⌋ : ℝ) ≤ t := by
    have := (le_div_iff₀ hσ).mp (Int.floor_le (t / σ))
    linarith
  have hτ : σ * (⌊t / σ⌋ : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨hτ0, hτle.trans ht.2⟩
  have htime := Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hσ t
  have hspace := Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hσ
    ((b 1 - qc) / D - 2 * t * ((b 0 - p₀) / D))
  exact ⟨hτ, htime, scalar_parameter_cell_box b hD ht hτ htime hp hv hdefect hspace⟩

end Submission.Obl.k4_subcritical_corrected_scalar_charts
