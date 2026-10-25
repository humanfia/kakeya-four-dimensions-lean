/-
Adapted from this LOT tree o203, session x0699, commit 4341160d,
Submission/Obl/k4_horizontal_supercritical_rate_candidates/ScalarCaps.lean (namespace
Submission.Obl.k4_horizontal_supercritical_rate_candidates renamed to
Submission.Obl.k4_horizontal_supercritical_three_projections.Parent).
-/
import Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.CellGeometry
import Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.RectangularGrid

namespace Submission.Obl.k4_horizontal_supercritical_three_projections.Parent

open Set MeasureTheory

noncomputable section

/-- The original fine joint caps control a scalar chart cell with an angular
intercept slice. The palette weight and angular width remain explicit. -/
theorem scalar_chart_cell_joint_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (b : Ω → Fin 6 → ℝ) (t f : Ω → ℝ) (E : Set Ω)
    {δ D σ β χ ζ H X V pc qc pa r₀ v τ : ℝ} (hδ : 0 < δ) (hD : 0 < D)
    (hσ : δ ≤ σ) (hB : δ ≤ D * β + χ)
    (hC : δ ≤ D * σ + σ * (D * β) + ζ + χ)
    (hH : 1 ≤ H) (hX : 0 ≤ X) (hw : |2 * pc - pa| ≤ H) (hv : |v| ≤ H)
    (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hE : ∀ z ∈ E, t z ∈ Icc (0 : ℝ) 1 ∧ |t z - τ| ≤ σ ∧
      |b z 0 - pa| ≤ D * β ∧ |b z 3 - v| ≤ χ ∧ |b z 4 + b z 0| ≤ ζ ∧
      |scalarParameter (t z) ((b z 0 - pc) / D) ((b z 1 - qc) / D) - r₀| ≤ σ ∧
      |f z| ≤ X)
    (weight : ENNReal)
    (hcap : ∀ c j, μ {z | (fun i => ⌊(![t z, b z 0 + t z * b z 3,
        b z 1 + t z * b z 4] : Fin 3 → ℝ) i / δ⌋) = c ∧ ⌊f z⌋ = j} ≤
      ENNReal.ofReal (V * δ ^ 3) * weight) :
    μ E ≤ ENNReal.ofReal (819 * H ^ 3 * σ * (D * β + χ) *
      (D * σ + σ * (D * β) + ζ + χ) * (2 * X + 5) * V) * weight := by
  have hτH : |τ| ≤ H := by
    rw [abs_of_nonneg hτ.1]
    exact hτ.2.trans hH
  refine rectangular_box_joint_bound μ
    (fun z => ![t z, b z 0 + t z * b z 3, b z 1 + t z * b z 4]) f E
    hδ hσ hB hC hH hX τ pa (qc + D * r₀) v (2 * pc - pa) τ hw hv hτH ?_ weight hcap
  intro z hz
  obtain ⟨ht, htτ, hp, hv, he, hR, hf⟩ := hE z hz
  obtain ⟨hZ, hY⟩ := scalar_cell_physical_box (b z) hD ht hτ htτ hp hv he hR
  exact ⟨htτ, hZ, hY, hf⟩

end

end Submission.Obl.k4_horizontal_supercritical_three_projections.Parent
