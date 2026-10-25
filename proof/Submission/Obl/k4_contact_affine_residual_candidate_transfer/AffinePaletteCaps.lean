import Submission.Lib.K4AffineMeshCaps.Transport

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open MeasureTheory Matrix
open Submission.Lib.K4AffineMeshCaps

/-- Affine base transport retains a finite original palette numerator
verbatim, including a zero bin. No normalization by its success mass is used. -/
theorem affine_mesh_cell_cap_with_palette {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (condition : Ω → Prop)
    (M : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ) (hM : M.det ≠ 0)
    {δ σ C : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) (hC : 0 ≤ C)
    (Γ : ENNReal) (hΓ : Γ ≠ ⊤)
    (hresolve : ∀ i, (∑ j, |M i j| * δ) ≤ σ)
    (hcap : ∀ q : Fin 3 → ℤ,
      μ {p | baseMesh δ (Z p) = q ∧ condition p} ≤ ENNReal.ofReal (C * δ ^ 3) * Γ)
    (q : Fin 3 → ℤ) :
    μ {p | baseMesh σ (affineBase M b (Z p)) = q ∧ condition p} ≤
      ENNReal.ofReal (27 * C * |M.det|⁻¹ * σ ^ 3) * Γ := by
  have hinput : ENNReal.ofReal ((C * Γ.toReal) * δ ^ 3) =
      ENNReal.ofReal (C * δ ^ 3) * Γ := by
    calc
      _ = ENNReal.ofReal ((C * δ ^ 3) * Γ.toReal) := by congr 1; ring
      _ = ENNReal.ofReal (C * δ ^ 3) * ENNReal.ofReal Γ.toReal :=
        ENNReal.ofReal_mul (by positivity)
      _ = _ := by rw [ENNReal.ofReal_toReal hΓ]
  have hh := affine_mesh_cell_cap μ Z condition M b hM hδ hσ
    (mul_nonneg hC ENNReal.toReal_nonneg) hresolve
    (fun q => (hcap q).trans_eq hinput.symm) q
  apply hh.trans_eq
  calc
    _ = ENNReal.ofReal ((27 * C * |M.det|⁻¹ * σ ^ 3) * Γ.toReal) := by congr 1; ring
    _ = ENNReal.ofReal (27 * C * |M.det|⁻¹ * σ ^ 3) * ENNReal.ofReal Γ.toReal :=
      ENNReal.ofReal_mul (by positivity)
    _ = _ := by rw [ENNReal.ofReal_toReal hΓ]

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
