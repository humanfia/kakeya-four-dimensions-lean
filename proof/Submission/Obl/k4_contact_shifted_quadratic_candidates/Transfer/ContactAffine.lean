/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/ContactAffine.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.ContactMatrix

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

noncomputable section

/-- An original affine function in a contact base chart. -/
def contactAffineCoeff (t₀ q Z₀ Y₀ : ℝ) (L : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![L 0 + L 1 * t₀ + L 2 * Z₀ + L 3 * Y₀, q * (L 1 - Z₀ * L 3),
    q * (L 2 + t₀ * L 3), q ^ 2 * L 3]

theorem contactAffine_value (t₀ Z₀ Y₀ : ℝ) {q : ℝ} (hq : q ≠ 0)
    (L : Fin 4 → ℝ) (t Z Y : ℝ) :
    contactAffineCoeff t₀ q Z₀ Y₀ L 0 +
      contactAffineCoeff t₀ q Z₀ Y₀ L 1 * ((t - t₀) / q) +
      contactAffineCoeff t₀ q Z₀ Y₀ L 2 * ((Z - Z₀) / q) +
      contactAffineCoeff t₀ q Z₀ Y₀ L 3 * ((Y - Y₀ + Z₀ * t - t₀ * Z) / q ^ 2) =
      L 0 + L 1 * t + L 2 * Z + L 3 * Y := by
  simp [contactAffineCoeff] <;> field_simp <;> ring

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
