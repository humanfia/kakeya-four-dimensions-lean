/- Adapted from: here:o222, session x0774, commit 3c748bb8.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/AffineSheetPullback.lean. -/
import Submission.Lib.K4AffineMeshCaps.Transport
import Submission.Lib.K4ContactNormalization.ResidualNormalization

/-! Return an affine hidden predictor from a row chart to original coordinates. -/

namespace Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation

open MvPolynomial Matrix Set
open Submission.Lib.K4ContactNormalization (affineBase)

noncomputable section

def affineHiddenPoint (A : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ)
    (h a : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  let z := Submission.Lib.K4AffineMeshCaps.affineBase A b (x ∘ Fin.castSucc)
  ![z 0, z 1, z 2, (x 3 - h) / a]

def affinePredictorPullback (A : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ)
    (h a : ℝ) (L : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![h + a * (L 0 + L 1 * b 0 + L 2 * b 1 + L 3 * b 2),
    a * (L 1 * A 0 0 + L 2 * A 1 0 + L 3 * A 2 0),
    a * (L 1 * A 0 1 + L 2 * A 1 1 + L 3 * A 2 1),
    a * (L 1 * A 0 2 + L 2 * A 1 2 + L 3 * A 2 2)]

/-- No bound on the affine coefficients is needed to return a full-time fit. -/
theorem affinePredictorPullback_residual (A : Matrix (Fin 3) (Fin 3) ℝ)
    (b : Fin 3 → ℝ) (h a : ℝ) (ha : a ≠ 0) (L x : Fin 4 → ℝ) :
    eval x (affineBase (affinePredictorPullback A b h a L)) - x 3 =
      a * (eval (affineHiddenPoint A b h a x) (affineBase L) -
        affineHiddenPoint A b h a x 3) := by
  simp [affinePredictorPullback, affineHiddenPoint, affineBase,
    Submission.Lib.K4AffineMeshCaps.affineBase, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, Function.comp_def]
  field_simp
  ring

theorem affinePredictorPullback_fit (A : Matrix (Fin 3) (Fin 3) ℝ)
    (b : Fin 3 → ℝ) (h a : ℝ) (ha : a ≠ 0) (L x : Fin 4 → ℝ) {E : ℝ}
    (hfit : |eval (affineHiddenPoint A b h a x) (affineBase L) -
      affineHiddenPoint A b h a x 3| ≤ E) :
    |eval x (affineBase (affinePredictorPullback A b h a L)) - x 3| ≤ |a| * E := by
  rw [affinePredictorPullback_residual A b h a ha L x, abs_mul]
  exact mul_le_mul_of_nonneg_left hfit (abs_nonneg a)

theorem affinePredictorPullback_full_fit {ι : Type*} (I : Set ι)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ) (h a : ℝ) (ha : a ≠ 0)
    (L : Fin 4 → ℝ) (X Y : ι → Fin 4 → ℝ) {E : ℝ}
    (hchart : ∀ t ∈ I, Y t = affineHiddenPoint A b h a (X t))
    (hfit : ∀ t ∈ I, |eval (Y t) (affineBase L) - Y t 3| ≤ E) :
    ∀ t ∈ I, |eval (X t) (affineBase (affinePredictorPullback A b h a L)) - X t 3| ≤
      |a| * E := by
  intro t ht
  apply affinePredictorPullback_fit A b h a ha L (X t)
  simpa only [hchart t ht] using hfit t ht

end

end Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation
