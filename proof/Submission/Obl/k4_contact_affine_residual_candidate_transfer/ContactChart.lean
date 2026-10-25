import Submission.Lib.K4ContactNormalization.RowNormalization

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open Submission.Lib.K4ContactNormalization

noncomputable section

/-- A parent base chart preserving the contact equation and the original
velocity coordinate `b 3`. The original base-volume scale is `q ^ 4`. -/
def contactChartCoeff (t₀ q Z₀ Y₀ : ℝ) (b : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![(b 0 + t₀ * b 3 - Z₀) / q,
    (b 1 + t₀ * b 4 - Y₀ + Z₀ * t₀ - t₀ * (b 0 + t₀ * b 3)) / q ^ 2,
    b 2 + t₀ * b 5,
    b 3,
    (b 4 + Z₀ - t₀ * b 3) / q,
    q * b 5]

def contactChartPoint (t₀ q Z₀ Y₀ : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![(x 0 - t₀) / q, (x 1 - Z₀) / q,
    (x 2 - Y₀ + Z₀ * x 0 - t₀ * x 1) / q ^ 2, x 3]

theorem point_contactChartCoeff (t₀ q Z₀ Y₀ : ℝ) (hq : q ≠ 0)
    (b : Fin 6 → ℝ) (τ : ℝ) :
    point (contactChartCoeff t₀ q Z₀ Y₀ b) τ =
      contactChartPoint t₀ q Z₀ Y₀ (point b (t₀ + q * τ)) := by
  funext i
  fin_cases i <;> simp [point, contactChartCoeff, contactChartPoint] <;>
    field_simp <;> ring

theorem contactChart_preserves_velocity (t₀ q Z₀ Y₀ : ℝ) (b : Fin 6 → ℝ) :
    contactChartCoeff t₀ q Z₀ Y₀ b 3 = b 3 := rfl

theorem contactChart_contact_error (t₀ q Z₀ Y₀ : ℝ) (b : Fin 6 → ℝ) :
    contactChartCoeff t₀ q Z₀ Y₀ b 4 + contactChartCoeff t₀ q Z₀ Y₀ b 0 =
      (b 4 + b 0) / q := by
  simp [contactChartCoeff]
  ring

/-- The velocity alternative pulls back using the original velocity palette. -/
theorem contactChart_strip_identity (t₀ q Z₀ Y₀ : ℝ) (hq : q ≠ 0)
    (b : Fin 6 → ℝ) (z : Fin 2 → ℝ) :
    b 4 - (q * z 0 - Z₀) - (t₀ + q * z 1) * b 3 =
      q * (contactChartCoeff t₀ q Z₀ Y₀ b 4 - z 0 -
        z 1 * contactChartCoeff t₀ q Z₀ Y₀ b 3) := by
  simp [contactChartCoeff]
  field_simp
  ring

/-- Transform a label's two row equations in the same contact chart. -/
def contactChartLabel (t₀ q Z₀ Y₀ : ℝ) (c : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![(c 0 + t₀ * c 1 - Z₀) / q, c 1,
    (c 2 + t₀ * c 3 + c 4 * Z₀ - Y₀) / q ^ 2,
    (c 3 + Z₀) / q, (c 4 - t₀) / q]

theorem contactChart_first_row (t₀ q Z₀ Y₀ : ℝ) (hq : q ≠ 0)
    (b : Fin 6 → ℝ) (c : Fin 5 → ℝ) (τ : ℝ) :
    point (contactChartCoeff t₀ q Z₀ Y₀ b) τ 1 -
      contactChartLabel t₀ q Z₀ Y₀ c 0 - τ * contactChartLabel t₀ q Z₀ Y₀ c 1 =
      (point b (t₀ + q * τ) 1 - c 0 - (t₀ + q * τ) * c 1) / q := by
  simp [point, contactChartCoeff, contactChartLabel]
  field_simp
  ring

theorem contactChart_second_row (t₀ q Z₀ Y₀ : ℝ) (hq : q ≠ 0)
    (b : Fin 6 → ℝ) (c : Fin 5 → ℝ) (τ : ℝ) :
    point (contactChartCoeff t₀ q Z₀ Y₀ b) τ 2 -
      contactChartLabel t₀ q Z₀ Y₀ c 2 - τ * contactChartLabel t₀ q Z₀ Y₀ c 3 -
      contactChartLabel t₀ q Z₀ Y₀ c 4 *
        point (contactChartCoeff t₀ q Z₀ Y₀ b) τ 1 =
      (point b (t₀ + q * τ) 2 - c 2 - (t₀ + q * τ) * c 3 -
        c 4 * point b (t₀ + q * τ) 1) / q ^ 2 := by
  simp [point, contactChartCoeff, contactChartLabel]
  field_simp
  ring

theorem contactChart_velocity_row (t₀ q Z₀ Y₀ : ℝ) (hq : q ≠ 0)
    (b : Fin 6 → ℝ) (c : Fin 5 → ℝ) :
    contactChartCoeff t₀ q Z₀ Y₀ b 4 - contactChartLabel t₀ q Z₀ Y₀ c 3 -
      contactChartLabel t₀ q Z₀ Y₀ c 4 * contactChartCoeff t₀ q Z₀ Y₀ b 3 =
      (b 4 - c 3 - c 4 * b 3) / q := by
  simp [contactChartCoeff, contactChartLabel]
  ring

end
end Submission.Obl.k4_contact_affine_residual_candidate_transfer
