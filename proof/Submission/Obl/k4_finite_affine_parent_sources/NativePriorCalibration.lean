-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.MassReturn
import Submission.Obl.k4_finite_affine_parent_sources.VelocityFrame

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory

noncomputable section

/-- Two full-prior saturation bounds give the exact relative prior
calibration. In particular the absolute profile offset cancels. -/
lemma saturated_prior_ratio
    (N K D₀ D₁ A₀ A₁ f₀ f₁ : ℝ)
    (hN : 0 < N) (hK : 0 < K) (hD₀ : 0 < D₀) (hD₁ : 0 < D₁)
    (hA₀ : 0 < A₀) (hA₁ : 0 < A₁)
    (hlo₀ : N ^ (-f₀) * D₀ / K ≤ A₀) (hup₀ : A₀ ≤ K * N ^ (-f₀) * D₀)
    (hlo₁ : N ^ (-f₁) * D₁ / K ≤ A₁) (hup₁ : A₁ ≤ K * N ^ (-f₁) * D₁) :
    N ^ (-(f₁ - f₀)) * (D₁ / D₀) / K ^ 2 ≤ A₁ / A₀ ∧
      A₁ / A₀ ≤ K ^ 2 * N ^ (-(f₁ - f₀)) * (D₁ / D₀) := by
  have heq : N ^ (-f₁) = N ^ (-(f₁ - f₀)) * N ^ (-f₀) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  have hpow : N ^ (-f₀) ≠ 0 := (Real.rpow_pos_of_pos hN _).ne'
  constructor
  · apply (le_of_eq ?_).trans (div_le_div₀ hA₁.le hlo₁ hA₀ hup₀)
    rw [heq]
    field_simp
  · apply (div_le_div₀ (by positivity) hup₁ (by positivity) hlo₀).trans_eq
    rw [heq]
    field_simp

lemma toReal_nuE_apply_subset
    {α : Type} [MeasurableSpace α] (ν : Measure α) (A₀ A : Set α)
    (hA : MeasurableSet A) (hsub : A ⊆ A₀) :
    (nuE ν A₀ A).toReal = (ν A).toReal / (ν A₀).toReal := by
  rw [nuE_apply_subset ν A₀ A hA hsub, ENNReal.toReal_mul, ENNReal.toReal_inv]
  ring

/-- The full model assignment has the expected native size, with the
actual time ratio and actual relative velocity determinant. No selected
incidence mass is used to define or calibrate this prior. -/
theorem native_full_prior_calibration
    {α : Type} [MeasurableSpace α] (ν : Measure α) (A₀ A₁ : Set α)
    (hA₁ : MeasurableSet A₁) (hsub : A₁ ⊆ A₀)
    (N K f₀ f₁ q₀ q₁ : ℝ) (Q₀ Q₁ : Matrix (Fin 2) (Fin 2) ℝ)
    (hN : 0 < N) (hK : 0 < K) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (hQ₀ : Q₀.det ≠ 0) (hQ₁ : Q₁.det ≠ 0)
    (hprior₀ : 0 < (ν A₀).toReal) (hprior₁ : 0 < (ν A₁).toReal)
    (hlo₀ : N ^ (-f₀) * |Q₀.det| / K ≤ (ν A₀).toReal)
    (hup₀ : (ν A₀).toReal ≤ K * N ^ (-f₀) * |Q₀.det|)
    (hlo₁ : N ^ (-f₁) * |Q₁.det| / K ≤ (ν A₁).toReal)
    (hup₁ : (ν A₁).toReal ≤ K * N ^ (-f₁) * |Q₁.det|) :
    N ^ (-(f₁ - f₀)) * (q₁ / q₀) ^ 2 *
        |(relativeVelocityFrame q₀ q₁ Q₀ Q₁).det| / K ^ 2 ≤ (nuE ν A₀ A₁).toReal ∧
      (nuE ν A₀ A₁).toReal ≤ K ^ 2 * N ^ (-(f₁ - f₀)) * (q₁ / q₀) ^ 2 *
        |(relativeVelocityFrame q₀ q₁ Q₀ Q₁).det| := by
  have h := saturated_prior_ratio N K |Q₀.det| |Q₁.det| (ν A₀).toReal (ν A₁).toReal
    f₀ f₁ hN hK (abs_pos.mpr hQ₀) (abs_pos.mpr hQ₁) hprior₀ hprior₁ hlo₀ hup₀ hlo₁ hup₁
  have hdet : (q₁ / q₀) ^ 2 * |(relativeVelocityFrame q₀ q₁ Q₀ Q₁).det| =
      |Q₁.det| / |Q₀.det| := by
    rw [relativeVelocityFrame_det]
    field_simp
  rw [toReal_nuE_apply_subset ν A₀ A₁ hA₁ hsub]
  constructor
  · simpa only [mul_assoc, ← mul_div_assoc, hdet] using h.1
  · calc
      _ ≤ K ^ 2 * N ^ (-(f₁ - f₀)) * (|Q₁.det| / |Q₀.det|) := h.2
      _ = _ := by rw [← hdet]; ring

end

end Submission.Obl.k4_finite_affine_parent_sources
