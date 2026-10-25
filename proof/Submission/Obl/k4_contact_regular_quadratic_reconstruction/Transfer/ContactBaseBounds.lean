/- Adapted from this LOT tree, obligation o243 (k4_contact_affine_residual_candidate_transfer),
   session x0835, branch x0835, commit c4aab87f,
   Submission/Obl/k4_contact_affine_residual_candidate_transfer/ContactBaseBounds.lean.
   Namespace and module paths renamed into o261's Transfer namespace;
   the accepted Data record is the same o238 one (k4_critical_switching_state_preparation). -/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer

/-- A centered contact row has bounded initial base coefficients after its
parabolic chart. The coefficient bound does not divide by the parent scale. -/
theorem contact_base_coefficient_bound {K J q g t₀ Z₀ Y₀ c₃ c₄ : ℝ}
    (hK : 0 ≤ K) (hJ : 0 ≤ J) (hq : 0 < q) (hg : g ≤ K * q)
    (b : Fin 6 → ℝ) (hv : |b 3| ≤ K)
    (hrow₁ : |b 0 + t₀ * b 3 - Z₀| ≤ K * q)
    (hrow₂ : |b 1 + t₀ * b 4 - Y₀ - c₄ * (b 0 + t₀ * b 3 - Z₀)| ≤ K * q * g)
    (hrow₃ : |b 4 - c₃ - c₄ * b 3| ≤ K * g)
    (hcenter : |c₃ + Z₀| ≤ J * q) (hpivot : |c₄ - t₀| ≤ J * q) :
    |(b 0 + t₀ * b 3 - Z₀) / q| +
      |(b 1 + t₀ * b 4 - Y₀ + Z₀ * t₀ - t₀ * (b 0 + t₀ * b 3)) / q ^ 2| +
      |b 3| + |(b 4 + Z₀ - t₀ * b 3) / q| ≤
        2 * K + 2 * K ^ 2 + 2 * J * K + J := by
  have h₁ : |(b 0 + t₀ * b 3 - Z₀) / q| ≤ K := by
    rw [abs_div, abs_of_pos hq]
    exact (div_le_iff₀ hq).mpr hrow₁
  have h₂ : |(b 1 + t₀ * b 4 - Y₀ + Z₀ * t₀ - t₀ * (b 0 + t₀ * b 3)) / q ^ 2| ≤
      K ^ 2 + J * K := by
    rw [abs_div, abs_of_pos (by positivity : 0 < q ^ 2)]
    apply (div_le_iff₀ (by positivity : 0 < q ^ 2)).mpr
    calc
      _ = |(b 1 + t₀ * b 4 - Y₀ - c₄ * (b 0 + t₀ * b 3 - Z₀)) +
          (c₄ - t₀) * (b 0 + t₀ * b 3 - Z₀)| := by congr 1; ring
      _ ≤ |b 1 + t₀ * b 4 - Y₀ - c₄ * (b 0 + t₀ * b 3 - Z₀)| +
          |c₄ - t₀| * |b 0 + t₀ * b 3 - Z₀| := by
        rw [← abs_mul]
        exact abs_add_le _ _
      _ ≤ K * q * g + (J * q) * (K * q) := add_le_add hrow₂
        (mul_le_mul hpivot hrow₁ (abs_nonneg _) (mul_nonneg hJ hq.le))
      _ ≤ (K ^ 2 + J * K) * q ^ 2 := by
        have hh := mul_le_mul_of_nonneg_left hg (mul_nonneg hK hq.le)
        nlinarith only [hh]
  have h₄ : |(b 4 + Z₀ - t₀ * b 3) / q| ≤ K ^ 2 + J + J * K := by
    rw [abs_div, abs_of_pos hq]
    apply (div_le_iff₀ hq).mpr
    calc
      _ = |(b 4 - c₃ - c₄ * b 3) + (c₃ + Z₀) + (c₄ - t₀) * b 3| := by congr 1; ring
      _ ≤ |b 4 - c₃ - c₄ * b 3| + |c₃ + Z₀| + |c₄ - t₀| * |b 3| := by
        rw [← abs_mul]
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ K * g + J * q + (J * q) * K :=
        add_le_add (add_le_add hrow₃ hcenter)
          (mul_le_mul hpivot hv (abs_nonneg _) (mul_nonneg hJ hq.le))
      _ ≤ (K ^ 2 + J + J * K) * q := by
        have hh := mul_le_mul_of_nonneg_left hg hK
        nlinarith only [hh]
  linarith

end Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer
