/- Adapted from this LOT tree o222, session x0774, commit 109e510d,
   Submission/Obl/k4_projected_parent_contact_reduction/TransverseRestoration.lean. -/
import Submission.Lib.K4ChartLifting.Normalize

/-! Restoring the transverse scale after applying Scalar in one crop. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open MeasureTheory Set MvPolynomial Submission.Lib.K4ChartLifting

noncomputable section

def transverseSubstitution (y₀ y₁ g : ℝ) : Fin 2 → MvPolynomial (Fin 2) ℝ :=
  ![X 0, C g⁻¹ * (X 1 - C y₀ - C y₁ * X 0)]

def transversePullback (y₀ y₁ g : ℝ) (P : MvPolynomial (Fin 2) ℝ) :
    MvPolynomial (Fin 2) ℝ := bind₁ (transverseSubstitution y₀ y₁ g) P

theorem transverseSubstitution_degree (y₀ y₁ g : ℝ) (i : Fin 2) :
    (transverseSubstitution y₀ y₁ g i).totalDegree ≤ 1 := by
  fin_cases i
  · exact deg1_X _
  · exact deg1_C_mul _ (deg1_sub (deg1_sub (deg1_X _) (deg1_C _))
      (deg1_C_mul _ (deg1_X _)))

theorem transversePullback_degree (y₀ y₁ g : ℝ) (P : MvPolynomial (Fin 2) ℝ) :
    (transversePullback y₀ y₁ g P).totalDegree ≤ P.totalDegree :=
  totalDegree_bind₁_le_of_le_one _ (transverseSubstitution_degree y₀ y₁ g) P

theorem eval_transversePullback (y₀ y₁ g : ℝ) (P : MvPolynomial (Fin 2) ℝ) (t Y : ℝ) :
    eval ![t, Y] (transversePullback y₀ y₁ g P) = eval ![t, (Y - y₀ - t * y₁) / g] P := by
  rw [transversePullback, eval_bind₁']
  apply congrArg (fun z : Fin 2 → ℝ => eval z P)
  funext i
  fin_cases i <;> simp [transverseSubstitution, div_eq_mul_inv] <;> ring

theorem eval_transversePullback_adapted (y₀ y₁ : ℝ) {g : ℝ} (hg : g ≠ 0)
    (P : MvPolynomial (Fin 2) ℝ) (u v beta t w : ℝ) :
    eval ![t, (y₀ + g * u) + t * (y₁ + g * v) + (g * beta) * w]
        (transversePullback y₀ y₁ g P) =
      eval ![t, u + t * v + beta * w] P := by
  rw [eval_transversePullback]
  apply congrArg (fun z : Fin 2 → ℝ => eval z P)
  ext i
  fin_cases i <;> simp <;> field_simp <;> ring

theorem transversePullback_adapted_bound (y₀ y₁ : ℝ) {g : ℝ} (hg : g ≠ 0)
    (P : MvPolynomial (Fin 2) ℝ) (u v beta H : ℝ)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |eval ![t, u + t * v + beta * w] P| ≤ H) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |eval ![t, (y₀ + g * u) + t * (y₁ + g * v) + (g * beta) * w]
        (transversePullback y₀ y₁ g P)| ≤ H := by
  intro t ht w hw
  rw [eval_transversePullback_adapted y₀ y₁ hg]
  exact h t ht w hw

theorem transverse_interval_error (y₀ y₁ : ℝ) {g : ℝ} (hg : 0 < g)
    (Y t u v beta H : ℝ)
    (h : |(Y - y₀ - t * y₁) / g - u - t * v| ≤ H * beta) :
    |Y - (y₀ + g * u) - t * (y₁ + g * v)| ≤ H * (g * beta) := by
  have heq : Y - (y₀ + g * u) - t * (y₁ + g * v) =
      g * ((Y - y₀ - t * y₁) / g - u - t * v) := by field_simp; ring
  rw [heq, abs_mul, abs_of_pos hg]
  convert mul_le_mul_of_nonneg_left h hg.le using 1 <;> ring


/-- A common smaller physical width preserves the scalar moving norm. -/
theorem transversePullback_smaller_width (y₀ y₁ : ℝ) {g beta width H : ℝ}
    (hg : 0 < g) (hb : 0 < beta) (hw : 0 ≤ width) (hwb : width ≤ g * beta)
    (P : MvPolynomial (Fin 2) ℝ) (u v : ℝ)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |eval ![t, u + t * v + beta * w] P| ≤ H) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |eval ![t, (y₀ + g * u) + t * (y₁ + g * v) + width * w]
        (transversePullback y₀ y₁ g P)| ≤ H := by
  have hr₀ : 0 ≤ width / (g * beta) := div_nonneg hw (mul_nonneg hg.le hb.le)
  have hr₁ : width / (g * beta) ≤ 1 := (div_le_one (mul_pos hg hb)).mpr hwb
  intro t ht w hw'
  have hww : |w| ≤ 1 := abs_le.mpr hw'
  have hscaled : (width / (g * beta)) * w ∈ Icc (-1 : ℝ) 1 := by
    apply abs_le.mp
    rw [abs_mul, abs_of_nonneg hr₀]
    simpa only [one_mul] using mul_le_mul hr₁ hww (abs_nonneg _) zero_le_one
  have H' := h t ht ((width / (g * beta)) * w) hscaled
  rw [eval_transversePullback]
  have heq : ((y₀ + g * u) + t * (y₁ + g * v) + width * w - y₀ - t * y₁) / g =
      u + t * v + beta * (width / (g * beta) * w) := by
    field_simp
    ring
  simpa only [heq] using H'

/-- Physical center coefficients have the original crop centers and only a
subpower addition from the normalized scalar centers. -/
theorem transverse_centers_bound {y₀ y₁ g u v B H : ℝ}
    (hg : 0 ≤ g) (hcenter : |y₀| + |y₁| ≤ B) (huv : |u| + |v| ≤ H) :
    |y₀ + g * u| + |y₁ + g * v| ≤ B + g * H := by
  calc
    _ ≤ (|y₀| + |g * u|) + (|y₁| + |g * v|) :=
      add_le_add (abs_add_le _ _) (abs_add_le _ _)
    _ = (|y₀| + |y₁|) + g * (|u| + |v|) := by rw [abs_mul, abs_mul, abs_of_nonneg hg]; ring
    _ ≤ B + g * H := add_le_add hcenter (mul_le_mul_of_nonneg_left huv hg)

end

end Submission.Obl.k4_general_parent_projected_layers
