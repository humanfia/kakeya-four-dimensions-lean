/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/QuadraticVariation.lean`. Original attributions are retained below. -/
/- Adapted from this LOT tree, o218, session x0760, commit 771cc68c5af90206a38343b7b1bbe9d5343eaf47,
   `Submission/Obl/k4_horizontal_endpoint_wide_return/Wide/ShortDomainFreezing.lean`.
   The file attributes its source to o218/x0764 1e7e16e835d514cecf4ea54a08623a6e3d7b33b0. -/
/- Adopted from this LOT obligation o218, session x0764, commit 1e7e16e835d514cecf4ea54a08623a6e3d7b33b0, Wide/ShortDomainFreezing.lean. -/

import Submission.Obl.k4_fixed_budget_quadratic_recovery.QuadraticCoefficients

set_option linter.unusedVariables false

/-!
# A quadratic controlled on a long domain is nearly constant on a short one

"On the whole short domain of a retained pairing this difference `F_{Φ_i} − F_Φ` now varies by
`≪ a_i`" (paper `prop:wide-interval`, comparing the projected fits at two domain sizes): a
quadratic in `(t, w)` bounded by `E` on the long normalized domain `[0,1] × [-1,1]` (unit time,
moving interval of width `D` in `w = (Y − Y_c(t))/D`) is `32 E`-Lipschitz there, so on a short
domain of time length `h` and transverse width `b` it varies by at most `32 E (h + 2b/D)`; this
is the offset freezing that turns finer projected fits into constant offsets `D_i`.

Uses accepted o177 `quadratic_coefficients_bound` (six samples bound the coefficients).
Rate-free.
-/

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set Submission.Obl.k4_fixed_budget_quadratic_recovery

/-- A quadratic bounded by `E` on `[0,1] × [-1,1]` is `32 E`-Lipschitz there (`ℓ¹` distance). -/
theorem quadratic_box_lipschitz {c : Fin 6 → ℝ} {E : ℝ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (-1 : ℝ) 1, |quadraticValue c t z| ≤ E)
    {t t' z z' : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (ht' : t' ∈ Icc (0 : ℝ) 1)
    (hz : z ∈ Icc (-1 : ℝ) 1) (hz' : z' ∈ Icc (-1 : ℝ) 1) :
    |quadraticValue c t z - quadraticValue c t' z'| ≤ 32 * E * (|t - t'| + |z - z'|) := by
  have hc := quadratic_coefficients_bound h
  have hE : 0 ≤ E := (abs_nonneg _).trans (h 0 (by norm_num) 0 (by norm_num))
  have hta : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hta' : |t'| ≤ 1 := abs_le.mpr ⟨by linarith [ht'.1], ht'.2⟩
  have hza : |z| ≤ 1 := abs_le.mpr ⟨hz.1, hz.2⟩
  have hza' : |z'| ≤ 1 := abs_le.mpr ⟨hz'.1, hz'.2⟩
  have heq : quadraticValue c t z - quadraticValue c t' z' =
      c 1 * (t - t') + c 2 * (z - z') + c 3 * ((t + t') * (t - t')) +
        c 4 * (t * (z - z') + z' * (t - t')) + c 5 * ((z + z') * (z - z')) := by
    simp only [quadraticValue]; ring
  rw [heq]
  have h1 : |c 1 * (t - t')| ≤ 8 * E * |t - t'| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hc 1) (abs_nonneg _)
  have h2 : |c 2 * (z - z')| ≤ 8 * E * |z - z'| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hc 2) (abs_nonneg _)
  have h3 : |c 3 * ((t + t') * (t - t'))| ≤ 8 * E * (2 * |t - t'|) := by
    rw [abs_mul, abs_mul]
    have : |t + t'| ≤ 2 := (abs_add_le _ _).trans (by linarith)
    exact mul_le_mul (hc 3) (mul_le_mul_of_nonneg_right this (abs_nonneg _)) (by positivity)
      (by positivity)
  have h4 : |c 4 * (t * (z - z') + z' * (t - t'))| ≤ 8 * E * (|z - z'| + |t - t'|) := by
    rw [abs_mul]
    have : |t * (z - z') + z' * (t - t')| ≤ |z - z'| + |t - t'| := by
      calc |t * (z - z') + z' * (t - t')| ≤ |t| * |z - z'| + |z'| * |t - t'| := by
            rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
        _ ≤ 1 * |z - z'| + 1 * |t - t'| := by gcongr
        _ = |z - z'| + |t - t'| := by ring
    exact mul_le_mul (hc 4) this (abs_nonneg _) (by positivity)
  have h5 : |c 5 * ((z + z') * (z - z'))| ≤ 8 * E * (2 * |z - z'|) := by
    rw [abs_mul, abs_mul]
    have : |z + z'| ≤ 2 := (abs_add_le _ _).trans (by linarith)
    exact mul_le_mul (hc 5) (mul_le_mul_of_nonneg_right this (abs_nonneg _)) (by positivity)
      (by positivity)
  calc |c 1 * (t - t') + c 2 * (z - z') + c 3 * ((t + t') * (t - t')) +
        c 4 * (t * (z - z') + z' * (t - t')) + c 5 * ((z + z') * (z - z'))|
      ≤ |c 1 * (t - t')| + |c 2 * (z - z')| + |c 3 * ((t + t') * (t - t'))| +
          |c 4 * (t * (z - z') + z' * (t - t'))| + |c 5 * ((z + z') * (z - z'))| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact abs_add_le _ _
    _ ≤ 8 * E * |t - t'| + 8 * E * |z - z'| + 8 * E * (2 * |t - t'|) +
          8 * E * (|z - z'| + |t - t'|) + 8 * E * (2 * |z - z'|) := by gcongr
    _ = 32 * E * (|t - t'| + |z - z'|) := by ring

/-- **Short-domain freezing.** On a short domain of time length `h` and normalized transverse
width `β` (all inside the long box), a quadratic bounded by `E` on the long box stays within
`32 E (h + β)` of its value at any base point of the short domain. -/
theorem quadratic_short_domain_freezing {c : Fin 6 → ℝ} {E h β t₁ w₁ t z : ℝ}
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (-1 : ℝ) 1, |quadraticValue c t z| ≤ E)
    (ht₁ : t₁ ∈ Icc (0 : ℝ) 1) (hw₁ : w₁ ∈ Icc (-1 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hz : z ∈ Icc (-1 : ℝ) 1) (hth : |t - t₁| ≤ h) (hzβ : |z - w₁| ≤ β) :
    |quadraticValue c t z - quadraticValue c t₁ w₁| ≤ 32 * E * (h + β) := by
  have hE : 0 ≤ E := (abs_nonneg _).trans (hbox 0 (by norm_num) 0 (by norm_num))
  calc |quadraticValue c t z - quadraticValue c t₁ w₁| ≤ 32 * E * (|t - t₁| + |z - w₁|) :=
        quadratic_box_lipschitz hbox ht ht₁ hz hw₁
    _ ≤ 32 * E * (h + β) := by gcongr

end Submission.Obl.k4_subcritical_corrected_scalar_charts
