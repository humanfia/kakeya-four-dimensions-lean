/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeScalarOscillation.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeScalarEntry
import Submission.Obl.k4_subcritical_corrected_scalar_charts.DirectionalCorrection

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set
open Submission.Obl.k4_fixed_budget_quadratic_recovery

noncomputable section

/-- An unrestricted constant coefficient has no cost in bilinear oscillation. -/
theorem bilinear_quadratic_oscillation {c : Fin 6 → ℝ} {B t t' z z' : ℝ}
    (hB : 0 ≤ B) (h1 : |c 1| ≤ B) (h2 : |c 2| ≤ B) (h4 : |c 4| ≤ B)
    (h3 : c 3 = 0) (h5 : c 5 = 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (ht' : t' ∈ Icc (0 : ℝ) 1)
    (hz : |z| ≤ 1) (hz' : |z'| ≤ 1) :
    |quadraticValue c t z - quadraticValue c t' z'| ≤
      2 * B * (|t - t'| + |z - z'|) := by
  have heq : quadraticValue c t z - quadraticValue c t' z' =
      c 1 * (t - t') + c 2 * (z - z') + c 4 * (t * (z - z') + z' * (t - t')) := by
    simp only [quadraticValue, h3, h5, zero_mul, add_zero]
    ring
  have hta : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hcross : |t * (z - z') + z' * (t - t')| ≤ |z - z'| + |t - t'| := by
    calc
      _ ≤ |t| * |z - z'| + |z'| * |t - t'| := by
        rw [← abs_mul, ← abs_mul]
        exact abs_add_le _ _
      _ ≤ 1 * |z - z'| + 1 * |t - t'| := by gcongr
      _ = _ := by ring
  rw [heq]
  calc
    _ ≤ |c 1 * (t - t')| + |c 2 * (z - z')| +
        |c 4 * (t * (z - z') + z' * (t - t'))| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ B * |t - t'| + B * |z - z'| + B * (|z - z'| + |t - t'|) := by
      simp only [abs_mul]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
        (mul_le_mul_of_nonneg_right h2 (abs_nonneg _)))
        (mul_le_mul h4 hcross (abs_nonneg _) hB)
    _ = _ := by ring

/-- Scalar entry variation needs only three nonconstant coefficients. Neither
the raw native constant nor the engine's displayed coefficient exponent enters. -/
theorem nativeScalarEntry_oscillation (H : Fin 6 → ℝ) (β : Fin 3 → ℝ) (L : Fin 4 → ℝ)
    (D A pc qc v : ℝ) {B t t' R R' : ℝ} (hB : 0 ≤ B)
    (h1 : |nativeScalarEntryCoeff H β L D A pc qc v 1| ≤ B)
    (h2 : |nativeScalarEntryCoeff H β L D A pc qc v 2| ≤ B)
    (h4 : |nativeScalarEntryCoeff H β L D A pc qc v 4| ≤ B)
    (ht : t ∈ Icc (0 : ℝ) 1) (ht' : t' ∈ Icc (0 : ℝ) 1)
    (hR : |R| ≤ 4) (hR' : |R'| ≤ 4) :
    |nativeScalarEntry H β L D A pc qc v t R - nativeScalarEntry H β L D A pc qc v t' R'| ≤
      2 * B * (|t - t'| + |R - R'|) := by
  have hz : |R / 4| ≤ 1 := by rw [abs_div]; norm_num; linarith
  have hz' : |R' / 4| ≤ 1 := by rw [abs_div]; norm_num; linarith
  have hdiff : |R / 4 - R' / 4| ≤ |R - R'| := by
    rw [← sub_div, abs_div]
    norm_num
    exact div_le_self (abs_nonneg _) (by norm_num)
  have hh := bilinear_quadratic_oscillation hB h1 h2 h4 (by rfl) (by rfl) ht ht' hz hz'
  simp only [nativeScalarEntryCoeff_eval, mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hdiff) (by positivity))

/-- Whole coarse endpoint norms control exactly the baseline combinations that
occur in the three scalar oscillation coefficients. -/
theorem endpoint_scalar_slopes {H : Fin 6 → ℝ} {pc qc D E : ℝ} (hD : 0 < D)
    (hnorm : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ Icc pc (pc + D), ∀ q ∈ Icc qc (qc + D),
      |parameterPredictor H t p q| ≤ E) :
    |H 1 + H 3 * pc + H 5 * qc| ≤ 2 * E ∧
      |H 4| ≤ 2 * E / D ∧ |H 5| ≤ 4 * E / D := by
  have hp : pc ∈ Icc pc (pc + D) := ⟨le_rfl, by linarith⟩
  have hq : qc ∈ Icc qc (qc + D) := ⟨le_rfl, by linarith⟩
  have hpD : pc + D ∈ Icc pc (pc + D) := ⟨by linarith, le_rfl⟩
  have hqD : qc + D ∈ Icc qc (qc + D) := ⟨by linarith, le_rfl⟩
  have h0 := predictor_slopes_of_corners hD
    (hnorm 0 (by norm_num) pc hp qc hq) (hnorm 0 (by norm_num) (pc + D) hpD qc hq)
    (hnorm 0 (by norm_num) pc hp (qc + D) hqD)
  have h1 := predictor_slopes_of_corners hD
    (hnorm 1 (by norm_num) pc hp qc hq) (hnorm 1 (by norm_num) (pc + D) hpD qc hq)
    (hnorm 1 (by norm_num) pc hp (qc + D) hqD)
  simp only [mul_zero, add_zero, mul_one] at h0 h1
  refine ⟨?_, h0.2, ?_⟩
  · have heq : H 1 + H 3 * pc + H 5 * qc =
        parameterPredictor H 1 pc qc - parameterPredictor H 0 pc qc := by
      simp only [parameterPredictor, Submission.Lib.K4FullTimeLayers.parameterPredictor]
      ring
    rw [heq]
    exact (abs_sub _ _).trans ((add_le_add (hnorm 1 (by norm_num) pc hp qc hq)
      (hnorm 0 (by norm_num) pc hp qc hq)).trans_eq (by ring))
  · have hh := abs_sub (H 4 + H 5) (H 4)
    rw [show H 4 + H 5 - H 4 = H 5 by ring] at hh
    exact hh.trans ((add_le_add h1.2 h0.2).trans_eq (by ring))

/-- Explicit nonconstant scalar coefficients from bounded genuine native slopes
and coarse whole-domain endpoint norms. The native constant is unrestricted. -/
theorem nativeScalarEntry_nonconstant_bounds (H : Fin 6 → ℝ) (β : Fin 3 → ℝ) (L : Fin 4 → ℝ)
    {D A pc qc v E M P Bβ : ℝ} (hD : 0 < D) (hA : 0 < A)
    (hM : 0 ≤ M) (hP : 0 ≤ P) (hBβ : 0 ≤ Bβ)
    (hL1 : |L 1| ≤ M) (hL2 : |L 2| ≤ M) (hL3 : |L 3| ≤ M)
    (hpc : |pc| ≤ P) (hv : |v| ≤ P) (hβ : |β 2| ≤ Bβ)
    (hnorm : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ Icc pc (pc + D), ∀ q ∈ Icc qc (qc + D),
      |parameterPredictor H t p q| ≤ E) :
    |nativeScalarEntryCoeff H β L D A pc qc v 1| ≤ ((1 + 2 * P) * M + 2 * E) / A ∧
    |nativeScalarEntryCoeff H β L D A pc qc v 2| ≤ (4 * D * M + 8 * E) / A ∧
    |nativeScalarEntryCoeff H β L D A pc qc v 4| ≤ 16 * E / A + 2 * Bβ := by
  obtain ⟨ht, h4, h5⟩ := endpoint_scalar_slopes hD hnorm
  have hE : 0 ≤ E := (abs_nonneg _).trans (hnorm 0 (by norm_num) pc ⟨le_rfl, by linarith⟩ qc ⟨le_rfl, by linarith⟩)
  have hvel : |v * L 2| ≤ P * M := by rw [abs_mul]; exact mul_le_mul hv hL2 (abs_nonneg _) hP
  have hpos : |pc * L 3| ≤ P * M := by rw [abs_mul]; exact mul_le_mul hpc hL3 (abs_nonneg _) hP
  refine ⟨?_, ?_, ?_⟩
  · change |(L 1 + v * L 2 - pc * L 3 - H 1 - H 3 * pc - H 5 * qc) / A| ≤ _
    rw [abs_div, abs_of_pos hA]
    apply div_le_div_of_nonneg_right _ hA.le
    have heq : L 1 + v * L 2 - pc * L 3 - H 1 - H 3 * pc - H 5 * qc =
        (L 1 + v * L 2 - pc * L 3) - (H 1 + H 3 * pc + H 5 * qc) := by ring
    rw [heq]
    calc
      _ ≤ (|L 1| + |v * L 2| + |pc * L 3|) + |H 1 + H 3 * pc + H 5 * qc| :=
        (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ ≤ (M + P * M + P * M) + 2 * E := by gcongr
      _ = _ := by ring
  · change |4 * D * (L 3 - H 4) / A| ≤ _
    rw [abs_div, abs_of_pos hA, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * D)]
    apply (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hL3 h4)) (by positivity)) hA.le).trans_eq
    field_simp
    ring
  · change |-4 * D * H 5 / A - 2 * β 2| ≤ _
    calc
      _ ≤ 4 * D * |H 5| / A + 2 * |β 2| := by
        have hh := abs_sub (-4 * D * H 5 / A) (2 * β 2)
        simpa only [abs_div, abs_mul, abs_neg, abs_of_pos hA, abs_of_pos hD,
          abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos (by norm_num : (0 : ℝ) < 2)] using hh
      _ ≤ 4 * D * (4 * E / D) / A + 2 * Bβ := by gcongr
      _ = _ := by field_simp; ring

/-- A single coefficient ceiling for the actual native slope bound. Only the
coarse box norm and the correction coefficient enter, beyond powers of K. -/
theorem nativeScalarEntry_uniform_nonconstant_bound (H : Fin 6 → ℝ) (β : Fin 3 → ℝ)
    (L : Fin 4 → ℝ) {K D A pc qc v E Bβ : ℝ} (hK : 1 ≤ K)
    (hD : 0 < D) (hD1 : D ≤ 1) (hA : 0 < A) (hBβ : 0 ≤ Bβ)
    (hL : ∀ e : Fin 3, |L e.succ| ≤ 36 * K ^ 4)
    (hpc : |pc| ≤ 3 * K) (hv : |v| ≤ 3 * K) (hβ : |β 2| ≤ Bβ)
    (hnorm : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ Icc pc (pc + D), ∀ q ∈ Icc qc (qc + D),
      |parameterPredictor H t p q| ≤ E) :
    let B := (512 * K ^ 5 + 32 * E) / A + 2 * Bβ
    |nativeScalarEntryCoeff H β L D A pc qc v 1| ≤ B ∧
    |nativeScalarEntryCoeff H β L D A pc qc v 2| ≤ B ∧
    |nativeScalarEntryCoeff H β L D A pc qc v 4| ≤ B := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hE : 0 ≤ E := (abs_nonneg _).trans
    (hnorm 0 (by norm_num) pc ⟨le_rfl, by linarith⟩ qc ⟨le_rfl, by linarith⟩)
  have hh := nativeScalarEntry_nonconstant_bounds H β L hD hA
    (by positivity : 0 ≤ 36 * K ^ 4) (by positivity : 0 ≤ 3 * K) hBβ
    (hL 0) (hL 1) (hL 2) hpc hv hβ hnorm
  have hK45 : K ^ 4 ≤ K ^ 5 := pow_le_pow_right₀ hK (by norm_num)
  have hK50 : 0 ≤ K ^ 5 := by positivity
  have hb : 0 ≤ 2 * Bβ := by positivity
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · refine hh.1.trans ((div_le_div_of_nonneg_right ?_ hA.le).trans (le_add_of_nonneg_right hb))
    nlinarith
  · refine hh.2.1.trans ((div_le_div_of_nonneg_right ?_ hA.le).trans (le_add_of_nonneg_right hb))
    have hd := mul_le_mul_of_nonneg_right hD1 (show 0 ≤ 144 * K ^ 4 by positivity)
    nlinarith
  · refine hh.2.2.trans (add_le_add (div_le_div_of_nonneg_right ?_ hA.le) le_rfl)
    nlinarith

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
