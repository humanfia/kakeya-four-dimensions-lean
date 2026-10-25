import Mathlib

/-! Absorb one fixed subpower loss into the packet improvement's arbitrary tolerance. -/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

/-- Keep the original packet mass and event while removing a fixed subpower
loss. The certificate may choose a different packet at each requested exponent. -/
theorem eventual_absorb_subpower_quadratic_packets {Ω : Type*} [MeasurableSpace Ω]
    (N H : ℕ → ℝ) (n : ℕ → ℕ)
    (h : (k : ℕ) → Fin (n k) → ℝ) (a : (k : ℕ) → Fin (n k) → ℝ≥0∞)
    (ρ : (k : ℕ) → Fin (n k) → Measure Ω)
    (Fit : (k : ℕ) → Fin (n k) → MvPolynomial (Fin 2) ℝ → ℝ → Set Ω)
    (R₀ d c : ℝ) (hN : ∀ k, 2 ≤ N k) (hH : ∀ k, 1 ≤ H k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε)
    (hh : ∀ k i, 0 ≤ h k i)
    (hFit : ∀ k i Q E E', E ≤ E' → Fit k i Q E ⊆ Fit k i Q E')
    (hcert : ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
      ∃ (i : Fin (n k)) (Q : MvPolynomial (Fin 2) ℝ), Q.totalDegree ≤ 2 ∧
        (∀ b, |Q.coeff b| ≤ H k * N k ^ R₀) ∧
        ENNReal.ofReal (h k i * N k ^ (-d * c) / H k) * a k i ≤
          ρ k i (Fit k i Q (H k * N k ^ δ * N k ^ (-1 - c)))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      ∃ (i : Fin (n k)) (Q : MvPolynomial (Fin 2) ℝ), Q.totalDegree ≤ 2 ∧
        (∀ b, |Q.coeff b| ≤ N k ^ (R₀ + 1)) ∧
        ENNReal.ofReal (h k i * N k ^ (-d * c - ε)) * a k i ≤
          ρ k i (Fit k i Q (N k ^ ε * N k ^ (-1 - c))) := by
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [hcert δ hδ, hsub 1 zero_lt_one, hsub δ hδ] with k hk hH1 hHδ
  obtain ⟨i, Q, hQ, hcoeff, hmass⟩ := hk
  have hNpos : 0 < N k := by linarith [hN k]
  have hN1 : 1 ≤ N k := by linarith [hN k]
  have hHpos : 0 < H k := zero_lt_one.trans_le (hH k)
  have hHε : H k ≤ N k ^ ε := hHδ.trans
    (Real.rpow_le_rpow_of_exponent_le hN1 (by dsimp [δ]; linarith))
  have herror : H k * N k ^ δ * N k ^ (-1 - c) ≤ N k ^ ε * N k ^ (-1 - c) := by
    calc
      H k * N k ^ δ * N k ^ (-1 - c) ≤ N k ^ δ * N k ^ δ * N k ^ (-1 - c) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hHδ (Real.rpow_nonneg hNpos.le _)) (Real.rpow_nonneg hNpos.le _)
      _ = _ := by
        rw [← Real.rpow_add hNpos]
        congr 2
        dsimp [δ]
        ring
  have hmassReal : h k i * N k ^ (-d * c - ε) ≤ h k i * N k ^ (-d * c) / H k := by
    calc
      h k i * N k ^ (-d * c - ε) = (h k i * N k ^ (-d * c)) / N k ^ ε := by
        rw [Real.rpow_sub hNpos]
        ring
      _ ≤ _ := div_le_div_of_nonneg_left
        (mul_nonneg (hh k i) (Real.rpow_nonneg hNpos.le _)) hHpos hHε
  refine ⟨i, Q, hQ, ?_, ?_⟩
  · intro b
    calc
      |Q.coeff b| ≤ H k * N k ^ R₀ := hcoeff b
      _ ≤ N k ^ 1 * N k ^ R₀ :=
        mul_le_mul_of_nonneg_right hH1 (Real.rpow_nonneg hNpos.le _)
      _ = N k ^ (R₀ + 1) := by rw [← Real.rpow_add hNpos]; congr 1; ring
  · calc
      ENNReal.ofReal (h k i * N k ^ (-d * c - ε)) * a k i ≤
          ENNReal.ofReal (h k i * N k ^ (-d * c) / H k) * a k i :=
        mul_le_mul (ENNReal.ofReal_le_ofReal hmassReal) le_rfl bot_le bot_le
      _ ≤ ρ k i (Fit k i Q (H k * N k ^ δ * N k ^ (-1 - c))) := hmass
      _ ≤ _ := measure_mono (hFit k i Q _ _ herror)

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
