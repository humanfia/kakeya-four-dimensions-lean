/- Adapted from: here:o223
   (session x0927, branch x0927).
   This is the library export of the o223 adapter, first committed at b6fc491c.
   Earlier source: here:o241, session x0842, branch x0842, for
   k4_contact_equal_rate_affine_palettes. Original authorship is retained:
   x0842 wrote the cube/budget adapter; x0927 adapted its namespaces and imports
   to the gate-accepted Submission.Lib.K4QuadraticSheetCore. -/
import Mathlib
import Submission.Lib.K4ContactAffine.Adapter.CubePalette

/-!
# Polynomial budgets of the affine-sheet core

The constants of x0777's core (`remezC`, `discBudget`, `stepGain`, `sffKappa`) and of the cube
palette (`cubeB₁`, `cubeErr`) are polynomials in `Λ` once the coefficient-control constant `Cs`
is fixed. `core_budgets` records one constant `C` with

* `cubeErr Cs Λ ≤ C Λ⁸⁰`, and
* `C Λ⁸⁰ (ε + ρ) ≤ 1` implies the three smallness conditions `hs1`, `hs2`, `hs3` of
  `sff_frame_bound` (and of `cube_palette`, `label_palette`),

for every `Λ ≥ 1`. With `Λ` a subpower times a small fixed power `N^{3v}` and `ε, ρ` negative
powers of `N`, both are then eventually true.
-/

namespace Submission.Lib.K4ContactAffine.Adapter

open Submission.Lib.K4QuadraticSheetCore

noncomputable section

theorem remezC_four (Λ : ℝ) : remezC 4 Λ = 160 ^ 12 * Λ ^ 12 := by
  simp only [remezC]
  norm_num
  ring

theorem discBudget_eq (Cs Λ : ℝ) : discBudget Cs Λ = 6 * Cs * 160 ^ 12 * Λ ^ 14 := by
  simp only [discBudget, remezC_four]
  ring

theorem stepGain_eq (Cs Λ : ℝ) :
    stepGain Cs Λ = 160 ^ 24 * (24 + 32 * Cs) * (6 * Cs) * Λ ^ 28 := by
  simp only [stepGain, discBudget_eq, remezC_four]
  ring

/-- **Budgets of the core.** One constant controls the cube error and all three smallness
conditions of the core, polynomially in `Λ`. -/
theorem core_budgets (Cs : ℝ) (hCs0 : 0 < Cs) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Λ ε ρ : ℝ, 1 ≤ Λ → 0 ≤ ε → 0 ≤ ρ →
      cubeErr Cs Λ ≤ C * Λ ^ 80 ∧
      (C * Λ ^ 80 * (ε + ρ) ≤ 1 →
        4 * Cs * remezC 4 Λ * ρ ≤ 1 ∧
        8 * discBudget Cs Λ * ρ * Λ ^ 2 ≤ 1 ∧
        192 * Cs * sffKappa Cs Λ * (ε + ρ) * Λ ^ 2 ≤ 1) := by
  -- the constant of `stepGain`
  set G : ℝ := 160 ^ 24 * (24 + 32 * Cs) * (6 * Cs) with hG
  have hG0 : 0 < G := by positivity
  -- `sffKappa ≤ Kc Λ⁷²`
  set Kc : ℝ := 160 ^ 12 * 32 * (1 + G + G ^ 2) with hKc
  have hKc0 : 0 < Kc := by positivity
  set C : ℝ := 1 + 4 * Cs * 160 ^ 12 + 8 * (6 * Cs * 160 ^ 12) + 192 * Cs * Kc +
    60 * (1 + 13 * 4 * 400 * Kc) with hC
  have hC1 : 1 ≤ C := by
    have : 0 ≤ 4 * Cs * 160 ^ 12 + 8 * (6 * Cs * 160 ^ 12) + 192 * Cs * Kc +
      60 * (1 + 13 * 4 * 400 * Kc) := by positivity
    linarith
  refine ⟨C, hC1, fun Λ ε ρ hΛ hε hρ => ?_⟩
  have hΛ0 : 0 < Λ := by linarith
  have hpow : ∀ m n : ℕ, m ≤ n → Λ ^ m ≤ Λ ^ n := fun m n hmn => pow_le_pow_right₀ hΛ hmn
  have hkappa : sffKappa Cs Λ ≤ Kc * Λ ^ 72 := by
    simp only [sffKappa, remezC_four, stepGain_eq]
    rw [← hG]
    have h28 : 1 ≤ Λ ^ 28 := one_le_pow₀ hΛ
    have h1 : 1 + G * Λ ^ 28 + (G * Λ ^ 28) ^ 2 ≤ (1 + G + G ^ 2) * Λ ^ 56 := by
      have e : (G * Λ ^ 28) ^ 2 = G ^ 2 * Λ ^ 56 := by ring
      rw [e]
      have h56 : Λ ^ 28 ≤ Λ ^ 56 := hpow 28 56 (by norm_num)
      have h0 : 1 ≤ Λ ^ 56 := one_le_pow₀ hΛ
      nlinarith [sq_nonneg G]
    calc 160 ^ 12 * Λ ^ 12 * (32 * Λ ^ 4) * (1 + G * Λ ^ 28 + (G * Λ ^ 28) ^ 2)
        ≤ 160 ^ 12 * Λ ^ 12 * (32 * Λ ^ 4) * ((1 + G + G ^ 2) * Λ ^ 56) := by
          gcongr
      _ = Kc * Λ ^ 72 := by rw [hKc]; ring
  have hkappa0 : 0 ≤ sffKappa Cs Λ := sffKappa_nonneg hCs0.le hΛ0.le
  refine ⟨?_, fun hsmall => ?_⟩
  · -- the cube error
    have hB : cubeB₁ Cs Λ ≤ 13 * 4 * 400 * Kc * Λ ^ 77 := by
      simp only [cubeB₁]
      calc 13 * (2 * Λ) ^ 2 * (400 * Λ ^ 3 * sffKappa Cs Λ)
          ≤ 13 * (2 * Λ) ^ 2 * (400 * Λ ^ 3 * (Kc * Λ ^ 72)) := by gcongr
        _ = 13 * 4 * 400 * Kc * Λ ^ 77 := by ring
    simp only [cubeErr]
    have h1 : Λ ≤ Λ ^ 77 := by
      calc Λ = Λ ^ 1 := (pow_one Λ).symm
        _ ≤ Λ ^ 77 := hpow 1 77 (by norm_num)
    calc 30 * Λ ^ 3 * (Λ + cubeB₁ Cs Λ) ≤ 30 * Λ ^ 3 * (Λ ^ 77 + 13 * 4 * 400 * Kc * Λ ^ 77) := by
          gcongr
      _ = 30 * (1 + 13 * 4 * 400 * Kc) * Λ ^ 80 := by ring
      _ ≤ C * Λ ^ 80 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [hC]
          have : 0 ≤ 4 * Cs * 160 ^ 12 + 8 * (6 * Cs * 160 ^ 12) + 192 * Cs * Kc :=
            by positivity
          nlinarith [hKc0]
  · have hΛ80 : 1 ≤ Λ ^ 80 := one_le_pow₀ hΛ
    have hερ : 0 ≤ ε + ρ := by linarith
    -- each condition is dominated by the single one
    have hdom : ∀ A : ℝ, 0 ≤ A → A ≤ C → ∀ n : ℕ, n ≤ 80 → ∀ x : ℝ, 0 ≤ x → x ≤ ε + ρ →
        A * Λ ^ n * x ≤ 1 := by
      intro A hA hAC n hn x hx hxe
      have hpn := hpow n 80 hn
      calc A * Λ ^ n * x ≤ C * Λ ^ 80 * (ε + ρ) := by gcongr
        _ ≤ 1 := hsmall
    have hc1 : 4 * Cs * 160 ^ 12 ≤ C := by
      rw [hC]; have : 0 ≤ 8 * (6 * Cs * 160 ^ 12) + 192 * Cs * Kc + 60 * (1 + 13 * 4 * 400 * Kc) :=
        by positivity
      linarith
    have hc2 : 8 * (6 * Cs * 160 ^ 12) ≤ C := by
      rw [hC]; have : 0 ≤ 4 * Cs * 160 ^ 12 + 192 * Cs * Kc + 60 * (1 + 13 * 4 * 400 * Kc) :=
        by positivity
      linarith
    have hc3 : 192 * Cs * Kc ≤ C := by
      rw [hC]; have : 0 ≤ 4 * Cs * 160 ^ 12 + 8 * (6 * Cs * 160 ^ 12) +
        60 * (1 + 13 * 4 * 400 * Kc) := by positivity
      linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [remezC_four]
      have := hdom (4 * Cs * 160 ^ 12) (by positivity) hc1 12 (by norm_num) ρ hρ (by linarith)
      calc 4 * Cs * (160 ^ 12 * Λ ^ 12) * ρ = 4 * Cs * 160 ^ 12 * Λ ^ 12 * ρ := by ring
        _ ≤ 1 := this
    · rw [discBudget_eq]
      have := hdom (8 * (6 * Cs * 160 ^ 12)) (by positivity) hc2 16 (by norm_num) ρ hρ
        (by linarith)
      calc 8 * (6 * Cs * 160 ^ 12 * Λ ^ 14) * ρ * Λ ^ 2 =
            8 * (6 * Cs * 160 ^ 12) * Λ ^ 16 * ρ := by ring
        _ ≤ 1 := this
    · have := hdom (192 * Cs * Kc) (by positivity) hc3 74 (by norm_num) (ε + ρ) hερ le_rfl
      calc 192 * Cs * sffKappa Cs Λ * (ε + ρ) * Λ ^ 2 ≤
            192 * Cs * (Kc * Λ ^ 72) * (ε + ρ) * Λ ^ 2 := by gcongr
        _ = 192 * Cs * Kc * Λ ^ 74 * (ε + ρ) := by ring
        _ ≤ 1 := this

end

end Submission.Lib.K4ContactAffine.Adapter
