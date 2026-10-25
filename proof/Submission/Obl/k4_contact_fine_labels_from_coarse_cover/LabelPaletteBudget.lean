-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/LabelPaletteBudget.lean
import Mathlib
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.LabelAdapter
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.CoreBudget

/-!
# The label palette with one polynomial budget

`label_palette_budget` is `label_palette` with the three smallness conditions replaced by the
single condition `C Λ⁸⁰ (ε/(q μ) + 7 K δ / q²) ≤ 1` (which also gives `56 K δ ≤ q²`) and the error bounded by `C Λ⁸⁰ a`, for the
universal constant `C` of `core_budgets` (with `Λ = labelΛ K θ lam`, `μ = labelμ K θ`).
-/

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover

open Submission.Lib.K4QuadraticSheetCore

open MvPolynomial Set MeasureTheory
open Submission.Lib.K4ContactNormalization

noncomputable section

/-- **Label palette with one budget.** There is a universal `C ≥ 1` such that, for every true
label as in `label_palette`, the single smallness condition `C Λ⁸⁰ (ε/(q μ) + 7Kδ/q²) ≤ 1`
gives three original affine entries with error `C Λ⁸⁰ a` on the whole block. -/
theorem label_palette_budget : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (K a q g ε θ δ lam t₀ : ℝ) (c : Fin 5 → ℝ) (F : MvPolynomial (Fin 4) ℝ)
      (SA SB SW : Set (Fin 6 → ℝ)) (E₀ : Set (Fin 3 → ℝ)),
    1 ≤ K → 0 < a → 0 < q → q ≤ 1 → g ≤ K * q → 0 ≤ g → 0 ≤ ε → ε ≤ q → 0 < θ → θ ≤ 1 →
    0 ≤ δ → 0 < lam → lam ≤ 1 → t₀ ∈ Icc (0 : ℝ) 1 → (∀ e, |c e| ≤ K) → F.totalDegree ≤ 2 →
    (∀ b ∈ SA, ∀ t ∈ Icc t₀ (t₀ + q), |b 0 + t * b 3 - c 0 - t * c 1| ≤ K * q ∧
        |b 1 + t * b 4 - c 2 - t * c 3 - c 4 * (b 0 + t * b 3)| ≤ K * q * g ∧
        |b 4 - c 3 - c 4 * b 3| ≤ K * g) →
    SB ⊆ SA → SW ⊆ SB →
    (∀ b ∈ SB, ∀ t ∈ Icc t₀ (t₀ + q), |eval (point b t) F| ≤ K * a ∧
        |eval (point b t) (pderiv 3 F)| ≤ K ∧
        |eval (point b t) (pderiv 3 (pderiv 3 F))| ≤ K / a) →
    (∀ b ∈ SW, |b 4 + b 0| ≤ ε ∧ |b 3| ≤ K) →
    (∀ p ∈ E₀, p 0 ∈ Icc t₀ (t₀ + q)) →
    ENNReal.ofReal (lam * q ^ 4) ≤ volume E₀ →
    (∀ p ∈ E₀, ∃ b₁ ∈ SW, ∃ b₂ ∈ SW, ∃ b₃ ∈ SW,
      ∃ τ₁ ∈ Icc t₀ (t₀ + q), ∃ τ₂ ∈ Icc t₀ (t₀ + q), ∃ τ₃ ∈ Icc t₀ (t₀ + q),
        (∀ i, |basePt b₁ τ₁ i - p i| ≤ δ) ∧ (∀ i, |basePt b₂ τ₂ i - p i| ≤ δ) ∧
        (∀ i, |basePt b₃ τ₃ i - p i| ≤ δ) ∧
        θ ≤ |b₁ 3 - b₂ 3| ∧ θ ≤ |b₁ 3 - b₃ 3| ∧ θ ≤ |b₂ 3 - b₃ 3| ∧
        K⁻¹ ≤ |eval (point b₁ τ₁) (pderiv 3 F)|) →
    C * labelΛ K θ lam ^ 80 * (ε / (q * labelμ K θ) + 7 * K * δ / q ^ 2) ≤ 1 →
    ∃ L : Fin 3 → Fin 4 → ℝ, ∀ b ∈ SB,
      (∃ τ ∈ Icc t₀ (t₀ + q), K⁻¹ ≤ |eval (point b τ) (pderiv 3 F)|) →
      ∃ u : Fin 3, ∀ t ∈ Icc t₀ (t₀ + q),
        |point b t 3 - (L u 0 + L u 1 * t + L u 2 * point b t 1 + L u 3 * point b t 2)| ≤
          C * labelΛ K θ lam ^ 80 * a := by
  obtain ⟨Cs, hCs0, hCs⟩ := exists_coefCtrl
  obtain ⟨C, hC1, hC⟩ := core_budgets Cs hCs0
  refine ⟨8 * C, by linarith, ?_⟩
  intro K a q g ε θ δ lam t₀ c F SA SB SW E₀ hK ha hq hq1 hgq hg0 hε hεq hθ hθ1 hδ hlam hlam1
    ht₀ hc hF hbox hBA hWB hfit hW hE₀ hvol hwit hsmall
  have hK0 : 0 < K := by linarith
  have hΛ1 : 1 ≤ labelΛ K θ lam := by
    rw [labelΛ, le_div_iff₀ (by positivity)]
    have hθ3le : θ ^ 3 ≤ 1 := pow_le_one₀ hθ.le hθ1
    have hlt1 : lam * θ ^ 3 ≤ 1 := mul_le_one₀ hlam1 (by positivity) hθ3le
    have h6 : 1 ≤ K ^ 6 := one_le_pow₀ hK
    nlinarith
  have hμpos : 0 < labelμ K θ := by rw [labelμ]; positivity
  have hε' : 0 ≤ ε / (q * labelμ K θ) := by positivity
  have hρ : 0 ≤ 7 * K * δ / q ^ 2 := by positivity
  obtain ⟨hErr, hcond⟩ := hC (labelΛ K θ lam) (ε / (q * labelμ K θ)) (7 * K * δ / q ^ 2)
    hΛ1 hε' hρ
  have hΛ80 : 1 ≤ labelΛ K θ lam ^ 80 := one_le_pow₀ hΛ1
  have hCΛ : 1 ≤ C * labelΛ K θ lam ^ 80 := by nlinarith
  have hsmall' : C * labelΛ K θ lam ^ 80 * (ε / (q * labelμ K θ) + 7 * K * δ / q ^ 2) ≤ 1 := by
    have h0 : 0 ≤ C * labelΛ K θ lam ^ 80 * (ε / (q * labelμ K θ) + 7 * K * δ / q ^ 2) := by
      positivity
    nlinarith
  obtain ⟨hs1, hs2, hs3⟩ := hcond hsmall'
  have hδq : 56 * K * δ ≤ q ^ 2 := by
    have h1 : 8 * (7 * K * δ / q ^ 2) ≤ 1 := by
      have e : 8 * (7 * K * δ / q ^ 2) ≤
          8 * C * labelΛ K θ lam ^ 80 * (ε / (q * labelμ K θ) + 7 * K * δ / q ^ 2) := by
        have : 7 * K * δ / q ^ 2 ≤ ε / (q * labelμ K θ) + 7 * K * δ / q ^ 2 := by linarith
        calc 8 * (7 * K * δ / q ^ 2) = 8 * 1 * (7 * K * δ / q ^ 2) := by ring
          _ ≤ 8 * (C * labelΛ K θ lam ^ 80) * (ε / (q * labelμ K θ) + 7 * K * δ / q ^ 2) := by
            gcongr
          _ = _ := by ring
      linarith
    have hq2 : 0 < q ^ 2 := by positivity
    rw [mul_div_assoc', div_le_one hq2] at h1
    linarith
  obtain ⟨L, hL⟩ := label_palette K a q g ε θ δ lam t₀ c F SA SB SW E₀ hK ha hq hq1 hgq hg0 hε
    hεq hθ hθ1 hδ hlam hlam1 ht₀ hc hF hbox hBA hWB hfit hW hE₀ hδq hvol hwit Cs hCs hCs0
    hs1 hs2 hs3
  refine ⟨L, fun b hb hev => ?_⟩
  obtain ⟨u, hu⟩ := hL b hb hev
  refine ⟨u, fun t ht => (hu t ht).trans ?_⟩
  have : cubeErr Cs (labelΛ K θ lam) ≤ 8 * C * labelΛ K θ lam ^ 80 := by
    have : 0 ≤ C * labelΛ K θ lam ^ 80 := by positivity
    linarith
  exact mul_le_mul_of_nonneg_right this ha.le

end

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover
