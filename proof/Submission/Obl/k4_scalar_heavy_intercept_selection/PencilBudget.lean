/- Adapted from this LOT tree oai_074_kakeya_four_dimensions, obligation o231,
session x0798, branch x0798, commit fbdba9e7,
Submission/Obl/k4_scalar_capped_heavy_potential/PencilBudget.lean.
Earlier source credits are retained below. -/

import Submission.Obl.k4_scalar_heavy_intercept_selection.BaseCap

namespace Submission.Obl.k4_scalar_heavy_intercept_selection

open MeasureTheory

noncomputable section

/-- The original state palette and original angular bins give the
thin-pencil budget used before intercept pruning. -/
theorem original_palette_pencil_budget {Ω Q : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (μ : Measure Ω) (state : Ω → Q) (hs : Measurable state)
    (v : Ω → ℝ) (hv : Measurable v) (π : Measure ℝ)
    {η H A : ℝ} (hη : 0 < η) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hπ : ∀ j : ℤ, π {x | (⌊x / η⌋ : ℤ) = j} ≤ ENNReal.ofReal A)
    (hcap : ∀ q (j : ℤ), μ {p | state p = q ∧ (⌊v p / η⌋ : ℤ) = j} ≤
      ENNReal.ofReal H * μ (state ⁻¹' {q}) * π {x | (⌊x / η⌋ : ℤ) = j})
    (hsmall : 14000 * H * A ≤ 1) (q : Q) (w : ℝ) :
    μ {p | state p = q ∧ |v p - w| < η} ≤
      ENNReal.ofReal (1 / 2000 : ℝ) * μ (state ⁻¹' {q}) := by
  have ht := state_velocity_pencil_cap μ state hs v hv hη
    (ENNReal.ofReal H) (ENNReal.ofReal A)
    (fun q j => (hcap q j).trans (mul_le_mul' le_rfl (hπ j))) q w
  have hcoeff : (7 : ENNReal) * ENNReal.ofReal H * ENNReal.ofReal A ≤
      ENNReal.ofReal (1 / 2000 : ℝ) := by
    rw [show (7 : ENNReal) = ENNReal.ofReal (7 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 7),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 7 * H)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  exact ht.trans (mul_le_mul' hcoeff le_rfl)

/-- Replacing a velocity map off an original incidence null set
preserves the same uniform statewise pencil budget. -/
theorem state_pencil_budget_of_ae_eq {Ω Q : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (state : Ω → Q) (v v' : Ω → ℝ) (heq : v =ᵐ[μ] v')
    (η : ℝ) (A : ENNReal)
    (hcap : ∀ q w, μ {p | state p = q ∧ |v p - w| < η} ≤ A * μ (state ⁻¹' {q})) :
    ∀ q w, μ {p | state p = q ∧ |v' p - w| < η} ≤ A * μ (state ⁻¹' {q}) := by
  intro q w
  have hm : μ {p | state p = q ∧ |v' p - w| < η} =
      μ {p | state p = q ∧ |v p - w| < η} := by
    apply measure_congr
    filter_upwards [heq] with p hp
    simp only [hp]
  rw [hm]
  exact hcap q w

end
end Submission.Obl.k4_scalar_heavy_intercept_selection
