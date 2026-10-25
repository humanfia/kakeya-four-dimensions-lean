-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleStripBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordStripBudgets
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Stages

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Filter

noncomputable section

/-- The actual front strip and grid-error exponents fit the final
display allowance, with no additional numerical premise. -/
theorem sample_strip_exponents
    (tune : Tuning) {κ₁ d₁ precision loss gain L δ₀ : ℝ} {Ep : ℕ}
    (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hloss : 0 < loss) (hgain : 0 < gain) (hL : 0 < L)
    (hδ : δ₀ ≤ (ubOf tune κ₁ d₁ Ep precision loss gain/8)/100) :
    0 < ubOf tune κ₁ d₁ Ep precision loss gain*L ∧
      ubOf tune κ₁ d₁ Ep precision loss gain*L ≤ loss*gain*L/((Ep:ℝ)+1) ∧
      2*δ₀*L ≤ (ubOf tune κ₁ d₁ Ep precision loss gain*L)/4 := by
  have hB : 0 < tune.budget κ₁ d₁ Ep precision loss := tune.budget_pos _ _ _ _ _
  have hB1 : tune.budget κ₁ d₁ Ep precision loss ≤ 1 := tune.budget_le_one _ _ _ _ _
  have hEp : 0 < (Ep:ℝ)+1 := by positivity
  let display := loss*gain*L/((Ep:ℝ)+1)
  have hdisplay : 0 < display := by dsimp only [display]; positivity
  have heq : ubOf tune κ₁ d₁ Ep precision loss gain*L=
      κ₁*tune.budget κ₁ d₁ Ep precision loss*display/4096 := by
    dsimp only [ubOf,display]
    field_simp
  have hub : 0 < ubOf tune κ₁ d₁ Ep precision loss gain*L := by rw [heq]; positivity
  have hκB : κ₁*tune.budget κ₁ d₁ Ep precision loss ≤ 1 :=
    mul_le_one₀ hκ1 hB.le hB1
  refine ⟨hub,?_,?_⟩
  · rw [heq,div_le_iff₀ (by norm_num : (0:ℝ)<4096)]
    have hh := mul_le_mul_of_nonneg_right hκB hdisplay.le
    change κ₁*tune.budget κ₁ d₁ Ep precision loss*display ≤ display*4096
    linarith only [hh,hdisplay]
  · have hh := mul_le_mul_of_nonneg_right hδ hL.le
    nlinarith only [hh,hub]

/-- Both original strip resolutions of P5 at the literal front and
final packet scales. The path exponent is chosen before k and every
actual ancestor; the strip for native preparation remains wider than
the final K/4 state strip. -/
theorem eventually_sample_original_strip_budgets
    (tune : Tuning) (N : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    {κ₁ d₁ precision loss gain L δ₀ : ℝ} {Ep : ℕ}
    (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hloss : 0 < loss) (hgain : 0 < gain) (hL : 0 < L)
    (hδ : δ₀ ≤ (ubOf tune κ₁ d₁ Ep precision loss gain/8)/100) :
    ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ κ : ℝ, 1 ≤ κ → κ ≤ N k^sigma →
        (KOf Ep loss gain (N k) L/4)^(-100:ℝ)*κ*N k^(2*δ₀*L) ≤
          N k^(-(ubOf tune κ₁ d₁ Ep precision loss gain*L)) ∧
        N k^(-(2*(ubOf tune κ₁ d₁ Ep precision loss gain*L)))*κ*N k^(2*δ₀*L) ≤
          N k^(-(ubOf tune κ₁ d₁ Ep precision loss gain*L)) := by
  obtain ⟨hfront,hdisplay,hgeometry⟩ := sample_strip_exponents tune hκ hκ1 hloss hgain hL hδ
  exact eventually_record_original_strip_budgets N hN hfront hdisplay hgeometry

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
