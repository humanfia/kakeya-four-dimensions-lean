import Submission.Obl.k4_subcritical_chart_projection.CorrectedCaps
import Submission.Obl.k4_subcritical_chart_projection.ScalarCoordinates
import Submission.Obl.k4_horizontal_supercritical_three_projections.ChartScalar

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Submission.Obl.k4_subcritical_chart_projection

open Set MeasureTheory
open Submission.Obl.k4_fixed_budget_quadratic_recovery
open Submission.Obl.k4_horizontal_supercritical_three_projections

/-- The pure corrected scalar cell ceiling on a measurable chart. -/
theorem corrected_pure_cap {α : Type} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) (b : α → Fin 6 → ℝ) (π : Measure ℝ)
    {χ D σ a w d H K : ℝ} {P Q vbin : ℤ} (g : Fin 6 → ℝ)
    (hχ : 0 < χ) (hD : 0 < D) (hD₁ : D ≤ 1) (hσ : 0 < σ) (hσ₁ : σ ≤ 1)
    (ha : 0 < a) (hw : 0 < w) (hH : 1 ≤ H) (hK : 0 ≤ K)
    (hχσ : χ ≤ D * σ) (hχσ₂ : χ ≤ D * σ ^ 2)
    (hsmall : 24 * H ^ 2 * χ / D ≤ a * w)
    (hnorm : ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ p ∈ Icc ((P : ℝ) * D) (((P : ℝ) + 1) * D),
      ∀ q ∈ Icc ((Q : ℝ) * D) (((Q : ℝ) + 1) * D), |predictor g t p q| ≤ H)
    (hcap : DirectionCap μ b π K χ χ (a * w) d vbin)
    (hsupp : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (G : Set α) (hsub : G ⊆ chartSet b H χ D χ P Q vbin)
    (hb : ∀ l ∈ G, ∀ e, |b l e| ≤ H) (z : Fin 2 → ℤ) (j : ℤ) :
    μ {p | p.1 ∈ G ∧ scalarCell (scalarCoefficients D a P Q g (b p.1)) p.2 σ = z ∧
      ⌊scalarX (scalarCoefficients D a P Q g (b p.1)) p.2 / w⌋ = j} ≤
      ENNReal.ofReal (8 * 10 ^ 6 * H ^ 3 * K * σ ^ 2 * D ^ 2 * (a * w) ^ d) *
        π {x | ⌊x / χ⌋ = vbin} := by
  classical
  let E : Set (α × ℝ) := {p | p.1 ∈ G ∧
    scalarCell (scalarCoefficients D a P Q g (b p.1)) p.2 σ = z ∧
      ⌊scalarX (scalarCoefficients D a P Q g (b p.1)) p.2 / w⌋ = j}
  rcases G.eq_empty_or_nonempty with hG | ⟨l₀, hl₀⟩
  · simp only [hG, mem_empty_iff_false, false_and, Set.ofPred_false, measure_empty]
    exact bot_le
  have hpc := (chartSet_bounds hD hχ (hsub hl₀)).2.2.2.2.2.2.1
  have hpa : |2 * ((P : ℝ) * D) - (P : ℝ) * D| ≤ 5 * H := by
    rw [show 2 * ((P : ℝ) * D) - (P : ℝ) * D = (P : ℝ) * D by ring]
    linarith
  apply (measure_le_of_time_support hsupp E).trans
  have hm := corrected_sliced_cell_cap μ b π (z := z) (j := j) g hχ hD hD₁ hσ ha hw hH hK
    hχσ hχσ₂ hσ₁ le_rfl hpa hsmall hnorm hcap
    (E ∩ {p | p.2 ∈ Icc (0 : ℝ) 1}) (fun p hp => ?_)
  · simpa only [mul_one] using hm
  · obtain ⟨⟨hG, hz, hj⟩, ht⟩ := hp
    have hchart := hsub hG
    refine ⟨hchart, ht, ?_, ?_, ?_, hb p.1 hG⟩
    · simpa only [scalarCoefficients_cell] using hz
    · simpa only [scalarCoefficients_x] using hj
    · simpa only [mul_one] using (chartSet_bounds hD hχ hchart).2.2.2.2.1

/-- A bin for the corrected scalar slope pins the first physical intercept
and therefore gains its full relative interval length. -/
theorem corrected_angular_cap {α : Type} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) (b : α → Fin 6 → ℝ) (π : Measure ℝ)
    {χ D σ a w d H K β : ℝ} {P Q vbin : ℤ} (g : Fin 6 → ℝ)
    (hχ : 0 < χ) (hD : 0 < D) (hD₁ : D ≤ 1) (hσ : 0 < σ)
    (ha : 0 < a) (hw : 0 < w) (hH : 1 ≤ H) (hK : 0 ≤ K)
    (hχσ : χ ≤ D * σ) (hχσ₂ : χ ≤ D * σ ^ 2)
    (hσβ : σ ≤ β) (hβ₁ : β ≤ 1)
    (hsmall : 24 * H ^ 2 * χ / D ≤ a * w)
    (hnorm : ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ p ∈ Icc ((P : ℝ) * D) (((P : ℝ) + 1) * D),
      ∀ q ∈ Icc ((Q : ℝ) * D) (((Q : ℝ) + 1) * D), |predictor g t p q| ≤ H)
    (hcap : DirectionCap μ b π K χ χ (a * w) d vbin)
    (hsupp : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (G : Set α) (hsub : G ⊆ chartSet b H χ D χ P Q vbin)
    (hb : ∀ l ∈ G, ∀ e, |b l e| ≤ H) (z : Fin 2 → ℤ) (j i : ℤ) :
    μ {p | p.1 ∈ G ∧ scalarCell (scalarCoefficients D a P Q g (b p.1)) p.2 σ = z ∧
      ⌊scalarX (scalarCoefficients D a P Q g (b p.1)) p.2 / w⌋ = j ∧
      ⌊scalarCoefficients D a P Q g (b p.1) 1 / β⌋ = i} ≤
      ENNReal.ofReal (8 * 10 ^ 6 * H ^ 3 * K * σ ^ 2 * β * D ^ 2 * (a * w) ^ d) *
        π {x | ⌊x / χ⌋ = vbin} := by
  classical
  let E : Set (α × ℝ) := {p | p.1 ∈ G ∧
    scalarCell (scalarCoefficients D a P Q g (b p.1)) p.2 σ = z ∧
    ⌊scalarX (scalarCoefficients D a P Q g (b p.1)) p.2 / w⌋ = j ∧
    ⌊scalarCoefficients D a P Q g (b p.1) 1 / β⌋ = i}
  rcases E.eq_empty_or_nonempty with hE0 | ⟨p₀, hp₀⟩
  · change μ E ≤ _
    rw [hE0, measure_empty]
    exact bot_le
  have hc₀ := hsub hp₀.1
  have hpc := (chartSet_bounds hD hχ hc₀).2.2.2.2.2.2.1
  have hpa : |2 * ((P : ℝ) * D) - b p₀.1 0| ≤ 5 * H := by
    calc
      _ ≤ 2 * |(P : ℝ) * D| + |b p₀.1 0| := by
        simpa only [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)] using
          abs_sub (2 * ((P : ℝ) * D)) (b p₀.1 0)
      _ ≤ _ := by linarith [hb p₀.1 hp₀.1 0]
  have hβ : 0 < β := hσ.trans_le hσβ
  have hslice (p : α × ℝ) (hp : p ∈ E) : |b p.1 0 - b p₀.1 0| ≤ D * β := by
    have hd := floor_diameter hβ (hp.2.2.2.trans hp₀.2.2.2.symm)
    have hid : scalarCoefficients D a P Q g (b p.1) 1 -
        scalarCoefficients D a P Q g (b p₀.1) 1 = -2 * (b p.1 0 - b p₀.1 0) / D := by
      change -2 * chartP D P (b p.1) - (-2 * chartP D P (b p₀.1)) = _
      unfold chartP
      ring
    rw [hid, abs_div, abs_mul, abs_of_pos hD] at hd
    norm_num at hd
    have hh := (div_le_iff₀ hD).mp hd
    nlinarith [mul_nonneg hD.le hβ.le]
  apply (measure_le_of_time_support hsupp E).trans
  exact corrected_sliced_cell_cap μ b π (z := z) (j := j) g hχ hD hD₁ hσ ha hw hH hK
    hχσ hχσ₂ hσβ hβ₁ hpa hsmall hnorm hcap
    (E ∩ {p | p.2 ∈ Icc (0 : ℝ) 1}) (by
      rintro p ⟨⟨hG, hz, hj, hi⟩, ht⟩
      exact ⟨hsub hG, ht, (scalarCoefficients_cell D a σ P Q g (b p.1) p.2) ▸ hz,
        (scalarCoefficients_x D a P Q g (b p.1) p.2) ▸ hj,
        hslice p ⟨hG, hz, hj, hi⟩, hb p.1 hG⟩)

end Submission.Obl.k4_subcritical_chart_projection
