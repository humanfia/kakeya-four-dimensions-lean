/-
Adapted from this LOT tree o203, session x0699, commit 4341160d,
Submission/Obl/k4_horizontal_supercritical_rate_candidates/ChartPartition.lean (namespace
Submission.Obl.k4_horizontal_supercritical_rate_candidates renamed to
Submission.Obl.k4_horizontal_supercritical_three_projections.Parent).
-/
import Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.Charts
import Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.Grid
import Submission.Obl.k4_row_cell_regularization.Palette

namespace Submission.Obl.k4_horizontal_supercritical_three_projections.Parent

open MeasureTheory Set
open Submission.Obl.k4_row_cell_regularization

noncomputable section

def chartLabel (D χ : ℝ) (b : Fin 6 → ℝ) : (ℤ × ℤ) × ℤ :=
  ((⌊b 0 / D⌋, ⌊b 1 / D⌋), ⌊b 3 / χ⌋)

def chartLabels (D χ K : ℝ) : Finset ((ℤ × ℤ) × ℤ) :=
  ((intervalBins D 0 K).product (intervalBins D 0 K)).product (intervalBins χ 0 K)

theorem measurable_chartLabel {α : Type*} [MeasurableSpace α]
    {b : α → Fin 6 → ℝ} (hb : Measurable b) (D χ : ℝ) :
    Measurable (fun l => chartLabel D χ (b l)) := by
  have h₀ : Measurable (fun l => ⌊b l 0 / D⌋) := Int.measurable_floor.comp (by fun_prop)
  have h₁ : Measurable (fun l => ⌊b l 1 / D⌋) := Int.measurable_floor.comp (by fun_prop)
  have h₃ : Measurable (fun l => ⌊b l 3 / χ⌋) := Int.measurable_floor.comp (by fun_prop)
  exact (h₀.prodMk h₁).prodMk h₃

theorem mem_chartLabels {D χ K : ℝ} (hD : 0 < D) (hχ : 0 < χ)
    (b : Fin 6 → ℝ) (h₀ : |b 0| ≤ K) (h₁ : |b 1| ≤ K) (h₃ : |b 3| ≤ K) :
    chartLabel D χ b ∈ chartLabels D χ K := by
  simp only [chartLabel, chartLabels, Finset.product_eq_sprod, Finset.mem_product]
  exact ⟨⟨mem_intervalBins hD (by simpa using h₀),
    mem_intervalBins hD (by simpa using h₁)⟩, mem_intervalBins hχ (by simpa using h₃)⟩

/-- Summing the chart reference numerators costs no inverse power of the
fine velocity mesh: its unchanged palette weights sum to at most one. -/
theorem chart_reference_budget (π : Measure ℝ) [IsProbabilityMeasure π]
    {D χ K : ℝ} (hD : 0 < D) (hD1 : D ≤ 1) (hχ : 0 < χ) (hK : 1 ≤ K)
    (V : Finset ℤ) :
    (∑ c ∈ ((intervalBins D 0 K).product (intervalBins D 0 K)).product V,
      D ^ 2 * binWeight π χ c.2) ≤ 49 * K ^ 2 := by
  let B := intervalBins D 0 K
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hcard : (B.card : ℝ) * D ≤ 7 * K := by
    have h := mul_le_mul_of_nonneg_right (card_intervalBins hD hK₀ 0) hD.le
    have heq : (2 * K / D + 5) * D = 2 * K + 5 * D := by field_simp
    rw [heq] at h
    change (B.card : ℝ) * D ≤ 7 * K
    linarith only [h, hD1, hK]
  have hsq : (B.card : ℝ) ^ 2 * D ^ 2 ≤ 49 * K ^ 2 := by
    calc
      _ = ((B.card : ℝ) * D) ^ 2 := by ring
      _ ≤ (7 * K) ^ 2 := pow_le_pow_left₀ (by positivity) hcard 2
      _ = _ := by ring
  have heq :
      (∑ c ∈ (B.product B).product V, D ^ 2 * binWeight π χ c.2) =
      (B.card : ℝ) ^ 2 * D ^ 2 * ∑ d ∈ V, binWeight π χ d := by
    simp only [Finset.product_eq_sprod, Finset.sum_product]
    rw [← Finset.mul_sum]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [heq]
  have hsum₀ : 0 ≤ ∑ d ∈ V, binWeight π χ d :=
    Finset.sum_nonneg (fun d _ => binWeight_nonneg π χ d)
  simpa only [mul_one] using mul_le_mul hsq (sum_binWeight_le_one hχ π V) hsum₀ (by positivity)

end

end Submission.Obl.k4_horizontal_supercritical_three_projections.Parent
