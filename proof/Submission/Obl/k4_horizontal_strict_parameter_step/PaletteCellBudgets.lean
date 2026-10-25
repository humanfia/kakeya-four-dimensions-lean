/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/PaletteCellBudgets.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeParameterGeometry
import Submission.Obl.k4_horizontal_strict_parameter_step.AssignmentBudgets
import Submission.Obl.k4_row_cell_regularization.Palette

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_row_cell_regularization

noncomputable section

/-- A separate area bound in every velocity colour sums with the unchanged
palette probabilities, with no cost for the number of velocity cells. -/
theorem palette_cell_budget (π : Measure ℝ) [IsProbabilityMeasure π]
    {χ D C : ℝ} (hχ : 0 < χ) (hC : 0 ≤ C) (S : Finset (Fin 3 → ℤ))
    (hcount : ∀ z : ℤ, ((S.filter (fun q => q 0 = z)).card : ℝ) * D ^ 2 ≤ C) :
    (∑ q ∈ S, D ^ 2 * binWeight π χ (q 0)) ≤ C := by
  classical
  rw [Finset.sum_comp (s := S) (fun z => D ^ 2 * binWeight π χ z) (fun q => q 0)]
  simp only [nsmul_eq_mul]
  calc
    _ ≤ ∑ z ∈ S.image (fun q => q 0), C * binWeight π χ z := by
      apply Finset.sum_le_sum
      intro z hz
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (hcount z) (binWeight_nonneg π χ z)
    _ = C * ∑ z ∈ S.image (fun q => q 0), binWeight π χ z :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left (sum_binWeight_le_one hχ π _) hC
    _ = C := mul_one _

/-- The possible static parameter cells of one true affine entry have a
palette-weighted area bounded by its cubic time scale. Only actual contacts enter. -/
theorem true_parameter_palette_budget (π : Measure ℝ) [IsProbabilityMeasure π]
    (c : Fin 5 → ℝ) {m h g χ K D : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hK : 1 ≤ K) (hm : |m| ≤ 1)
    (hc : |c 4| ≤ K) (hg : g ≤ K * h) (hχ : 0 < χ) (hχh : χ ≤ h ^ 2)
    (hD : 0 < D) (hDh : D ≤ h ^ 2) (S : Finset (Fin 3 → ℤ))
    (hS : ∀ q ∈ S, ∃ b : Fin 6 → ℝ,
      ⌊b 3 / χ⌋ = q 0 ∧ parameterCode D ![b 0, b 1] = Fin.tail q ∧
      |b 4 + b 0| ≤ χ ∧
      |b 0 + m * b 3 - c 0 - m * c 1| ≤ K * h ∧
      |b 1 + m * b 4 - c 2 - m * c 3 - c 4 * (b 0 + m * b 3)| ≤ K * h * g) :
    (∑ q ∈ S, D ^ 2 * binWeight π χ (q 0)) ≤ 128 * K ^ 3 * h ^ 3 := by
  classical
  apply palette_cell_budget π hχ (by positivity) S
  intro z
  let Sz := S.filter (fun q => q 0 = z)
  have hinj : Set.InjOn Fin.tail (↑Sz : Set (Fin 3 → ℤ)) := by
    intro q hq q' hq' he
    have hq0 := (Finset.mem_filter.mp hq).2
    have hq0' := (Finset.mem_filter.mp hq').2
    funext i
    fin_cases i
    · exact hq0.trans hq0'.symm
    · exact congrFun he 0
    · exact congrFun he 1
  have hcount := true_parameter_cell_count c hh hh1 hK hm hc hg hχh hD hDh
    (Sz.image Fin.tail) (by
      intro q hq
      obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨b, hv, hb, hd, hf, hs⟩ := hS q' (Finset.mem_filter.mp hq').1
      have hvz : ⌊b 3 / χ⌋ = z := hv.trans (Finset.mem_filter.mp hq').2
      have hfloor := Int.floor_eq_iff.mp hvz
      rw [le_div_iff₀ hχ, div_lt_iff₀ hχ] at hfloor
      have hvel : |b 3 - (z : ℝ) * χ| ≤ χ := by
        apply abs_le.mpr
        constructor <;> nlinarith [hfloor.1, hfloor.2]
      exact ⟨b, hb, hvel, hd, hf, hs⟩)
  rw [Finset.card_image_iff.mpr hinj] at hcount
  exact hcount

/-- Original cubic prior floors pay for all true-entry/reference-domain
thresholds, after the palette-weighted parameter area estimate. -/
theorem true_reference_domain_budget {n : ℕ} (π : Measure ℝ)
    (S : Fin n → Finset (Fin 3 → ℤ)) {χ D q a d K : ℝ}
    (hq : 0 ≤ q) (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hbudget : (n : ℝ) * q ^ 4 * a ^ d ≤ K ^ 2)
    (harea : ∀ i, (∑ z ∈ S i, D ^ 2 * binWeight π χ (z 0)) ≤ 128 * K ^ 3 * q ^ 3) :
    (∑ i, ∑ z ∈ S i, q * D ^ 2 * a ^ d * binWeight π χ (z 0)) ≤ 128 * K ^ 5 := by
  have hqa : 0 ≤ q * a ^ d := mul_nonneg hq (Real.rpow_nonneg ha _)
  calc
    _ = ∑ i, (q * a ^ d) * ∑ z ∈ S i, D ^ 2 * binWeight π χ (z 0) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ ≤ ∑ _i : Fin n, (q * a ^ d) * (128 * K ^ 3 * q ^ 3) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (harea i) hqa)
    _ = 128 * K ^ 3 * ((n : ℝ) * q ^ 4 * a ^ d) := by simp; ring
    _ ≤ 128 * K ^ 3 * K ^ 2 := mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = _ := by ring

end

end Submission.Obl.k4_horizontal_strict_parameter_step
