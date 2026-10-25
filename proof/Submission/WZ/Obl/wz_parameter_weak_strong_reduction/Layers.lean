-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_parameter_weak_strong_reduction.Layers.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_parameter_weak_strong_reduction

open MeasureTheory Set
open scoped ENNReal

/-- A finite sequence of thresholds catches every value between its endpoints. -/
theorem exists_band {α : Type*} [LinearOrder α] (t : ℕ → α) (m : α)
    (K : ℕ) (h0 : t 0 ≤ m) (hK : m ≤ t (K + 1)) :
    ∃ j ∈ Finset.range (K + 1), t j ≤ m ∧ m ≤ t (j + 1) := by
  induction K with
  | zero => exact ⟨0, by simp, h0, hK⟩
  | succ K ih =>
    by_cases h : m ≤ t (K + 1)
    · obtain ⟨j, hj, hlow, hupp⟩ := ih h
      exact ⟨j, Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega), hlow, hupp⟩
    · exact ⟨K + 1, by simp, (lt_of_not_ge h).le, hK⟩

/-- Dominate the power integral by finitely many superlevel estimates. -/
theorem integral_le_layers {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ≥0∞) (hf : Measurable f) (t : ℕ → ℝ) (ht : ∀ j, 0 ≤ t j)
    (p : ℝ) (hp : 0 < p) (K : ℕ)
    (hlow : ∀ x, f x = 0 ∨ ENNReal.ofReal (t 0) ≤ f x)
    (hupp : ∀ x, f x ≤ ENNReal.ofReal (t (K + 1))) :
    (∫⁻ x, (f x) ^ p ∂μ) ≤
      ∑ j ∈ Finset.range (K + 1),
        ENNReal.ofReal ((t (j + 1)) ^ p) * μ {x | ENNReal.ofReal (t j) ≤ f x} := by
  classical
  let E : ℕ → Set α := fun j => {x | ENNReal.ofReal (t j) ≤ f x}
  have hE : ∀ j, MeasurableSet (E j) := fun j => measurableSet_le measurable_const hf
  calc
    (∫⁻ x, (f x) ^ p ∂μ) ≤
        ∫⁻ x, ∑ j ∈ Finset.range (K + 1),
          (E j).indicator (fun _ => ENNReal.ofReal ((t (j + 1)) ^ p)) x ∂μ := by
      apply lintegral_mono
      intro x
      rcases hlow x with hx | hx
      · simp [hx, ENNReal.zero_rpow_of_pos hp]
      · obtain ⟨j, hj, hlowj, hu⟩ := exists_band (fun j => ENNReal.ofReal (t j)) (f x) K hx (hupp x)
        calc
          (f x) ^ p ≤ (ENNReal.ofReal (t (j + 1))) ^ p := ENNReal.rpow_le_rpow hu hp.le
          _ = ENNReal.ofReal ((t (j + 1)) ^ p) := ENNReal.ofReal_rpow_of_nonneg (ht _) hp.le
          _ = (E j).indicator (fun _ => ENNReal.ofReal ((t (j + 1)) ^ p)) x := by
            rw [Set.indicator_of_mem (show x ∈ E j from hlowj)]
          _ ≤ _ := Finset.single_le_sum
            (f := fun k => (E k).indicator (fun _ => ENNReal.ofReal ((t (k + 1)) ^ p)) x)
            (fun _ _ => by positivity) hj
    _ = _ := by
      rw [lintegral_finsetSum _ (fun j _ => measurable_const.indicator (hE j))]
      apply Finset.sum_congr rfl
      intro j hj
      rw [lintegral_indicator (hE j), lintegral_const, Measure.restrict_apply_univ]

end WangZahlLot.Obl.wz_parameter_weak_strong_reduction
