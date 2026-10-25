/- Adapted within this LOT tree from o190/x0630, commit adb2f45f4ccde121d91c5954051b6c45263cd6de,
Submission/Obl/k4_pair_bin_atlas_assembly/FiniteChoices.lean. Existing provenance comments are retained below. -/
import Mathlib

namespace Submission.Obl.k4_matched_pair_representative_realization.Selection

open MeasureTheory Set
open scoped ENNReal

/-- A source has at most two bin options. Fixing the better option loses at
most a factor of two, including sources with no successful pairs. -/
theorem exists_two_bin_mass_choice {X B : Type*}
    [MeasurableSpace X] [DecidableEq B] (b₀ : B)
    (μ : Measure X) (H : Set X) (bins : Finset B) (hcard : bins.card ≤ 2)
    (G : B → Set X) (hcover : H ⊆ ⋃ b ∈ bins, G b) :
    ∃ b : B, (bins.Nonempty → b ∈ bins) ∧ μ H ≤ 2 * μ (G b) := by
  classical
  by_cases hne : bins.Nonempty
  · obtain ⟨b, hb, hmax⟩ := bins.exists_max_image (fun b => μ (G b)) hne
    refine ⟨b, fun _ => hb, ?_⟩
    calc
      _ ≤ μ (⋃ b ∈ bins, G b) := measure_mono hcover
      _ ≤ ∑ b ∈ bins, μ (G b) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _b ∈ bins, μ (G b) := Finset.sum_le_sum fun b hb => hmax b hb
      _ = (bins.card : ℝ≥0∞) * μ (G b) := by simp
      _ ≤ 2 * μ (G b) := by gcongr; exact_mod_cast hcard
  · refine ⟨b₀, fun hh => (hne hh).elim, ?_⟩
    have hzero : μ H = 0 := by
      apply measure_mono_null hcover
      simp [Finset.not_nonempty_iff_eq_empty.mp hne]
    rw [hzero]
    exact bot_le

/-- The coin is fixed once for each finite source label, before source-time
freezing; no regularity of a pathwise branch choice is required. -/
theorem exists_source_bin_table {X B ι : Type*}
    [MeasurableSpace X] [DecidableEq B] [Fintype ι] (b₀ : B)
    (μ : ι → Measure X) (H : ι → Set X)
    (bins : ι → Finset B) (hcard : ∀ i, (bins i).card ≤ 2)
    (G : ι → B → Set X) (hcover : ∀ i, H i ⊆ ⋃ b ∈ bins i, G i b)
    (w : ι → ℝ≥0∞) :
    ∃ b : ι → B, (∀ i, (bins i).Nonempty → b i ∈ bins i) ∧
      (∑ i, w i * μ i (H i)) ≤ 2 * ∑ i, w i * μ i (G i (b i)) := by
  classical
  choose b hb hm using fun i =>
    exists_two_bin_mass_choice b₀ (μ i) (H i) (bins i) (hcard i) (G i) (hcover i)
  refine ⟨b, hb, ?_⟩
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ w i * (2 * μ i (G i (b i))) := by gcongr; exact hm i
    _ = _ := by ac_rfl

end Submission.Obl.k4_matched_pair_representative_realization.Selection
