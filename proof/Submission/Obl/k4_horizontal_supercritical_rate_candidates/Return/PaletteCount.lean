import Mathlib

/-!
# Counting states with a conditional palette bound

If every state `S j` (non-null, finite) satisfies `m(S j ∩ direction v) ≤ C m(S j) π(bin v)`
for a probability palette `π`, then the number of states is at most `C` times the largest
number of states meeting one direction bin.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The palette bins of width `χ` cover the line once. -/
theorem tsum_bins_eq_one (π : Measure ℝ) [IsProbabilityMeasure π] {χ : ℝ} (hχ : 0 < χ) :
    ∑' v : ℤ, π (Ico ((v : ℝ) * χ) (((v : ℝ) + 1) * χ)) = 1 := by
  rw [← measure_iUnion]
  · have : (⋃ v : ℤ, Ico ((v : ℝ) * χ) (((v : ℝ) + 1) * χ)) = univ := by
      ext w
      simp only [mem_iUnion, mem_Ico, mem_univ, iff_true]
      refine ⟨⌊w / χ⌋, ?_, ?_⟩
      · have := Int.floor_le (w / χ); rwa [le_div_iff₀ hχ] at this
      · have := Int.lt_floor_add_one (w / χ); rwa [div_lt_iff₀ hχ] at this
    rw [this, measure_univ]
  · intro v v' hvv'
    refine Set.disjoint_left.mpr (fun w hw hw' => hvv' ?_)
    have h1 : ⌊w / χ⌋ = v := by
      rw [Int.floor_eq_iff, le_div_iff₀ hχ, div_lt_iff₀ hχ]; exact hw
    have h2 : ⌊w / χ⌋ = v' := by
      rw [Int.floor_eq_iff, le_div_iff₀ hχ, div_lt_iff₀ hχ]; exact hw'
    rw [← h1, ← h2]
  · intro v; exact measurableSet_Ico

/-- A measure splits over direction bins. -/
theorem measure_eq_tsum_dir {X : Type*} [MeasurableSpace X] (m : Measure X) {χ : ℝ}
    (dir : X → ℝ) (hdir : Measurable dir) {S : Set X} (hS : MeasurableSet S) :
    m S = ∑' v : ℤ, m (S ∩ {x | ⌊dir x / χ⌋ = v}) := by
  rw [← measure_iUnion]
  · congr 1
    ext x
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun h => ⟨⌊dir x / χ⌋, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  · intro v v' hvv'
    refine Set.disjoint_left.mpr (fun x hx hx' => hvv' ?_)
    rw [← hx.2, ← hx'.2]
  · intro v
    exact hS.inter ((Int.measurable_floor.comp (hdir.div_const χ)) (measurableSet_singleton v))

/-- Counting states with a conditional palette bound. -/
theorem palette_count {X ι : Type*} [MeasurableSpace X] (m : Measure X) (π : Measure ℝ)
    [IsProbabilityMeasure π] {χ : ℝ} (hχ : 0 < χ) (dir : X → ℝ) (hdir : Measurable dir)
    (J : Finset ι) (S : ι → Set X) (hS : ∀ j ∈ J, MeasurableSet (S j))
    (hnz : ∀ j ∈ J, m (S j) ≠ 0) (hfin : ∀ j ∈ J, m (S j) ≠ ⊤) (C : ℝ≥0∞)
    (hpal : ∀ j ∈ J, ∀ v : ℤ, m (S j ∩ {x | ⌊dir x / χ⌋ = v}) ≤
      C * m (S j) * π (Ico ((v : ℝ) * χ) (((v : ℝ) + 1) * χ)))
    (Nmax : ℕ) (hN : ∀ v : ℤ, (J.filter (fun j => m (S j ∩ {x | ⌊dir x / χ⌋ = v}) ≠ 0)).card ≤ Nmax) :
    (J.card : ℝ≥0∞) ≤ C * Nmax := by
  classical
  set bin : ℤ → ℝ≥0∞ := fun v => π (Ico ((v : ℝ) * χ) (((v : ℝ) + 1) * χ)) with hbin
  set ind : ι → ℤ → ℝ≥0∞ := fun j v =>
    if m (S j ∩ {x | ⌊dir x / χ⌋ = v}) ≠ 0 then bin v else 0 with hind
  have hone : ∀ j ∈ J, 1 ≤ C * ∑' v, ind j v := by
    intro j hj
    have hsplit := measure_eq_tsum_dir m dir hdir (χ := χ) (hS j hj)
    have hle : m (S j) ≤ m (S j) * (C * ∑' v, ind j v) := by
      calc m (S j) = ∑' v : ℤ, m (S j ∩ {x | ⌊dir x / χ⌋ = v}) := hsplit
        _ ≤ ∑' v : ℤ, C * m (S j) * ind j v := by
            refine ENNReal.tsum_le_tsum (fun v => ?_)
            simp only [hind]
            split_ifs with h
            · exact hpal j hj v
            · push Not at h; rw [h]; exact zero_le
        _ = m (S j) * (C * ∑' v, ind j v) := by
            rw [ENNReal.tsum_mul_left]; ring
    have h2 : m (S j) * 1 ≤ m (S j) * (C * ∑' v, ind j v) := by rw [mul_one]; exact hle
    exact (ENNReal.mul_le_mul_iff_right (hnz j hj) (hfin j hj)).mp h2
  calc (J.card : ℝ≥0∞) = ∑ _j ∈ J, (1 : ℝ≥0∞) := by rw [Finset.sum_const, nsmul_one]
    _ ≤ ∑ j ∈ J, C * ∑' v, ind j v := Finset.sum_le_sum hone
    _ = C * ∑' v, ∑ j ∈ J, ind j v := by
        rw [← Finset.mul_sum, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ ≤ C * ∑' v, (Nmax : ℝ≥0∞) * bin v := by
        gcongr with v
        calc ∑ j ∈ J, ind j v
            = ∑ j ∈ J.filter (fun j => m (S j ∩ {x | ⌊dir x / χ⌋ = v}) ≠ 0), bin v := by
              rw [Finset.sum_filter]
          _ = ((J.filter (fun j => m (S j ∩ {x | ⌊dir x / χ⌋ = v}) ≠ 0)).card : ℝ≥0∞) * bin v := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (Nmax : ℝ≥0∞) * bin v := by gcongr; exact_mod_cast hN v
    _ = C * Nmax := by
        rw [ENNReal.tsum_mul_left, tsum_bins_eq_one π hχ, mul_one]

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
