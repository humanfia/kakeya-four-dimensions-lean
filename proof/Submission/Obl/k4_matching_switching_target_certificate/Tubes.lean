-- Adapted from this LOT tree, o040, session x0118, Submission/Obl/k4_matching_refinement_exponent/Tubes.lean.
import Mathlib

/-!
# Volumes of target tubes

A target tube in `ℝ × (Fin m → ℝ)` is the set of `(s, Y)` with `s ∈ S` and every
coordinate `Y j` within `w j` of a measurable center `c j s`. Its volume is at most
`volume S * ∏ j, 2 w j` (Fubini), however fast the centers move with `s`.
-/

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set MeasureTheory

/-- The tube of half-widths `w` around the measurable centers `c` over the times `S`. -/
def tube {m : ℕ} (S : Set ℝ) (c : Fin m → ℝ → ℝ) (w : Fin m → ℝ) :
    Set (ℝ × (Fin m → ℝ)) :=
  {x | x.1 ∈ S ∧ ∀ j, |x.2 j - c j x.1| ≤ w j}

lemma measurableSet_tube {m : ℕ} {S : Set ℝ} {c : Fin m → ℝ → ℝ} (w : Fin m → ℝ)
    (hS : MeasurableSet S) (hc : ∀ j, Measurable (c j)) : MeasurableSet (tube S c w) := by
  have h : tube S c w = (Prod.fst ⁻¹' S) ∩
      ⋂ j, {x : ℝ × (Fin m → ℝ) | |x.2 j - c j x.1| ≤ w j} := by
    ext x; simp [tube]
  rw [h]
  refine (measurable_fst hS).inter (MeasurableSet.iInter fun j => ?_)
  exact measurableSet_le
    (((measurable_pi_apply j).comp measurable_snd).sub ((hc j).comp measurable_fst)).abs
    measurable_const

/-- **Fubini for tubes.** -/
theorem volume_tube_le {m : ℕ} {S : Set ℝ} {c : Fin m → ℝ → ℝ} (w : Fin m → ℝ)
    (hS : MeasurableSet S) (hc : ∀ j, Measurable (c j)) :
    volume (tube S c w) ≤ volume S * ∏ j, ENNReal.ofReal (2 * w j) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_tube w hS hc)]
  calc ∫⁻ s, volume (Prod.mk s ⁻¹' tube S c w)
      ≤ ∫⁻ s, S.indicator (fun _ => ∏ j, ENNReal.ofReal (2 * w j)) s := by
        refine lintegral_mono fun s => ?_
        by_cases hs : s ∈ S
        · rw [indicator_of_mem hs]
          have hsub : Prod.mk s ⁻¹' tube S c w ⊆
              Icc (fun j => c j s - w j) (fun j => c j s + w j) := by
            intro y hy
            have hy' := hy.2
            refine ⟨fun j => ?_, fun j => ?_⟩
            · have := abs_le.mp (hy' j); simp only at this; linarith [this.1]
            · have := abs_le.mp (hy' j); simp only at this; linarith [this.2]
          calc volume (Prod.mk s ⁻¹' tube S c w)
              ≤ volume (Icc (fun j => c j s - w j) (fun j => c j s + w j)) :=
                measure_mono hsub
            _ = ∏ j, ENNReal.ofReal (2 * w j) := by
                rw [Real.volume_Icc_pi]
                congr 1; funext j; congr 1; ring
        · rw [indicator_of_notMem hs]
          have : Prod.mk s ⁻¹' tube S c w = ∅ := by
            ext y; simp [tube, hs]
          rw [this, measure_empty]
    _ = (∏ j, ENNReal.ofReal (2 * w j)) * volume S := lintegral_indicator_const hS _
    _ = volume S * ∏ j, ENNReal.ofReal (2 * w j) := mul_comm _ _

/-- A finite union of tubes with common widths and time sets of volume at most `v`. -/
theorem volume_iUnion_tube_le {m : ℕ} {ι : Type*} (I : Finset ι) {S : ι → Set ℝ}
    {c : ι → Fin m → ℝ → ℝ} (w : Fin m → ℝ) (hS : ∀ i, MeasurableSet (S i))
    (hc : ∀ i j, Measurable (c i j)) {v : ENNReal} (hv : ∀ i ∈ I, volume (S i) ≤ v) :
    volume (⋃ i ∈ I, tube (S i) (c i) w) ≤
      I.card * (v * ∏ j, ENNReal.ofReal (2 * w j)) := by
  calc volume (⋃ i ∈ I, tube (S i) (c i) w)
      ≤ ∑ i ∈ I, volume (tube (S i) (c i) w) := measure_biUnion_finset_le I _
    _ ≤ ∑ i ∈ I, v * ∏ j, ENNReal.ofReal (2 * w j) := by
        refine Finset.sum_le_sum fun i hi => ?_
        exact (volume_tube_le w (hS i) (hc i)).trans (by gcongr; exact hv i hi)
    _ = I.card * (v * ∏ j, ENNReal.ofReal (2 * w j)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

end Submission.Obl.k4_matching_switching_target_certificate
