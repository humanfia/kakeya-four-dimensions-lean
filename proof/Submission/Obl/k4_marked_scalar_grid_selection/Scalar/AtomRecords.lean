/- Adapted from this LOT tree, obligation o100, session x0340, commit fb1668b,
   Submission/Obl/k4_scalar_marked_profile_selection/AtomRecords.lean. -/
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.AtomDensity
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.RecordSupport
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.Motion
import Submission.Obl.k4_matching_homogeneous_records.Offsets

noncomputable section

namespace Submission.Obl.k4_marked_scalar_grid_selection.Scalar

open MeasureTheory Set
open scoped ENNReal

abbrev atomRecord {H J : ℕ} (σ a q : ℝ) (b : Fin H → Fin 5 → ℝ)
    (j : Fin H) (z : Fin J) : Record J :=
  (z, (⌊y ((j : ℕ), b j) ((z : ℝ) / J) / σ⌋,
    (⌊x ((j : ℕ), b j) ((z : ℝ) / J) / a⌋, ⌊b j 1 / q⌋)))

/-- Every realization of one tag/time cell lies in its deterministic record
support. This statement permits bins finer than the noise in the velocity label. -/
theorem atom_mem_recordSupport {H J : ℕ} (hJ : 0 < J) {σ a ρ q K R : ℝ}
    (hσ : 0 < σ) (hmesh : 1 ≤ (J : ℝ) * σ) (ha : σ ≤ a)
    (hρ : 0 < ρ) (hqσ : σ ≤ q) (hqρ : ρ ≤ q)
    (hK : 0 ≤ K) (hR : 10 * (K + 1) ≤ R)
    (b : Fin H → Fin 5 → ℝ) (hb : ∀ j i, |b j i| ≤ K)
    (j : Fin H) (z : Fin J) (u : Fin 5 → ℝ) (hu : ∀ i, u i ∈ Icc 0 σ)
    (t : ℝ) (ht : t ∈ cell J z) :
    widthObservation a ρ (atomMap b j (u, t)) ∈
      recordSupport σ ρ q R (atomRecord σ a q b j z) := by
  have ha0 : 0 < a := hσ.trans_le ha
  have hq0 : 0 < q := hσ.trans_le hqσ
  have hR0 : 0 ≤ R := by linarith
  obtain ⟨ht01, ht₀, hstep⟩ := cell_time_control hJ hmesh z ht
  have huabs (i : Fin 5) : |u i| ≤ σ := by rw [abs_of_nonneg (hu i).1]; exact (hu i).2
  have hy : |y ((j : ℕ), b j + u) t - y ((j : ℕ), b j) ((z : ℝ) / J)| ≤ R * σ := by
    have h := quadratic_atom_motion (![b j 0, b j 1, 0]) (![u 0, u 1, 0]) hK hσ.le
      (by intro i; fin_cases i <;> simp [hb, hK])
      (by intro i; fin_cases i <;> simp [huabs, hσ.le]) ht01 ht₀ hstep
    have h' : |y ((j : ℕ), b j + u) t - y ((j : ℕ), b j) ((z : ℝ) / J)| ≤
        9 * (K + 1) * σ := by simpa [y, Pi.add_apply] using h
    exact h'.trans (mul_le_mul_of_nonneg_right (by linarith : 9 * (K + 1) ≤ R) hσ.le)
  have hx : |x ((j : ℕ), b j + u) t - x ((j : ℕ), b j) ((z : ℝ) / J)| ≤ R * σ := by
    have h := quadratic_atom_motion (![b j 2, b j 3, b j 4]) (![u 2, u 3, u 4]) hK hσ.le
      (by intro i; fin_cases i <;> simp [hb])
      (by intro i; fin_cases i <;> simp [huabs]) ht01 ht₀ hstep
    have h' : |x ((j : ℕ), b j + u) t - x ((j : ℕ), b j) ((z : ℝ) / J)| ≤
        9 * (K + 1) * σ := by simpa [x, Pi.add_apply] using h
    exact h'.trans (mul_le_mul_of_nonneg_right (by linarith : 9 * (K + 1) ≤ R) hσ.le)
  have hyfloor := Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hσ
    (y ((j : ℕ), b j) ((z : ℝ) / J))
  have hytri := abs_sub_le (y ((j : ℕ), b j + u) t)
    (y ((j : ℕ), b j) ((z : ℝ) / J))
    (σ * (⌊y ((j : ℕ), b j) ((z : ℝ) / J) / σ⌋ : ℝ))
  have hybase : |y ((j : ℕ), b j + u) t -
      σ * (⌊y ((j : ℕ), b j) ((z : ℝ) / J) / σ⌋ : ℝ)| ≤ (R + 1) * σ := by
    linarith
  have hxdiff : |x ((j : ℕ), b j + u) t / a - x ((j : ℕ), b j) ((z : ℝ) / J) / a| ≤ R := by
    rw [← sub_div, abs_div, abs_of_pos ha0]
    apply (div_le_iff₀ ha0).mpr
    exact hx.trans (mul_le_mul_of_nonneg_left ha hR0)
  have hxfloor := Submission.Obl.k4_matching_homogeneous_records.floor_sub_bound
    (x ((j : ℕ), b j + u) t / a) (x ((j : ℕ), b j) ((z : ℝ) / J) / a)
  have hvfloor := Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hρ (b j 1 + u 1)
  have hbv := Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hq0 (b j 1)
  have hvtri := abs_sub_le (ρ * (⌊(b j 1 + u 1) / ρ⌋ : ℝ)) (b j 1 + u 1)
    (q * (⌊b j 1 / q⌋ : ℝ))
  have hbtri := abs_sub_le (b j 1 + u 1) (b j 1) (q * (⌊b j 1 / q⌋ : ℝ))
  rw [abs_sub_comm] at hvfloor
  simp only [add_sub_cancel_left] at hbtri
  have hv : |ρ * (⌊(b j 1 + u 1) / ρ⌋ : ℝ) - q * (⌊b j 1 / q⌋ : ℝ)| ≤ 3 * q := by
    linarith [huabs 1]
  change (t ∈ cell J z ∧ _ ∈ Icc _ _) ∧
    (⌊x ((j : ℕ), b j + u) t / a⌋ ∈ integerWindow 1 _ _) ∧
    (⌊(b j 1 + u 1) / ρ⌋ ∈ integerWindow ρ _ _)
  refine ⟨⟨ht, ?_⟩, ?_, hv⟩
  · change σ * (⌊y ((j : ℕ), b j) ((z : ℝ) / J) / σ⌋ : ℝ) - (R + 1) * σ ≤
        y ((j : ℕ), b j + u) t ∧ y ((j : ℕ), b j + u) t ≤
          σ * (⌊y ((j : ℕ), b j) ((z : ℝ) / J) / σ⌋ : ℝ) + (R + 1) * σ
    obtain ⟨hylo, hyhi⟩ := abs_le.mp hybase
    constructor <;> linarith
  · change |1 * (⌊x ((j : ℕ), b j + u) t / a⌋ : ℝ) -
      (⌊x ((j : ℕ), b j) ((z : ℝ) / J) / a⌋ : ℝ)| ≤ R + 2
    rw [one_mul]
    push_cast at hxfloor
    linarith

/-- The deterministic support inclusion also holds for the noisy atom law. -/
theorem atom_supported_on_record {H J : ℕ} (hJ : 0 < J) {σ a ρ q K R : ℝ}
    (hσ : 0 < σ) (hmesh : 1 ≤ (J : ℝ) * σ) (ha : σ ≤ a)
    (hρ : 0 < ρ) (hqσ : σ ≤ q) (hqρ : ρ ≤ q)
    (hK : 0 ≤ K) (hR : 10 * (K + 1) ≤ R)
    (b : Fin H → Fin 5 → ℝ) (hb : ∀ j i, |b j i| ≤ K)
    (j : Fin H) (z : Fin J) :
    ∀ᵐ p ∂atom σ J b j z, widthObservation a ρ p ∈
      recordSupport σ ρ q R (atomRecord σ a q b j z) := by
  have hS := measurable_recordSupport σ ρ q R (atomRecord σ a q b j z)
  have hmap : Measurable (atomMap b j) := by fun_prop
  have hobs := measurable_widthObservation a ρ
  rw [atom]
  apply (ae_map_iff hmap.aemeasurable (hS.preimage hobs)).mpr
  apply (Measure.ae_prod_iff_ae_ae (hS.preimage (hobs.comp hmap))).mpr
  filter_upwards [noise_support hσ] with u hu
  filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
  exact atom_mem_recordSupport hJ hσ hmesh ha hρ hqσ hqρ hK hR b hb j z u hu t ht

end Submission.Obl.k4_marked_scalar_grid_selection.Scalar
