import Mathlib
import Submission.Obl.k4_scalar_lift_plank.Cells

namespace Submission.Obl.k4_scalar_marked_terminal_support

open MeasureTheory Set
open scoped ENNReal

noncomputable def neighborBins (K : ℝ) (k : ℤ) : Finset ℤ :=
  (Finset.Icc (-⌈10 * K⌉) ⌈10 * K⌉).image (fun i => k + i)

lemma card_neighborBins_le {K : ℝ} (hK : 1 ≤ K) (k : ℤ) :
    ((neighborBins K k).card : ℝ) ≤ 23 * K := by
  have hc := Submission.Obl.k4_scalar_lift_plank.card_ceil_interval_le
    (show 0 ≤ 10 * K by linarith)
  have hi := Finset.card_image_le (s := Finset.Icc (-⌈10 * K⌉) ⌈10 * K⌉)
    (f := fun i => k + i)
  change (((Finset.Icc (-⌈10 * K⌉) ⌈10 * K⌉).image (fun i => k + i)).card : ℝ) ≤ _
  exact (Nat.cast_le (α := ℝ)).mpr hi |>.trans (by linarith)

lemma mem_neighborBins {K : ℝ} {k i : ℤ} (h : |(i : ℝ) - (k : ℝ)| ≤ 10 * K) :
    i ∈ neighborBins K k := by
  have hi : |i - k| ≤ ⌈10 * K⌉ := by
    exact_mod_cast h.trans (Int.le_ceil (10 * K))
  exact Finset.mem_image.mpr ⟨i - k, Finset.mem_Icc.mpr (abs_le.mp hi), by omega⟩

noncomputable def observationTile (K σ : ℝ) (f : (Fin 2 → ℤ) × ℤ) :
    Set ((Fin 2 → ℝ) × ℤ) :=
  Icc ![σ * (f.1 0 : ℝ) - 2 * σ, σ * (f.1 1 : ℝ) - 10 * K * σ]
      ![σ * (f.1 0 : ℝ) + 2 * σ, σ * (f.1 1 : ℝ) + 10 * K * σ] ×ˢ
    (neighborBins K f.2 : Set ℤ)

lemma measurableSet_observationTile (K σ : ℝ) (f : (Fin 2 → ℤ) × ℤ) :
    MeasurableSet (observationTile K σ f) :=
  measurableSet_Icc.prod (Finset.measurableSet _)

lemma mem_observationTile {K σ t y : ℝ} {i : ℤ} {f : (Fin 2 → ℤ) × ℤ}
    (ht : |t - σ * (f.1 0 : ℝ)| ≤ 2 * σ)
    (hy : |y - σ * (f.1 1 : ℝ)| ≤ 10 * K * σ)
    (hi : |(i : ℝ) - (f.2 : ℝ)| ≤ 10 * K) :
    (![t, y], i) ∈ observationTile K σ f := by
  refine ⟨⟨?_, ?_⟩, mem_neighborBins hi⟩
  · intro j
    fin_cases j
    · change σ * (f.1 0 : ℝ) - 2 * σ ≤ t
      linarith [(abs_le.mp ht).1]
    · change σ * (f.1 1 : ℝ) - 10 * K * σ ≤ y
      linarith [(abs_le.mp hy).1]
  · intro j
    fin_cases j
    · change t ≤ σ * (f.1 0 : ℝ) + 2 * σ
      linarith [(abs_le.mp ht).2]
    · change y ≤ σ * (f.1 1 : ℝ) + 10 * K * σ
      linarith [(abs_le.mp hy).2]

lemma reference_observationTile_le {K σ : ℝ} (hK : 1 ≤ K) (hσ : 0 ≤ σ)
    (f : (Fin 2 → ℤ) × ℤ) :
    (volume.prod (Measure.count : Measure ℤ)) (observationTile K σ f) ≤
      ENNReal.ofReal (2000 * K ^ 2 * σ ^ 2) := by
  have hK0 : 0 ≤ K := by linarith
  have hv : volume (Icc
      ![σ * (f.1 0 : ℝ) - 2 * σ, σ * (f.1 1 : ℝ) - 10 * K * σ]
      ![σ * (f.1 0 : ℝ) + 2 * σ, σ * (f.1 1 : ℝ) + 10 * K * σ]) =
      ENNReal.ofReal (80 * K * σ ^ 2) := by
    rw [Real.volume_Icc_pi]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← ENNReal.ofReal_mul (by linarith : 0 ≤
      σ * (f.1 0 : ℝ) + 2 * σ - (σ * (f.1 0 : ℝ) - 2 * σ))]
    congr 1
    ring
  unfold observationTile
  rw [Measure.prod_prod, hv, Measure.count_apply_finset]
  have hc : ((neighborBins K f.2).card : ENNReal) ≤ ENNReal.ofReal (23 * K) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (card_neighborBins_le hK _)
  calc
    _ ≤ ENNReal.ofReal (80 * K * σ ^ 2) * ENNReal.ofReal (23 * K) :=
      by gcongr
    _ = ENNReal.ofReal (1840 * K ^ 2 * σ ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by gcongr <;> norm_num)

noncomputable def observationCover (K σ : ℝ) (F : Finset ((Fin 2 → ℤ) × ℤ)) :
    Set ((Fin 2 → ℝ) × ℤ) :=
  ⋃ f ∈ F, observationTile K σ f

lemma measurableSet_observationCover (K σ : ℝ) (F : Finset ((Fin 2 → ℤ) × ℤ)) :
    MeasurableSet (observationCover K σ F) := by
  classical
  exact F.finite_toSet.measurableSet_biUnion (fun f _ => measurableSet_observationTile K σ f)

lemma mem_observationCover {K σ t y : ℝ} {i : ℤ} {F : Finset ((Fin 2 → ℤ) × ℤ)}
    {f : (Fin 2 → ℤ) × ℤ} (hf : f ∈ F)
    (ht : |t - σ * (f.1 0 : ℝ)| ≤ 2 * σ)
    (hy : |y - σ * (f.1 1 : ℝ)| ≤ 10 * K * σ)
    (hi : |(i : ℝ) - (f.2 : ℝ)| ≤ 10 * K) :
    (![t, y], i) ∈ observationCover K σ F :=
  mem_iUnion.mpr ⟨f, mem_iUnion.mpr ⟨hf, mem_observationTile ht hy hi⟩⟩

lemma reference_observationCover_le {K σ : ℝ} (hK : 1 ≤ K) (hσ : 0 ≤ σ)
    (F : Finset ((Fin 2 → ℤ) × ℤ)) :
    (volume.prod (Measure.count : Measure ℤ)) (observationCover K σ F) ≤
      ENNReal.ofReal (2000 * K ^ 2 * ((F.card : ℝ) * σ ^ 2)) := by
  classical
  calc
    _ ≤ ∑ f ∈ F, (volume.prod (Measure.count : Measure ℤ)) (observationTile K σ f) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _f ∈ F, ENNReal.ofReal (2000 * K ^ 2 * σ ^ 2) := by
      exact Finset.sum_le_sum (fun f _ => reference_observationTile_le hK hσ f)
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      ring

end Submission.Obl.k4_scalar_marked_terminal_support
