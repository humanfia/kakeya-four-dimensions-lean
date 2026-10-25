-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.RegularDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.DensityCut
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.DensityClasses

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement (Space)

/-- One common measurable support gives comparable original-union densities
at every prescribed scale, while retaining shading-incidence mass. -/
theorem regular_ball_density_shading {k n : ℕ} (r : Fin k → ℝ) (hr : ∀ j, 0 < r j)
    (hr1 : ∀ j, r j ≤ 1) {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 8)
    (U : Set Space) (hUm : MeasurableSet U) (hUball : U ⊆ ball 0 1)
    (Y : Fin n → Set Space) (hYU : ∀ i, Y i ⊆ U)
    (hfin : (∑ i, volume (Y i)) ≠ ⊤)
    (hbudget : ENNReal.ofReal (4096 * k * n * t) ≤ (1 / 2 : ℝ≥0∞) * ∑ i, volume (Y i)) :
    ∃ (lam : Fin k → ℝ) (Z : Set Space), MeasurableSet Z ∧ Z ⊆ U ∧
      (∀ j, t / 2 ≤ lam j ∧ lam j ≤ 4) ∧
      (∀ p ∈ Z, ∀ j,
        ENNReal.ofReal (lam j * (r j) ^ 3) ≤ volume (U ∩ ball p (r j)) ∧
        volume (U ∩ ball p (r j)) ≤ ENNReal.ofReal (2 * lam j * (r j) ^ 3)) ∧
      (1 / 2 : ℝ≥0∞) * (∑ i, volume (Y i)) ≤
        (((Scale.dyExp 8 t + 1) ^ k : ℕ) : ℝ≥0∞) * ∑ i, volume (Y i ∩ Z) := by
  obtain ⟨Z₀, hZ₀m, hZ₀U, hZ₀low, hmass⟩ :=
    finite_density_cut r hr hr1 ht.le U hUm hUball Y hYU
  have hhalf : (1 / 2 : ℝ≥0∞) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Y i ∩ Z₀) := by
    have he : (1 / 2 : ℝ≥0∞) * (∑ i, volume (Y i)) +
        (1 / 2 : ℝ≥0∞) * (∑ i, volume (Y i)) = ∑ i, volume (Y i) := by
      rw [← add_mul, one_div, ENNReal.inv_two_add_inv_two, one_mul]
    have hh : (1 / 2 : ℝ≥0∞) * (∑ i, volume (Y i)) +
        (1 / 2 : ℝ≥0∞) * (∑ i, volume (Y i)) ≤
        (∑ i, volume (Y i ∩ Z₀)) + (1 / 2 : ℝ≥0∞) * (∑ i, volume (Y i)) := by
      calc
        _ = ∑ i, volume (Y i) := he
        _ ≤ _ := hmass.trans (add_le_add le_rfl hbudget)
    exact (ENNReal.add_le_add_iff_right (ENNReal.mul_ne_top (by norm_num) hfin)).mp hh
  obtain ⟨lam, Z, hZm, hZZ₀, hlam, hden, hretain⟩ := finite_density_pigeonhole
    (shadingMeasure Y) (fun j => ballDensity U (r j)) (fun j => ballDensity_measurable hUm (r j))
    hZ₀m ht (by norm_num : (0 : ℝ) < 8) ht8
    (fun p hp j => ⟨hZ₀low p hp j, (ballDensity_bounds U p (hr j)).2⟩)
  refine ⟨lam, Z, hZm, hZZ₀.trans hZ₀U, ?_, ?_, ?_⟩
  · simpa only [show (8 : ℝ) / 2 = 4 by norm_num] using hlam
  · intro p hp j
    rw [← ballDensity_mass U p (hr j)]
    exact ⟨ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hden p hp j).1 (pow_pos (hr j) 3).le),
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hden p hp j).2 (pow_pos (hr j) 3).le)⟩
  · rw [shadingMeasure_apply Y hZ₀m, shadingMeasure_apply Y hZm] at hretain
    exact hhalf.trans hretain

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
