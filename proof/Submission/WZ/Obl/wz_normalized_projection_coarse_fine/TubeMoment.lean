-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.TubeMoment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.Holder
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.ProjectionMeasure

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

noncomputable section

def graphStrip (δ : ℝ) (f : ℝ → ℝ) (c : ℝ) (q : Space) : Set (ℝ × ℝ) :=
  {p | p.2 ∈ Icc (-1 : ℝ) 1 ∧
    |p.1 - (q 0 + c * p.2 + q 1 * f p.2 + q 2 * p.2 * f p.2)| ≤ δ}

lemma measurableSet_graphStrip {f : ℝ → ℝ} (hf : Continuous f)
    (δ c : ℝ) (q : Space) : MeasurableSet (graphStrip δ f c q) := by
  apply MeasurableSet.inter
  · exact measurable_snd measurableSet_Icc
  · exact (isClosed_le (show Continuous (fun p : ℝ × ℝ =>
        |p.1 - (q 0 + c * p.2 + q 1 * f p.2 + q 2 * p.2 * f p.2)|) by fun_prop)
      continuous_const).measurableSet

lemma projection_tube_subset_strip {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hderiv : ∀ z ∈ Icc (-1 : ℝ) 1, |deriv f z| ≤ 2) (hf0 : |f 0| ≤ 1)
    {δ : ℝ} {x v : Space} (hv : ‖v‖ = 1) (htrans : (1 / 2 : ℝ) ≤ |v 2|)
    (hball : Tube δ x v ⊆ ball 0 1) :
    projection f '' Tube δ x v ⊆ graphStrip (12 * δ) f (slope v 0) (parameters x v) := by
  rintro _ ⟨p, hp, rfl⟩
  have hn : ‖p‖ < 1 := by simpa using hball hp
  have hz : p 2 ∈ Icc (-1 : ℝ) 1 :=
    abs_le.mp ((abs_coordinate_le_norm p 2).trans hn.le)
  refine ⟨hz, ?_⟩
  exact (tube_projection_bound hv htrans hp (normalized_slope_bound hf hderiv hf0 hz)).le

/-- Transfer a finite cinematic moment to a projected-area bound for arbitrary shadings. -/
theorem tube_mass_cubed_le_projection_moment {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hderiv : ∀ z ∈ Icc (-1 : ℝ) 1, |deriv f z| ≤ 2) (hf0 : |f 0| ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (x v : Fin n → Space) (Y : Fin n → Set Space)
    (hv : ∀ i, ‖v i‖ = 1) (htrans : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1)
    (hY : ∀ i, Y i ⊆ Tube δ (x i) (v i)) :
    (∑ i, volume (Y i)) ^ 3 ≤ ENNReal.ofReal (6 * δ) ^ 3 *
      volume (projection f '' (⋃ i, Y i)) *
      (∫⁻ p : ℝ × ℝ, (multiplicity
        (fun i => graphStrip (12 * δ) f (slope (v i) 0) (parameters (x i) (v i))) p)
          ^ (3 / 2 : ℝ)) ^ 2 := by
  have hmass : ∑ i, volume (Y i) ≤
      ENNReal.ofReal (6 * δ) * ∑ i, volume (projection f '' Y i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      volume_le_projection_volume hf.continuous.measurable hδ (hv i) (htrans i) (hY i)
  have hmoment := sum_outer_measure_cubed_le_moment volume
    (fun i => measurableSet_graphStrip hf.continuous (12 * δ) (slope (v i) 0)
      (parameters (x i) (v i)))
    (fun i => (image_mono (hY i)).trans
      (projection_tube_subset_strip hf hderiv hf0 (hv i) (htrans i) (hball i)))
  rw [← image_iUnion] at hmoment
  calc
    _ ≤ (ENNReal.ofReal (6 * δ) * ∑ i, volume (projection f '' Y i)) ^ 3 :=
      pow_le_pow_left' hmass 3
    _ = ENNReal.ofReal (6 * δ) ^ 3 * (∑ i, volume (projection f '' Y i)) ^ 3 := mul_pow _ _ _
    _ ≤ ENNReal.ofReal (6 * δ) ^ 3 * (volume (projection f '' (⋃ i, Y i)) * _) :=
      by gcongr
    _ = _ := (mul_assoc _ _ _).symm

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
