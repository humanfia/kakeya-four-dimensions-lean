-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.LocalNormalize.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.CoarseNormalize
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.Incidence

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open WangZahlLot.Obl.wz_extremal_lipschitz_grains (incidence incidence_eq_ncard)
open scoped ENNReal Classical

noncomputable section

/-- Translation to the local ball followed by a uniform dilation. -/
def localMap {r : ℝ} (hr : 0 < r) (c : Space) : Space ≃ᴬ[ℝ] Space :=
  (ContinuousAffineEquiv.constVAdd ℝ Space (-c)).trans
    (uniformMap (by positivity : 0 < (100 * r)⁻¹))

@[simp] theorem localMap_apply {r : ℝ} (hr : 0 < r) (c p : Space) :
    localMap hr c p = (100 * r)⁻¹ • (p - c) := by
  change (100 * r)⁻¹ • (-c + p) = _
  rw [sub_eq_add_neg, add_comm]

theorem localMap_dist {r : ℝ} (hr : 0 < r) (c p q : Space) :
    dist (localMap hr c p) (localMap hr c q) = (100 * r)⁻¹ * dist p q := by
  simp only [localMap_apply, dist_smul₀, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < (100 * r)⁻¹), dist_sub_right]

theorem localMap_volume {r : ℝ} (hr : 0 < r) (c : Space) (W : Set Space) :
    volume (localMap hr c '' W) = ENNReal.ofReal ((100 * r)⁻¹ ^ 3) * volume W := by
  have he : localMap hr c '' W =
      uniformMap (by positivity : 0 < (100 * r)⁻¹) '' ((fun p => -c + p) '' W) := by
    rw [image_image]
    rfl
  rw [he, uniformMap_volume]
  congr 1
  have ht : (fun p => -c + p) '' W = (fun p => c + p) ⁻¹' W := by
    ext p
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa only [add_neg_cancel_left] using hq
    · intro hp
      exact ⟨c + p, hp, by abel⟩
  rw [ht, measure_preimage_add]

theorem localMap_measurableSet {r : ℝ} (hr : 0 < r) (c : Space)
    {W : Set Space} (hW : MeasurableSet W) : MeasurableSet (localMap hr c '' W) :=
  (localMap hr c).toHomeomorph.measurableEmbedding.measurableSet_image.mpr hW

theorem localMap_incidence {r : ℝ} (hr : 0 < r) (c : Space) {n : ℕ}
    (Y : Fin n → Set Space) (p : Space) :
    incidence (fun i => localMap hr c '' Y i) (localMap hr c p) = incidence Y p := by
  rw [incidence_eq_ncard, incidence_eq_ncard]
  have he : {i | localMap hr c p ∈ localMap hr c '' Y i} = {i | p ∈ Y i} := by
    ext i
    constructor
    · rintro ⟨q, hq, hqp⟩
      exact (localMap hr c).injective hqp ▸ hq
    · intro hp
      exact ⟨p, hp, rfl⟩
  rw [he]

/-- A tube meeting a local ball has a unit carrier after normalization. The
carrier covers the entire local part, even if the chosen shading is smaller. -/
theorem local_tube_carrier {δ r : ℝ} (hr : 0 < r) (hδr : δ ≤ r)
    (x v c : Space) (hv : ‖v‖ = 1)
    (hmeet : (Tube δ x v ∩ ball c r).Nonempty) :
    ∃ z : Space, Tube (δ / (100 * r)) z v ⊆ ball 0 1 ∧
      localMap hr c '' (Tube δ x v ∩ ball c r) ⊆ Tube (δ / (100 * r)) z v := by
  obtain ⟨p₀, hp₀, hp₀c⟩ := hmeet
  obtain ⟨q₀, hq₀, hp₀q₀⟩ := mem_thickening_iff.mp hp₀
  have hq₀c : dist q₀ c < 2 * r := by
    have ht := dist_triangle q₀ p₀ c
    rw [dist_comm q₀ p₀] at ht
    have hp₀c' : dist p₀ c < r := hp₀c
    linarith
  let z := localMap hr c q₀ - (1 / 2 : ℝ) • v
  refine ⟨z, ?_, ?_⟩
  · apply wz_affine_robust_cluster_estimate.centered_tube_subset_ball hv
    · rw [localMap_apply, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < (100 * r)⁻¹), ← dist_eq_norm]
      have hh := mul_le_mul_of_nonneg_left hq₀c.le
        (by positivity : 0 ≤ (100 * r)⁻¹)
      have hc : (100 * r)⁻¹ * (2 * r) = (1 / 50 : ℝ) := by field_simp; ring
      linarith
    · exact (div_le_iff₀ (by positivity : 0 < 100 * r)).mpr (by linarith)
  · rintro _ ⟨p, ⟨hp, hpc⟩, rfl⟩
    obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
    have hqc : dist q c < 2 * r := by
      have ht := dist_triangle q p c
      rw [dist_comm q p] at ht
      have hpc' : dist p c < r := hpc
      linarith
    have hqq₀ : dist q q₀ < 4 * r := by
      have ht := dist_triangle q c q₀
      rw [dist_comm c q₀] at ht
      linarith
    apply mem_thickening_iff.mpr
    refine ⟨localMap hr c q, ?_, ?_⟩
    · rw [segment_eq_image'] at hq₀ hq ⊢
      obtain ⟨s₀, hs₀, rfl⟩ := hq₀
      obtain ⟨s, hs, rfl⟩ := hq
      simp only [add_sub_cancel_left] at hqq₀ ⊢
      have he : (x + s • v) - (x + s₀ • v) = (s - s₀) • v := by module
      rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, hv, mul_one] at hqq₀
      have habs : |(100 * r)⁻¹ * (s - s₀)| ≤ 1 / 2 := by
        rw [abs_mul, abs_of_pos (by positivity : 0 < (100 * r)⁻¹)]
        have hh := mul_le_mul_of_nonneg_left hqq₀.le
          (by positivity : 0 ≤ (100 * r)⁻¹)
        have hc : (100 * r)⁻¹ * (4 * r) = (1 / 25 : ℝ) := by field_simp; ring
        linarith
      refine ⟨1 / 2 + (100 * r)⁻¹ * (s - s₀),
        ⟨by linarith [(abs_le.mp habs).1], by linarith [(abs_le.mp habs).2]⟩, ?_⟩
      dsimp [z]
      simp only [localMap_apply]
      module
    · rw [localMap_dist]
      have hh := mul_lt_mul_of_pos_left hpq (by positivity : 0 < (100 * r)⁻¹)
      simpa only [div_eq_mul_inv, mul_comm] using hh

/-- Empty local shadings cause no exception in the carrier assignment. -/
theorem local_shading_carrier {δ r : ℝ} (hr : 0 < r) (hδr : δ ≤ r)
    (x v c : Space) (hv : ‖v‖ = 1) (Y : Set Space)
    (hY : Y ⊆ Tube δ x v ∩ ball c r) :
    ∃ z : Space, Tube (δ / (100 * r)) z v ⊆ ball 0 1 ∧
      localMap hr c '' Y ⊆ Tube (δ / (100 * r)) z v ∧
      (Y.Nonempty → localMap hr c '' (Tube δ x v ∩ ball c r) ⊆
        Tube (δ / (100 * r)) z v) := by
  by_cases hne : Y.Nonempty
  · obtain ⟨z, hz, hlocal⟩ := local_tube_carrier hr hδr x v c hv (hne.mono hY)
    exact ⟨z, hz, (image_mono hY).trans hlocal, fun _ => hlocal⟩
  · refine ⟨-(1 / 2 : ℝ) • v, ?_, ?_, fun hh => (hne hh).elim⟩
    · have hcenter := wz_affine_robust_cluster_estimate.centered_tube_subset_ball
        (q := (0 : Space)) hv (by norm_num : ‖(0 : Space)‖ ≤ (1 / 4 : ℝ))
        ((div_le_iff₀ (by positivity : 0 < 100 * r)).mpr (by linarith : δ ≤ 1 / 100 * (100 * r)))
      simpa only [zero_sub, neg_smul, Tube, wz_affine_robust_cluster_estimate.tube] using hcenter
    · rw [not_nonempty_iff_eq_empty.mp hne, image_empty]
      exact empty_subset _

end
end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
