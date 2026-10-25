-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.RepresentativeSlabs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.RepresentativeCount
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.SlabComparison
import Submission.WZ.Obl.wz_direction_density_transfer

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives
  (doubled centered_segment centered_doubled_segment SlabBound tube_subset_doubled)

lemma doubled_volume_upper {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (x v : Space) (hv : ‖v‖ = 1) : volume (doubled r x v) ≤ ENNReal.ofReal (256 * r ^ 2) := by
  let z := x - (1 / 2 : ℝ) • v
  have hseg : segment ℝ z (z + 2 • v) ⊆ segment ℝ z (z + (6 : ℝ) • v) := by
    apply (convex_segment z (z + (6 : ℝ) • v)).segment_subset (left_mem_segment ℝ _ _)
    rw [segment_eq_image']
    refine ⟨1 / 3, ⟨by norm_num, by norm_num⟩, ?_⟩
    simp only [add_sub_cancel_left]
    module
  have hsub : doubled r x v ⊆
      WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.Cylinder (2 * r) z v :=
    thickening_subset_of_subset (2 * r) hseg
  have hvol := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.cylinder_scaled_volume_le
    hv z (by norm_num : (0 : ℝ) ≤ 2) hr hr1
  exact (measure_mono hsub).trans (by norm_num at hvol ⊢; exact hvol)

lemma doubled_volume_lower {r : ℝ} (hr : 0 < r) (x v : Space) (hv : ‖v‖ = 1) :
    ENNReal.ofReal (r ^ 2) ≤ volume (doubled r x v) :=
  (WangZahlLot.Obl.wz_direction_density_transfer.tube_volume_lower hr x v hv).trans
    (measure_mono (tube_subset_doubled hr.le x v))

/-- The old doubled cover has a uniform buffer inside the new doubled cover,
about every point of the new unit cover. -/
lemma representative_buffer {s r R b : ℝ} (hs : 0 < s) (hr : 0 < r)
    (hR : 20 * r ≤ R) (hb : |b| ≤ 1 / 8) {x v y w p : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hT : Tube s x v ⊆ doubled r y w)
    (hp : p ∈ Tube R x v) :
    AffineMap.homothety p b '' doubled r y w ⊆ doubled R x v := by
  have hR0 : 0 < R := (mul_pos (by norm_num) hr).trans_le hR
  obtain ⟨t, ht, hpt⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hp
  let c : ℝ := t - 1 / 2
  have hc : |c| ≤ 1 / 2 := abs_le.mpr ⟨by dsimp [c]; linarith [ht.1], by dsimp [c]; linarith [ht.2]⟩
  have hpc : ‖p - (axisMidpoint x v + c • v)‖ < R := by
    convert hpt using 1
    congr 1
    dsimp [axisMidpoint, c]
    module
  have h1b : |1 - b| ≤ 9 / 8 := (abs_sub 1 b).trans (by norm_num; linarith)
  rintro q ⟨z, hz, rfl⟩
  obtain ⟨a, ha, hza⟩ := doubled_cover_representative hs hv hw hT z hz
  have hpar : |(1 - b) * c + b * a| ≤ 1 := by
    calc
      _ ≤ |(1 - b) * c| + |b * a| := abs_add_le _ _
      _ ≤ (9 / 8 : ℝ) * (1 / 2) + (1 / 8 : ℝ) * 2 := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul h1b hc (abs_nonneg _) (by norm_num))
          (mul_le_mul hb ha (abs_nonneg _) (by norm_num))
      _ ≤ 1 := by norm_num
  refine mem_thickening_iff.mpr ⟨axisMidpoint x v + ((1 - b) * c + b * a) • v,
    centered_doubled_segment x v hpar, ?_⟩
  rw [dist_eq_norm]
  have he : AffineMap.homothety p b z -
      (axisMidpoint x v + ((1 - b) * c + b * a) • v) =
      (1 - b) • (p - (axisMidpoint x v + c • v)) +
        b • (z - (axisMidpoint x v + a • v)) := by
    rw [AffineMap.homothety_apply]
    simp only [vsub_eq_sub, vadd_eq_add]
    module
  rw [he]
  calc
    _ ≤ ‖(1 - b) • (p - (axisMidpoint x v + c • v))‖ +
        ‖b • (z - (axisMidpoint x v + a • v))‖ := norm_add_le _ _
    _ ≤ (9 / 8 : ℝ) * R + (1 / 8 : ℝ) * R := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact add_le_add (mul_le_mul h1b hpc.le (norm_nonneg _) (by norm_num))
        (mul_le_mul hb (hza.le.trans hR) (norm_nonneg _) (by norm_num))
    _ < 2 * R := by linarith

lemma representative_volume_ratio {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hR1 : R ≤ 1)
    (x v y w : Space) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    volume (doubled R x v) ≤ ENNReal.ofReal (256 * (R / r) ^ 2) * volume (doubled r y w) := by
  calc
    _ ≤ ENNReal.ofReal (256 * R ^ 2) := doubled_volume_upper hR hR1 x v hv
    _ = ENNReal.ofReal (256 * (R / r) ^ 2) * ENNReal.ofReal (r ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    _ ≤ _ := mul_le_mul' le_rfl (doubled_volume_lower hr y w hw)

/-- Relative slab bounds survive replacement by a representative axis. Enlarging
the child radii is allowed as well, which is needed when old tower levels expand. -/
theorem representative_fibre_slab {s s' r R L : ℝ}
    (hs : 0 < s) (hss : s ≤ s') (hr : 0 < r) (hR : 20 * r ≤ R) (hR1 : R ≤ 1)
    {x₀ v₀ y w : Space} (hv₀ : ‖v₀‖ = 1) (hw : ‖w‖ = 1)
    (hrep : Tube s x₀ v₀ ⊆ doubled r y w)
    {n : ℕ} (P : Fin n → Prop) (x v : Fin n → Space)
    (hT : ∀ i, P i → Tube s (x i) (v i) ⊆ doubled r y w)
    (hmid : ∀ i, P i → axisMidpoint (x i) (v i) ∈ Tube R x₀ v₀)
    (hSb : SlabBound (doubled r y w) L P (fun i => Tube s (x i) (v i))) :
    SlabBound (doubled R x₀ v₀) (262144 * (R / r) ^ 2 * L) P
      (fun i => Tube s' (x i) (v i)) := by
  have hR0 : 0 < R := (mul_pos (by norm_num) hr).trans_le hR
  have hs' : 0 < s' := hs.trans_le hss
  have hh := WangZahlLot.Obl.wz_rescaled_fibre_alternatives.slabBound_of_comparable
    (a := 1 / 8) (B := 256 * (R / r) ^ 2) (C := 1)
    (by norm_num) (by positivity) le_rfl (by norm_num)
    (fun i => axisMidpoint (x i) (v i))
    (U := fun i => Tube s' (x i) (v i)) (V := fun i => Tube s (x i) (v i))
    (D := doubled R x₀ v₀) (E := doubled r y w)
    (fun i _ => self_subset_thickening hs' _ (by
      simpa only [axisMidpoint, zero_smul, add_zero] using
        centered_segment (x i) (v i) (a := 0) (by norm_num))) hT
    (fun i _ p hp => ⟨p, thickening_mono hss (segment ℝ (x i) (x i + v i)) hp,
      by simp⟩)
    (fun i hi => representative_buffer hs hr hR (by norm_num : |(1 / 8 : ℝ)| ≤ 1 / 8)
      hv₀ hw hrep (hmid i hi))
    (fun i hi => representative_buffer hs hr hR (by norm_num : |(-(1 / 8) : ℝ)| ≤ 1 / 8)
      hv₀ hw hrep (hmid i hi))
    (representative_volume_ratio hr hR0.le hR1 x₀ v₀ y w hv₀ hw) hSb
  convert hh using 1 <;> congr 1 <;> ring

end WangZahlLot.Obl.wz_multiscale_finite_tower
