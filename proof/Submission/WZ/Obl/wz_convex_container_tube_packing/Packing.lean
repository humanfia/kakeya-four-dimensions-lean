-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_convex_container_tube_packing.Packing.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_convex_container_tube_packing.Geometry
import Submission.WZ.Obl.wz_direction_density_transfer.Geometry

namespace WangZahlLot.Obl.wz_convex_container_tube_packing

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

/-- The product of the two endpoint contractions of a tube. -/
def endpointProduct (δ : ℝ) (x v : Space) : Set (Space × Space) :=
  (AffineMap.homothety x (1 / 10 : ℝ) '' Tube δ x v) ×ˢ
    (AffineMap.homothety (x + v) (1 / 10 : ℝ) '' Tube δ x v)

theorem endpointProduct_measurable (δ : ℝ) (x v : Space) :
    MeasurableSet (endpointProduct δ x v) := by
  apply MeasurableSet.prod
  · exact ((AffineMap.homothety_isOpenMap x (1 / 10 : ℝ) (by norm_num))
      _ isOpen_thickening).measurableSet
  · exact ((AffineMap.homothety_isOpenMap (x + v) (1 / 10 : ℝ) (by norm_num))
      _ isOpen_thickening).measurableSet

theorem endpointProduct_subset {δ : ℝ} (hδ : 0 < δ) (x v : Space) :
    endpointProduct δ x v ⊆ Tube δ x v ×ˢ Tube δ x v := by
  apply Set.prod_mono
  · simpa using contract_subset hδ x v (c := 0) (r := 1 / 10)
      (by norm_num) (by norm_num)
  · simpa using contract_subset hδ x v (c := 1) (r := 1 / 10)
      (by norm_num) (by norm_num)

/-- Essential distinctness makes the endpoint products disjoint. -/
theorem endpointProduct_disjoint {δ : ℝ} (hδ : 0 < δ) {x v y w : Space}
    (hfin : volume (Tube δ x v) ≠ ⊤)
    (hover : volume (Tube δ x v ∩ Tube δ y w) ≤ (1 / 2 : ENNReal) * volume (Tube δ x v)) :
    Disjoint (endpointProduct δ x v) (endpointProduct δ y w) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  have hsub := central_contract_subset_inter hδ hz.1 hz'.1 hz.2 hz'.2
  have hvol := (measure_mono hsub).trans hover
  rw [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin] at hvol
  have hpos : volume (Tube δ x v) ≠ 0 := by
    apply ne_of_gt
    exact (measure_ball_pos volume x hδ).trans_le
      (measure_mono (ball_subset_thickening (left_mem_segment ℝ x (x + v)) δ))
  have hcoeff := (ENNReal.mul_le_mul_iff_left hpos hfin).mp hvol
  have hcoeff_real := ENNReal.toReal_mono (by norm_num : (1 / 2 : ENNReal) ≠ ⊤) hcoeff
  norm_num at hcoeff_real

/-- Each endpoint product has volume at least `δ⁴ / 10⁶`. -/
theorem endpointProduct_volume_lower {δ : ℝ} (hδ : 0 < δ) (x v : Space) (hv : ‖v‖ = 1) :
    ENNReal.ofReal (δ ^ 4 / 1000000) ≤
      (volume.prod volume) (endpointProduct δ x v) := by
  have hT := WangZahlLot.Obl.wz_direction_density_transfer.tube_volume_lower hδ x v hv
  rw [endpointProduct, Measure.prod_prod]
  simp only [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin]
  calc
    ENNReal.ofReal (δ ^ 4 / 1000000) =
        (ENNReal.ofReal (|(1 / 10 : ℝ) ^ 3|) * ENNReal.ofReal (δ ^ 2)) *
        (ENNReal.ofReal (|(1 / 10 : ℝ) ^ 3|) * ENNReal.ofReal (δ ^ 2)) := by
      rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      norm_num
      ring
    _ ≤ _ := mul_le_mul' (mul_le_mul' le_rfl hT) (mul_le_mul' le_rfl hT)

/-- A packing estimate in an arbitrary finite-volume container. -/
theorem packing {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (x v : Fin n → Space)
    {W : Set Space} (hWfin : volume W ≠ ⊤)
    (hv : ∀ i, ‖v i‖ = 1) (hTW : ∀ i, Tube δ (x i) (v i) ⊆ W)
    (hover : ∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (Tube δ (x i) (v i))) :
    ENNReal.ofReal ((n : ℝ) * δ ^ 4) ≤ ENNReal.ofReal 1000000 * (volume W) ^ 2 := by
  classical
  have hdisj : Pairwise (fun i j : Fin n =>
      Disjoint (endpointProduct δ (x i) (v i)) (endpointProduct δ (x j) (v j))) := by
    intro i j hij
    exact endpointProduct_disjoint hδ
      (ne_top_of_le_ne_top hWfin (measure_mono (hTW i))) (hover i j hij)
  have hsub : (⋃ i, endpointProduct δ (x i) (v i)) ⊆ W ×ˢ W := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact (Set.prod_mono (hTW i) (hTW i)) (endpointProduct_subset hδ (x i) (v i) hi)
  have hsum : (n : ENNReal) * ENNReal.ofReal (δ ^ 4 / 1000000) ≤ (volume W) ^ 2 := by
    calc
      _ = ∑ i : Fin n, ENNReal.ofReal (δ ^ 4 / 1000000) := by simp
      _ ≤ ∑ i : Fin n, (volume.prod volume) (endpointProduct δ (x i) (v i)) :=
        Finset.sum_le_sum (fun i _ => endpointProduct_volume_lower hδ (x i) (v i) (hv i))
      _ = (volume.prod volume) (⋃ i, endpointProduct δ (x i) (v i)) := by
        rw [measure_iUnion hdisj (fun i => endpointProduct_measurable δ (x i) (v i)),
          tsum_fintype]
      _ ≤ (volume.prod volume) (W ×ˢ W) := measure_mono hsub
      _ = (volume W) ^ 2 := by rw [Measure.prod_prod, pow_two]
  calc
    ENNReal.ofReal ((n : ℝ) * δ ^ 4) =
        ENNReal.ofReal 1000000 * ((n : ENNReal) * ENNReal.ofReal (δ ^ 4 / 1000000)) := by
      rw [← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg n), ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring
    _ ≤ _ := mul_le_mul' le_rfl hsum

end WangZahlLot.Obl.wz_convex_container_tube_packing
