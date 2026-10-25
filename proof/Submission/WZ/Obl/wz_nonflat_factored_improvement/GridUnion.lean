-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.GridUnion.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.GridGeometry

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set Metric

noncomputable section

def gridUnion (b : ℝ) (s : Finset (Fin 3 → ℤ)) : Set Space := ⋃ z ∈ s, gridCell b z

theorem gridUnion_measurable (b : ℝ) (s : Finset (Fin 3 → ℤ)) :
    MeasurableSet (gridUnion b s) := by
  exact MeasurableSet.iUnion (fun z => MeasurableSet.iUnion (fun _ => gridCell_measurable b z))

theorem gridUnion_volume {b : ℝ} (hb : 0 < b) (s : Finset (Fin 3 → ℤ)) :
    volume (gridUnion b s) = ENNReal.ofReal (s.card * b ^ 3) := by
  rw [gridUnion, measure_biUnion_finset
    (fun i _ j _ h => gridCell_disjoint hb h) (fun z _ => gridCell_measurable b z)]
  simp only [gridCell_volume hb.le, Finset.sum_const, nsmul_eq_mul]
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

theorem gridUnion_volume_ne_top {b : ℝ} (hb : 0 < b) (s : Finset (Fin 3 → ℤ)) :
    volume (gridUnion b s) ≠ ⊤ := by rw [gridUnion_volume hb]; exact ENNReal.ofReal_ne_top

theorem inter_gridUnion (b : ℝ) (s : Finset (Fin 3 → ℤ)) (Y : Set Space) :
    Y ∩ gridUnion b s = ⋃ z ∈ s, Y ∩ gridCell b z := by
  simp only [gridUnion, inter_iUnion]

theorem measure_inter_gridUnion {b : ℝ} (hb : 0 < b) (s : Finset (Fin 3 → ℤ))
    {Y : Set Space} (hY : MeasurableSet Y) :
    volume (Y ∩ gridUnion b s) = ∑ z ∈ s, volume (Y ∩ gridCell b z) := by
  rw [inter_gridUnion, measure_biUnion_finset]
  · intro i _ j _ h
    exact (gridCell_disjoint hb h).mono inter_subset_right inter_subset_right
  · exact fun z _ => hY.inter (gridCell_measurable b z)

theorem tube_gridUnion_volume {b : ℝ} (hb : 0 < b) (δ : ℝ) (x v : Space)
    (hv : ‖v‖ = 1) (s : Finset (Fin 3 → ℤ)) :
    volume (tube δ x v ∩ gridUnion b s) ≤
      ENNReal.ofReal (16 * δ ^ 2 / b ^ 2) * volume (gridUnion b s) := by
  rw [measure_inter_gridUnion hb s isOpen_thickening.measurableSet,
    gridUnion_volume hb, ← ENNReal.ofReal_mul (by positivity)]
  calc
    _ ≤ ∑ _z ∈ s, ENNReal.ofReal (16 * b * δ ^ 2) :=
      Finset.sum_le_sum fun z _ => tube_gridCell_volume hb δ x v hv z
    _ = ENNReal.ofReal (16 * δ ^ 2 / b ^ 2 * (s.card * b ^ 3)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      field_simp

theorem gridUnion_subset_prism_neighborhood {a b : ℝ} (hb : 0 < b)
    (s : Finset (Fin 3 → ℤ)) (e : AffineIsometryEquiv ℝ Space Space)
    (hs : ∀ z ∈ s, (e '' standardPrism a b ∩ gridCell b z).Nonempty) :
    gridUnion b s ⊆ thickening (2 * b) (e '' standardPrism a b) := by
  exact Set.iUnion₂_subset fun z hz => gridCell_subset_neighborhood hb (hs z hz)

theorem gridUnion_prism_volume {a b : ℝ} (hb : 0 < b) (hab : a ≤ b) (hb1 : b ≤ 1)
    (s : Finset (Fin 3 → ℤ)) (e : AffineIsometryEquiv ℝ Space Space)
    (hs : ∀ z ∈ s, (e '' standardPrism a b ∩ gridCell b z).Nonempty) :
    volume (gridUnion b s) ≤ ENNReal.ofReal (288 * b ^ 2) :=
  (measure_mono (gridUnion_subset_prism_neighborhood hb s e hs)).trans
    (prism_neighborhood_volume hab hb1 e)

theorem gridUnion_product {b : ℝ} (hb : 0 < b) (s : Finset (Fin 3 → ℤ))
    (S : Set Space) (hS : MeasurableSet S) (r : ENNReal)
    (hr : ∀ z ∈ s, r * volume (gridCell b z) ≤ volume (S ∩ gridCell b z)) :
    r * volume (gridUnion b s) ≤ volume S := by
  calc
    _ = ∑ z ∈ s, r * volume (gridCell b z) := by
      rw [gridUnion, measure_biUnion_finset
        (fun i _ j _ h => gridCell_disjoint hb h) (fun z _ => gridCell_measurable b z),
        Finset.mul_sum]
    _ ≤ ∑ z ∈ s, volume (S ∩ gridCell b z) := Finset.sum_le_sum hr
    _ = volume (S ∩ gridUnion b s) := (measure_inter_gridUnion hb s hS).symm
    _ ≤ volume S := measure_mono inter_subset_left

theorem gridCell_volume_ne_top {b : ℝ} (hb : 0 < b) (z : Fin 3 → ℤ) :
    volume (gridCell b z) ≠ ⊤ := by rw [gridCell_volume hb.le]; exact ENNReal.ofReal_ne_top

theorem gridCell_volumeReal {b : ℝ} (hb : 0 < b) (z : Fin 3 → ℤ) :
    volume.real (gridCell b z) = b ^ 3 := by
  rw [measureReal_def, gridCell_volume hb.le, ENNReal.toReal_ofReal (by positivity)]

theorem gridUnion_volumeReal {b : ℝ} (hb : 0 < b) (s : Finset (Fin 3 → ℤ)) :
    volume.real (gridUnion b s) = s.card * b ^ 3 := by
  rw [measureReal_def, gridUnion_volume hb, ENNReal.toReal_ofReal (by positivity)]

theorem volumeReal_inter_gridUnion {b : ℝ} (hb : 0 < b) (s : Finset (Fin 3 → ℤ))
    {Y : Set Space} (hY : MeasurableSet Y) :
    volume.real (Y ∩ gridUnion b s) = ∑ z ∈ s, volume.real (Y ∩ gridCell b z) := by
  rw [inter_gridUnion]
  apply measureReal_biUnion_finset
  · intro i _ j _ h
    exact (gridCell_disjoint hb h).mono inter_subset_right inter_subset_right
  · exact fun z _ => hY.inter (gridCell_measurable b z)
  · intro z _
    exact ne_top_of_le_ne_top (gridCell_volume_ne_top hb z) (measure_mono inter_subset_right)

theorem gridUnion_volumeReal_mono {b : ℝ} (hb : 0 < b) {s t : Finset (Fin 3 → ℤ)}
    (hst : s ⊆ t) : volume.real (gridUnion b s) ≤ volume.real (gridUnion b t) := by
  rw [gridUnion_volumeReal hb, gridUnion_volumeReal hb]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hst)) (by positivity)

theorem tube_gridUnion_volumeReal {b : ℝ} (hb : 0 < b) (δ : ℝ) (x v : Space)
    (hv : ‖v‖ = 1) (s : Finset (Fin 3 → ℤ)) :
    volume.real (tube δ x v ∩ gridUnion b s) ≤
      16 * δ ^ 2 / b ^ 2 * volume.real (gridUnion b s) := by
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (gridUnion_volume_ne_top hb s))
    (tube_gridUnion_volume hb δ x v hv s)
  simpa only [measureReal_def, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 16 * δ ^ 2 / b ^ 2)] using h

end

end WangZahlLot.Obl.wz_nonflat_factored_improvement
