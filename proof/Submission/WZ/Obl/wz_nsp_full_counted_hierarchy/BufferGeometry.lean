-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.BufferGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Geometry
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Mass

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_tower_convex_count_composition (Counts)

/-- Enlarge a used cover tube to any prescribed radius while retaining the
common-descendant containment estimate. -/
theorem enlarged_common_descendant {δ r s R : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    {x v y w z u : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hsmall : Tube δ x v ⊆ Tube s y w) (hlarge : Tube δ x v ⊆ Tube r z u) :
    Tube R y w ⊆ Tube (R + r + 4 * s) z u := by
  have hcore := (self_subset_thickening hs (segment ℝ y (y + w))).trans
    (common_descendant_nesting hδ hs hv hw hsmall hlarge)
  apply (thickening_subset_of_subset R hcore).trans
  simpa only [Tube, add_assoc] using thickening_thickening_subset R (r + 4 * s) (segment ℝ z (z + u))

/-- A factor-thirty-two enlargement and a separated scale pair leave the
quarter-radius buffer needed by the copying theorem. -/
theorem buffered_common_descendant {δ r s : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    (hsep : 16 * s ≤ r) {x v y w z u : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hsmall : Tube δ x v ⊆ Tube s y w) (hlarge : Tube δ x v ⊆ Tube r z u) :
    Tube (32 * s) y w ⊆ Tube ((32 * r) / 4) z u := by
  apply (enlarged_common_descendant (R := 32 * s) hδ hs hv hw hsmall hlarge).trans
  apply thickening_mono
  linarith

/-- Passing to an injectively indexed subfamily only decreases convex counts. -/
theorem counts_injective {r L : ℝ} {n m : ℕ} (x v : Fin n → Space)
    (f : Fin m → Fin n) (hf : Function.Injective f) (hcounts : Counts r L n x v) :
    Counts r L m (x ∘ f) (v ∘ f) := by
  intro W hW
  apply le_trans _ (hcounts W hW)
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Nat.cast_le.mpr
  exact Set.ncard_le_ncard_of_injOn f (by intro i hi; exact hi) hf.injOn

/-- A fixed enlargement of the tube radii costs only its square in the
convex-count constant. -/
theorem counts_enlarged {r L t : ℝ} {n : ℕ} (hr : 0 ≤ r) (ht : 1 ≤ t)
    (x v : Fin n → Space) (hcounts : Counts r L n x v) :
    Counts (t * r) (t ^ 2 * L) n x v := by
  intro W hW
  have hmono : r ≤ t * r := by nlinarith
  have hc : Set.ncard {i | Tube (t * r) (x i) (v i) ⊆ W} ≤
      Set.ncard {i | Tube r (x i) (v i) ⊆ W} := by
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    intro i hi
    exact (thickening_mono hmono _).trans hi
  calc
    ENNReal.ofReal ((Set.ncard {i | Tube (t * r) (x i) (v i) ⊆ W} : ℝ) * (t * r) ^ 2) ≤
        ENNReal.ofReal (t ^ 2 * ((Set.ncard {i | Tube r (x i) (v i) ⊆ W} : ℝ) * r ^ 2)) := by
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ).mpr hc)
        (sq_nonneg (t * r))
      nlinarith only [hh]
    _ = ENNReal.ofReal (t ^ 2) * ENNReal.ofReal
        ((Set.ncard {i | Tube r (x i) (v i) ⊆ W} : ℝ) * r ^ 2) := ENNReal.ofReal_mul (sq_nonneg _)
    _ ≤ ENNReal.ofReal (t ^ 2) * (ENNReal.ofReal L * volume W) := mul_le_mul' le_rfl (hcounts W hW)
    _ = ENNReal.ofReal (t ^ 2 * L) * volume W := by rw [ENNReal.ofReal_mul (sq_nonneg _), mul_assoc]

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
