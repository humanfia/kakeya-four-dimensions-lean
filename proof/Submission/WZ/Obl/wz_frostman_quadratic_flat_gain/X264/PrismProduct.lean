-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.PrismProduct.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.Cells
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.PrismNeighborhoods
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file PrismProduct.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_nonflat_factored_improvement (gridUnion)

/-- The cell product inequalities for prism packets, with the neighborhood volume
absorbed into an absolute constant. -/
lemma prism_cell_product {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1)
    (ht : 0 ≤ t) {E : Set Space} (hE : MeasurableSet E)
    (S : Finset (Fin 3 → ℤ))
    (hblocks : ∀ z ∈ S, ENNReal.ofReal (t * (27 * a ^ 3)) ≤ volume (E ∩ block a z) ∧
      volume (E ∩ block a z) ≤ ENNReal.ofReal (2 * t * (27 * a ^ 3)))
    {n p : ℕ} (Y : Fin n → Set Space) (hYS : ∀ i, Y i ⊆ gridUnion a S)
    (hYE : ∀ i, Y i ⊆ E) (c e₁ e₂ e₃ : Fin p → Space)
    (he : ∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j]) :
    (∀ j, volume (prism a b (c j) (e₁ j) (e₂ j) (e₃ j) ∩ ⋃ i, Y i) ≤
      ENNReal.ofReal (1458 * t) * volume (prism a b (c j) (e₁ j) (e₂ j) (e₃ j))) ∧
    ENNReal.ofReal t * volume (⋃ j, prism a b (c j) (e₁ j) (e₂ j) (e₃ j) ∩
      thickening a (prism a b (c j) (e₁ j) (e₂ j) (e₃ j) ∩ ⋃ i, Y i)) ≤
        27 * volume E := by
  let P := fun j => prism a b (c j) (e₁ j) (e₂ j) (e₃ j)
  have h := two_level_product ha ht hE S hblocks P (fun j => P j ∩ ⋃ i, Y i)
    (fun _ => inter_subset_right.trans (Set.iUnion_subset hYS))
    (fun _ => inter_subset_right.trans (Set.iUnion_subset hYE))
    (fun _ => inter_subset_left)
  refine ⟨?_, h.2⟩
  intro j
  calc
    _ ≤ ENNReal.ofReal (54 * t) * volume (thickening (2 * a) (P j)) := h.1 j
    _ ≤ ENNReal.ofReal (54 * t) * (27 * volume (P j)) :=
      mul_le_mul' le_rfl (thickening_twice_prism_volume_le ha.le hab hb
        (c j) (e₁ j) (e₂ j) (e₃ j) (he j))
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_ofNat 27, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
