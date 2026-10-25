-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.Cells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Basic

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

/-- Uniform density on disjoint measurable cells transfers volume from a coarse shading. -/
theorem cell_density_transfer {n : ℕ} (C : Fin n → Set Space) {E E' : Set Space}
    {a : ℝ≥0∞} (hC : ∀ i, MeasurableSet (C i))
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j))) (hE : MeasurableSet E)
    (hcover : E' ⊆ ⋃ i, C i) (hdensity : ∀ i, a * volume (C i) ≤ volume (C i ∩ E)) :
    a * volume E' ≤ volume E := by
  have hsum : volume (⋃ i, C i) = ∑ i, volume (C i) := by
    simpa only [Finset.mem_univ, Set.iUnion_true] using
      measure_biUnion_finset (s := Finset.univ) (f := C)
        (fun i _ j _ hij => hdisj hij) (fun i _ => hC i)
  have hsumE : volume (⋃ i, C i ∩ E) = ∑ i, volume (C i ∩ E) := by
    simpa only [Finset.mem_univ, Set.iUnion_true] using
      measure_biUnion_finset (s := Finset.univ) (f := fun i => C i ∩ E)
        (fun i _ j _ hij => (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left)
        (fun i _ => (hC i).inter hE)
  calc
    a * volume E' ≤ a * volume (⋃ i, C i) := mul_le_mul' le_rfl (measure_mono hcover)
    _ = ∑ i, a * volume (C i) := by rw [hsum, Finset.mul_sum]
    _ ≤ ∑ i, volume (C i ∩ E) := Finset.sum_le_sum (fun i _ => hdensity i)
    _ = volume (⋃ i, C i ∩ E) := hsumE.symm
    _ ≤ volume E := measure_mono (Set.iUnion_subset fun _ => Set.inter_subset_right)

/-- Successive density transfers multiply with no loss beyond their stated constants. -/
theorem volume_product (E : ℕ → Set Space) (a : ℕ → ℝ≥0∞) (J : ℕ)
    (hstep : ∀ j, j < J → a j * volume (E j) ≤ volume (E (j + 1))) :
    (∏ j ∈ Finset.range J, a j) * volume (E 0) ≤ volume (E J) := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hprev := ih (fun j hj => hstep j (by omega))
    rw [Finset.prod_range_succ]
    calc
      (∏ j ∈ Finset.range J, a j) * a J * volume (E 0) =
          a J * ((∏ j ∈ Finset.range J, a j) * volume (E 0)) := by ac_rfl
      _ ≤ a J * volume (E J) := mul_le_mul' le_rfl hprev
      _ ≤ volume (E (J + 1)) := hstep J (by omega)

/-- A finite sequence of compatible cell shadings yields the multiscale density product. -/
theorem cell_volume_product (E : ℕ → Set Space) (a : ℕ → ℝ≥0∞) (J : ℕ)
    (N : ℕ → ℕ) (C : ∀ j, Fin (N j) → Set Space)
    (hC : ∀ j, j < J → ∀ i, MeasurableSet (C j i))
    (hdisj : ∀ j, j < J → Pairwise (fun i k => Disjoint (C j i) (C j k)))
    (hE : ∀ j, j < J → MeasurableSet (E (j + 1)))
    (hcover : ∀ j, j < J → E j ⊆ ⋃ i, C j i)
    (hdensity : ∀ j, j < J → ∀ i, a j * volume (C j i) ≤ volume (C j i ∩ E (j + 1))) :
    (∏ j ∈ Finset.range J, a j) * volume (E 0) ≤ volume (E J) := by
  apply volume_product
  intro j hj
  exact cell_density_transfer (C j) (hC j hj) (hdisj j hj) (hE j hj) (hcover j hj) (hdensity j hj)

end WangZahlLot.Obl.wz_multiscale_finite_tower
