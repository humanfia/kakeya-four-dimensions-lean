-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CubeVolume.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.CubeHeights
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Grid

namespace WangZahlLot.Obl.wz_slab_local_linearity

open Set MeasureTheory

lemma gridCube_eq_gridCell (ρ : ℝ) (k : Fin 3 → ℤ) :
    gridCube ρ k = wz_nonflat_factored_improvement.gridCell ρ k := by
  ext p
  simp only [gridCube, wz_nonflat_factored_improvement.gridCell, mul_comm]

lemma gridCube_measurable (ρ : ℝ) (k : Fin 3 → ℤ) : MeasurableSet (gridCube ρ k) := by
  rw [gridCube_eq_gridCell]
  exact wz_nonflat_factored_improvement.gridCell_measurable ρ k

lemma gridCube_volume {ρ : ℝ} (hρ : 0 ≤ ρ) (k : Fin 3 → ℤ) :
    volume (gridCube ρ k) = ENNReal.ofReal (ρ ^ 3) := by
  rw [gridCube_eq_gridCell]
  exact wz_nonflat_factored_improvement.gridCell_volume hρ k

lemma gridCube_disjoint {ρ : ℝ} (hρ : 0 < ρ) :
    Pairwise (fun k l : Fin 3 → ℤ => Disjoint (gridCube ρ k) (gridCube ρ l)) := by
  simpa only [gridCube_eq_gridCell] using wz_nonflat_factored_improvement.gridCell_disjoint hρ

lemma gridCubes_volume {ρ : ℝ} (hρ : 0 < ρ) (K : Finset (Fin 3 → ℤ)) :
    volume (gridCubes ρ K) = ENNReal.ofReal ((K.card : ℝ) * ρ ^ 3) := by
  rw [gridCubes, measure_biUnion_finset (fun k _ l _ hkl => gridCube_disjoint hρ hkl)
    (fun k _ => gridCube_measurable ρ k)]
  simp only [gridCube_volume hρ.le, Finset.sum_const, nsmul_eq_mul]
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

end WangZahlLot.Obl.wz_slab_local_linearity
