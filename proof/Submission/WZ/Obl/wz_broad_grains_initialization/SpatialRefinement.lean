-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.SpatialRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.SeparatedCubes

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped Classical
open wz_nonflat_factored_improvement (gridCell gridKey gridKeys mem_gridCell_key
  gridKey_mem gridCell_disjoint)

lemma cubeCell_subset_cube {b : ℝ} (hb : 0 < b) (e : Space ≃ₗᵢ[ℝ] Space) (j : Fin 3 → ℤ) :
    cubeCell b e j ⊆ cube (20 * b) (cubeCenter b e j) e := by
  intro p hp
  apply mem_cube_iff.mpr
  intro i
  have hh := mem_cube_iff.mp (cubeCell_subset_core hb e j hp) i
  linarith

/-- Retain one spatial residue class by a common point cut. The enclosing
cubes are disjoint, while all retained points lie in their much smaller cores. -/
theorem spatial_cube_refinement {n : ℕ} {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (e : Space ≃ₗᵢ[ℝ] Space) (Y : Fin n → Set Space) (hY : ∀ i, MeasurableSet (Y i))
    (hball : ∀ i, Y i ⊆ Metric.ball (0 : Space) 1) :
    ∃ F : Finset (Fin 3 → ℤ), F ⊆ gridKeys b ∧
      (∀ j ∈ F, ∀ k ∈ F, cubeColor j = cubeColor k) ∧
      (∑ i, volume (Y i)) ≤ (64000 : ENNReal) *
        ∑ i, volume (Y i ∩ ⋃ j ∈ F, cubeCell b e j) := by
  classical
  let E := Fintype.equivFin CubeColor
  have hcard : Fintype.card CubeColor = 64000 := by simp [CubeColor]
  have hpos : 0 < Fintype.card CubeColor := by rw [hcard]; norm_num
  have hdisj : (gridKeys b : Set (Fin 3 → ℤ)).Pairwise
      (fun j k => Disjoint (cubeCell b e j) (cubeCell b e k)) := by
    intro j _ k _ hne
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact Set.disjoint_left.mp (gridCell_disjoint hb hne) hp hq
  have hcover (i : Fin n) : Y i ⊆ ⋃ j ∈ gridKeys b, cubeCell b e j := by
    intro p hp
    have hep : e p ∈ Metric.ball (0 : Space) 1 := by
      simpa only [Metric.mem_ball, dist_zero_right, e.norm_map] using hball i hp
    exact Set.mem_iUnion₂.mpr ⟨gridKey b (e p), gridKey_mem hb hb1 hep, mem_gridCell_key hb (e p)⟩
  obtain ⟨k, hk⟩ := colored_partition_cut hpos (gridKeys b) (cubeCell b e)
    (fun j => E (cubeColor j)) (fun _ _ => cubeCell_measurable b e _) hdisj Y hY hcover
  refine ⟨(gridKeys b).filter (fun j => E (cubeColor j) = k), Finset.filter_subset _ _, ?_, ?_⟩
  · intro j hj l hl
    exact E.injective ((Finset.mem_filter.mp hj).2.trans (Finset.mem_filter.mp hl).2.symm)
  · simpa only [hcard, Nat.cast_ofNat] using hk

/-- On a separated collection of cubes, a retained point in one enclosing
cube belongs to that cube's own grid core. -/
theorem retained_cube_is_own_cell {n : ℕ} {b : ℝ} (hb : 0 < b)
    (e : Space ≃ₗᵢ[ℝ] Space) (F : Finset (Fin 3 → ℤ)) (Y : Fin n → Set Space)
    (hcolor : ∀ j ∈ F, ∀ k ∈ F, cubeColor j = cubeColor k)
    (hcover : ∀ i, Y i ⊆ ⋃ j ∈ F, cubeCell b e j)
    {j : Fin 3 → ℤ} (hj : j ∈ F) :
    (⋃ i, Y i) ∩ cube (20 * b) (cubeCenter b e j) e ⊆ cubeCell b e j := by
  rintro p ⟨hp, hpU⟩
  obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hp
  obtain ⟨k, hk, hpC⟩ := Set.mem_iUnion₂.mp (hcover i hpi)
  by_cases hkj : k = j
  · simpa only [hkj] using hpC
  · exact False.elim (Set.disjoint_left.mp
      (same_color_cubes_disjoint hb e (hcolor k hk j hj) hkj)
      (cubeCell_subset_cube hb e k hpC) hpU)

end WangZahlLot.Obl.wz_broad_grains_initialization
