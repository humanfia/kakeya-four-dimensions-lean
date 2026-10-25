-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.GrainFamily.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.SpatialRefinement
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainTransfer
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Indexing

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open wz_clustered_cover_volume_gain (bodyCount)
open wz_regular_transverse_affine_cells (enumerate enumerate_mem enumerate_surj)
open scoped Classical

/-- The geometric data for initialization at coarse scale one. The local
convex coefficient is supplied separately by `initial_local_grain_count`. -/
structure UnitGrainFamily (δ h : ℝ) {n : ℕ} (x v : Fin n → Space)
    (Z : Fin n → Set Space) (c : ℝ) where
  L : ℕ
  center : Fin L → Space
  frame : Fin L → Space ≃ₗᵢ[ℝ] Space
  shading : Fin L → Set Space
  multiplicity : ℝ
  lower_side : δ ≤ c
  upper_side : c ≤ 1
  measurable : ∀ j, MeasurableSet (shading j)
  subset_cube : ∀ j, shading j ⊆ cube c (center j) (frame j)
  cube_in_ball : ∀ j, cube c (center j) (frame j) ⊆ Metric.ball (0 : Space) 1
  disjoint : Pairwise (fun j k => Disjoint (shading j) (shading k))
  cover : (⋃ j, shading j) = ⋃ i, Z i
  mass : ENNReal.ofReal (δ ^ h * L * c ^ 3) ≤ ∑ j, volume (shading j)
  level : ∀ p ∈ ⋃ i, Z i, bodyCount Z p ∈ Set.Icc multiplicity (2 * multiplicity)
  crossing : ∀ i j, (Z i ∩ shading j).Nonempty →
    Z i ∩ cube c (center j) (frame j) ⊆ shading j ∧
    (∀ p ∈ Metric.thickening δ (segment ℝ (x i) (x i + v i)) ∩
      frontier (cube c (center j) (frame j)), |frame j (p - center j) 2| = c / 2) ∧
    ∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
      ∃ p ∈ Metric.thickening δ (segment ℝ (x i) (x i + v i)) ∩
        cube c (center j) (frame j), frame j (p - center j) 2 = t

/-- Dense separated grid cores, with endpoint clearance and one common
multiplicity level, give all of the geometric initialization data. -/
theorem unit_grain_family_of_cells {n : ℕ} {δ b h m : ℝ}
    (hδ : 0 < δ) (hb : 0 < b) (hb1 : 20 * b ≤ 1 / 1000) (hδb : δ ≤ b / 5)
    (x v : Fin n → Space) (Z : Fin n → Set Space) (e : Space ≃ₗᵢ[ℝ] Space)
    (F : Finset (Fin 3 → ℤ)) (hv : ∀ i, ‖v i‖ = 1)
    (hball : ∀ i, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : Space) 1)
    (hZm : ∀ i, MeasurableSet (Z i))
    (hZT : ∀ i, Z i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i)))
    (hdir : ∀ i, (Z i).Nonempty →
      1 / 2 ≤ e (v i) 2 ∧ ∀ j : Fin 3, j ≠ 2 → |e (v i) j| ≤ 1 / 100)
    (hend : ∀ i p, p ∈ Z i →
      100 * (20 * b) ≤ dist p (x i) ∧ 100 * (20 * b) ≤ dist p (x i + v i))
    (hcolor : ∀ j ∈ F, ∀ k ∈ F, cubeColor j = cubeColor k)
    (hcover : ∀ i, Z i ⊆ ⋃ j ∈ F, cubeCell b e j)
    (hdense : ∀ j ∈ F, ENNReal.ofReal (δ ^ h * (20 * b) ^ 3) ≤
      volume ((⋃ i, Z i) ∩ cubeCell b e j))
    (hlevel : ∀ p ∈ ⋃ i, Z i, bodyCount Z p ∈ Set.Icc m (2 * m)) :
    Nonempty (UnitGrainFamily δ h x v Z (20 * b)) := by
  classical
  let z : Fin F.card → Space := fun j => cubeCenter b e (enumerate F j)
  let U : Fin F.card → Set Space := fun j => cube (20 * b) (z j) e
  let H : Fin F.card → Set Space := fun j => (⋃ i, Z i) ∩ U j
  have hc : 0 < 20 * b := by positivity
  have hδc : δ ≤ (20 * b) / 100 := by linarith
  have hcell (j : Fin F.card) : H j ⊆ cubeCell b e (enumerate F j) :=
    retained_cube_is_own_cell hb e F Z hcolor hcover (enumerate_mem F j)
  have hcellmass (j : Fin F.card) : ENNReal.ofReal (δ ^ h * (20 * b) ^ 3) ≤ volume (H j) :=
    (hdense _ (enumerate_mem F j)).trans (measure_mono
      (inter_subset_inter_right _ (cubeCell_subset_cube hb e (enumerate F j))))
  have hcube (j : Fin F.card) : U j ⊆ Metric.ball (0 : Space) 1 := by
    have hne : ((⋃ i, Z i) ∩ cubeCell b e (enumerate F j)).Nonempty := by
      by_contra hn
      have hz : volume ((⋃ i, Z i) ∩ cubeCell b e (enumerate F j)) = 0 := by
        rw [Set.not_nonempty_iff_eq_empty.mp hn, measure_empty]
      have hh := hdense _ (enumerate_mem F j)
      rw [hz] at hh
      exact (not_le_of_gt (ENNReal.ofReal_pos.mpr (by positivity))) hh
    obtain ⟨p, hpZ, hpC⟩ := hne
    obtain ⟨i, hp⟩ := Set.mem_iUnion.mp hpZ
    exact tube_core_cube_subset_ball hc hb1 hδ hδc e (hv i) (hball i) (hZT i hp)
      (cubeCell_subset_core hb e _ hpC) (hend i p hp).1 (hend i p hp).2
  refine ⟨{
    L := F.card, center := z, frame := fun _ => e, shading := H,
    multiplicity := m, lower_side := by linarith, upper_side := by linarith,
    measurable := fun j => (MeasurableSet.iUnion hZm).inter (cube_isClosed _ _ _).measurableSet,
    subset_cube := fun _ => inter_subset_right, cube_in_ball := hcube,
    disjoint := ?_, cover := ?_, mass := ?_, level := hlevel, crossing := ?_ }⟩
  · intro j k hjk
    exact (same_color_cubes_disjoint hb e (hcolor _ (enumerate_mem F j) _ (enumerate_mem F k))
      (fun he => hjk ((enumerate F).injective he))).mono inter_subset_right inter_subset_right
  · apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun _ => inter_subset_left
    · intro p hp
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
      obtain ⟨k, hk, hpC⟩ := Set.mem_iUnion₂.mp (hcover i hi)
      obtain ⟨j, rfl⟩ := enumerate_surj F hk
      exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨i, hi⟩, cubeCell_subset_cube hb e _ hpC⟩
  · calc
      _ = ∑ _j : Fin F.card, ENNReal.ofReal (δ ^ h * (20 * b) ^ 3) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast F.card, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        ring
      _ ≤ _ := Finset.sum_le_sum fun j _ => hcellmass j
  · intro i j hne
    obtain ⟨p, hpZ, hpH⟩ := hne
    have hpC := cubeCell_subset_core hb e _ (hcell j hpH)
    have hdi := hdir i ⟨p, hpZ⟩
    refine ⟨fun q hq => ⟨Set.mem_iUnion.mpr ⟨i, hq.1⟩, hq.2⟩,
      tube_cube_frontier hc hδc e hdi.1 hdi.2 (hZT i hpZ) hpC, ?_⟩
    exact tube_cube_crosses hc hδ hδc e (hv i) hdi.1 hdi.2 (hZT i hpZ) hpC
      (by linarith [(hend i p hpZ).1]) (by linarith [(hend i p hpZ).2])

end WangZahlLot.Obl.wz_broad_grains_initialization
