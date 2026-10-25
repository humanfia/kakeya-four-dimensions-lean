-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.SeparatedCubes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.CubeGeometry
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Grid
import Submission.WZ.Obl.wz_tower_balanced_refinement.Regularize

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped Classical
open wz_nonflat_factored_improvement (gridCell gridKey gridKeys gridCell_measurable
  mem_gridCell_key gridKey_mem gridCell_disjoint)

/-- Centres of a fine grid, expressed in the selected orthogonal frame. -/
noncomputable def cubeCenter (b : ℝ) (e : Space ≃ₗᵢ[ℝ] Space) (k : Fin 3 → ℤ) : Space :=
  e.symm (WithLp.toLp 2 (fun i => b * ((k i : ℝ) + 1 / 2)))

def cubeCell (b : ℝ) (e : Space ≃ₗᵢ[ℝ] Space) (k : Fin 3 → ℤ) : Set Space :=
  e ⁻¹' gridCell b k

abbrev CubeColor := Fin 3 → Fin 40

def cubeColor (k : Fin 3 → ℤ) : CubeColor := fun i =>
  ⟨(k i % 40).toNat, by
    have := Int.emod_nonneg (k i) (by norm_num : (40 : ℤ) ≠ 0)
    have := Int.emod_lt_of_pos (k i) (by norm_num : (0 : ℤ) < 40)
    omega⟩

lemma cubeCenter_coord (b : ℝ) (e : Space ≃ₗᵢ[ℝ] Space) (k : Fin 3 → ℤ) (i : Fin 3) :
    e (cubeCenter b e k) i = b * ((k i : ℝ) + 1 / 2) := by
  simp [cubeCenter]

lemma cubeCell_measurable (b : ℝ) (e : Space ≃ₗᵢ[ℝ] Space) (k : Fin 3 → ℤ) :
    MeasurableSet (cubeCell b e k) := (gridCell_measurable b k).preimage e.continuous.measurable

lemma cubeCell_subset_core {b : ℝ} (hb : 0 < b) (e : Space ≃ₗᵢ[ℝ] Space) (k : Fin 3 → ℤ) :
    cubeCell b e k ⊆ cube ((20 * b) / 10) (cubeCenter b e k) e := by
  intro p hp
  apply mem_cube_iff.mpr
  intro i
  rw [map_sub, PiLp.sub_apply, cubeCenter_coord]
  have hi := hp i
  apply abs_le.mpr
  constructor <;> linarith

/-- Cubes twenty times wider than their grid cores are disjoint within each
of the forty-by-forty-by-forty residue classes. -/
theorem same_color_cubes_disjoint {b : ℝ} (hb : 0 < b) (e : Space ≃ₗᵢ[ℝ] Space)
    {k l : Fin 3 → ℤ} (hcolor : cubeColor k = cubeColor l) (hne : k ≠ l) :
    Disjoint (cube (20 * b) (cubeCenter b e k) e) (cube (20 * b) (cubeCenter b e l) e) := by
  apply Set.disjoint_left.mpr
  intro p hpk hpl
  apply hne
  funext i
  have hk := mem_cube_iff.mp hpk i
  have hl := mem_cube_iff.mp hpl i
  rw [map_sub, PiLp.sub_apply, cubeCenter_coord] at hk hl
  have hkr := abs_le.mp hk
  have hlr := abs_le.mp hl
  have hlo : -(20 : ℝ) ≤ (k i : ℝ) - (l i : ℝ) := by
    by_contra h
    have hp := mul_pos hb (sub_pos.mpr (lt_of_not_ge h))
    nlinarith
  have hhi : (k i : ℝ) - (l i : ℝ) ≤ 20 := by
    by_contra h
    have hp := mul_pos hb (sub_pos.mpr (lt_of_not_ge h))
    nlinarith
  have hloZ : -(20 : ℤ) ≤ k i - l i := by exact_mod_cast hlo
  have hhiZ : k i - l i ≤ 20 := by exact_mod_cast hhi
  have hh := congrArg Fin.val (congrFun hcolor i)
  dsimp only [cubeColor] at hh
  omega

/-- Finite colouring of a measurable partition retains a fixed share of the
incidence mass by a common point restriction. -/
theorem colored_partition_cut {n K : ℕ} (hK : 0 < K) {ι : Type*} [DecidableEq ι]
    (G : Finset ι) (C : ι → Set Space) (color : ι → Fin K)
    (hCm : ∀ j ∈ G, MeasurableSet (C j))
    (hdisj : (G : Set ι).Pairwise (fun j j' => Disjoint (C j) (C j')))
    (Y : Fin n → Set Space) (hY : ∀ i, MeasurableSet (Y i))
    (hcover : ∀ i, Y i ⊆ ⋃ j ∈ G, C j) :
    ∃ k : Fin K, (∑ i, volume (Y i)) ≤
      (K : ENNReal) * ∑ i, volume (Y i ∩ ⋃ j ∈ G.filter (fun j => color j = k), C j) := by
  classical
  have hsum (F : Finset ι) (hFG : F ⊆ G) :
      (∑ j ∈ F, ∑ i, volume (Y i ∩ C j)) = ∑ i, volume (Y i ∩ ⋃ j ∈ F, C j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [inter_iUnion]
    simp_rw [inter_iUnion]
    symm
    exact measure_biUnion_finset
      (fun j hj j' hj' hne => (hdisj (hFG hj) (hFG hj') hne).mono inter_subset_right inter_subset_right)
      (fun j hj => (hY i).inter (hCm j (hFG hj)))
  obtain ⟨k, hk⟩ := wz_tower_balanced_refinement.weighted_color hK G color
    (fun j => ∑ i, volume (Y i ∩ C j))
  rw [hsum G (fun _ h => h), hsum _ (Finset.filter_subset _ _)] at hk
  refine ⟨k, ?_⟩
  simpa only [inter_eq_left.mpr (hcover _)] using hk

end WangZahlLot.Obl.wz_broad_grains_initialization
