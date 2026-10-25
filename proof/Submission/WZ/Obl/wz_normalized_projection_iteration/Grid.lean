-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_iteration.Grid.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_iteration.Lines
import Submission.WZ.Obl.wz_normalized_projection_iteration.Interior
import Submission.WZ.Obl.wz_balanced_cluster_cover
import Submission.WZ.Obl.wz_separated_cover_refinement

namespace WangZahlLot.Obl.wz_normalized_projection_iteration

open Set Metric MeasureTheory
open scoped ENNReal

/-- Six coordinates specifying a transverse line at a small fixed fraction of the coarse scale. -/
noncomputable def lineCell (r : ℝ) (x v : Space) : (Fin 3 → ℤ) × (Fin 3 → ℤ) :=
  (WangZahlLot.Obl.wz_balanced_cluster_cover.cell (r / 1000) v,
    WangZahlLot.Obl.wz_balanced_cluster_cover.cell (r / 1000) (lineBase x v))

theorem lineCell_close {r : ℝ} (hr : 0 < r) {x v y w : Space}
    (hcell : lineCell r x v = lineCell r y w) :
    ‖v - w‖ ≤ r ∧ ‖lineBase x v - lineBase y w‖ ≤ r := by
  have hv := WangZahlLot.Obl.wz_balanced_cluster_cover.norm_sub_le_of_cell_eq
    (by positivity : 0 < r / 1000) (congrArg Prod.fst hcell)
  have hb := WangZahlLot.Obl.wz_balanced_cluster_cover.norm_sub_le_of_cell_eq
    (by positivity : 0 < r / 1000) (congrArg Prod.snd hcell)
  constructor <;> linarith

def linePalette : ℕ := 2000000003 ^ 6

/-- An injective family of line cells has a bounded number of nearby cells. -/
theorem lineCell_degree {I : Type*} [Fintype I] {r : ℝ} (hr : 0 < r)
    (x v : I → Space) (hinj : Function.Injective fun i => lineCell r (x i) (v i)) (i : I) :
    (Finset.univ.filter fun j => ‖v i - v j‖ ≤ 1000000 * r ∧
      ‖lineBase (x i) (v i) - lineBase (x j) (v j)‖ ≤ 1000000 * r).card < linePalette := by
  classical
  let J : Finset I := Finset.univ.filter fun j => ‖v i - v j‖ ≤ 1000000 * r ∧
      ‖lineBase (x i) (v i) - lineBase (x j) (v j)‖ ≤ 1000000 * r
  let B₁ := WangZahlLot.Obl.wz_balanced_cluster_cover.box (r / 1000) (v i) (1000000 * r)
  let B₂ := WangZahlLot.Obl.wz_balanced_cluster_cover.box (r / 1000) (lineBase (x i) (v i)) (1000000 * r)
  have hsub : J.image (fun j => lineCell r (x j) (v j)) ⊆ B₁ ×ˢ B₂ := by
    intro b hb
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hv, hb⟩ := (Finset.mem_filter.mp hj).2
    apply Finset.mem_product.mpr
    constructor
    · apply WangZahlLot.Obl.wz_balanced_cluster_cover.cell_mem_box (by positivity)
      simpa only [norm_sub_rev] using hv
    · apply WangZahlLot.Obl.wz_balanced_cluster_cover.cell_mem_box (by positivity)
      simpa only [norm_sub_rev] using hb
  have hcard : J.card ≤ B₁.card * B₂.card := by
    rw [← Finset.card_product, ← Finset.card_image_of_injective J hinj]
    exact Finset.card_le_card hsub
  have hratio : 2 * (1000000 * r) / (r / 1000) + 2 = (2000000002 : ℝ) := by
    field_simp
    ring
  have hB₁ : (B₁.card : ℝ) ≤ (2000000002 : ℝ) ^ 3 := by
    simpa only [hratio] using
      WangZahlLot.Obl.wz_balanced_cluster_cover.card_box_le (by positivity : 0 < r / 1000)
        (v i) (by positivity : 0 ≤ 1000000 * r)
  have hB₂ : (B₂.card : ℝ) ≤ (2000000002 : ℝ) ^ 3 := by
    simpa only [hratio] using
      WangZahlLot.Obl.wz_balanced_cluster_cover.card_box_le (by positivity : 0 < r / 1000)
        (lineBase (x i) (v i)) (by positivity : 0 ≤ 1000000 * r)
  have hreal : (J.card : ℝ) < linePalette := by
    calc
      _ ≤ (B₁.card : ℝ) * B₂.card := by exact_mod_cast hcard
      _ ≤ (2000000002 : ℝ) ^ 3 * 2000000002 ^ 3 :=
        mul_le_mul hB₁ hB₂ (Nat.cast_nonneg _) (by positivity)
      _ < (linePalette : ℝ) := by norm_num [linePalette]
  exact_mod_cast hreal

/-- A fixed palette separates coarse tubes without losing more than a fixed fraction of weight. -/
theorem color_line_cells {I : Type*} [Fintype I] {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1 / 100000) (x v : I → Space)
    (hv : ∀ i, ‖v i‖ = 1) (hv2 : ∀ i, (1 / 2 : ℝ) ≤ v i 2)
    (hx : ∀ i, ‖x i‖ ≤ 1) (hxv : ∀ i, ‖x i + v i‖ ≤ 1)
    (hinj : Function.Injective fun i => lineCell r (x i) (v i)) :
    ∃ c : I → Fin linePalette, ∀ i j, i ≠ j → c i = c j →
      volume (Tube r (inwardStart r (x i) (v i)) (v i) ∩
        Tube r (inwardStart r (x j) (v j)) (v j)) ≤
        (1 / 2 : ENNReal) * volume (Tube r (inwardStart r (x i) (v i)) (v i)) := by
  classical
  let R : I → I → Prop := fun i j => ‖v i - v j‖ ≤ 1000000 * r ∧
    ‖lineBase (x i) (v i) - lineBase (x j) (v j)‖ ≤ 1000000 * r
  have hRsymm : ∀ {i j}, R i j → R j i := by
    intro i j hij
    simpa only [R, norm_sub_rev] using hij
  obtain ⟨c, hc⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.color_relation
    (show 0 < linePalette by norm_num [linePalette]) R hRsymm (fun i => by simpa only [R] using lineCell_degree hr x v hinj i)
  refine ⟨c, ?_⟩
  intro i j hij heq
  by_cases hdir : 100000 * r ≤ ‖v i - v j‖
  · apply WangZahlLot.Obl.wz_direction_density_transfer.intersection_le_half hr (hv i) (hv j) hdir
    have hcoord := coordinate_abs_le (v i + v j) 2
    simp only [PiLp.add_apply] at hcoord
    have hpos : 0 ≤ v i 2 + v j 2 := by linarith [hv2 i, hv2 j]
    rw [abs_of_nonneg hpos] at hcoord
    linarith [hv2 i, hv2 j]
  · have hdis : Disjoint (Tube r (inwardStart r (x i) (v i)) (v i))
        (Tube r (inwardStart r (x j) (v j)) (v j)) := by
      apply Set.disjoint_left.mpr
      intro p hpi hpj
      have hpb := inward_tube_subset_ball hr (by linarith) (hx i) (hxv i) (hv i) hpi
      have hp1 : ‖p‖ ≤ 1 := (by simpa using hpb : ‖p‖ < 1).le
      have hb := lineBase_dist_of_inter (hv i) (hv j) (hv2 i) (hv2 j) ⟨hpi, hpj⟩ hp1
      have hshift (k : I) : ‖lineBase (inwardStart r (x k) (v k)) (v k) -
          lineBase (x k) (v k)‖ ≤ 18 * r := by
        have h1 := lineBase_dist_start (x := inwardStart r (x k) (v k))
          (y := x k) (hv k) (hv2 k)
        have h2 := inward_start_dist hr.le (hx k) (hv k)
        rw [dist_eq_norm] at h2
        linarith
      have hbase : ‖lineBase (x i) (v i) - lineBase (x j) (v j)‖ ≤ 1000000 * r := by
        have ht1 := norm_sub_le_norm_sub_add_norm_sub (lineBase (x i) (v i))
          (lineBase (inwardStart r (x i) (v i)) (v i)) (lineBase (x j) (v j))
        have ht2 := norm_sub_le_norm_sub_add_norm_sub
          (lineBase (inwardStart r (x i) (v i)) (v i))
          (lineBase (inwardStart r (x j) (v j)) (v j)) (lineBase (x j) (v j))
        have hs := hshift i
        rw [norm_sub_rev] at hs
        linarith [hshift j]
      have hRij : R i j := ⟨by linarith, hbase⟩
      exact hc i j hij hRij heq
    rw [Set.disjoint_iff_inter_eq_empty.mp hdis, measure_empty]
    exact zero_le

end WangZahlLot.Obl.wz_normalized_projection_iteration
