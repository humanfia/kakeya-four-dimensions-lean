-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.BodyCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyIteration
import Submission.WZ.Obl.wz_transverse_cell_weighted_cover.Assembly

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (AffineCell)
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover
  (netConst net_cover axisDir norm_axisDir cTube cTube_subset_ball
    cell_density asm_norm_lt)

structure RoundBodyCover {n K : ℕ} (G : AffineCell n K) (d : ℝ) where
  count : ℕ
  count_pos : 0 < count
  start : Fin count → Space
  direction : Fin count → Space
  fiber : Fin count → Finset (Fin n)
  shading : Fin count → Set Space
  unit_direction : ∀ j, ‖direction j‖ = 1
  bounded : ∀ j, Tube (4 * G.b) (start j) (direction j) ⊆ ball (0 : Space) 1
  separated : ∀ j k, j ≠ k →
    volume (Tube (4 * G.b) (start j) (direction j) ∩ Tube (4 * G.b) (start k) (direction k)) ≤
      (1 / 2 : ℝ≥0∞) * volume (Tube (4 * G.b) (start j) (direction j))
  measurable : ∀ j, MeasurableSet (shading j)
  shading_tube : ∀ j, shading j ⊆ Tube (4 * G.b) (start j) (direction j)
  shading_cell : ∀ j, shading j ⊆ ⋃ i ∈ G.indices, G.shading i
  density : ∀ j, ENNReal.ofReal (d * (4 * G.b) ^ 2) ≤ volume (shading j)
  fiber_indices : ∀ j, fiber j ⊆ G.indices
  fiber_nonempty : ∀ j, (fiber j).Nonempty
  fiber_disjoint : ∀ j k, j ≠ k → Disjoint (fiber j) (fiber k)
  retained : netConst * (G.indices.card : ℝ) ≤ ∑ j, ((fiber j).card : ℝ)
  whole : ∀ j, ∀ i ∈ fiber j, G.body i ⊆ Tube (4 * G.b) (start j) (direction j)

theorem affine_cell_log {n K : ℕ} (G : AffineCell n K) :
    Real.log (G.b / G.a) ≤ K := by
  have ha : 0 < G.a := by dsimp [AffineCell.a]; positivity
  have hb : 0 < G.b := by dsimp [AffineCell.b]; positivity
  have hb1 : G.b ≤ 1 := by
    dsimp [AffineCell.b]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  calc
    Real.log (G.b / G.a) ≤ Real.log (1 / G.a) :=
      Real.log_le_log (div_pos hb ha) (div_le_div_of_nonneg_right hb1 ha.le)
    _ = (G.first.val : ℝ) * Real.log 2 := by
      rw [one_div, Real.log_inv, AffineCell.a, Real.log_pow, one_div, Real.log_inv]
      ring
    _ ≤ G.first.val := by nlinarith [mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg G.first.val)]
    _ ≤ K := by exact_mod_cast (Nat.lt_succ_iff.mp G.first.isLt)

theorem cover_body_cell : ∃ c : ℝ, 0 < c ∧
    ∀ (n K : ℕ) (U Y : Fin n → Set Space) (B h : ℝ) (G : AffineCell n K),
    0 < h → (K + 1 : ℕ) * h ≤ 1 → BodyCellValid U Y B h G →
    Nonempty (RoundBodyCover G (c * h ^ 9)) := by
  obtain ⟨C, hC, hdense⟩ := cell_density
  refine ⟨C / 16, by positivity, ?_⟩
  intro n K U Y B h G hh hKh H
  have ha : 0 < G.a := by dsimp [AffineCell.a]; positivity
  have hb : 0 < G.b := ha.trans_le H.ordered
  have hb1 : G.b ≤ 1 := H.small.trans (by norm_num)
  have hK1 : (1 : ℝ) ≤ (K + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le K)
  have hh1 : h ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_right hK1 hh.le]
  have hu (i : Fin n) (_ : i ∈ G.indices) : Orthonormal ℝ (G.axes i : Fin 3 → Space) :=
    (G.axes i).orthonormal
  have hcenter (i : Fin n) (hi : i ∈ G.indices) : ‖G.center i‖ < 1 / 100 :=
    asm_norm_lt ha.le hb.le (H.body_small i hi)
  obtain ⟨M, k, F, hM, hk, hFI, hFne, hFdisj, hFmass, hwhole, hsep⟩ :=
    net_cover G.indices H.nonempty ha.le H.ordered hb H.small G.center
      (fun i => (G.axes i : Fin 3 → Space)) hu hcenter
  have hlogpos : 0 < 1 + Real.log (G.b / G.a) := by
    have hlog := Real.log_nonneg ((one_le_div ha).mpr H.ordered)
    linarith
  have hlogh : h * (1 + Real.log (G.b / G.a)) ≤ 1 := by
    have hlog := affine_cell_log G
    push_cast at hKh
    nlinarith [mul_le_mul_of_nonneg_left hlog hh.le]
  have hcompare : (C / 16 * h ^ 9) * (4 * G.b) ^ 2 ≤
      C * h ^ 8 * G.b ^ 2 / (1 + Real.log (G.b / G.a)) := by
    rw [le_div_iff₀ hlogpos]
    calc
      _ = (C * h ^ 8 * G.b ^ 2) * (h * (1 + Real.log (G.b / G.a))) := by ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hlogh
  refine ⟨{
    count := M, count_pos := hM,
    start := fun j => G.center (k j) - (1 / 2 : ℝ) • axisDir (G.axes (k j)),
    direction := fun j => axisDir (G.axes (k j)), fiber := F,
    shading := fun j => cTube G.b (G.center (k j)) (G.axes (k j)) ∩ ⋃ i ∈ G.indices, G.shading i,
    unit_direction := fun j => norm_axisDir (hu _ (hk j)),
    bounded := fun j => cTube_subset_ball hb.le (H.small.trans (by norm_num))
      (hu _ (hk j)) (hcenter _ (hk j)), separated := hsep,
    measurable := fun _ => isOpen_thickening.measurableSet.inter
      (Finset.measurableSet_biUnion _ H.measurable),
    shading_tube := fun _ => inter_subset_left, shading_cell := fun _ => inter_subset_right,
    density := ?_, fiber_indices := hFI, fiber_nonempty := hFne,
    fiber_disjoint := hFdisj, retained := hFmass, whole := hwhole }⟩
  intro j
  apply (ENNReal.ofReal_le_ofReal hcompare).trans
  exact hdense n G.indices G.a G.b h G.center (fun i => (G.axes i : Fin 3 → Space))
    G.shading (k j) ha H.ordered H.small hh hh1 hu H.measurable
    (fun i hi => (H.shading i hi).trans inter_subset_left)
    (fun i hi p hp => H.regular i hi p hp G.b H.ordered hb1) (hk j) (H.density _ (hk j))
    (by
      intro p hp
      obtain ⟨i, hi, j, hj, hpi, hpj, hangle⟩ := H.transverse p hp
      exact ⟨i, j, hi, hj, hpi, hpj, hangle⟩)

end WangZahlLot.Obl.wz_flat_factored_improvement
