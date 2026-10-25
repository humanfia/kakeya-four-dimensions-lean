-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_scales_gain.Padding.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.GridUnion
import Submission.WZ.Obl.wz_tower_convex_count_composition.Geometry

namespace WangZahlLot.Obl.wz_separated_scales_gain

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_nonflat_factored_improvement

/-- Cells near a tube give a shading of that tube after a controlled enlargement. -/
noncomputable def paddedShading (b : ℝ) (s : Finset (Fin 3 → ℤ))
    (x v : Space) : Set Space := tube b x v ∩ thickening (4 * b) (gridUnion b s)

theorem paddedShading_measurable (b : ℝ) (s : Finset (Fin 3 → ℤ)) (x v : Space) :
    MeasurableSet (paddedShading b s x v) :=
  isOpen_thickening.measurableSet.inter isOpen_thickening.measurableSet

/-- Every point of the selected cells sees an entire radius-`b` ball in the padded shading. -/
theorem ball_in_paddedShading {b : ℝ} (hb : 0 < b) (s : Finset (Fin 3 → ℤ)) (x v : Space)
    (hmeet : ∀ z ∈ s, (tube b x v ∩ gridCell b z).Nonempty)
    {y : Space} (hy : y ∈ gridUnion b s) :
    ∃ q : Space, ball q b ⊆ paddedShading b s x v ∩ ball y (4 * b) := by
  obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp hy
  obtain ⟨p, hp, hpz⟩ := hmeet z hz
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  have hyp := gridCell_dist_lt hb hyz hpz
  refine ⟨q, ?_⟩
  intro a ha
  have haq : dist a q < b := ha
  have hay : dist a y < 4 * b := by
    have h1 := dist_triangle a q p
    have h2 := dist_triangle a p y
    rw [dist_comm q p] at h1
    rw [dist_comm p y] at h2
    linarith
  exact ⟨⟨mem_thickening_iff.mpr ⟨q, hq, haq⟩,
    mem_thickening_iff.mpr ⟨y, hy, hay⟩⟩, hay⟩

/-- Padding inside the parent tube retains at least one sixty-fourth of the grid volume. -/
theorem grid_volume_le_paddedShading {b : ℝ} (hb : 0 < b)
    (s : Finset (Fin 3 → ℤ)) (x v : Space)
    (hmeet : ∀ z ∈ s, (tube b x v ∩ gridCell b z).Nonempty) :
    volume (gridUnion b s) ≤ 64 * volume (paddedShading b s x v) := by
  let C := paddedShading b s x v
  let U := gridUnion b s
  let V := volume (ball (0 : Space) b)
  have hm : MeasurableSet C := paddedShading_measurable b s x v
  have hu : MeasurableSet U := gridUnion_measurable b s
  have hlocal (y : Space) (hy : y ∈ U) : V ≤ volume (C ∩ ball y (4 * b)) := by
    obtain ⟨q, hq⟩ := ball_in_paddedShading hb s x v hmeet hy
    calc
      V = volume (ball q b) := (Measure.addHaar_ball_center volume q b).symm
      _ ≤ _ := measure_mono hq
  have hint : V * volume U ≤ volume C * volume (ball (0 : Space) (4 * b)) := by
    rw [← WangZahlLot.Obl.wz_tower_convex_count_composition.lintegral_inter_ball hm (4 * b),
      ← lintegral_indicator_const hu]
    apply lintegral_mono
    intro y
    by_cases hy : y ∈ U
    · rw [indicator_of_mem hy]
      exact hlocal y hy
    · rw [indicator_of_notMem hy]
      exact zero_le
  have hscale : volume (ball (0 : Space) (4 * b)) = 64 * V := by
    dsimp [V]
    rw [EuclideanSpace.volume_ball_fin_three, EuclideanSpace.volume_ball_fin_three]
    rw [ENNReal.ofReal_mul (by norm_num), mul_pow]
    norm_num
    ring
  rw [hscale] at hint
  have he : volume C * (64 * V) = V * (64 * volume C) := by ring
  rw [he] at hint
  exact (ENNReal.mul_le_mul_iff_right (ne_of_gt (measure_ball_pos volume (0 : Space) hb))
    (ne_of_lt measure_ball_lt_top)).mp hint

/-- A uniform enlargement of a grid union increases its volume by a fixed factor. -/
theorem thickening_gridUnion_volume {b : ℝ} (hb : 0 < b) (s : Finset (Fin 3 → ℤ)) :
    volume (thickening (4 * b) (gridUnion b s)) ≤ 4096 * volume (gridUnion b s) := by
  classical
  let c : (Fin 3 → ℤ) → Space := fun z => WithLp.toLp 2 (fun i => (z i : ℝ) * b)
  have hc (z : Fin 3 → ℤ) : c z ∈ gridCell b z := by
    intro i
    change (z i : ℝ) * b ≤ (z i : ℝ) * b ∧ (z i : ℝ) * b < ((z i : ℝ) + 1) * b
    constructor
    · exact le_rfl
    · linarith
  have hsub : thickening (4 * b) (gridUnion b s) ⊆ ⋃ z ∈ s, ball (c z) (6 * b) := by
    intro p hp
    obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
    obtain ⟨z, hz, hqz⟩ := mem_iUnion₂.mp hq
    refine mem_iUnion₂.mpr ⟨z, hz, ?_⟩
    have hqc := gridCell_dist_lt hb hqz (hc z)
    exact (dist_triangle p q (c z)).trans_lt (by linarith)
  have hball (z : Fin 3 → ℤ) : volume (ball (c z) (6 * b)) ≤ ENNReal.ofReal (4096 * b ^ 3) := by
    rw [EuclideanSpace.volume_ball_fin_three, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hπ : 0 < Real.pi := Real.pi_pos
    have hπ4 := Real.pi_lt_four
    have hb3 : 0 ≤ b ^ 3 := by positivity
    have hh := mul_le_mul_of_nonneg_right hπ4.le hb3
    nlinarith only [hh, hb3]
  calc
    _ ≤ ∑ z ∈ s, volume (ball (c z) (6 * b)) :=
      (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _z ∈ s, ENNReal.ofReal (4096 * b ^ 3) :=
      Finset.sum_le_sum fun z _ => hball z
    _ = 4096 * volume (gridUnion b s) := by
      rw [gridUnion_volume hb]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]
      norm_num
      ring

/-- Local density on grid cells controls the union of all padded parent shadings. -/
theorem padded_union_product {b : ℝ} (hb : 0 < b) {p : ℕ}
    (s : Fin p → Finset (Fin 3 → ℤ)) (x v : Fin p → Space)
    (S : Set Space) (hS : MeasurableSet S) (d : ENNReal)
    (hd : ∀ i z, z ∈ s i → d * volume (gridCell b z) ≤ volume (S ∩ gridCell b z)) :
    d * volume (⋃ i, paddedShading b (s i) (x i) (v i)) ≤ 4096 * volume S := by
  classical
  let all := Finset.univ.biUnion s
  have hsub : (⋃ i, paddedShading b (s i) (x i) (v i)) ⊆
      thickening (4 * b) (gridUnion b all) := by
    apply iUnion_subset
    intro i
    apply inter_subset_right.trans
    apply thickening_subset_of_subset
    intro q hq
    obtain ⟨z, hz, hqz⟩ := mem_iUnion₂.mp hq
    exact mem_iUnion₂.mpr ⟨z, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hz⟩, hqz⟩
  have hgrid := gridUnion_product hb all S hS d (by
    intro z hz
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hz
    exact hd i z hi)
  calc
    _ ≤ d * (4096 * volume (gridUnion b all)) :=
      mul_le_mul' le_rfl ((measure_mono hsub).trans (thickening_gridUnion_volume hb all))
    _ = 4096 * (d * volume (gridUnion b all)) := by ring
    _ ≤ _ := mul_le_mul' le_rfl hgrid

end WangZahlLot.Obl.wz_separated_scales_gain
