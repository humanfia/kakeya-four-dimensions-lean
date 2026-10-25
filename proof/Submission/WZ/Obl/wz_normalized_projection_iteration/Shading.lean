-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_iteration.Shading.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_iteration.Expansion
import Submission.WZ.Obl.wz_normalized_projection_iteration.Projection
import Submission.WZ.Obl.wz_normalized_projection_iteration.Interior

namespace WangZahlLot.Obl.wz_normalized_projection_iteration

open Set Metric MeasureTheory
open scoped ENNReal Pointwise

/-- Translation preserves a tube's radius and direction. -/
theorem translate_subset_tube {δ : ℝ} (a x v : Space) :
    (fun p => a + p) '' Tube δ x v ⊆ Tube δ (a + x) v := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  refine mem_thickening_iff.mpr ⟨a + q, ?_, by simpa using hpq⟩
  rw [segment_eq_image'] at hq ⊢
  obtain ⟨t, ht, rfl⟩ := hq
  refine ⟨t, ht, ?_⟩
  simp only [add_sub_cancel_left]
  abel

/-- A shading can be moved into the unit ball and expanded at any larger tube scale. -/
theorem exists_expanded_shading {δ r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) (hr1 : r ≤ 1 / 4)
    {x v : Space} (hv : ‖v‖ = 1) (hball : Tube δ x v ⊆ ball 0 1)
    {Y : Set Space} (hYm : MeasurableSet Y) (hY : Y ⊆ Tube δ x v) :
    ∃ Z : Set Space, MeasurableSet Z ∧ Z ⊆ Tube r (inwardStart r x v) v ∧
      ENNReal.ofReal (r ^ 2) * volume Y ≤ ENNReal.ofReal (73728 * δ ^ 2) * volume Z ∧
      ∀ p ∈ Z, ∃ q ∈ Y, dist p q < 7 * r := by
  have hr : 0 < r := hδ.trans_le hδr
  have hx : ‖x‖ ≤ 1 := by
    have hh := hball ((self_subset_thickening hδ _) (left_mem_segment ℝ x (x + v)))
    exact (by simpa using hh : ‖x‖ < 1).le
  have hxv : ‖x + v‖ ≤ 1 := by
    have hh := hball ((self_subset_thickening hδ _) (right_mem_segment ℝ x (x + v)))
    exact (by simpa using hh : ‖x + v‖ < 1).le
  let a : Space := inwardStart r x v - x
  have ha : ‖a‖ ≤ 6 * r := inward_start_dist hr.le hx hv
  have hax : a + x = inwardStart r x v := by dsimp [a]; abel
  have hmeasure (E : Set Space) : volume ((fun p => a + p) '' E) = volume E := by
    rw [image_add_left, measure_preimage_add]
  by_cases hlarge : δ ≤ r / 4
  · let E : Set Space := thickening (r / 4) Y
    let Z : Set Space := (fun p => a + p) '' E
    have hZT : Z ⊆ Tube r (inwardStart r x v) v := by
      have hE : E ⊆ Tube (r / 4 + δ) x v :=
        (thickening_subset_of_subset (r / 4) hY).trans
          (thickening_thickening_subset (r / 4) δ _)
      have htrans := (Set.image_mono hE).trans (translate_subset_tube a x v)
      rw [hax] at htrans
      exact htrans.trans (thickening_mono (by linarith : r / 4 + δ ≤ r) _)
    have hvolume : ENNReal.ofReal (r ^ 2) * volume Y ≤
        ENNReal.ofReal (73728 * δ ^ 2) * volume Z := by
      have hexp := tube_shading_expansion hδ hlarge x v hv hY (hY.trans hball)
      rw [show volume Z = volume E from hmeasure E]
      calc
        _ = ENNReal.ofReal 16 * (ENNReal.ofReal ((r / 4) ^ 2) * volume Y) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
          congr 2
          ring
        _ ≤ ENNReal.ofReal 16 * (ENNReal.ofReal (4608 * δ ^ 2) * volume E) :=
          mul_le_mul_right hexp _
        _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
          congr 2
          ring
    refine ⟨Z, ?_, hZT, hvolume, ?_⟩
    · dsimp [Z]
      rw [image_add_left]
      exact isOpen_thickening.measurableSet.preimage (by fun_prop)
    · rintro p ⟨u, hu, rfl⟩
      obtain ⟨q, hq, huq⟩ := mem_thickening_iff.mp hu
      refine ⟨q, hq, ?_⟩
      have htri := dist_triangle (a + u) u q
      have had : dist (a + u) u = ‖a‖ := by simp [dist_eq_norm]
      rw [had] at htri
      linarith
  · let Z : Set Space := (fun p => a + p) '' Y
    have hZT : Z ⊆ Tube r (inwardStart r x v) v := by
      have htrans := (Set.image_mono hY).trans (translate_subset_tube a x v)
      rw [hax] at htrans
      exact htrans.trans (thickening_mono hδr _)
    refine ⟨Z, ?_, hZT, ?_, ?_⟩
    · dsimp [Z]
      rw [image_add_left]
      exact hYm.preimage (by fun_prop)
    · rw [show volume Z = volume Y from hmeasure Y]
      apply mul_le_mul_left
      apply ENNReal.ofReal_le_ofReal
      have hh : r < 4 * δ := by linarith
      nlinarith [sq_nonneg (4 * δ - r)]
    · rintro p ⟨q, hq, rfl⟩
      refine ⟨q, hq, ?_⟩
      have hh : dist (a + q) q = ‖a‖ := by simp [dist_eq_norm]
      rw [hh]
      linarith

/-- Spatial displacement by a fixed scale costs only a fixed factor in projected area. -/
theorem projected_area_of_nearby {r : ℝ} (hr : 0 < r)
    {f : ℝ → ℝ} (hf : Slope f) (hf0 : |f 0| ≤ 1)
    {E Z : Set Space} (hE : E ⊆ closedBall 0 1) (hZ : Z ⊆ closedBall 0 1)
    (hnear : ∀ p ∈ Z, ∃ q ∈ E, dist p q < 7 * r) :
    volume (Projection f Z) ≤ ENNReal.ofReal 7396 * volume (thickening r (Projection f E)) := by
  have hsub : Projection f Z ⊆ thickening (42 * r) (Projection f E) := by
    apply projection_subset_thickening hf hf0 hE hZ
    simpa only [show 42 * r / 6 = 7 * r by ring] using hnear
  have hbound : TotallyBounded (Projection f E) :=
    (isCompact_closedBall (0 : ℝ × ℝ) 6).totallyBounded.subset (projection_subset_ball hf hf0 hE)
  have hd := planar_thickening_doubling hbound hr (show (0 : ℝ) ≤ 42 by norm_num)
  norm_num only [show (4 : ℝ) * (42 + 1) ^ 2 = 7396 by norm_num] at hd
  exact (measure_mono hsub).trans hd

end WangZahlLot.Obl.wz_normalized_projection_iteration
