-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_convex_container_tube_packing.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
namespace WangZahlLot.Obl.wz_convex_container_tube_packing

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

abbrev Tube (δ : ℝ) (x v : Space) : Set Space :=
  thickening δ (segment ℝ x (x + v))

/-- A contraction about an axis point stays in the tube. -/
theorem contract_subset {δ : ℝ} (hδ : 0 < δ) (x v : Space) {c r : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1) :
    AffineMap.homothety (x + c • v) r '' Tube δ x v ⊆ Tube δ x v := by
  have hc' : x + c • v ∈ Tube δ x v := by
    apply self_subset_thickening hδ
    rw [segment_eq_image']
    exact ⟨c, hc, by simp⟩
  rintro _ ⟨p, hp, rfl⟩
  have heq : AffineMap.homothety (x + c • v) r p =
      (1 - r) • (x + c • v) + r • p := by
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    module
  rw [heq]
  exact ((convex_segment (𝕜 := ℝ) x (x + v)).thickening δ) hc' hp
    (sub_nonneg.mpr hr.2) hr.1 (by ring)

/-- Locate a point of a contracted tube near the corresponding contracted axis. -/
theorem contract_axis {δ : ℝ} {x v p : Space} {c r : ℝ} (hr : 0 < r)
    (hp : p ∈ AffineMap.homothety (x + c • v) r '' Tube δ x v) :
    ∃ t ∈ Icc ((1 - r) * c) ((1 - r) * c + r),
      dist p (x + t • v) < r * δ := by
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨a, ha, hqa⟩ := mem_thickening_iff.mp hq
  rw [segment_eq_image'] at ha
  obtain ⟨s, hs, rfl⟩ := ha
  simp only [add_sub_cancel_left] at hqa
  refine ⟨(1 - r) * c + r * s, ⟨?_, ?_⟩, ?_⟩
  · nlinarith [hs.1]
  · nlinarith [hs.2]
  · have heq : x + ((1 - r) * c + r * s) • v =
        AffineMap.homothety (x + c • v) r (x + s • v) := by
      simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
      module
    rw [heq, dist_homothety, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_lt_mul_of_pos_left hqa hr

/-- Convex combinations preserve a common strict distance bound. -/
theorem dist_combo_lt {a b c d : Space} {ε t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hac : dist a c < ε) (hbd : dist b d < ε) :
    dist ((1 - t) • a + t • b) ((1 - t) • c + t • d) < ε := by
  rw [dist_eq_norm]
  have heq : (1 - t) • a + t • b - ((1 - t) • c + t • d) =
      (1 - t) • (a - c) + t • (b - d) := by module
  rw [heq]
  calc
    ‖(1 - t) • (a - c) + t • (b - d)‖
      ≤ (1 - t) * dist a c + t * dist b d := by
        simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1,
          abs_of_nonneg (sub_nonneg.mpr ht.2), dist_eq_norm] using
          norm_add_le ((1 - t) • (a - c)) (t • (b - d))
    _ < (1 - t) * ε + t * ε := by
      rcases eq_or_lt_of_le ht.1 with h | h
      · simp only [← h, sub_zero, zero_mul, one_mul, add_zero]
        exact hac
      · exact add_lt_add_of_le_of_lt
          (mul_le_mul_of_nonneg_left hac.le (sub_nonneg.mpr ht.2))
          (mul_lt_mul_of_pos_left hbd h)
    _ = ε := by ring

/-- Matching two endpoint neighborhoods matches the central part of the first axis. -/
theorem central_axis_close {δ : ℝ} {x v y w p q : Space}
    (hp₁ : p ∈ AffineMap.homothety x (1 / 10 : ℝ) '' Tube δ x v)
    (hp₂ : p ∈ AffineMap.homothety y (1 / 10 : ℝ) '' Tube δ y w)
    (hq₁ : q ∈ AffineMap.homothety (x + v) (1 / 10 : ℝ) '' Tube δ x v)
    (hq₂ : q ∈ AffineMap.homothety (y + w) (1 / 10 : ℝ) '' Tube δ y w)
    {t : ℝ} (ht : t ∈ Icc (1 / 10 : ℝ) (9 / 10)) :
    ∃ z ∈ segment ℝ y (y + w), dist (x + t • v) z < δ / 5 := by
  obtain ⟨a, ha, hpa⟩ := contract_axis (c := 0) (by norm_num : (0 : ℝ) < 1 / 10)
    (by simpa using hp₁)
  obtain ⟨b, hb, hpb⟩ := contract_axis (c := 0) (by norm_num : (0 : ℝ) < 1 / 10)
    (by simpa using hp₂)
  obtain ⟨c, hc, hqc⟩ := contract_axis (c := 1) (by norm_num : (0 : ℝ) < 1 / 10)
    (by simpa using hq₁)
  obtain ⟨d, hd, hqd⟩ := contract_axis (c := 1) (by norm_num : (0 : ℝ) < 1 / 10)
    (by simpa using hq₂)
  norm_num at ha hb hc hd
  have hac : a < c := by linarith [ha.2, hc.1]
  let s : ℝ := (t - a) / (c - a)
  have hs0 : 0 ≤ s := div_nonneg (by linarith [ha.2, ht.1]) (by linarith)
  have hs1 : s ≤ 1 := (div_le_one (by linarith : 0 < c - a)).2
    (by linarith [ht.2, hc.1])
  have hs_eq : (1 - s) * a + s * c = t := by
    dsimp [s]
    field_simp [sub_ne_zero.mpr hac.ne']
    ring
  have hab : dist (x + a • v) (y + b • w) < δ / 5 := by
    have := dist_triangle (x + a • v) p (y + b • w)
    rw [dist_comm (x + a • v) p] at this
    linarith
  have hcd : dist (x + c • v) (y + d • w) < δ / 5 := by
    have := dist_triangle (x + c • v) q (y + d • w)
    rw [dist_comm (x + c • v) q] at this
    linarith
  refine ⟨(1 - s) • (y + b • w) + s • (y + d • w), ?_, ?_⟩
  · apply (convex_segment (𝕜 := ℝ) y (y + w))
    · rw [segment_eq_image']
      exact ⟨b, ⟨hb.1, by linarith [hb.2]⟩, by simp⟩
    · rw [segment_eq_image']
      exact ⟨d, ⟨by linarith [hd.1], hd.2⟩, by simp⟩
    · linarith
    · exact hs0
    · ring
  · have heq : (1 - s) • (x + a • v) + s • (x + c • v) = x + t • v := by
      calc
        _ = x + ((1 - s) * a + s * c) • v := by module
        _ = _ := by rw [hs_eq]
    rw [← heq]
    exact dist_combo_lt ⟨hs0, hs1⟩ hab hcd

/-- Intersecting endpoint products force a large common contracted tube. -/
theorem central_contract_subset_inter {δ : ℝ} (hδ : 0 < δ) {x v y w p q : Space}
    (hp₁ : p ∈ AffineMap.homothety x (1 / 10 : ℝ) '' Tube δ x v)
    (hp₂ : p ∈ AffineMap.homothety y (1 / 10 : ℝ) '' Tube δ y w)
    (hq₁ : q ∈ AffineMap.homothety (x + v) (1 / 10 : ℝ) '' Tube δ x v)
    (hq₂ : q ∈ AffineMap.homothety (y + w) (1 / 10 : ℝ) '' Tube δ y w) :
    AffineMap.homothety (x + (1 / 2 : ℝ) • v) (4 / 5 : ℝ) '' Tube δ x v ⊆
      Tube δ x v ∩ Tube δ y w := by
  intro z hz
  refine ⟨contract_subset hδ x v (by norm_num) (by norm_num) hz, ?_⟩
  obtain ⟨t, ht, hzt⟩ := contract_axis (by norm_num : (0 : ℝ) < 4 / 5) hz
  norm_num at ht
  obtain ⟨a, ha, hta⟩ := central_axis_close hp₁ hp₂ hq₁ hq₂ ht
  exact mem_thickening_iff.mpr ⟨a, ha,
    (dist_triangle z (x + t • v) a).trans_lt (by linarith)⟩

end WangZahlLot.Obl.wz_convex_container_tube_packing
