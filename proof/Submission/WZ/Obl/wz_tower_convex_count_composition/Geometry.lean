-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_tower_convex_count_composition.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_direction_density_transfer.Geometry
import Submission.WZ.Obl.wz_direction_convex_count

namespace WangZahlLot.Obl.wz_tower_convex_count_composition

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

abbrev Tube (r : ℝ) (x v : Space) := thickening r (segment ℝ x (x + v))

/-- The volume of a moving ball intersected with a measurable set, integrated over
its center, is the product of the two volumes. -/
theorem lintegral_inter_ball {W : Set Space} (hW : MeasurableSet W) (R : ℝ) :
    ∫⁻ z : Space, volume (W ∩ ball z R) = volume W * volume (ball (0 : Space) R) := by
  let S : Set (Space × Space) := {p | p.2 ∈ W ∧ dist p.2 p.1 < R}
  have hS : MeasurableSet S :=
    (measurable_snd hW).inter (isOpen_lt (continuous_snd.dist continuous_fst) continuous_const).measurableSet
  have h1 : (volume.prod volume) S = ∫⁻ z : Space, volume (W ∩ ball z R) := by
    rw [Measure.prod_apply hS]
    rfl
  have h2 : (volume.prod volume) S =
      ∫⁻ p : Space, W.indicator (fun _ => volume (ball (0 : Space) R)) p := by
    rw [Measure.prod_apply_symm hS]
    congr 1
    funext p
    by_cases hp : p ∈ W
    · rw [indicator_of_mem hp]
      have he : (fun z => (z, p)) ⁻¹' S = ball p R := by
        ext z
        simp only [S, mem_preimage, mem_ofPred_eq, hp, true_and, mem_ball, dist_comm]
      rw [he, Measure.addHaar_ball_center]
    · rw [indicator_of_notMem hp]
      have he : (fun z => (z, p)) ⁻¹' S = ∅ := by
        ext z
        simp [S, hp]
      rw [he, measure_empty]
  rw [← h1, h2, lintegral_indicator_const hW, mul_comm]

/-- Midpoint convexity gives a lower bound for every moving-ball intersection
whose center lies in a half-size copy of the thickening. -/
theorem inter_ball_midpoint {W : Set Space} (hW : Convex ℝ W) {R : ℝ}
    (z y : Space) (hy : y ∈ thickening R W) :
    ENNReal.ofReal ((1 / 2 : ℝ) ^ 3) * volume (W ∩ ball z R) ≤
      volume (W ∩ ball ((1 / 2 : ℝ) • (y + z)) R) := by
  obtain ⟨w, hw, hyw⟩ := mem_thickening_iff.mp hy
  have hsub : AffineMap.homothety w (1 / 2 : ℝ) '' (W ∩ ball z R) ⊆
      W ∩ ball ((1 / 2 : ℝ) • (y + z)) R := by
    rintro _ ⟨u, hu, rfl⟩
    have he : AffineMap.homothety w (1 / 2 : ℝ) u =
        (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • w := by
      rw [AffineMap.homothety_apply]
      simp only [vsub_eq_sub, vadd_eq_add]
      module
    rw [he]
    refine ⟨hW hu.1 hw (by norm_num) (by norm_num) (by norm_num), ?_⟩
    rw [mem_ball, dist_eq_norm]
    have he2 : (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • w - (1 / 2 : ℝ) • (y + z) =
        (1 / 2 : ℝ) • ((u - z) + (w - y)) := by module
    rw [he2, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    have hu' : ‖u - z‖ < R := by simpa only [mem_ball, dist_eq_norm] using hu.2
    have hw' : ‖w - y‖ < R := by simpa only [dist_eq_norm, norm_sub_rev] using hyw
    have hn := norm_add_le (u - z) (w - y)
    linarith
  calc
    ENNReal.ofReal ((1 / 2 : ℝ) ^ 3) * volume (W ∩ ball z R) =
        volume (AffineMap.homothety w (1 / 2 : ℝ) '' (W ∩ ball z R)) := by
      rw [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin]
      norm_num
    _ ≤ _ := measure_mono hsub

/-- A thickening and any ball intersection of a convex set have complementary
volume bounds. This is a direct midpoint-convexity version of a convolution bound. -/
theorem thickening_mul_inter_ball {W : Set Space} (hW : Convex ℝ W)
    (hWo : IsOpen W) (R : ℝ) (z : Space) :
    volume (thickening R W) * volume (W ∩ ball z R) ≤
      64 * volume W * volume (ball (0 : Space) R) := by
  let A := AffineMap.homothety z (1 / 2 : ℝ) '' thickening R W
  have hAo : IsOpen A :=
    AffineMap.homothety_isOpenMap z (1 / 2 : ℝ) (by norm_num) _ isOpen_thickening
  have hA : volume A = ENNReal.ofReal ((1 / 2 : ℝ) ^ 3) * volume (thickening R W) := by
    dsimp [A]
    rw [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin]
    norm_num
  have hlo : ∀ q ∈ A, ENNReal.ofReal ((1 / 2 : ℝ) ^ 3) * volume (W ∩ ball z R) ≤
      volume (W ∩ ball q R) := by
    rintro _ ⟨y, hy, rfl⟩
    have he : AffineMap.homothety z (1 / 2 : ℝ) y = (1 / 2 : ℝ) • (y + z) := by
      rw [AffineMap.homothety_apply]
      simp only [vsub_eq_sub, vadd_eq_add]
      module
    rw [he]
    exact inter_ball_midpoint hW z y hy
  have hi : (ENNReal.ofReal ((1 / 2 : ℝ) ^ 3) * volume (W ∩ ball z R)) * volume A ≤
      volume W * volume (ball (0 : Space) R) := by
    rw [← lintegral_inter_ball hWo.measurableSet R,
      ← lintegral_indicator_const hAo.measurableSet]
    apply lintegral_mono
    intro q
    by_cases hq : q ∈ A
    · rw [indicator_of_mem hq]
      exact hlo q hq
    · rw [indicator_of_notMem hq]
      exact zero_le
  rw [hA] at hi
  have hc : (64 : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ 3) *
      ENNReal.ofReal ((1 / 2 : ℝ) ^ 3) = 1 := by
    rw [show (64 : ℝ≥0∞) = ENNReal.ofReal (64 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  calc
    volume (thickening R W) * volume (W ∩ ball z R) =
      (64 * ENNReal.ofReal ((1 / 2 : ℝ) ^ 3) * ENNReal.ofReal ((1 / 2 : ℝ) ^ 3)) *
        (volume (thickening R W) * volume (W ∩ ball z R)) := by rw [hc, one_mul]
    _ = 64 * ((ENNReal.ofReal ((1 / 2 : ℝ) ^ 3) * volume (W ∩ ball z R)) *
        (ENNReal.ofReal ((1 / 2 : ℝ) ^ 3) * volume (thickening R W))) := by ring
    _ ≤ 64 * (volume W * volume (ball (0 : Space) R)) := by gcongr
    _ = _ := by ring

/-- The elementary grid along a unit segment gives a controlled ball cover. -/
theorem tube_ball_cover {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (x v : Space)
    (hv : ‖v‖ = 1) :
    ∃ K : ℕ, (K : ℝ) * r ≤ 2 ∧
      Tube r x v ⊆ ⋃ k ∈ Finset.range K, ball (x + ((k : ℝ) * r) • v) (4 * r) := by
  refine ⟨⌊1 / r⌋₊ + 1, ?_, ?_⟩
  · have hf := Nat.floor_le (show 0 ≤ 1 / r by positivity)
    have hf' := (mul_le_mul_of_nonneg_right hf hr.le)
    rw [div_mul_cancel₀ 1 hr.ne'] at hf'
    push_cast
    nlinarith
  · intro p hp
    obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
    rw [segment_eq_image'] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    simp only [add_sub_cancel_left] at hpq
    let k := ⌊t / r⌋₊
    have hk : k ≤ ⌊1 / r⌋₊ := Nat.floor_mono ((div_le_div_iff_of_pos_right hr).mpr ht.2)
    have hkr : (k : ℝ) * r ≤ t := by
      have hf := Nat.floor_le (show 0 ≤ t / r from div_nonneg ht.1 hr.le)
      exact (le_div_iff₀ hr).mp hf
    have htr : t < ((k : ℝ) + 1) * r := by
      exact (div_lt_iff₀ hr).mp (Nat.lt_floor_add_one (t / r))
    refine mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr (by omega), ?_⟩
    rw [mem_ball]
    have hd : dist (x + t • v) (x + ((k : ℝ) * r) • v) < r := by
      rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, hv, mul_one,
        Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hkr)]
      linarith
    exact (dist_triangle _ (x + t • v) _).trans_lt (by linarith)

/-- The ball-cover estimate cancels one power of the thickening radius. -/
theorem thickening_mul_inter_tube {W : Set Space} (hW : Convex ℝ W)
    (hWo : IsOpen W) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (x v : Space) (hv : ‖v‖ = 1) :
    volume (thickening (4 * r) W) * volume (W ∩ Tube r x v) ≤
      ENNReal.ofReal (131072 * r ^ 2) * volume W := by
  classical
  obtain ⟨K, hK, hcover⟩ := tube_ball_cover hr hr1 x v hv
  have hsub : W ∩ Tube r x v ⊆
      ⋃ k ∈ Finset.range K, W ∩ ball (x + ((k : ℝ) * r) • v) (4 * r) := by
    intro p hp
    obtain ⟨k, hk, hpk⟩ := mem_iUnion₂.mp (hcover hp.2)
    exact mem_iUnion₂.mpr ⟨k, hk, hp.1, hpk⟩
  have hball : volume (ball (0 : Space) (4 * r)) ≤ ENNReal.ofReal (1024 * r ^ 3) := by
    rw [EuclideanSpace.volume_ball_fin_three, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hpi : Real.pi * 4 / 3 ≤ 16 := by linarith [Real.pi_lt_four]
    have := mul_le_mul_of_nonneg_left hpi (show 0 ≤ (4 * r) ^ 3 by positivity)
    nlinarith only [this]
  calc
    volume (thickening (4 * r) W) * volume (W ∩ Tube r x v) ≤
      volume (thickening (4 * r) W) *
        ∑ k ∈ Finset.range K, volume (W ∩ ball (x + ((k : ℝ) * r) • v) (4 * r)) :=
      by
        gcongr
        exact (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ = ∑ k ∈ Finset.range K, volume (thickening (4 * r) W) *
        volume (W ∩ ball (x + ((k : ℝ) * r) • v) (4 * r)) := by rw [Finset.mul_sum]
    _ ≤ ∑ _k ∈ Finset.range K, 64 * volume W * volume (ball (0 : Space) (4 * r)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact thickening_mul_inter_ball hW hWo _ _
    _ = (K : ℝ≥0∞) * (64 * volume W * volume (ball (0 : Space) (4 * r))) := by simp
    _ ≤ (K : ℝ≥0∞) * (64 * volume W * ENNReal.ofReal (1024 * r ^ 3)) := by gcongr
    _ = ENNReal.ofReal ((K : ℝ) * (64 * (1024 * r ^ 3))) * volume W := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64), ENNReal.ofReal_natCast]
      norm_num
      ring
    _ ≤ ENNReal.ofReal (131072 * r ^ 2) * volume W := by
      gcongr 1
      apply ENNReal.ofReal_le_ofReal
      have := mul_le_mul_of_nonneg_right hK (show 0 ≤ 65536 * r ^ 2 by positivity)
      nlinarith only [this]

end WangZahlLot.Obl.wz_tower_convex_count_composition
