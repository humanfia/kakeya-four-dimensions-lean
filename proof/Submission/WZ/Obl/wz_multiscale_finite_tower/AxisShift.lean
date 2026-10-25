-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.AxisShift.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.AlignedAxes
import Submission.WZ.Obl.wz_direction_density_transfer.Geometry

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya

noncomputable def axialReflection (v p : Space) : Space := p - (2 * inner ℝ v p) • v

lemma axialReflection_norm {v : Space} (hv : ‖v‖ = 1) (p : Space) :
    ‖axialReflection v p‖ = ‖p‖ := by
  have hh : ‖axialReflection v p‖ ^ 2 = ‖p‖ ^ 2 := by
    dsimp [axialReflection]
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, hv, mul_one, sq_abs,
      inner_smul_right, real_inner_comm p v]
    ring
  nlinarith [norm_nonneg (axialReflection v p), norm_nonneg p]

lemma axialReflection_sub (v p q : Space) :
    axialReflection v (p - q) = axialReflection v p - axialReflection v q := by
  simp only [axialReflection, inner_sub_right]
  module

lemma axialReflection_involutive {v : Space} (hv : ‖v‖ = 1) (p : Space) :
    axialReflection v (axialReflection v p) = p := by
  have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  simp only [axialReflection, inner_sub_right, inner_smul_right, hvv, mul_one]
  module

/-- Reflecting across the plane normal to the axis gives the opposite axial
midpoint while leaving the unoriented tube direction unchanged. -/
lemma reflected_tube {d : ℝ} (x v : Space) (hv : ‖v‖ = 1) :
    Tube d (x - (2 * inner ℝ v (axisMidpoint x v)) • v) v =
      axialReflection v '' Tube d x v := by
  have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have he (t : ℝ) : axialReflection v (x + t • v) =
      x - (2 * inner ℝ v (axisMidpoint x v)) • v + (1 - t) • v := by
    simp only [axialReflection, axisMidpoint, inner_add_right, inner_smul_right, hvv, mul_one]
    module
  have hmem {p : Space} (hp : p ∈ Tube d x v) :
      axialReflection v p ∈ Tube d (x - (2 * inner ℝ v (axisMidpoint x v)) • v) v := by
    obtain ⟨t, ht, hpt⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hp
    apply mem_thickening_iff.mpr
    refine ⟨x - (2 * inner ℝ v (axisMidpoint x v)) • v + (1 - t) • v, ?_, ?_⟩
    · rw [segment_eq_image']
      exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by simp⟩
    · rw [← he t, dist_eq_norm, ← axialReflection_sub, axialReflection_norm hv]
      exact hpt
  apply Subset.antisymm
  · intro p hp
    refine ⟨axialReflection v p, ?_, axialReflection_involutive hv p⟩
    obtain ⟨t, ht, hpt⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hp
    apply mem_thickening_iff.mpr
    refine ⟨x + (1 - t) • v, ?_, ?_⟩
    · rw [segment_eq_image']
      exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by simp⟩
    · have he' := he (1 - t)
      rw [show 1 - (1 - t) = t by ring] at he'
      have hnorm := axialReflection_norm hv
        (axialReflection v p - (x + (1 - t) • v))
      rw [axialReflection_sub, axialReflection_involutive hv, he'] at hnorm
      rw [dist_eq_norm, ← hnorm]
      exact hpt
  · rintro _ ⟨p, hp, rfl⟩
    exact hmem hp

lemma tube_convex_interpolation {d a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    {x y v : Space} {W : Set Space} (hW : Convex ℝ W)
    (hx : Tube d x v ⊆ W) (hy : Tube d y v ⊆ W) :
    Tube d ((1 - a) • x + a • y) v ⊆ W := by
  intro p hp
  obtain ⟨t, ht, hpt⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hp
  let e := p - (((1 - a) • x + a • y) + t • v)
  have hxe : x + t • v + e ∈ Tube d x v := by
    apply mem_thickening_iff.mpr
    refine ⟨x + t • v, ?_, ?_⟩
    · rw [segment_eq_image']; exact ⟨t, ht, by simp⟩
    · simpa only [dist_eq_norm, add_sub_cancel_left] using hpt
  have hye : y + t • v + e ∈ Tube d y v := by
    apply mem_thickening_iff.mpr
    refine ⟨y + t • v, ?_, ?_⟩
    · rw [segment_eq_image']; exact ⟨t, ht, by simp⟩
    · simpa only [dist_eq_norm, add_sub_cancel_left] using hpt
  have hp' := hW (hx hxe) (hy hye) (show 0 ≤ 1 - a by linarith) ha (by ring : 1 - a + a = 1)
  convert hp' using 1
  dsimp [e]
  module

/-- Moving the scalar midpoint toward zero preserves unit-ball containment. -/
theorem inward_axis_shift {d h : ℝ} {x v : Space} (hv : ‖v‖ = 1)
    (hh : |h| ≤ |inner ℝ v (axisMidpoint x v)|)
    (hT : Tube d x v ⊆ ball 0 1) :
    Tube d (x + (h - inner ℝ v (axisMidpoint x v)) • v) v ⊆ ball 0 1 := by
  let b := inner ℝ v (axisMidpoint x v)
  have hb : |h| ≤ |b| := hh
  have hreflect : Tube d (x - (2 * b) • v) v ⊆ ball 0 1 := by
    rw [reflected_tube x v hv]
    rintro _ ⟨p, hp, rfl⟩
    simpa only [mem_ball_zero_iff, axialReflection_norm hv] using hT hp
  by_cases hb0 : b = 0
  · have hh0 : h = 0 := abs_nonpos_iff.mp (by simpa only [hb0, abs_zero] using hb)
    simpa only [b, hb0, hh0, sub_zero, zero_smul, add_zero] using hT
  let a := (b - h) / (2 * b)
  have ha : 0 ≤ a ∧ a ≤ 1 := by
    rcases lt_or_gt_of_ne hb0 with hbneg | hbpos
    · rw [abs_of_neg hbneg] at hb
      obtain ⟨hl, hu⟩ := abs_le.mp hb
      constructor
      · exact div_nonneg_of_nonpos (by linarith) (by linarith)
      · exact (div_le_iff_of_neg (by linarith : 2 * b < 0)).mpr (by linarith)
    · rw [abs_of_pos hbpos] at hb
      obtain ⟨hl, hu⟩ := abs_le.mp hb
      constructor
      · exact div_nonneg (by linarith) (by linarith)
      · exact (div_le_iff₀ (by linarith : 0 < 2 * b)).mpr (by linarith)
  have he : (1 - a) • x + a • (x - (2 * b) • v) = x + (h - b) • v := by
    have hab : a * (2 * b) = b - h := div_mul_cancel₀ _ (mul_ne_zero (by norm_num) hb0)
    rw [smul_sub, smul_smul, hab]
    module
  have hh' := tube_convex_interpolation ha.1 ha.2 (convex_ball (0 : Space) 1) hT hreflect
  rwa [he] at hh'

/-- A small longitudinal shift only removes two short endpoint strips. -/
lemma axis_shift_diff_subset {d a b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (ha : |a| ≤ b) (x v : Space) :
    Tube d x v \ Tube d (x + a • v) v ⊆
      thickening d ((fun t : ℝ => x + t • v) '' Icc 0 b) ∪
        thickening d ((fun t : ℝ => x + t • v) '' Icc (1 - b) 1) := by
  rintro p ⟨hp, hpn⟩
  obtain ⟨t, ht, hpt⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hp
  by_cases hlo : t ≤ b
  · exact Or.inl (mem_thickening_iff.mpr ⟨x + t • v, ⟨t, ⟨ht.1, hlo⟩, rfl⟩,
      by simpa only [dist_eq_norm] using hpt⟩)
  by_cases hhi : 1 - b ≤ t
  · exact Or.inr (mem_thickening_iff.mpr ⟨x + t • v, ⟨t, ⟨hhi, ht.2⟩, rfl⟩,
      by simpa only [dist_eq_norm] using hpt⟩)
  exfalso
  apply hpn
  refine mem_thickening_iff.mpr ⟨x + t • v, ?_, by simpa only [dist_eq_norm] using hpt⟩
  rw [segment_eq_image']
  refine ⟨t - a, ⟨?_, ?_⟩, ?_⟩
  · linarith [(abs_le.mp ha).2]
  · linarith [(abs_le.mp ha).1]
  · simp only [add_sub_cancel_left]
    module

lemma axis_shift_volume_loss {d a b : ℝ} (hd : 0 < d) (hdb : d ≤ b) (hb1 : b ≤ 1)
    (ha : |a| ≤ b) (x v : Space) (hv : ‖v‖ = 1) :
    volume (Tube d x v \ Tube d (x + a • v) v) ≤ ENNReal.ofReal (768 * b * d ^ 2) := by
  have hb : 0 ≤ b := (hd.trans_le hdb).le
  have hfirst := WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper
    x v hv (show Icc (0 : ℝ) b ⊆ Icc 0 1 from fun _ ht => ⟨ht.1, ht.2.trans hb1⟩) hd hb
    (by intro s hs t ht; rw [Real.dist_eq, abs_le]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2])
  have hlast := WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper
    x v hv (show Icc (1 - b) 1 ⊆ Icc (0 : ℝ) 1 from fun _ ht => ⟨by linarith [ht.1], ht.2⟩) hd hb
    (by intro s hs t ht; rw [Real.dist_eq, abs_le]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2])
  calc
    _ ≤ volume (thickening d ((fun t : ℝ => x + t • v) '' Icc 0 b) ∪
        thickening d ((fun t : ℝ => x + t • v) '' Icc (1 - b) 1)) :=
      measure_mono (axis_shift_diff_subset hb hb1 ha x v)
    _ ≤ volume (thickening d ((fun t : ℝ => x + t • v) '' Icc 0 b)) +
        volume (thickening d ((fun t : ℝ => x + t • v) '' Icc (1 - b) 1)) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (128 * (2 * b + d) * d ^ 2) +
        ENNReal.ofReal (128 * (2 * b + d) * d ^ 2) := add_le_add hfirst hlast
    _ ≤ _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_le_mul_of_nonneg_right hdb (sq_nonneg d)]

lemma shading_axis_shift_loss {d a b : ℝ} (hd : 0 < d) (hdb : d ≤ b) (hb1 : b ≤ 1)
    (ha : |a| ≤ b) (x v : Space) (hv : ‖v‖ = 1) {Y : Set Space}
    (hY : Y ⊆ Tube d x v) :
    volume Y ≤ volume (Y ∩ Tube d (x + a • v) v) + ENNReal.ofReal (768 * b * d ^ 2) := by
  have hdiff : volume (Y \ Tube d (x + a • v) v) ≤ ENNReal.ofReal (768 * b * d ^ 2) :=
    (measure_mono (sdiff_subset_sdiff_left hY)).trans (axis_shift_volume_loss hd hdb hb1 ha x v hv)
  calc
    _ = volume ((Y ∩ Tube d (x + a • v) v) ∪ (Y \ Tube d (x + a • v) v)) := by
      rw [inter_union_sdiff]
    _ ≤ volume (Y ∩ Tube d (x + a • v) v) + volume (Y \ Tube d (x + a • v) v) := measure_union_le _ _
    _ ≤ _ := add_le_add le_rfl hdiff

lemma midpoint_bound_of_unit_ball {d : ℝ} (hd : 0 < d) {x v : Space}
    (hv : ‖v‖ = 1) (hT : Tube d x v ⊆ ball 0 1) :
    ‖axisMidpoint x v‖ ≤ 7 / 8 := by
  have hx : ‖x‖ < 1 := (mem_ball_zero_iff.mp
    (hT (self_subset_thickening hd _ (left_mem_segment ℝ _ _))))
  have hy : ‖x + v‖ < 1 := (mem_ball_zero_iff.mp
    (hT (self_subset_thickening hd _ (right_mem_segment ℝ _ _))))
  have he : ‖axisMidpoint x v‖ ^ 2 =
      (‖x‖ ^ 2 + ‖x + v‖ ^ 2) / 2 - 1 / 4 := by
    simp only [axisMidpoint, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
      inner_smul_right, hv]
    norm_num
    ring
  have hx2 : ‖x‖ ^ 2 < 1 := by nlinarith [norm_nonneg x]
  have hy2 : ‖x + v‖ ^ 2 < 1 := by nlinarith [norm_nonneg (x + v)]
  nlinarith [norm_nonneg (axisMidpoint x v)]

/-- Axes from one direction cap and the unit ball have a fixed margin in a
centered root tube. This margin allows all later representative radii. -/
lemma representative_root_buffer {R : ℝ} (hR : R ≤ 1 / 32)
    {x v u : Space} (hmid : ‖axisMidpoint x v‖ ≤ 7 / 8)
    (hdir : ‖v - u‖ ≤ 1 / 10) : Tube R x v ⊆ Tube (31 / 32) (- (1 / 2 : ℝ) • u) u := by
  intro p hp
  obtain ⟨t, ht, hpt⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hp
  have ht' : |t - 1 / 2| ≤ 1 / 2 := abs_le.mpr
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine mem_thickening_iff.mpr ⟨- (1 / 2 : ℝ) • u + t • u, ?_, ?_⟩
  · rw [segment_eq_image']; exact ⟨t, ht, by simp⟩
  · rw [dist_eq_norm]
    have he : p - (- (1 / 2 : ℝ) • u + t • u) =
        (p - (x + t • v)) + axisMidpoint x v + (t - 1 / 2) • (v - u) := by
      dsimp [axisMidpoint]
      module
    rw [he]
    calc
      _ ≤ (‖p - (x + t • v)‖ + ‖axisMidpoint x v‖) +
          ‖(t - 1 / 2) • (v - u)‖ := (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ (‖p - (x + t • v)‖ + 7 / 8) + (1 / 2 : ℝ) * (1 / 10) := by
        rw [norm_smul, Real.norm_eq_abs]
        exact add_le_add (add_le_add le_rfl hmid) (mul_le_mul ht' hdir (norm_nonneg _) (by norm_num))
      _ < 31 / 32 := by linarith

lemma representative_root_containment {R : ℝ} (hR : R ≤ 1 / 32)
    {x v u : Space} (hmid : ‖axisMidpoint x v‖ ≤ 7 / 8)
    (hdir : ‖v - u‖ ≤ 1 / 10) : Tube R x v ⊆ Tube 1 (- (1 / 2 : ℝ) • u) u :=
  (representative_root_buffer hR hmid hdir).trans (thickening_mono (by norm_num) _)

end WangZahlLot.Obl.wz_multiscale_finite_tower
