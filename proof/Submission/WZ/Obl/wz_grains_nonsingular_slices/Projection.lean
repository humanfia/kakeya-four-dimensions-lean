-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_grains_nonsingular_slices.Projection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_grains_nonsingular_slices.Basic

namespace WangZahlLot.Obl.wz_grains_nonsingular_slices

open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_separated_cover_refinement
open scoped ENNReal

/-- A unit tube meets a transverse slab in volume proportional to the reciprocal angle. -/
lemma tube_slab_volume_le {δ r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r)
    (x v u : Space) (hv : ‖v‖ = 1) (hu : ‖u‖ ≤ 1)
    (hq : 0 < |inner ℝ u v|) (c : ℝ) :
    volume (Tube δ x v ∩ {p | |inner ℝ u p - c| ≤ r}) ≤
      ENNReal.ofReal (1152 * (r / |inner ℝ u v|) * δ ^ 2) := by
  let q := |inner ℝ u v|
  have hq1 : q ≤ 1 := by
    exact (abs_real_inner_le_norm u v).trans (by simpa [hv] using hu)
  have hr : 0 < r := hδ.trans_le hδr
  let S : Set ℝ := Icc 0 1 ∩ {t | |inner ℝ u (x + t • v) - c| ≤ r + δ}
  have hsub : Tube δ x v ∩ {p | |inner ℝ u p - c| ≤ r} ⊆
      thickening δ ((fun t : ℝ => x + t • v) '' S) := by
    rintro p ⟨hp, hpc⟩
    change |inner ℝ u p - c| ≤ r at hpc
    obtain ⟨t, ht, hpt⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hp
    have hinner : |inner ℝ u (x + t • v) - inner ℝ u p| ≤ δ := by
      rw [← inner_sub_right]
      calc |inner ℝ u (x + t • v - p)| ≤ ‖u‖ * ‖x + t • v - p‖ :=
          abs_real_inner_le_norm _ _
        _ ≤ 1 * ‖x + t • v - p‖ :=
          mul_le_mul_of_nonneg_right hu (norm_nonneg _)
        _ ≤ δ := by simpa only [one_mul, norm_sub_rev] using hpt.le
    have htS : t ∈ S := by
      refine ⟨ht, ?_⟩
      have h := abs_add_le (inner ℝ u (x + t • v) - inner ℝ u p) (inner ℝ u p - c)
      rw [sub_add_sub_cancel] at h
      exact h.trans (by linarith)
    exact mem_thickening_iff.mpr ⟨x + t • v, ⟨t, htS, rfl⟩, by
      simpa only [dist_eq_norm] using hpt⟩
  have hdiam : ∀ s ∈ S, ∀ t ∈ S, dist s t ≤ 4 * r / q := by
    intro s hs t ht
    have hs2 : |inner ℝ u (x + s • v) - c| ≤ r + δ := hs.2
    have ht2 : |inner ℝ u (x + t • v) - c| ≤ r + δ := ht.2
    have hid : inner ℝ u (x + s • v) - inner ℝ u (x + t • v) =
        (s - t) * inner ℝ u v := by
      simp only [inner_add_right, inner_smul_right]
      ring
    have hdiff : |(s - t) * inner ℝ u v| ≤ 2 * (r + δ) := by
      rw [← hid]
      have h := abs_sub (inner ℝ u (x + s • v) - c) (inner ℝ u (x + t • v) - c)
      rw [sub_sub_sub_cancel_right] at h
      exact h.trans (by linarith [hs2, ht2])
    rw [Real.dist_eq, le_div_iff₀ hq]
    simpa only [abs_mul] using hdiff.trans (by linarith : 2 * (r + δ) ≤ 4 * r)
  have hvol := WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper
    x v hv (show S ⊆ Icc 0 1 from inter_subset_left) hδ
    (show 0 ≤ 4 * r / q by positivity) hdiam
  refine (measure_mono hsub).trans (hvol.trans (ENNReal.ofReal_le_ofReal ?_))
  have hdr : δ ≤ r / q := by
    apply (le_div_iff₀ hq).mpr
    exact (mul_le_mul_of_nonneg_left hq1 hδ.le).trans (by simpa using hδr)
  have hbound : 128 * (2 * (4 * r / q) + δ) ≤ 1152 * (r / q) := by
    rw [show 4 * r / q = 4 * (r / q) by ring]
    linarith
  exact mul_le_mul_of_nonneg_right hbound (sq_nonneg δ)

/-- Covering the normal projection by intervals controls the mass inside a tube. -/
lemma volume_le_of_projection_cover {δ r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r)
    (x v u : Space) (hv : ‖v‖ = 1) (hu : ‖u‖ ≤ 1)
    (hq : 0 < |inner ℝ u v|) {F : Set Space} (hF : F ⊆ Tube δ x v)
    {m : ℕ} (c : Fin m → ℝ)
    (hcov : (fun p : Space => inner ℝ u p) '' F ⊆ ⋃ j, closedBall (c j) r) :
    volume F ≤ ENNReal.ofReal ((m : ℝ) * (1152 * (r / |inner ℝ u v|) * δ ^ 2)) := by
  have hsub : F ⊆ ⋃ j, Tube δ x v ∩ {p | |inner ℝ u p - c j| ≤ r} := by
    intro p hp
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcov ⟨p, hp, rfl⟩)
    exact mem_iUnion.mpr ⟨j, hF hp, by simpa only [Set.mem_ofPred, mem_closedBall, Real.dist_eq] using hj⟩
  calc volume F ≤ volume (⋃ j, Tube δ x v ∩ {p | |inner ℝ u p - c j| ≤ r}) :=
        measure_mono hsub
    _ ≤ ∑ j, volume (Tube δ x v ∩ {p | |inner ℝ u p - c j| ≤ r}) :=
        measure_iUnion_fintype_le volume _
    _ ≤ ∑ j : Fin m, ENNReal.ofReal (1152 * (r / |inner ℝ u v|) * δ ^ 2) :=
        Finset.sum_le_sum (fun j _ => tube_slab_volume_le hδ hδr x v u hv hu hq (c j))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- The quantitative projection inequality underlying the almost-orthogonality lemma.
It requires only an upper bound on the dimension of the projected set. -/
lemma shading_projection_inequality {δ r α C a R lam L : ℝ}
    (hδ : 0 < δ) (hδr : δ ≤ r) (hrR : r ≤ R)
    (x v u : Space) (hv : ‖v‖ = 1) (hu : ‖u‖ ≤ 1)
    (hq : 0 < |inner ℝ u v|) {F : Set Space} (hF : F ⊆ Tube δ x v)
    (hmass : ENNReal.ofReal (lam * L * δ ^ 2) ≤ volume F)
    (hproj : (fun p : Space => inner ℝ u p) '' F ⊆ Icc a (a + R))
    (hAD : AD r α C ((fun p : Space => inner ℝ u p) '' F)) :
    lam * L * |inner ℝ u v| ≤ 1152 * C * r * (R / r) ^ α := by
  have hr : 0 < r := hδ.trans_le hδr
  obtain ⟨m, c, hc, hm⟩ := hAD r R a le_rfl hrR
  have hcover : (fun p : Space => inner ℝ u p) '' F ⊆ ⋃ j, closedBall (c j) r := by
    simpa only [inter_eq_left.mpr hproj] using hc
  have hvF := volume_le_of_projection_cover hδ hδr x v u hv hu hq hF c hcover
  have hmass' : lam * L * δ ^ 2 ≤ (m : ℝ) * (1152 * (r / |inner ℝ u v|) * δ ^ 2) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hmass.trans hvF)
  have hcancel : lam * L ≤ (m : ℝ) * (1152 * (r / |inner ℝ u v|)) := by
    apply (mul_le_mul_iff_left₀ (show 0 < δ ^ 2 by positivity)).mp
    nlinarith [hmass']
  have hmul := mul_le_mul_of_nonneg_right hcancel hq.le
  have heq : (m : ℝ) * (1152 * (r / |inner ℝ u v|)) * |inner ℝ u v| =
      1152 * r * (m : ℝ) := by field_simp
  rw [heq] at hmul
  refine hmul.trans ?_
  calc 1152 * r * (m : ℝ) ≤ 1152 * r * (C * (R / r) ^ α) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

/-- Solving the power inequality in the projection argument. -/
lemma angle_bound_of_power {lam C t α : ℝ} (hlam : 0 < lam) (hC : 0 < C)
    (ht : 0 < t) (hα : α < 1) (h : lam * t ≤ 1152 * C * (4 * t) ^ α) :
    t ≤ (4608 * C / lam) ^ (1 - α)⁻¹ := by
  have hfour : (4 : ℝ) ^ α ≤ 4 := by
    calc (4 : ℝ) ^ α ≤ 4 ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hα.le
      _ = 4 := Real.rpow_one _
  rw [Real.mul_rpow (by norm_num) ht.le] at h
  have h' : lam * t ≤ (4608 * C) * t ^ α := by
    have hmul := mul_le_mul_of_nonneg_left hfour
      (show 0 ≤ 1152 * C * t ^ α by positivity)
    nlinarith
  have hpow : t ^ (1 - α) ≤ 4608 * C / lam := by
    rw [Real.rpow_sub ht, Real.rpow_one]
    apply (div_le_div_iff₀ (Real.rpow_pos_of_pos ht _) hlam).mpr
    nlinarith
  have he : 0 < 1 - α := by linarith
  calc t = (t ^ (1 - α)) ^ (1 - α)⁻¹ :=
      (Real.rpow_rpow_inv ht.le he.ne').symm
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hpow (inv_nonneg.mpr he.le)

/-- A densely shaded short tube with a low-dimensional projection is almost orthogonal
 to that projection. This is the finite-scale estimate used in sticky Lemma 6.2. -/
theorem projection_almost_orthogonal {δ r L lam C α : ℝ}
    (hδ : 0 < δ) (hδr : δ ≤ r) (hL : 0 < L) (hlam : 0 < lam)
    (hC : 0 < C) (hα : α < 1)
    (x v u : Space) (hv : ‖v‖ = 1) (hu : ‖u‖ ≤ 1)
    {F : Set Space} (hF : F ⊆ Tube δ x v)
    (hshort : F ⊆ thickening δ ((fun t : ℝ => x + t • v) '' Icc 0 L))
    (hmass : ENNReal.ofReal (lam * L * δ ^ 2) ≤ volume F)
    (hAD : AD r α C ((fun p : Space => inner ℝ u p) '' F)) :
    |inner ℝ u v| ≤ max 1 ((4608 * C / lam) ^ (1 - α)⁻¹) * (r / L) := by
  have hr : 0 < r := hδ.trans_le hδr
  let q := |inner ℝ u v|
  by_cases hsmall : q * L ≤ r
  · have hq : q ≤ r / L := (le_div_iff₀ hL).mpr hsmall
    exact hq.trans (le_mul_of_one_le_left (by positivity) (le_max_left _ _))
  have hrq : r < q * L := lt_of_not_ge hsmall
  have hq : 0 < q := (mul_pos_iff_of_pos_right hL).mp (hr.trans hrq)
  let a := inner ℝ u x - 2 * q * L
  have hproj : (fun p : Space => inner ℝ u p) '' F ⊆ Icc a (a + 4 * q * L) := by
    rintro b ⟨p, hp, rfl⟩
    obtain ⟨y, ⟨t, ht, rfl⟩, hpt⟩ := mem_thickening_iff.mp (hshort hp)
    have herror : |inner ℝ u (p - (x + t • v))| ≤ δ := by
      calc _ ≤ ‖u‖ * ‖p - (x + t • v)‖ := abs_real_inner_le_norm _ _
        _ ≤ 1 * ‖p - (x + t • v)‖ :=
          mul_le_mul_of_nonneg_right hu (norm_nonneg _)
        _ ≤ δ := by simpa only [one_mul, dist_eq_norm] using hpt.le
    have heq : inner ℝ u p - inner ℝ u x =
        inner ℝ u (p - (x + t • v)) + t * inner ℝ u v := by
      simp only [inner_sub_right, inner_add_right, inner_smul_right]
      ring
    have hb : |inner ℝ u p - inner ℝ u x| ≤ 2 * q * L := by
      rw [heq]
      calc _ ≤ |inner ℝ u (p - (x + t • v))| + |t * inner ℝ u v| := abs_add_le _ _
        _ = |inner ℝ u (p - (x + t • v))| + t * q := by
          rw [abs_mul, abs_of_nonneg ht.1]
        _ ≤ δ + L * q := add_le_add herror (mul_le_mul_of_nonneg_right ht.2 hq.le)
        _ ≤ 2 * q * L := by linarith
    obtain ⟨hb0, hb1⟩ := abs_le.mp hb
    constructor <;> dsimp [a] <;> linarith
  have hineq := shading_projection_inequality hδ hδr
    (show r ≤ 4 * q * L by linarith) x v u hv hu hq hF hmass hproj hAD
  have hscale : lam * (q * L / r) ≤ 1152 * C * (4 * (q * L / r)) ^ α := by
    change lam * L * q ≤ _ at hineq
    rw [show 4 * q * L / r = 4 * (q * L / r) by ring] at hineq
    calc lam * (q * L / r) = (lam * L * q) / r := by ring
      _ ≤ (1152 * C * r * (4 * (q * L / r)) ^ α) / r :=
        div_le_div_of_nonneg_right hineq hr.le
      _ = _ := by field_simp
  have hbound := angle_bound_of_power hlam hC (show 0 < q * L / r by positivity) hα hscale
  have hqbound : q ≤ ((4608 * C / lam) ^ (1 - α)⁻¹) * (r / L) := by
    have hmul := (div_le_iff₀ hr).mp hbound
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hL).mpr hmul
  exact hqbound.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end WangZahlLot.Obl.wz_grains_nonsingular_slices
