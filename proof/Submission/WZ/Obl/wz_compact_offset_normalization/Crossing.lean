-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_compact_offset_normalization.Crossing.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_compact_offset_normalization.Basic
import Submission.WZ.Obl.wz_direction_density_transfer

/-!
# Heavily overlapping unit tubes are close

If two unit `δ`-tubes intersect in volume more than `δ² / 2`, then the second one lies in the
`5000 δ`-neighbourhood of the five-fold extension of the axis of the first one, a set of volume
`O(δ²)`.
-/

namespace WangZahlLot.Obl.wz_compact_offset_normalization

open Set Metric MeasureTheory
open scoped ENNReal

/-- Parameters of the axis of `(y', u')` that come `2δ`-close to the axis of `(y, u)`. -/
def closeParams (δ : ℝ) (y u y' u' : Space) : Set ℝ :=
  {t | t ∈ Icc (0 : ℝ) 1 ∧ y' + t • u' ∈ thickening (2 * δ) (segment ℝ y (y + u))}

theorem inter_subset_closeParams (δ : ℝ) (y u y' u' : Space) :
    Tube δ y u ∩ Tube δ y' u' ⊆
      thickening δ ((fun t : ℝ => y' + t • u') '' closeParams δ y u y' u') := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp.1
  obtain ⟨t, ht, hpt⟩ := mem_tube_iff.mp hp.2
  apply mem_thickening_iff.mpr
  refine ⟨y' + t • u', ⟨t, ⟨ht, ?_⟩, rfl⟩, hpt⟩
  apply mem_thickening_iff.mpr
  refine ⟨q, hq, ?_⟩
  have := dist_triangle (y' + t • u') p q
  rw [dist_comm (y' + t • u') p] at this
  linarith

/-- A heavy intersection forces two far apart close parameters. -/
theorem wide_of_big {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10000) {y u y' u' : Space}
    (hu' : ‖u'‖ = 1)
    (hbig : ENNReal.ofReal (δ ^ 2 / 2) < volume (Tube δ y u ∩ Tube δ y' u')) :
    ∃ s ∈ closeParams δ y u y' u', ∃ t ∈ closeParams δ y u y' u', 1 / 1024 < |s - t| := by
  by_contra h
  push Not at h
  have hdiam : ∀ s ∈ closeParams δ y u y' u', ∀ t ∈ closeParams δ y u y' u',
      dist s t ≤ 1 / 1024 := fun s hs t ht => by rw [Real.dist_eq]; exact h s hs t ht
  have hvol := WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper y' u' hu'
    (fun _ ht => ht.1) hδ (by norm_num) hdiam
  have hle : volume (Tube δ y u ∩ Tube δ y' u') ≤ ENNReal.ofReal (δ ^ 2 / 2) := by
    calc volume (Tube δ y u ∩ Tube δ y' u') ≤ _ :=
          measure_mono (inter_subset_closeParams δ y u y' u')
      _ ≤ _ := hvol
      _ ≤ ENNReal.ofReal (δ ^ 2 / 2) := by
        apply ENNReal.ofReal_le_ofReal
        have : 128 * (2 * (1 / 1024) + δ) ≤ 1 / 2 := by linarith
        nlinarith [sq_nonneg δ]
  exact absurd hbig (not_lt.mpr hle)

/-- The extended axis segment used as a container. -/
def extSeg (y u : Space) : Set Space := segment ℝ (y - (2 : ℝ) • u) (y + (3 : ℝ) • u)

theorem mem_extSeg {y u : Space} {l : ℝ} (hl : l ∈ Icc (-2 : ℝ) 3) : y + l • u ∈ extSeg y u := by
  rw [extSeg, segment_eq_image']
  refine ⟨(l + 2) / 5, ⟨by linarith [hl.1], by linarith [hl.2]⟩, ?_⟩
  simp only
  have : y + (3 : ℝ) • u - (y - (2 : ℝ) • u) = (5 : ℝ) • u := by module
  rw [this, smul_smul]
  have : (l + 2) / 5 * 5 = l + 2 := by ring
  rw [this]
  module

/-- **Crossing lemma.** A unit tube meeting another one in volume more than `δ² / 2` lies in the
`5000 δ`-neighbourhood of the extended axis of the other one. -/
theorem crossing {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10000) {y u y' u' : Space}
    (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1)
    (hbig : ENNReal.ofReal (δ ^ 2 / 2) < volume (Tube δ y u ∩ Tube δ y' u')) :
    Tube δ y' u' ⊆ thickening (5000 * δ) (extSeg y u) := by
  obtain ⟨s, hs, t, ht, hst⟩ := wide_of_big hδ hδ1 hu' hbig
  obtain ⟨qs, hqs, hds⟩ := mem_thickening_iff.mp hs.2
  obtain ⟨qt, hqt, hdt⟩ := mem_thickening_iff.mp ht.2
  obtain ⟨α, hα, rfl⟩ := mem_segment_param.mp hqs
  obtain ⟨β, hβ, rfl⟩ := mem_segment_param.mp hqt
  intro p hp
  obtain ⟨τ, hτ, hpτ⟩ := mem_tube_iff.mp hp
  have hts : t - s ≠ 0 := by
    intro h0
    rw [abs_sub_comm, h0, abs_zero] at hst
    norm_num at hst
  set σ : ℝ := (τ - s) / (t - s) with hσdef
  have hσ : σ * (t - s) = τ - s := div_mul_cancel₀ _ hts
  have hσabs : |σ| ≤ 1024 := by
    rw [hσdef, abs_div, div_le_iff₀ (abs_pos.mpr hts)]
    have h1 : |τ - s| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hτ.1, hτ.2, hs.1.1, hs.1.2]
    rw [abs_sub_comm] at hst
    nlinarith
  set es : Space := y' + s • u' - (y + α • u) with hes
  set et : Space := y' + t • u' - (y + β • u) with het
  have hesn : ‖es‖ < 2 * δ := by rw [hes, ← dist_eq_norm]; exact hds
  have hetn : ‖et‖ < 2 * δ := by rw [het, ← dist_eq_norm]; exact hdt
  set l : ℝ := α + σ * (β - α) with hl
  have key : y' + τ • u' - (y + l • u) = es + σ • (et - es) := by
    rw [hes, het, hl, show τ = s + σ * (t - s) by rw [hσ]; ring]
    module
  have hclose : ‖y' + τ • u' - (y + l • u)‖ < 4098 * δ := by
    rw [key]
    calc ‖es + σ • (et - es)‖ ≤ ‖es‖ + |σ| * (‖et‖ + ‖es‖) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs]
          gcongr
          exact norm_sub_le _ _
      _ < 2 * δ + 1024 * (2 * δ + 2 * δ) := by
          have h4 : |σ| * (‖et‖ + ‖es‖) ≤ 1024 * (2 * δ + 2 * δ) :=
            mul_le_mul hσabs (by linarith) (by positivity) (by norm_num)
          linarith
      _ = 4098 * δ := by ring
  -- the comparison point stays on the extended axis
  have hlα : |l - α| ≤ 4100 * δ + 1 := by
    have h1 : |l - α| = ‖(y + l • u) - (y + α • u)‖ := by
      rw [show (y + l • u) - (y + α • u) = (l - α) • u by module, norm_smul, hu, mul_one,
        Real.norm_eq_abs]
    have h2 : ‖(y' + τ • u') - (y' + s • u')‖ ≤ 1 := by
      rw [show (y' + τ • u') - (y' + s • u') = (τ - s) • u' by module, norm_smul, hu', mul_one,
        Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hτ.1, hτ.2, hs.1.1, hs.1.2]
    rw [h1]
    calc ‖(y + l • u) - (y + α • u)‖
        ≤ ‖(y + l • u) - (y' + τ • u')‖ + ‖(y' + τ • u') - (y' + s • u')‖ +
            ‖(y' + s • u') - (y + α • u)‖ := by
          have := norm_sub_le_norm_sub_add_norm_sub (y + l • u) (y' + τ • u') (y + α • u)
          have h3 := norm_sub_le_norm_sub_add_norm_sub (y' + τ • u') (y' + s • u') (y + α • u)
          linarith
      _ ≤ 4098 * δ + 1 + 2 * δ := by
          rw [norm_sub_rev]
          have : ‖(y' + s • u') - (y + α • u)‖ = ‖es‖ := by rw [hes]
          rw [this]
          linarith
      _ = 4100 * δ + 1 := by ring
  have hlmem : l ∈ Icc (-2 : ℝ) 3 := by
    rw [abs_le] at hlα
    constructor <;> linarith [hα.1, hα.2]
  apply mem_thickening_iff.mpr
  refine ⟨y + l • u, mem_extSeg hlmem, ?_⟩
  calc dist p (y + l • u) ≤ dist p (y' + τ • u') + dist (y' + τ • u') (y + l • u) :=
        dist_triangle _ _ _
    _ < δ + 4098 * δ := by
        rw [dist_eq_norm (y' + τ • u')]
        linarith
    _ ≤ 5000 * δ := by linarith

/-- The extended axis is covered by five unit pieces. -/
theorem extSeg_subset (y u : Space) :
    extSeg y u ⊆ ⋃ k : Fin 5,
      (fun t : ℝ => (y + ((k : ℝ) - 2) • u) + t • u) '' Icc (0 : ℝ) 1 := by
  intro z hz
  rw [extSeg, segment_eq_image'] at hz
  obtain ⟨θ, hθ, rfl⟩ := hz
  set l : ℝ := 5 * θ - 2 with hl
  have hz : y - (2 : ℝ) • u + θ • (y + (3 : ℝ) • u - (y - (2 : ℝ) • u)) = y + l • u := by
    rw [hl]; module
  beta_reduce
  rw [hz, mem_iUnion]
  have hpiece : ∀ k : Fin 5, l ∈ Icc ((k : ℝ) - 2) ((k : ℝ) - 1) →
      y + l • u ∈ (fun t : ℝ => (y + ((k : ℝ) - 2) • u) + t • u) '' Icc (0 : ℝ) 1 := by
    intro k hk
    refine ⟨l - ((k : ℝ) - 2), ⟨by linarith [hk.1], by linarith [hk.2]⟩, ?_⟩
    simp only
    module
  have hθ0 := hθ.1
  have hθ1 := hθ.2
  rcases le_or_gt l (-1) with h1 | h1
  · exact ⟨0, hpiece 0 ⟨by simp; linarith, by simp; linarith⟩⟩
  rcases le_or_gt l 0 with h2 | h2
  · exact ⟨1, hpiece 1 ⟨by simp; linarith, by simp; linarith⟩⟩
  rcases le_or_gt l 1 with h3 | h3
  · exact ⟨2, hpiece 2 ⟨by norm_num; linarith, by norm_num; linarith⟩⟩
  rcases le_or_gt l 2 with h4 | h4
  · exact ⟨3, hpiece 3 ⟨by norm_num; linarith, by norm_num; linarith⟩⟩
  · exact ⟨4, hpiece 4 ⟨by norm_num; linarith, by norm_num; linarith⟩⟩

/-- The neighbourhood of the extended axis has volume `O(δ²)`. -/
theorem extSeg_thickening_volume {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 10000) (y u : Space)
    (hu : ‖u‖ = 1) :
    volume (thickening (5000 * δ) (extSeg y u)) ≤ ENNReal.ofReal (10 ^ 11 * δ ^ 2) := by
  have hr : 0 < 5000 * δ := by positivity
  have hpiece : ∀ k : Fin 5, volume (thickening (5000 * δ)
      ((fun t : ℝ => (y + ((k : ℝ) - 2) • u) + t • u) '' Icc (0 : ℝ) 1)) ≤
        ENNReal.ofReal (2 * 10 ^ 10 * δ ^ 2) := by
    intro k
    refine (WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper
      (y + ((k : ℝ) - 2) • u) u hu subset_rfl hr (A := 1) zero_le_one ?_).trans ?_
    · intro s hs t ht
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
    · apply ENNReal.ofReal_le_ofReal
      have : 128 * (2 * 1 + 5000 * δ) * (5000 * δ) ^ 2 =
          (128 * (2 + 5000 * δ) * 25000000) * δ ^ 2 := by ring
      rw [this]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg δ)
      nlinarith
  calc volume (thickening (5000 * δ) (extSeg y u))
      ≤ volume (⋃ k : Fin 5, thickening (5000 * δ)
          ((fun t : ℝ => (y + ((k : ℝ) - 2) • u) + t • u) '' Icc (0 : ℝ) 1)) := by
        rw [← thickening_iUnion]
        exact measure_mono (thickening_subset_of_subset _ (extSeg_subset y u))
    _ ≤ ∑ k : Fin 5, volume (thickening (5000 * δ)
          ((fun t : ℝ => (y + ((k : ℝ) - 2) • u) + t • u) '' Icc (0 : ℝ) 1)) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _k : Fin 5, ENNReal.ofReal (2 * 10 ^ 10 * δ ^ 2) := Finset.sum_le_sum fun k _ => hpiece k
    _ = ENNReal.ofReal (10 ^ 11 * δ ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show ((5 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 5 by simp, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

end WangZahlLot.Obl.wz_compact_offset_normalization
