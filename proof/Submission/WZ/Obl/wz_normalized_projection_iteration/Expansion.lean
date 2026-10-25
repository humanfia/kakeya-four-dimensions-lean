-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_iteration.Expansion.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_iteration.Basic
import Submission.WZ.Obl.wz_normalized_projection_iteration.Iteration
import Submission.WZ.Obl.wz_direction_density_transfer

namespace WangZahlLot.Obl.wz_normalized_projection_iteration

open Set Metric MeasureTheory

/-- A tube has at most its cross-sectional area times the radius inside a ball. -/
theorem tube_inter_ball_volume_le {δ r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r)
    (x v c : Space) (hv : ‖v‖ = 1) :
    volume (Tube δ x v ∩ closedBall c r) ≤ ENNReal.ofReal (1152 * r * δ ^ 2) := by
  have hr : 0 < r := hδ.trans_le hδr
  let T : Set ℝ := {t | t ∈ Icc 0 1 ∧ dist (x + t • v) c ≤ r + δ}
  have hT : T ⊆ Icc 0 1 := fun _ ht => ht.1
  have hdiam : ∀ s ∈ T, ∀ t ∈ T, dist s t ≤ 2 * (r + δ) := by
    intro s hs t ht
    rw [← WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.dist_segment_param x v hv]
    have htri := dist_triangle (x + s • v) c (x + t • v)
    rw [dist_comm c (x + t • v)] at htri
    linarith [hs.2, ht.2]
  have hsub : Tube δ x v ∩ closedBall c r ⊆
      thickening δ ((fun t : ℝ => x + t • v) '' T) := by
    intro p hp
    obtain ⟨z, hz, hpz⟩ := mem_thickening_iff.mp hp.1
    rw [segment_eq_image'] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    simp only [add_sub_cancel_left] at hpz
    have hpc : dist p c ≤ r := hp.2
    apply mem_thickening_iff.mpr
    refine ⟨x + t • v, ⟨t, ⟨ht, ?_⟩, rfl⟩, hpz⟩
    have htri := dist_triangle (x + t • v) p c
    rw [dist_comm (x + t • v) p] at htri
    linarith
  calc
    _ ≤ volume (thickening δ ((fun t : ℝ => x + t • v) '' T)) := measure_mono hsub
    _ ≤ ENNReal.ofReal (128 * (2 * (2 * (r + δ)) + δ) * δ ^ 2) :=
      WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper x v hv hT
        hδ (by positivity) hdiam
    _ ≤ ENNReal.ofReal (1152 * r * δ ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith [sq_nonneg δ, mul_nonneg (sq_nonneg δ) (sub_nonneg.mpr hδr)]

/-- Thickening a shading of a thin tube gains two powers of the radius ratio. -/
theorem tube_shading_expansion {δ r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r)
    (x v : Space) (hv : ‖v‖ = 1) {Y : Set Space}
    (hY : Y ⊆ Tube δ x v) (hYb : Y ⊆ ball 0 1) :
    ENNReal.ofReal (r ^ 2) * volume Y ≤
      ENNReal.ofReal (4608 * δ ^ 2) * volume (thickening r Y) := by
  classical
  have hr : 0 < r := hδ.trans_le hδr
  obtain ⟨F, hFY, hsep, hcover⟩ :=
    WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.exists_finset_separated_cover
      ((isCompact_closedBall (0 : Space) 1).totallyBounded.subset
        (hYb.trans ball_subset_closedBall)) hr
  have hsub : Y ⊆ ⋃ p ∈ F, Tube δ x v ∩ closedBall p r := by
    intro y hy
    obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp (hcover hy)
    exact mem_iUnion₂.mpr ⟨p, hp, hY hy, hyp⟩
  have hupper : volume Y ≤ ENNReal.ofReal ((F.card : ℝ) * (1152 * r * δ ^ 2)) := by
    calc
      _ ≤ ∑ p ∈ F, volume (Tube δ x v ∩ closedBall p r) :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
      _ ≤ ∑ _p ∈ F, ENNReal.ofReal (1152 * r * δ ^ 2) :=
        Finset.sum_le_sum (fun p _ => tube_inter_ball_volume_le hδ hδr x v p hv)
      _ = _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
        simp
  have hdisj : (F : Set Space).PairwiseDisjoint (fun p => ball p (r / 2)) := by
    intro p hp q hq hpq
    apply ball_disjoint_ball
    linarith [hsep p hp q hq hpq]
  have hsub' : (⋃ p ∈ F, ball p (r / 2)) ⊆ thickening r Y := by
    intro y hy
    obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp hy
    apply mem_thickening_iff.mpr
    exact ⟨p, hFY hp, (show dist y p < r / 2 from hyp).trans (by linarith)⟩
  have hlower : ENNReal.ofReal ((F.card : ℝ) * r ^ 3 / 4) ≤ volume (thickening r Y) := by
    calc
      _ ≤ ENNReal.ofReal ((F.card : ℝ) * ((r / 2) ^ 3 * (Real.pi * 4 / 3))) := by
        apply ENNReal.ofReal_le_ofReal
        have hpi := Real.pi_gt_three.le
        have hmul := mul_le_mul_of_nonneg_left hpi (show 0 ≤ (F.card : ℝ) * r ^ 3 by positivity)
        nlinarith [show 0 ≤ (F.card : ℝ) * r ^ 3 by positivity]
      _ = volume (⋃ p ∈ F, ball p (r / 2)) := by
        rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)]
        simp only [EuclideanSpace.volume_ball_fin_three]
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
        simp
      _ ≤ volume (thickening r Y) := measure_mono hsub'
  calc
    _ ≤ ENNReal.ofReal (r ^ 2) * ENNReal.ofReal ((F.card : ℝ) * (1152 * r * δ ^ 2)) :=
      mul_le_mul_right hupper _
    _ = ENNReal.ofReal (4608 * δ ^ 2) * ENNReal.ofReal ((F.card : ℝ) * r ^ 3 / 4) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_right hlower _

/-- Increasing a planar thickening by a fixed factor costs only a fixed area factor. -/
theorem planar_thickening_doubling {E : Set (ℝ × ℝ)} (hE : TotallyBounded E)
    {r L : ℝ} (hr : 0 < r) (hL : 0 ≤ L) :
    volume (thickening (L * r) E) ≤
      ENNReal.ofReal (4 * (L + 1) ^ 2) * volume (thickening r E) := by
  classical
  obtain ⟨F, hFE, hsep, hcover⟩ :=
    WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.exists_finset_separated_cover hE hr
  have hsub : thickening (L * r) E ⊆ ⋃ p ∈ F, ball p ((L + 1) * r) := by
    intro z hz
    obtain ⟨y, hy, hzy⟩ := mem_thickening_iff.mp hz
    obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp (hcover hy)
    apply mem_iUnion₂.mpr
    refine ⟨p, hp, ?_⟩
    rw [mem_ball]
    have htri := dist_triangle z y p
    have hyp' : dist y p ≤ r := hyp
    nlinarith
  have hupper : volume (thickening (L * r) E) ≤
      ENNReal.ofReal ((F.card : ℝ) * (4 * ((L + 1) * r) ^ 2)) := by
    calc
      _ ≤ ∑ p ∈ F, volume (ball p ((L + 1) * r)) :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
      _ = _ := by
        simp only [planar_ball_volume (r := (L + 1) * r) (hr := by positivity)]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
        simp
  have hdisj : (F : Set (ℝ × ℝ)).PairwiseDisjoint (fun p => ball p (r / 2)) := by
    intro p hp q hq hpq
    apply ball_disjoint_ball
    linarith [hsep p hp q hq hpq]
  have hsub' : (⋃ p ∈ F, ball p (r / 2)) ⊆ thickening r E := by
    intro z hz
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.mp hz
    apply mem_thickening_iff.mpr
    exact ⟨p, hFE hp, (show dist z p < r / 2 from hzp).trans (by linarith)⟩
  have hlower : ENNReal.ofReal ((F.card : ℝ) * r ^ 2) ≤ volume (thickening r E) := by
    calc
      _ = volume (⋃ p ∈ F, ball p (r / 2)) := by
        rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)]
        simp only [planar_ball_volume (r := r / 2) (hr := by positivity)]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
        simp only [Finset.sum_const, nsmul_eq_mul]
        congr 1
        ring
      _ ≤ _ := measure_mono hsub'
  calc
    _ ≤ ENNReal.ofReal ((F.card : ℝ) * (4 * ((L + 1) * r) ^ 2)) := hupper
    _ = ENNReal.ofReal (4 * (L + 1) ^ 2) * ENNReal.ofReal ((F.card : ℝ) * r ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_right hlower _

end WangZahlLot.Obl.wz_normalized_projection_iteration
