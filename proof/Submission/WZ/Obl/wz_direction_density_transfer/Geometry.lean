-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_direction_density_transfer.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_direction_density_transfer.Basic
import Submission.WZ.Obl.kakeya_three_le_dimH_of_tube_estimate.Packing

namespace WangZahlLot.Obl.wz_direction_density_transfer

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

private theorem scale_nonneg_sep {u w : Space} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    {a b θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hsep : θ ≤ ‖u - w‖) :
    θ * a ≤ 2 * ‖a • u - b • w‖ := by
  have hab : |a - b| ≤ ‖a • u - b • w‖ := by
    simpa [norm_smul, hu, hw, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
      using abs_norm_sub_norm_le (a • u) (b • w)
  have ht : a * ‖u - w‖ ≤ ‖a • u - b • w‖ + |a - b| := by
    calc
      a * ‖u - w‖ = ‖a • u - a • w‖ := by
        rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
      _ ≤ ‖a • u - b • w‖ + ‖b • w - a • w‖ := by
        simpa [dist_eq_norm] using dist_triangle (a • u) (b • w) (a • w)
      _ = ‖a • u - b • w‖ + |a - b| := by
        rw [← sub_smul, norm_smul, Real.norm_eq_abs, hw, mul_one, abs_sub_comm]
  nlinarith

/-- Separation of unoriented unit vectors controls all scalar multiples. -/
theorem scale_sep {u w : Space} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    {a b θ : ℝ} (hsub : θ ≤ ‖u - w‖) (hadd : θ ≤ ‖u + w‖) :
    θ * |a| ≤ 2 * ‖a • u - b • w‖ := by
  have hpos : ∀ (u w : Space) (a b : ℝ), ‖u‖ = 1 → ‖w‖ = 1 → 0 ≤ a →
      θ ≤ ‖u - w‖ → θ ≤ ‖u + w‖ → θ * a ≤ 2 * ‖a • u - b • w‖ := by
    intro u w a b hu hw ha hsub hadd
    rcases le_or_gt 0 b with hb | hb
    · exact scale_nonneg_sep hu hw ha hb hsub
    · simpa using scale_nonneg_sep hu (show ‖-w‖ = 1 by simpa using hw) ha
        (show 0 ≤ -b by linarith) (show θ ≤ ‖u - -w‖ by simpa using hadd)
  rcases le_or_gt 0 a with ha | ha
  · simpa [abs_of_nonneg ha] using hpos u w a b hu hw ha hsub hadd
  · have h₁ : θ ≤ ‖-u - w‖ := by
      rw [show -u - w = -(u + w) by abel, norm_neg]
      exact hadd
    have h₂ : θ ≤ ‖-u + w‖ := by
      rw [show -u + w = -(u - w) by abel, norm_neg]
      exact hsub
    simpa [abs_of_neg ha] using hpos (-u) w (-a) b (by simpa using hu) hw
      (by linarith) h₁ h₂

/-- A unit tube has volume at least its squared radius. -/
theorem tube_volume_lower {δ : ℝ} (hδ : 0 < δ) (x v : Space) (hv : ‖v‖ = 1) :
    ENNReal.ofReal (δ ^ 2) ≤ volume (Tube δ x v) := by
  have h := WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.segment_shading_volume_lower
    x v hv (T := Icc 0 1) Subset.rfl (r := 2 * δ) (a := 1) (by positivity) (by simp)
  have hseg : (fun t : ℝ => x + t • v) '' Icc 0 1 = segment ℝ x (x + v) := by
    rw [segment_eq_image']
    simp
  have heq : (1 : ℝ) * (2 * δ) ^ 2 / 4 = δ ^ 2 := by ring
  simpa only [hseg, mul_div_cancel_left₀ δ (by norm_num : (2 : ℝ) ≠ 0), heq] using h

/-- Nearby points on two well-separated segments force nearby parameters. -/
theorem parameter_diameter {δ : ℝ} (hδ : 0 < δ) {x v y w : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hsub : 100000 * δ ≤ ‖v - w‖) (hadd : 100000 * δ ≤ ‖v + w‖)
    {s t : ℝ}
    (hs : x + s • v ∈ thickening (2 * δ) (segment ℝ y (y + w)))
    (ht : x + t • v ∈ thickening (2 * δ) (segment ℝ y (y + w))) :
    dist s t ≤ 1 / 10000 := by
  obtain ⟨p, hp, hsp⟩ := mem_thickening_iff.mp hs
  obtain ⟨q, hq, htq⟩ := mem_thickening_iff.mp ht
  rw [segment_eq_image'] at hp hq
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨b, hb, rfl⟩ := hq
  simp only [add_sub_cancel_left, dist_eq_norm] at hsp htq
  have hd : ‖(s - t) • v - (a - b) • w‖ < 4 * δ := by
    have heq : (s - t) • v - (a - b) • w =
        (x + s • v - (y + a • w)) - (x + t • v - (y + b • w)) := by module
    rw [heq]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  have hscl := scale_sep (a := s - t) (b := a - b) hv hw hsub hadd
  rw [Real.dist_eq]
  nlinarith [abs_nonneg (s - t)]

/-- A thickened portion of a segment is controlled by the diameter of its parameters. -/
theorem segment_piece_volume_upper (x v : Space) (hv : ‖v‖ = 1)
    {T : Set ℝ} (hT : T ⊆ Icc 0 1) {r A : ℝ} (hr : 0 < r) (hA : 0 ≤ A)
    (hdiam : ∀ s ∈ T, ∀ t ∈ T, dist s t ≤ A) :
    volume (thickening r ((fun t : ℝ => x + t • v) '' T)) ≤
      ENNReal.ofReal (128 * (2 * A + r) * r ^ 2) := by
  classical
  obtain ⟨F, hFT, hsep, hcover⟩ :=
    WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.exists_finset_separated_cover
      ((totallyBounded_Icc 0 1).subset hT) hr
  have hcard : (F.card : ℝ) * r ≤ 2 * A + r := by
    rcases F.eq_empty_or_nonempty with hF | hF
    · simp only [hF, Finset.card_empty, Nat.cast_zero, zero_mul]
      positivity
    obtain ⟨t₀, ht₀⟩ := hF
    have hd : (F : Set ℝ).PairwiseDisjoint (fun t => ball t (r / 2)) := by
      intro s hs t ht hst
      apply ball_disjoint_ball
      linarith [hsep s hs t ht hst]
    have hs : (⋃ t ∈ F, ball t (r / 2)) ⊆ ball t₀ (A + r / 2) := by
      intro z hz
      obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp hz
      rw [mem_ball] at hzt ⊢
      exact (dist_triangle z t t₀).trans_lt (by linarith [hdiam t (hFT ht) t₀ (hFT ht₀)])
    have hm := measure_mono (μ := volume) hs
    rw [measure_biUnion_finset hd (fun _ _ => measurableSet_ball)] at hm
    simp only [Real.volume_ball] at hm
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)] at hm
    simp only [Finset.sum_const, nsmul_eq_mul] at hm
    have hreal := (ENNReal.ofReal_le_ofReal_iff (show 0 ≤ 2 * (A + r / 2) by positivity)).mp hm
    nlinarith
  have hsub : thickening r ((fun t : ℝ => x + t • v) '' T) ⊆
      ⋃ t ∈ F, ball (x + t • v) (2 * r) := by
    intro z hz
    obtain ⟨_, ⟨t, ht, rfl⟩, hzt⟩ := mem_thickening_iff.mp hz
    obtain ⟨s, hs, hts⟩ := mem_iUnion₂.mp (hcover ht)
    refine mem_iUnion₂.mpr ⟨s, hs, ?_⟩
    rw [mem_closedBall] at hts
    rw [mem_ball]
    have hdist := WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.dist_segment_param x v hv t s
    exact (dist_triangle z (x + t • v) (x + s • v)).trans_lt (by linarith)
  calc
    volume (thickening r ((fun t : ℝ => x + t • v) '' T)) ≤
        ∑ t ∈ F, volume (ball (x + t • v) (2 * r)) :=
      (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ = ENNReal.ofReal ((F.card : ℝ) * ((2 * r) ^ 3 * (Real.pi * 4 / 3))) := by
      simp only [EuclideanSpace.volume_ball_fin_three]
      rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
      simp
    _ ≤ ENNReal.ofReal (128 * (2 * A + r) * r ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        (F.card : ℝ) * ((2 * r) ^ 3 * (Real.pi * 4 / 3)) ≤
            (F.card : ℝ) * ((2 * r) ^ 3 * 16) := by
          gcongr
          linarith [Real.pi_lt_four]
        _ = ((F.card : ℝ) * r) * (128 * r ^ 2) := by ring
        _ ≤ (2 * A + r) * (128 * r ^ 2) := by gcongr
        _ = _ := by ring

/-- Tubes with line directions separated by a large fixed multiple of their radius
have intersection at most half the volume of the first tube. -/
theorem intersection_le_half {δ : ℝ} (hδ : 0 < δ) {x v y w : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hsub : 100000 * δ ≤ ‖v - w‖) (hadd : 100000 * δ ≤ ‖v + w‖) :
    volume (Tube δ x v ∩ Tube δ y w) ≤ (1 / 2 : ℝ≥0∞) * volume (Tube δ x v) := by
  let T : Set ℝ := {t | t ∈ Icc 0 1 ∧ x + t • v ∈ thickening (2 * δ) (segment ℝ y (y + w))}
  have hT : T ⊆ Icc 0 1 := fun _ ht => ht.1
  have hdiam : ∀ s ∈ T, ∀ t ∈ T, dist s t ≤ 1 / 10000 :=
    fun _ hs _ ht => parameter_diameter hδ hv hw hsub hadd hs.2 ht.2
  have hsubT : Tube δ x v ∩ Tube δ y w ⊆ thickening δ ((fun t : ℝ => x + t • v) '' T) := by
    intro p hp
    obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp.1
    obtain ⟨z, hz, hpz⟩ := mem_thickening_iff.mp hp.2
    rw [segment_eq_image'] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    simp only [add_sub_cancel_left] at hpq
    apply mem_thickening_iff.mpr
    refine ⟨x + t • v, ⟨t, ⟨ht, ?_⟩, rfl⟩, hpq⟩
    apply mem_thickening_iff.mpr
    refine ⟨z, hz, ?_⟩
    have := dist_triangle (x + t • v) p z
    rw [dist_comm (x + t • v) p] at this
    linarith
  have hδsmall : δ ≤ 1 / 50000 := by
    have h := norm_sub_le v w
    rw [hv, hw] at h
    linarith
  calc
    volume (Tube δ x v ∩ Tube δ y w) ≤
        volume (thickening δ ((fun t : ℝ => x + t • v) '' T)) := measure_mono hsubT
    _ ≤ ENNReal.ofReal (128 * (2 * (1 / 10000) + δ) * δ ^ 2) :=
      segment_piece_volume_upper x v hv hT hδ (by norm_num) hdiam
    _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg δ)
      linarith
    _ = (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (δ ^ 2) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    _ ≤ (1 / 2 : ℝ≥0∞) * volume (Tube δ x v) := by
      gcongr
      exact tube_volume_lower hδ x v hv

end WangZahlLot.Obl.wz_direction_density_transfer
