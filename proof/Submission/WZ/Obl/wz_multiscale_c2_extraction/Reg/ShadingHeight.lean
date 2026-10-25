-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.ShadingHeight.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.FitSmoothing

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set MeasureTheory
open scoped ENNReal

noncomputable def shadingHeightMeasure {n : ℕ} (Y : Fin n → Set Space) : Measure ℝ :=
  ∑ i, Measure.map (fun p : Space => p 2) (volume.restrict (Y i))

def shadingHeights {n : ℕ} (Y : Fin n → Set Space) : Set ℝ :=
  (fun p : Space => p 2) '' (⋃ i, Y i)

def restrictShadingHeights {n : ℕ} (Y : Fin n → Set Space) (D : Set ℝ) : Fin n → Set Space :=
  fun i => Y i ∩ (fun p : Space => p 2) ⁻¹' D

theorem shadingHeightMeasure_apply {n : ℕ} (Y : Fin n → Set Space)
    {D : Set ℝ} (hD : MeasurableSet D) :
    shadingHeightMeasure Y D = ∑ i, volume (restrictShadingHeights Y D i) := by
  have hc : Continuous (fun p : Space => p 2) := by fun_prop
  simp only [shadingHeightMeasure, Measure.finsetSum_apply,
    Measure.map_apply hc.measurable hD, Measure.restrict_apply (hc.measurable hD),
    restrictShadingHeights, inter_comm]

theorem isCompact_shadingHeights {n : ℕ} {Y : Fin n → Set Space}
    (hY : ∀ i, IsCompact (Y i)) : IsCompact (shadingHeights Y) :=
  (isCompact_iUnion hY).image (by fun_prop)

theorem restrictShadingHeights_compact {n : ℕ} {Y : Fin n → Set Space}
    (hY : ∀ i, IsCompact (Y i)) {D : Set ℝ} (hD : IsCompact D) :
    ∀ i, IsCompact (restrictShadingHeights Y D i) :=
  fun i => (hY i).inter_right (hD.isClosed.preimage (by fun_prop))

theorem restrictShadingHeights_subset {n : ℕ} (Y : Fin n → Set Space) (D : Set ℝ) :
    ∀ i, restrictShadingHeights Y D i ⊆ Y i := fun _ => inter_subset_left

theorem shadingHeightMeasure_total {n : ℕ} {Y : Fin n → Set Space}
    (hY : ∀ i, IsCompact (Y i)) :
    shadingHeightMeasure Y (shadingHeights Y) = ∑ i, volume (Y i) := by
  rw [shadingHeightMeasure_apply Y (isCompact_shadingHeights hY).measurableSet]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply inter_eq_left.mpr
  intro p hp
  exact ⟨p, mem_iUnion.mpr ⟨i, hp⟩, rfl⟩

theorem shadingHeights_subset {n : ℕ} {Y : Fin n → Set Space}
    (hY : (⋃ i, Y i) ⊆ Metric.ball (0 : Space) 1) :
    shadingHeights Y ⊆ Icc (-1 : ℝ) 1 := by
  rintro z ⟨p, hp, rfl⟩
  have hp1 : ‖p‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hY hp
  exact abs_le.mp ((PiLp.norm_apply_le p 2).trans hp1.le)

/-- Retained height sets translate exactly into compact subshadings; the height
measure records the sum of shading volumes, including overlaps between tubes. -/
theorem smooth_shadings_from_affine_fits : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (t ζ L : ℝ) (n : ℕ) (Y : Fin n → Set Space) (f : ℝ → ℝ),
      0 < N → 0 < t → t ≤ 1 → 0 ≤ ζ → 0 ≤ L →
      (∀ i, IsCompact (Y i)) → (⋃ i, Y i) ⊆ Metric.ball (0 : Space) 1 →
      (∀ l u : ℝ, shadingHeightMeasure Y (Icc l u) ≤
        ENNReal.ofReal L * ENNReal.ofReal (u - l)) →
      (∀ z ∈ Icc (-1 : ℝ) 1, |f z| ≤ 3) →
      (∀ k : Fin N, AffineSlopeFit (t ^ (((k : ℝ) + 1) / N)) f Y) →
      ∃ (Z : Fin n → Set Space) (g : ℝ → ℝ),
        (∀ i, Z i ⊆ Y i) ∧ (∀ i, IsCompact (Z i)) ∧
        (∑ i, volume (Y i)) ≤ (∑ i, volume (Z i)) +
          ENNReal.ofReal (55 * N * L * (t ^ ζ + t ^ (1 / (2 * (N : ℝ))))) ∧
        ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ p ∈ ⋃ i, Z i, |f (p 2) - g (p 2)| ≤ t) ∧
        ∀ z, |g z| ≤ C * N * t ^ (-(1 / (N : ℝ) + 2 * ζ)) ∧
          |deriv g z| ≤ C * N * t ^ (-(1 / (N : ℝ) + 2 * ζ)) ∧
          |deriv (deriv g) z| ≤ C * N * t ^ (-(1 / (N : ℝ) + 2 * ζ)) := by
  obtain ⟨C, hC, hext⟩ := exists_smooth_from_affine_fits
  refine ⟨C, hC, ?_⟩
  intro N t ζ L n Y f hN ht ht1 hζ hL hY hYbox hmass hfb hfit
  choose B hgrid happrox using hfit
  have hDbox := shadingHeights_subset hYbox
  obtain ⟨D', g, hD'sub, hD'c, hret, hg, hgf, hgb⟩ :=
    hext N t ζ (shadingHeightMeasure Y) L (shadingHeights Y) f B
      hN ht ht1 hζ hL hmass (isCompact_shadingHeights hY) hDbox
      (fun z hz => hfb z (hDbox hz)) hgrid
      (fun k z hz => by obtain ⟨p, hp, rfl⟩ := hz; exact happrox k p hp)
  refine ⟨restrictShadingHeights Y D', g, restrictShadingHeights_subset Y D',
    restrictShadingHeights_compact hY hD'c, ?_, hg, ?_, hgb⟩
  · rwa [shadingHeightMeasure_total hY, shadingHeightMeasure_apply Y hD'c.measurableSet] at hret
  · intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact hgf (p 2) hi.2

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
