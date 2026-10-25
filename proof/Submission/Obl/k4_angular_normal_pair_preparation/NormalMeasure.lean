-- Adapted from this LOT tree, o104, session x0472, commit 48795996,
-- Submission/Obl/k4_terminal_time_extension/NormalMeasure.lean (cylinders and closed hidden bins)
-- and SatVolume.lean (`chartBox`, `continuous_chartBoxFun`).
import Submission.Obl.k4_angular_normal_pair_preparation.NormalBins
import Submission.Obl.k4_terminal_label_saturation.SatVolume

/-!
# Observation regions of one source chart on a longer block

For a source chart and a time interval `Icc a b` (the new block), the terminal
observations of its extrapolated incidences lie in

* the cylinder `{v | v 0 ∈ Icc a b ∧ ‖Q⁻¹ (y - c - t u)‖ ≤ κ'}`, of volume at most
  `(b - a) π κ'² |det Q|`;
* hidden bins whose closure meets the regular sublevel set of the source test,
  at most `16 (1 + ε / (β h))` per base point.

The set of such observations is measurable, and its `volume × count` measure is
bounded by the product of the two estimates.
-/

namespace Submission.Obl.k4_angular_normal_pair_preparation

open MeasureTheory Set MvPolynomial
open scoped ENNReal

-- Reuse the accepted spatial test and continuity theorem.
abbrev chartBox := Submission.Obl.k4_terminal_label_saturation.chartBox
abbrev continuous_chartBoxFun := Submission.Obl.k4_terminal_label_saturation.continuous_chartBoxFun

/-- The space-time cylinder over an interval. -/
def boxCylinder (a b κ : ℝ) (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  {v | v 0 ∈ Icc a b ∧ chartBox κ c u Q v}

theorem isClosed_boxCylinder (a b κ : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) : IsClosed (boxCylinder a b κ c u Q) := by
  have h0 : Continuous (fun v : EuclideanSpace ℝ (Fin 3) => v 0) := by fun_prop
  exact (isClosed_Icc.preimage h0).inter
    (isClosed_le (continuous_chartBoxFun c u Q) continuous_const)

theorem volume_boxCylinder_le (a b κ : ℝ) (hκ : 0 ≤ κ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0) :
    volume (boxCylinder a b κ c u Q) ≤
      ENNReal.ofReal ((b - a) * (Real.pi * κ ^ 2 * |Q.det|)) := by
  let e : EuclideanSpace ℝ (Fin 3) ≃ᵐ ℝ × (Fin 2 → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)
  have he : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).comp
      (PiLp.volume_preserving_ofLp (Fin 3))
  have he_apply (v : EuclideanSpace ℝ (Fin 3)) :
      e v = (v 0, fun i : Fin 2 => v i.succ) := by
    rfl
  let C : Set (ℝ × (Fin 2 → ℝ)) := {z | z.1 ∈ Icc a b ∧
    ‖(Q⁻¹).toEuclideanLin (WithLp.toLp 2 (fun i => z.2 i - c i - z.1 * u i))‖ ≤ κ}
  have hset : boxCylinder a b κ c u Q = e ⁻¹' C := by
    ext v
    simp only [boxCylinder, chartBox, Submission.Obl.k4_terminal_label_saturation.chartBox, mem_ofPred_eq, mem_preimage, he_apply, C]
    have hv : (WithLp.toLp 2 ![v 1, v 2] - c - (v 0) • u : EuclideanSpace ℝ (Fin 2)) =
        WithLp.toLp 2 (fun i : Fin 2 => v i.succ - c i - v 0 * u i) := by
      ext i
      fin_cases i <;> simp
    rw [hv]
  have hCmeas : MeasurableSet C := by
    have hcont : Continuous (fun z : ℝ × (Fin 2 → ℝ) =>
        ‖(Q⁻¹).toEuclideanLin (WithLp.toLp 2 (fun i => z.2 i - c i - z.1 * u i))‖) := by
      have hlin : Continuous (Q⁻¹).toEuclideanLin :=
        LinearMap.continuous_of_finiteDimensional _
      have hc : Continuous (fun z : ℝ × (Fin 2 → ℝ) =>
          (WithLp.toLp 2 (fun i => z.2 i - c i - z.1 * u i) : EuclideanSpace ℝ (Fin 2))) := by
        apply (PiLp.continuous_toLp 2 _).comp
        fun_prop
      exact (hlin.comp hc).norm
    exact (measurable_fst measurableSet_Icc).inter
      (measurableSet_le hcont.measurable measurable_const)
  rw [hset, he.measure_preimage_emb e.measurableEmbedding]
  change ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))) C ≤ _
  rw [Measure.prod_apply hCmeas]
  have hfib (t : ℝ) : volume (Prod.mk t ⁻¹' C) ≤
      (Icc a b).indicator (fun _ => ENNReal.ofReal (Real.pi * κ ^ 2 * |Q.det|)) t := by
    by_cases ht : t ∈ Icc a b
    · rw [indicator_of_mem ht]
      have hs : Prod.mk t ⁻¹' C = {y : Fin 2 → ℝ | ‖(Q⁻¹).toEuclideanLin
          (WithLp.toLp 2 (fun i => y i - c i - t * u i))‖ ≤ κ} := by
        ext y
        simp only [C, mem_preimage, mem_ofPred_eq]
        exact ⟨fun h => h.2, fun h => ⟨ht, h⟩⟩
      rw [hs, Submission.Obl.k4_quadratic_slope_volume.volume_coordinate_ellipse Q hQ c u t κ hκ]
    · rw [indicator_of_notMem ht]
      have hs : Prod.mk t ⁻¹' C = ∅ := by
        ext y
        simp only [C, mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun h => absurd h ht
      rw [hs, measure_empty]
  calc ∫⁻ t, volume (Prod.mk t ⁻¹' C) ≤
        ∫⁻ t, (Icc a b).indicator (fun _ => ENNReal.ofReal (Real.pi * κ ^ 2 * |Q.det|)) t :=
        lintegral_mono hfib
    _ = ENNReal.ofReal (Real.pi * κ ^ 2 * |Q.det|) * volume (Icc a b) :=
        lintegral_indicator_const measurableSet_Icc _
    _ = ENNReal.ofReal ((b - a) * (Real.pi * κ ^ 2 * |Q.det|)) := by
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- Observations whose closed hidden bin meets the regular sublevel set of `R`. -/
def hidClosed (R : MvPolynomial (Fin 4) ℝ) (ε β h : ℝ) :
    Set (EuclideanSpace ℝ (Fin 3) × ℤ) :=
  {o | ∃ w ∈ Icc ((o.2 : ℝ) * h) (((o.2 : ℝ) + 1) * h),
    |eval ![o.1 0, o.1 1, o.1 2, w] R| ≤ ε ∧
      β ≤ |eval ![o.1 0, o.1 1, o.1 2, w] (pderiv 3 R)|}

/-- For a fixed bin, the base points of `hidClosed` form a closed set
(projection along a compact bin). -/
theorem isClosed_hidClosed_fibre (R : MvPolynomial (Fin 4) ℝ) (ε β h : ℝ) (n : ℤ) :
    IsClosed {v : EuclideanSpace ℝ (Fin 3) | (v, n) ∈ hidClosed R ε β h} := by
  set K := Icc ((n : ℝ) * h) (((n : ℝ) + 1) * h) with hK
  have : CompactSpace K := isCompact_iff_compactSpace.mp isCompact_Icc
  set P : Set (EuclideanSpace ℝ (Fin 3) × K) := {q |
    |eval ![q.1 0, q.1 1, q.1 2, (q.2 : ℝ)] R| ≤ ε ∧
      β ≤ |eval ![q.1 0, q.1 1, q.1 2, (q.2 : ℝ)] (pderiv 3 R)|} with hP
  have hcont (S : MvPolynomial (Fin 4) ℝ) : Continuous (fun q : EuclideanSpace ℝ (Fin 3) × K =>
      eval ![q.1 0, q.1 1, q.1 2, (q.2 : ℝ)] S) := by
    apply S.continuous_eval.comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp
    all_goals fun_prop
  have hPc : IsClosed P :=
    (isClosed_le (hcont R).abs continuous_const).inter
      (isClosed_le continuous_const (hcont _).abs)
  have himg : {v : EuclideanSpace ℝ (Fin 3) | (v, n) ∈ hidClosed R ε β h} = Prod.fst '' P := by
    ext v
    simp only [hidClosed, mem_ofPred_eq, mem_image, hP, Prod.exists]
    constructor
    · rintro ⟨w, hw, h1, h2⟩
      exact ⟨v, ⟨w, hw⟩, ⟨h1, h2⟩, rfl⟩
    · rintro ⟨v', ⟨w, hw⟩, ⟨h1, h2⟩, rfl⟩
      exact ⟨w, hw, h1, h2⟩
  rw [himg]
  exact isClosedMap_fst_of_compactSpace P hPc

theorem measurableSet_hidClosed (R : MvPolynomial (Fin 4) ℝ) (ε β h : ℝ) :
    MeasurableSet (hidClosed R ε β h) := by
  have heq : hidClosed R ε β h = ⋃ n : ℤ,
      (Prod.fst ⁻¹' {v : EuclideanSpace ℝ (Fin 3) | (v, n) ∈ hidClosed R ε β h} ∩
        Prod.snd ⁻¹' {n}) := by
    ext o
    simp only [mem_iUnion, mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · intro ho
      exact ⟨o.2, by simpa using ho, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      simpa using hn
  rw [heq]
  exact MeasurableSet.iUnion (fun n =>
    (measurable_fst (isClosed_hidClosed_fibre R ε β h n).measurableSet).inter
      (measurable_snd (measurableSet_singleton n)))

/-- The number of closed hidden bins over one base point. -/
theorem hidClosed_card_le (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    {ε β h : ℝ} (hε : 0 ≤ ε) (hβ : 0 < β) (hh : 0 < h) (v : EuclideanSpace ℝ (Fin 3)) :
    {n : ℤ | (v, n) ∈ hidClosed R ε β h}.Finite ∧
      (({n : ℤ | (v, n) ∈ hidClosed R ε β h}.ncard : ℕ) : ℝ) ≤ 16 * (1 + ε / (β * h)) := by
  have hset : {n : ℤ | (v, n) ∈ hidClosed R ε β h} =
      {n : ℤ | ∃ w ∈ Icc ((n : ℝ) * h) (((n : ℝ) + 1) * h),
        |(hiddenSlice R (v 0) (v 1) (v 2)).eval w| ≤ ε ∧
        β ≤ |(hiddenSlice R (v 0) (v 1) (v 2)).derivative.eval w|} := by
    ext n
    simp only [hidClosed, mem_ofPred_eq, hiddenSlice_eval, hiddenSlice_derivative]
  rw [hset]
  exact closed_bins_card_le _ (hiddenSlice_natDegree R hR _ _ _) hε hβ hh

/-- The `volume × count` measure of observations in a cylinder whose closed hidden
bin meets the regular sublevel set of `R`. -/
theorem volume_cylinder_hidClosed_le (a b κ : ℝ) (hκ : 0 ≤ κ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0) (R : MvPolynomial (Fin 4) ℝ)
    (hR : R.totalDegree ≤ 2) {ε β h : ℝ} (hε : 0 ≤ ε) (hβ : 0 < β) (hh : 0 < h) :
    ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count)
        ((Prod.fst ⁻¹' boxCylinder a b κ c u Q) ∩ hidClosed R ε β h) ≤
      ENNReal.ofReal ((b - a) * (Real.pi * κ ^ 2 * |Q.det|) * (16 * (1 + ε / (β * h)))) := by
  have hmeas : MeasurableSet ((Prod.fst ⁻¹' boxCylinder a b κ c u Q) ∩ hidClosed R ε β h) :=
    (measurable_fst (isClosed_boxCylinder a b κ c u Q).measurableSet).inter
      (measurableSet_hidClosed R ε β h)
  rw [Measure.prod_apply hmeas]
  have hcount (v : EuclideanSpace ℝ (Fin 3)) :
      Measure.count (Prod.mk v ⁻¹' ((Prod.fst ⁻¹' boxCylinder a b κ c u Q) ∩ hidClosed R ε β h))
        ≤ (boxCylinder a b κ c u Q).indicator
          (fun _ => ENNReal.ofReal (16 * (1 + ε / (β * h)))) v := by
    by_cases hv : v ∈ boxCylinder a b κ c u Q
    · rw [indicator_of_mem hv]
      have hs : Prod.mk v ⁻¹' ((Prod.fst ⁻¹' boxCylinder a b κ c u Q) ∩ hidClosed R ε β h) =
          {n : ℤ | (v, n) ∈ hidClosed R ε β h} := by
        ext n
        simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq]
        exact ⟨fun h' => h'.2, fun h' => ⟨hv, h'⟩⟩
      rw [hs]
      obtain ⟨hfin, hcard⟩ := hidClosed_card_le R hR hε hβ hh v
      rw [Measure.count_apply_finite _ hfin, ← ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      rw [← Set.ncard_eq_toFinset_card _ hfin]
      exact hcard
    · rw [indicator_of_notMem hv]
      have hs : Prod.mk v ⁻¹' ((Prod.fst ⁻¹' boxCylinder a b κ c u Q) ∩ hidClosed R ε β h) =
          ∅ := by
        ext n
        simp only [mem_preimage, mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
        exact fun h' => absurd h' hv
      rw [hs, measure_empty]
  calc ∫⁻ v, Measure.count (Prod.mk v ⁻¹'
        ((Prod.fst ⁻¹' boxCylinder a b κ c u Q) ∩ hidClosed R ε β h)) ≤
        ∫⁻ v, (boxCylinder a b κ c u Q).indicator
          (fun _ => ENNReal.ofReal (16 * (1 + ε / (β * h)))) v := lintegral_mono hcount
    _ = ENNReal.ofReal (16 * (1 + ε / (β * h))) * volume (boxCylinder a b κ c u Q) :=
        lintegral_indicator_const (isClosed_boxCylinder a b κ c u Q).measurableSet _
    _ ≤ ENNReal.ofReal (16 * (1 + ε / (β * h))) *
          ENNReal.ofReal ((b - a) * (Real.pi * κ ^ 2 * |Q.det|)) :=
        mul_le_mul' le_rfl (volume_boxCylinder_le a b κ hκ c u Q hQ)
    _ = ENNReal.ofReal ((b - a) * (Real.pi * κ ^ 2 * |Q.det|) * (16 * (1 + ε / (β * h)))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end Submission.Obl.k4_angular_normal_pair_preparation
