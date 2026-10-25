-- Adapted from this LOT tree, obligation o104, session x0472, commit 5cdf90d72f0b.
-- Original file: Submission/Obl/k4_terminal_time_extension/SatVolume.lean
import Submission.Obl.k4_terminal_label_saturation.SatBins
import Submission.Obl.k4_quadratic_slope_volume.SpatialVolume

/-!
# The observations compatible with one chart, and their volume

An observation at depth `L` is a point `(t, y₁, y₂)` of `ℝ³` together with a
hidden bin `n ∈ ℤ` of width `δ / B`.  A chart is compatible with it when the
time lies in the chart's dyadic block, the spatial point lies in the chart's
moving box, and the bin passes `hiddenBinTest`.  Under `volume × count` this set
has measure at most `2^-T * (π κ² |det Q|) * (14 + 48 κ²)`, the chart's own
space-time volume times a polynomial in the slack (paper Lemma 2.8).
-/

namespace Submission.Obl.k4_terminal_label_saturation

open MeasureTheory Set MvPolynomial
open scoped ENNReal

/-- The spatial test of a chart, in observation coordinates. -/
def chartBox (κ : ℝ) (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (v : EuclideanSpace ℝ (Fin 3)) : Prop :=
  ‖Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![v 1, v 2] - c - (v 0) • u)‖ ≤ κ

/-- The observations compatible with one chart. -/
def chartCompat (T : ℕ) (j κ δ B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (R : MvPolynomial (Fin 4) ℝ) :
    Set (EuclideanSpace ℝ (Fin 3) × ℤ) :=
  {o | o.1 0 ∈ Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T) ∧ chartBox κ c u Q o.1 ∧
    hiddenBinTest R (o.1 0) (o.1 1) (o.1 2) (3 * κ * δ) (B / (2 * κ)) (δ / B) o.2}

theorem continuous_chartBoxFun (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    Continuous (fun v : EuclideanSpace ℝ (Fin 3) =>
      ‖Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![v 1, v 2] - c - (v 0) • u)‖) := by
  have hlin : Continuous (Matrix.toEuclideanLin Q⁻¹) :=
    LinearMap.continuous_of_finiteDimensional _
  have hcoord : Continuous (fun v : EuclideanSpace ℝ (Fin 3) =>
      WithLp.toLp 2 ![v 1, v 2] - c - (v 0) • u) := by
    have h1 : Continuous (fun v : EuclideanSpace ℝ (Fin 3) =>
        (WithLp.toLp 2 ![v 1, v 2] : EuclideanSpace ℝ (Fin 2))) := by
      apply (PiLp.continuous_toLp 2 _).comp
      apply continuous_pi
      intro i
      fin_cases i <;> simp <;> fun_prop
    fun_prop
  exact (hlin.comp hcoord).norm

theorem continuous_eval_obs (P : MvPolynomial (Fin 4) ℝ) (w : ℝ) :
    Continuous (fun v : EuclideanSpace ℝ (Fin 3) => eval ![v 0, v 1, v 2, w] P) := by
  apply P.continuous_eval.comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

/-- The fibre of `chartCompat` over one hidden bin is closed. -/
theorem isClosed_chartCompat_fibre (T : ℕ) (j κ δ B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (R : MvPolynomial (Fin 4) ℝ) (n : ℤ) :
    IsClosed {v : EuclideanSpace ℝ (Fin 3) | (v, n) ∈ chartCompat T j κ δ B c u Q R} := by
  have h0 : Continuous (fun v : EuclideanSpace ℝ (Fin 3) => v 0) := by fun_prop
  have hI : IsClosed {v : EuclideanSpace ℝ (Fin 3) |
      v 0 ∈ Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T)} :=
    isClosed_Icc.preimage h0
  have hbox : IsClosed {v : EuclideanSpace ℝ (Fin 3) | chartBox κ c u Q v} :=
    isClosed_le (continuous_chartBoxFun c u Q) continuous_const
  have hval : IsClosed {v : EuclideanSpace ℝ (Fin 3) |
      |eval ![v 0, v 1, v 2, (n : ℝ) * (δ / B)] R| ≤ 3 * κ * δ} :=
    isClosed_le (continuous_eval_obs R _).abs continuous_const
  have hder : IsClosed {v : EuclideanSpace ℝ (Fin 3) |
      |curvature R 3| * (δ / B) ≤ B / (2 * κ) →
        B / (2 * κ) ≤ |eval ![v 0, v 1, v 2, (n : ℝ) * (δ / B)] (pderiv 3 R)|} := by
    by_cases hlow : |curvature R 3| * (δ / B) ≤ B / (2 * κ)
    · simp only [hlow, forall_const]
      exact isClosed_le continuous_const (continuous_eval_obs _ _).abs
    · simp only [hlow, IsEmpty.forall_iff, setOf_true]
      exact isClosed_univ
  have heq : {v : EuclideanSpace ℝ (Fin 3) | (v, n) ∈ chartCompat T j κ δ B c u Q R} =
      {v | v 0 ∈ Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T)} ∩
        ({v | chartBox κ c u Q v} ∩
          ({v | |eval ![v 0, v 1, v 2, (n : ℝ) * (δ / B)] R| ≤ 3 * κ * δ} ∩
            {v | |curvature R 3| * (δ / B) ≤ B / (2 * κ) →
              B / (2 * κ) ≤ |eval ![v 0, v 1, v 2, (n : ℝ) * (δ / B)] (pderiv 3 R)|})) := by
    ext v
    simp only [chartCompat, hiddenBinTest, mem_ofPred_eq, mem_inter_iff]
  rw [heq]
  exact hI.inter (hbox.inter (hval.inter hder))

theorem measurableSet_chartCompat (T : ℕ) (j κ δ B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (R : MvPolynomial (Fin 4) ℝ) :
    MeasurableSet (chartCompat T j κ δ B c u Q R) := by
  have heq : chartCompat T j κ δ B c u Q R = ⋃ n : ℤ,
      (Prod.fst ⁻¹' {v : EuclideanSpace ℝ (Fin 3) | (v, n) ∈ chartCompat T j κ δ B c u Q R} ∩
        Prod.snd ⁻¹' {n}) := by
    ext o
    simp only [mem_iUnion, mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · intro ho
      exact ⟨o.2, by simpa using ho, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      simpa using hn
  rw [heq]
  refine MeasurableSet.iUnion (fun n => ?_)
  exact (measurable_fst (isClosed_chartCompat_fibre T j κ δ B c u Q R n).measurableSet).inter
    (measurable_snd (measurableSet_singleton n))

/-- The space-time cylinder of a chart. -/
def chartCylinder (T : ℕ) (j κ : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {v | v 0 ∈ Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T) ∧ chartBox κ c u Q v}

theorem volume_chartCylinder_le (T : ℕ) (j κ : ℝ) (hκ : 0 ≤ κ)
    (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0) :
    volume (chartCylinder T j κ c u Q) ≤
      ENNReal.ofReal (((2 : ℝ) ^ T)⁻¹ * (Real.pi * κ ^ 2 * |Q.det|)) := by
  -- split off the time coordinate
  let e : EuclideanSpace ℝ (Fin 3) ≃ᵐ ℝ × (Fin 2 → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)
  have he : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).comp
      (PiLp.volume_preserving_ofLp (Fin 3))
  have he_apply (v : EuclideanSpace ℝ (Fin 3)) :
      e v = (v 0, fun i : Fin 2 => v i.succ) := by
    rfl
  let C : Set (ℝ × (Fin 2 → ℝ)) := {z | z.1 ∈ Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T) ∧
    ‖(Q⁻¹).toEuclideanLin (WithLp.toLp 2 (fun i => z.2 i - c i - z.1 * u i))‖ ≤ κ}
  have hset : chartCylinder T j κ c u Q = e ⁻¹' C := by
    ext v
    simp only [chartCylinder, chartBox, mem_ofPred_eq, mem_preimage, he_apply, C]
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
      (Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T)).indicator
        (fun _ => ENNReal.ofReal (Real.pi * κ ^ 2 * |Q.det|)) t := by
    by_cases ht : t ∈ Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T)
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
        ∫⁻ t, (Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T)).indicator
          (fun _ => ENNReal.ofReal (Real.pi * κ ^ 2 * |Q.det|)) t := lintegral_mono hfib
    _ = ENNReal.ofReal (Real.pi * κ ^ 2 * |Q.det|) *
          volume (Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T)) :=
        lintegral_indicator_const measurableSet_Icc _
    _ = ENNReal.ofReal (((2 : ℝ) ^ T)⁻¹ * (Real.pi * κ ^ 2 * |Q.det|)) := by
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring

/-- The `volume × count` measure of the observations compatible with one chart. -/
theorem volume_chartCompat_le (T : ℕ) (j : ℝ) {κ δ B : ℝ} (hκ : 1 ≤ κ) (hδ : 0 < δ)
    (hB : 0 < B) (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (hQ : Q.det ≠ 0) (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2) :
    ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count)
        (chartCompat T j κ δ B c u Q R) ≤
      ENNReal.ofReal (((2 : ℝ) ^ T)⁻¹ * (Real.pi * κ ^ 2 * |Q.det|) * (14 + 48 * κ ^ 2)) := by
  have hκpos : 0 < κ := lt_of_lt_of_le one_pos hκ
  rw [Measure.prod_apply (measurableSet_chartCompat T j κ δ B c u Q R)]
  have hcount (v : EuclideanSpace ℝ (Fin 3)) :
      Measure.count (Prod.mk v ⁻¹' chartCompat T j κ δ B c u Q R) ≤
        (chartCylinder T j κ c u Q).indicator
          (fun _ => ENNReal.ofReal (14 + 48 * κ ^ 2)) v := by
    by_cases hv : v ∈ chartCylinder T j κ c u Q
    · rw [indicator_of_mem hv]
      have hs : Prod.mk v ⁻¹' chartCompat T j κ δ B c u Q R =
          {n : ℤ | hiddenBinTest R (v 0) (v 1) (v 2) (3 * κ * δ) (B / (2 * κ)) (δ / B) n} := by
        ext n
        simp only [chartCompat, mem_preimage, mem_ofPred_eq]
        exact ⟨fun h => h.2.2, fun h => ⟨hv.1, hv.2, h⟩⟩
      rw [hs]
      obtain ⟨hfin, hcard⟩ := hiddenBinTest_card_le R hR (v 0) (v 1) (v 2)
        (ε := 3 * κ * δ) (β := B / (2 * κ)) (h := δ / B) (by positivity) (by positivity)
        (by positivity)
      rw [Measure.count_apply_finite _ hfin]
      have hcard' : ((hfin.toFinset.card : ℕ) : ℝ) ≤ 14 + 48 * κ ^ 2 := by
        rw [Set.ncard_eq_toFinset_card _ hfin] at hcard
        calc ((hfin.toFinset.card : ℕ) : ℝ) ≤ 14 + 8 * (3 * κ * δ) / (B / (2 * κ) * (δ / B)) :=
              hcard
          _ = 14 + 48 * κ ^ 2 := by field_simp; ring
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hcard'
    · rw [indicator_of_notMem hv]
      have hs : Prod.mk v ⁻¹' chartCompat T j κ δ B c u Q R = ∅ := by
        ext n
        simp only [chartCompat, mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨h1, h2, _⟩
        exact hv ⟨h1, h2⟩
      rw [hs, measure_empty]
  have hcyl : MeasurableSet (chartCylinder T j κ c u Q) := by
    have h0 : Continuous (fun v : EuclideanSpace ℝ (Fin 3) => v 0) := by fun_prop
    exact ((isClosed_Icc.preimage h0).inter
      (isClosed_le (continuous_chartBoxFun c u Q) continuous_const)).measurableSet
  calc ∫⁻ v, Measure.count (Prod.mk v ⁻¹' chartCompat T j κ δ B c u Q R) ≤
        ∫⁻ v, (chartCylinder T j κ c u Q).indicator
          (fun _ => ENNReal.ofReal (14 + 48 * κ ^ 2)) v := lintegral_mono hcount
    _ = ENNReal.ofReal (14 + 48 * κ ^ 2) * volume (chartCylinder T j κ c u Q) :=
        lintegral_indicator_const hcyl _
    _ ≤ ENNReal.ofReal (14 + 48 * κ ^ 2) *
          ENNReal.ofReal (((2 : ℝ) ^ T)⁻¹ * (Real.pi * κ ^ 2 * |Q.det|)) :=
        mul_le_mul' le_rfl (volume_chartCylinder_le T j κ hκpos.le c u Q hQ)
    _ = ENNReal.ofReal (((2 : ℝ) ^ T)⁻¹ * (Real.pi * κ ^ 2 * |Q.det|) * (14 + 48 * κ ^ 2)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end Submission.Obl.k4_terminal_label_saturation
