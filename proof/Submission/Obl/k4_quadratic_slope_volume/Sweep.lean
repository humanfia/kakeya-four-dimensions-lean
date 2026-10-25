import Mathlib
import Submission.Obl.k4_quadratic_slope_volume.Area

namespace Submission.Obl.k4_quadratic_slope_volume

open Set MeasureTheory
open scoped ENNReal

/-- The measure-theoretic sweep estimate. A lower bound on the time spent by
 each slope and an upper bound on each time slice give a bound for all slopes. -/
theorem measure_sweep_bound {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SFinite μ] (S : Set E) (hS : MeasurableSet S)
    (I : Set ℝ) (hI : MeasurableSet I) (G : Set (E × ℝ)) (hG : MeasurableSet G)
    (J L V : ℝ≥0∞) (hJ : J ≠ ∞)
    (hlow : ∀ s ∈ S, L ≤ (volume.restrict I) {t : ℝ | (s, t) ∈ G})
    (hhigh : ∀ t ∈ I, J * (μ.restrict S) {s : E | (s, t) ∈ G} ≤ V) :
    J * L * μ S ≤ V * volume I := by
  let μS := μ.restrict S
  let νI := (volume : Measure ℝ).restrict I
  have hlower : L * μ S ≤ (μS.prod νI) G := by
    rw [Measure.prod_apply hG]
    calc
      L * μ S = ∫⁻ _ : E, L ∂μS := by simp [μS]
      _ ≤ ∫⁻ s, νI (Prod.mk s ⁻¹' G) ∂μS := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hS] with s hs
        exact hlow s hs
  calc
    J * L * μ S = J * (L * μ S) := mul_assoc _ _ _
    _ ≤ J * (μS.prod νI) G := by gcongr
    _ = J * ∫⁻ t : ℝ, μS ((fun s : E => (s, t)) ⁻¹' G) ∂νI := by
      rw [Measure.prod_apply_symm hG]
    _ = ∫⁻ t : ℝ, J * μS ((fun s : E => (s, t)) ⁻¹' G) ∂νI :=
      (lintegral_const_mul' J _ hJ).symm
    _ ≤ ∫⁻ _ : ℝ, V ∂νI := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hI] with t ht
      exact hhigh t ht
    _ = V * volume I := by simp [νI]

/-- The numerical constants produced by the cubic-Jacobian sweep. -/
theorem slope_volume_of_time_slice_bounds
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : MeasurableSet S)
    (t₀ q : ℝ) (hq : 0 < q)
    (G : Set (EuclideanSpace ℝ (Fin 3) × ℝ)) (hG : MeasurableSet G)
    (V : ℝ≥0∞)
    (hlow : ∀ s ∈ S, ENNReal.ofReal (q / 2) ≤
      (volume.restrict (Icc t₀ (t₀ + q))) {t : ℝ | (s, t) ∈ G})
    (hhigh : ∀ t ∈ Icc t₀ (t₀ + q), ENNReal.ofReal ((q / 24) ^ 3) *
      (volume.restrict S) {s : EuclideanSpace ℝ (Fin 3) | (s, t) ∈ G} ≤ V) :
    volume S ≤ ENNReal.ofReal (27648 / q ^ 3) * V := by
  have h := measure_sweep_bound volume S hS (Icc t₀ (t₀ + q)) measurableSet_Icc
    G hG (ENNReal.ofReal ((q / 24) ^ 3)) (ENNReal.ofReal (q / 2)) V
    ENNReal.ofReal_ne_top hlow hhigh
  rw [Real.volume_Icc, add_sub_cancel_left] at h
  have hcoef : ENNReal.ofReal ((q / 24) ^ 3) * ENNReal.ofReal (q / 2) =
      ENNReal.ofReal (q ^ 4 / 27648) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [hcoef] at h
  have hcancel : ENNReal.ofReal (27648 / q ^ 4) * ENNReal.ofReal (q ^ 4 / 27648) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    have hq0 : q ≠ 0 := ne_of_gt hq
    field_simp
    norm_num
  have hmul : ENNReal.ofReal (27648 / q ^ 4) *
      (ENNReal.ofReal (q ^ 4 / 27648) * volume S) ≤
      ENNReal.ofReal (27648 / q ^ 4) * (V * ENNReal.ofReal q) := by gcongr
  rw [← mul_assoc, hcancel, one_mul] at hmul
  calc
    volume S ≤ ENNReal.ofReal (27648 / q ^ 4) * (V * ENNReal.ofReal q) := hmul
    _ = ENNReal.ofReal (27648 / q ^ 3) * V := by
      rw [mul_comm V (ENNReal.ofReal q), ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      field_simp

/-- A measurable family with a uniformly bounded finite injective cover at each
 time obeys the slope-volume sweep bound. This isolates the geometric selector
 construction from the change-of-variables and Fubini arguments. -/
theorem slope_volume_of_injective_covers
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : MeasurableSet S)
    (t₀ q : ℝ) (hq : 0 < q) (N : ℕ)
    (G : Set (EuclideanSpace ℝ (Fin 3) × ℝ)) (hG : MeasurableSet G)
    (F : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (F' : ℝ → EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (pieces : ℝ → Fin N → Set (EuclideanSpace ℝ (Fin 3)))
    (V : ℝ≥0∞)
    (hlow : ∀ s ∈ S, ENNReal.ofReal (q / 2) ≤
      (volume.restrict (Icc t₀ (t₀ + q))) {t : ℝ | (s, t) ∈ G})
    (hcover : ∀ t ∈ Icc t₀ (t₀ + q), {s | (s, t) ∈ G} ∩ S ⊆ ⋃ i, pieces t i)
    (hpieces : ∀ t ∈ Icc t₀ (t₀ + q), ∀ i, MeasurableSet (pieces t i))
    (hderiv : ∀ t ∈ Icc t₀ (t₀ + q), ∀ i s, s ∈ pieces t i →
      HasFDerivWithinAt (F t) (F' t s) (pieces t i) s)
    (hinj : ∀ t ∈ Icc t₀ (t₀ + q), ∀ i, InjOn (F t) (pieces t i))
    (hjac : ∀ t ∈ Icc t₀ (t₀ + q), ∀ i s, s ∈ pieces t i →
      (q / 24) ^ 3 ≤ |(F' t s).det|)
    (himage : ∀ t ∈ Icc t₀ (t₀ + q), ∀ i, volume (F t '' pieces t i) ≤ V) :
    volume S ≤ ENNReal.ofReal (27648 * N / q ^ 3) * V := by
  have hhigh : ∀ t ∈ Icc t₀ (t₀ + q), ENNReal.ofReal ((q / 24) ^ 3) *
      (volume.restrict S) {s : EuclideanSpace ℝ (Fin 3) | (s, t) ∈ G} ≤ (N : ℝ≥0∞) * V := by
    intro t ht
    have hm : MeasurableSet {s : EuclideanSpace ℝ (Fin 3) | (s, t) ∈ G} :=
      hG.preimage (measurable_id.prodMk measurable_const)
    rw [Measure.restrict_apply hm]
    exact jacobian_mul_measure_le_finite_cover volume _ (pieces t) (hcover t ht)
      (hpieces t ht) (F t) (F' t) (hderiv t ht) (hinj t ht) _ (hjac t ht) V (himage t ht)
  calc
    volume S ≤ ENNReal.ofReal (27648 / q ^ 3) * ((N : ℝ≥0∞) * V) :=
      slope_volume_of_time_slice_bounds S hS t₀ q hq G hG _ hlow hhigh
    _ = ENNReal.ofReal (27648 * N / q ^ 3) * V := by
      rw [← mul_assoc, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring

end Submission.Obl.k4_quadratic_slope_volume
