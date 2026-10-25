-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.CandidateMarginal

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial
open scoped ENNReal
open Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

noncomputable section

/-- The unchanged exact base and one raw hidden bin of an arbitrary point map. -/
def signalObservation {Ω : Type*} (point : Ω → Fin 4 → ℝ) (a : ℝ)
    (z : Ω) : EuclideanSpace ℝ (Fin 3) × ℤ :=
  (WithLp.toLp 2 (fun j : Fin 3 => point z j.castSucc), ⌊point z 3 / a⌋)

theorem measurable_signalObservation {Ω : Type*} [MeasurableSpace Ω]
    (point : Ω → Fin 4 → ℝ) (hp : Measurable point) (a : ℝ) :
    Measurable (signalObservation point a) := by
  apply Measurable.prodMk
  · exact (PiLp.volume_preserving_toLp (Fin 3)).measurable.comp
      (measurable_pi_iff.mpr fun j => (measurable_pi_apply j.castSucc).comp hp)
  · exact Int.measurable_floor.comp (((measurable_pi_apply 3).comp hp).div_const a)

/-- A raw observation ceiling gives the same quadratic-signal ceiling up
to a quadratic slack factor. This imports the accepted regular-fiber
count and support projection; no bound on sheet height or base gradients
is used. It also applies after restricting to one original velocity bin. -/
theorem quadratic_signal_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (point : Ω → Fin 4 → ℝ) (hp : Measurable point)
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (A : Set (EuclideanSpace ℝ (Fin 3))) (hA : MeasurableSet A)
    (E : Set Ω) (hE : MeasurableSet E) (a κ : ℝ) (D : ℝ≥0∞)
    (ha : 0 < a) (hκ : 0 < κ)
    (hcap : μ.map (signalObservation point a) ≤
      D • (volume.prod Measure.count))
    (hbase : ∀ z ∈ E, (signalObservation point a z).1 ∈ A)
    (hfit : ∀ᵐ z ∂μ, z ∈ E →
      |eval (point z) P| ≤ κ * a ∧
      κ⁻¹ ≤ |eval (point z) (pderiv (3 : Fin 4) P)|) :
    μ E ≤ D * (volume A * ENNReal.ofReal (16 * (1 + κ ^ 2))) := by
  let obs := signalObservation point a
  let S := polynomialBinSupport P (κ * a) κ⁻¹ a
  have hobs : Measurable obs := measurable_signalObservation point hp a
  have hS : MeasurableSet S := measurableSet_polynomialBinSupport P _ _ _
  have heq (z : Ω) : Fin.snoc (fun j : Fin 3 => (obs z).1 j) (point z 3) = point z := by
    ext j
    fin_cases j <;> rfl
  have hmem (z : Ω) (hz : |eval (point z) P| ≤ κ * a ∧
      κ⁻¹ ≤ |eval (point z) (pderiv (3 : Fin 4) P)|) : obs z ∈ S := by
    apply mem_polynomialBinSupport P ha (obs z).1
    · rw [heq]; exact hz.1
    · rw [heq]; exact hz.2
  have hsupp : (μ.restrict E) (obs ⁻¹' Sᶜ) = 0 := by
    rw [Measure.restrict_apply (hS.compl.preimage hobs)]
    apply le_antisymm _ bot_le
    apply (measure_mono_ae (t := (∅ : Set Ω)) ?_).trans_eq (measure_empty)
    filter_upwards [hfit] with z hz
    intro hbad
    exact hbad.1 (hmem z (hz hbad.2))
  have hdom : (μ.restrict E).map obs ≤ D • (volume.prod Measure.count) :=
    (Measure.map_mono Measure.restrict_le_self hobs).trans hcap
  have hfiber (u : EuclideanSpace ℝ (Fin 3)) :
      Measure.count (Prod.mk u ⁻¹' S) ≤ ENNReal.ofReal (16 * (1 + κ ^ 2)) := by
    have h := count_candidate_support P hP ha (show (0 : ℝ) < 1 by norm_num) hκ u
    simp only [one_div, div_one] at h
    exact h
  calc
    _ = (μ.restrict E) E := by simp [Measure.restrict_apply hE]
    _ ≤ (μ.restrict E) {z | (obs z).1 ∈ A} := measure_mono hbase
    _ ≤ (D * ENNReal.ofReal (16 * (1 + κ ^ 2))) * volume A :=
      Submission.Lib.K4ListedExceptions.observation_base_marginal_bound
        (μ.restrict E) volume Measure.count obs hobs S hS hsupp hdom hfiber A hA
    _ = _ := by ring

end
end Submission.Obl.k4_finite_affine_parent_sources
