import Mathlib

/-! Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at d50c59d5b1367f287a76eef33f4c400a8e312ee2,
file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/DensityCutoff.lean`.
The namespace and internal imports are changed to o272. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set

/-- Cutting below half the weighted mass leaves a dense indicator event under the
unchanged probability prior, and bounds the weighted law above and below there. -/
theorem density_cutoff {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {f : X → ENNReal} (hf : Measurable f)
    {δ K : ℝ} (hδ : 0 < δ) (hK : 0 < K)
    (hbound : ∀ x, f x ≤ ENNReal.ofReal K)
    (hmass : ENNReal.ofReal δ ≤ μ.withDensity f univ) :
    ∃ E : Set X, MeasurableSet E ∧
      μ.withDensity f Eᶜ ≤ ENNReal.ofReal (δ / 2) ∧
      ENNReal.ofReal (δ / 2) ≤ μ.withDensity f E ∧
      ENNReal.ofReal (δ / (2 * K)) ≤ μ E ∧
      ENNReal.ofReal (δ / 2) • μ.restrict E ≤ (μ.withDensity f).restrict E ∧
      (μ.withDensity f).restrict E ≤ ENNReal.ofReal K • μ.restrict E := by
  let E := {x | ENNReal.ofReal (δ / 2) ≤ f x}
  have hE : MeasurableSet E := measurableSet_le measurable_const hf
  have hupper : μ.withDensity f ≤ ENNReal.ofReal K • μ := by
    simpa only [withDensity_const] using withDensity_mono (ae_of_all μ hbound)
  have hupperE : μ.withDensity f E ≤ ENNReal.ofReal K * μ E := by
    simpa only [Measure.smul_apply, smul_eq_mul] using hupper E
  have htotal : μ.withDensity f univ ≤ ENNReal.ofReal K := by
    simpa only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] using hupper univ
  have hfinite : μ.withDensity f E ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((measure_mono (subset_univ E)).trans htotal)
  have hsmall : μ.withDensity f Eᶜ ≤ ENNReal.ofReal (δ / 2) := by
    rw [withDensity_apply _ hE.compl]
    calc
      ∫⁻ x in Eᶜ, f x ∂μ ≤ ∫⁻ _x in Eᶜ, ENNReal.ofReal (δ / 2) ∂μ := by
        apply setLIntegral_mono measurable_const
        intro x hx
        exact (lt_of_not_ge (show ¬ ENNReal.ofReal (δ / 2) ≤ f x from hx)).le
      _ = ENNReal.ofReal (δ / 2) * μ Eᶜ := by simp
      _ ≤ ENNReal.ofReal (δ / 2) * 1 := by gcongr; exact (measure_mono (subset_univ Eᶜ)).trans_eq (measure_univ)
      _ = _ := mul_one _
  have hsplit : ENNReal.ofReal δ ≤ μ.withDensity f E + ENNReal.ofReal (δ / 2) := by
    calc
      _ ≤ μ.withDensity f univ := hmass
      _ = μ.withDensity f E + μ.withDensity f Eᶜ := (measure_add_measure_compl hE).symm
      _ ≤ _ := add_le_add le_rfl hsmall
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hfinite, ENNReal.ofReal_ne_top⟩) hsplit
  simp only [ENNReal.toReal_ofReal hδ.le, ENNReal.toReal_add hfinite ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (show 0 ≤ δ / 2 by positivity)] at hreal
  have hlarge : ENNReal.ofReal (δ / 2) ≤ μ.withDensity f E :=
    (ENNReal.ofReal_le_iff_le_toReal hfinite).mpr (by linarith)
  have hbase := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ E)) (hlarge.trans hupperE)
  simp only [ENNReal.toReal_ofReal (show 0 ≤ δ / 2 by positivity), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hK.le] at hbase
  have hbase' : ENNReal.ofReal (δ / (2 * K)) ≤ μ E := by
    apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ E)).mpr
    apply (div_le_iff₀ (by positivity : 0 < 2 * K)).mpr
    nlinarith
  refine ⟨E, hE, hsmall, hlarge, hbase', ?_, ?_⟩
  · rw [restrict_withDensity hE, ← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hE] with x hx using hx
  · rw [restrict_withDensity hE, ← withDensity_const]
    exact withDensity_mono (ae_of_all _ hbound)

end Submission.Obl.k4_horizontal_strict_parameter_step
