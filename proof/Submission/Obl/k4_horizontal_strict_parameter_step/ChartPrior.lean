import Submission.Obl.k4_horizontal_strict_parameter_step.DensityCutoff
import Submission.Lib.K4ChartLifting.NormTerminal

/-! Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at d50c59d5b1367f287a76eef33f4c400a8e312ee2,
file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/ChartPrior.lean`.
The namespace and internal imports are changed to o272. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set

/-- A dominated finite chart law has an everywhere bounded measurable density under
its unchanged reference probability. Null exceptional points are clipped away. -/
theorem bounded_chart_density {X : Type*} [MeasurableSpace X]
    (ν lam : Measure X) [IsProbabilityMeasure ν] {K : ℝ}
    (hle : lam ≤ ENNReal.ofReal K • ν) :
    ∃ f : X → ENNReal, Measurable f ∧
      (∀ x, f x ≤ ENNReal.ofReal K) ∧ lam = ν.withDensity f := by
  haveI : IsFiniteMeasure lam := ⟨(hle univ).trans_lt (by
    simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact ENNReal.ofReal_lt_top)⟩
  obtain ⟨g, hg, hgeq⟩ := Submission.Lib.K4ChartLifting.exists_density_of_le
    ν lam (fun _ => ENNReal.ofReal K) (by simpa only [withDensity_const] using hle)
  have hgae : g ≤ᵐ[ν] fun _ => ENNReal.ofReal K := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite hg
    intro s hs _
    rw [← withDensity_apply _ hs, ← hgeq]
    simpa only [lintegral_const, Measure.restrict_apply_univ, Measure.smul_apply,
      smul_eq_mul] using hle s
  refine ⟨fun x => min (g x) (ENNReal.ofReal K), hg.min measurable_const,
    fun x => min_le_right _ _, ?_⟩
  rw [hgeq]
  apply withDensity_congr_ae
  filter_upwards [hgae] with x hx
  exact (min_eq_left hx).symm

/-- A dense chart submeasure can be replaced by a dense indicator event under the
same prior, with two-sided comparison to the weighted law. -/
theorem chart_indicator_cutoff {X : Type*} [MeasurableSpace X]
    (ν lam : Measure X) [IsProbabilityMeasure ν] {δ K : ℝ}
    (hδ : 0 < δ) (hK : 0 < K) (hle : lam ≤ ENNReal.ofReal K • ν)
    (hmass : ENNReal.ofReal δ ≤ lam univ) :
    ∃ E : Set X, MeasurableSet E ∧
      lam Eᶜ ≤ ENNReal.ofReal (δ / 2) ∧
      ENNReal.ofReal (δ / 2) ≤ lam E ∧
      ENNReal.ofReal (δ / (2 * K)) ≤ ν E ∧
      ENNReal.ofReal (δ / 2) • ν.restrict E ≤ lam.restrict E ∧
      lam.restrict E ≤ ENNReal.ofReal K • ν.restrict E := by
  obtain ⟨f, hf, hbound, heq⟩ := bounded_chart_density ν lam hle
  rw [heq] at hmass ⊢
  exact density_cutoff ν hf hδ hK hbound hmass

/-- Conditioning a full-time trajectory assignment normalizes the prior and its
current incidence law by the same original denominator. -/
theorem normalize_chart_prior {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (lam : Measure (α × ℝ))
    {K : ℝ} (hle : lam ≤ ENNReal.ofReal K • ν.prod volume)
    (A : Set α) (hA : MeasurableSet A) (hA0 : ν A ≠ 0) :
    let νH := (ν A)⁻¹ • ν.restrict A
    let lamH := (ν A)⁻¹ • lam.restrict (A ×ˢ Icc (0 : ℝ) 1)
    IsProbabilityMeasure νH ∧
      lamH ≤ ENNReal.ofReal K • νH.prod (volume.restrict (Icc (0 : ℝ) 1)) ∧
      lamH univ = (ν A)⁻¹ * lam (A ×ˢ Icc (0 : ℝ) 1) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · apply isProbabilityMeasure_iff.mpr
    simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hA0 (measure_ne_top ν A)
  · rw [Measure.prod_smul_left, Measure.prod_restrict]
    exact (smul_le_smul_left ((ν A)⁻¹ : ENNReal)
      (Measure.restrict_mono (s := A ×ˢ Icc (0 : ℝ) 1) le_rfl hle)).trans_eq
      (by simp only [Measure.restrict_smul, smul_smul, mul_comm])
  · simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]

end Submission.Obl.k4_horizontal_strict_parameter_step
