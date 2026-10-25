import Mathlib

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

open Set MeasureTheory

/-- A dominated original incidence law supported on a bounded time interval
is finite, even though the unrestricted product with time is infinite. -/
theorem finite_original_incidence {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (μ : Measure (α × ℝ))
    (H a b : ℝ) (hdom : μ ≤ ENNReal.ofReal H • ν.prod volume)
    (hsupport : μ {p | p.2 ∈ Set.Icc a b}ᶜ = 0) : IsFiniteMeasure μ := by
  have hmem : ∀ᵐ p ∂μ, p.2 ∈ Set.Icc a b := (ae_iff).mpr hsupport
  have heq : μ Set.univ = μ {p | p.2 ∈ Set.Icc a b} := by
    apply measure_congr
    filter_upwards [hmem] with p hp
    simp only [Set.mem_univ, hp]
  have hset : {p : α × ℝ | p.2 ∈ Set.Icc a b} = Set.univ ×ˢ Set.Icc a b := by
    ext p
    simp
  constructor
  calc
    μ Set.univ = μ {p | p.2 ∈ Set.Icc a b} := heq
    _ ≤ (ENNReal.ofReal H • ν.prod volume) (Set.univ ×ˢ Set.Icc a b) := by
      rw [hset]
      exact hdom _
    _ = ENNReal.ofReal H * volume (Set.Icc a b) := by
      rw [Measure.smul_apply, Measure.prod_prod, measure_univ, one_mul, smul_eq_mul]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_lt_top)

/-- Prior almost-everywhere properties transfer to the original incidence
law using domination alone. -/
theorem ae_original_incidence {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (μ : Measure (α × ℝ)) (H : ℝ)
    (hdom : μ ≤ ENNReal.ofReal H • ν.prod volume) {P : α → Prop}
    (hP : ∀ᵐ l ∂ν, P l) : ∀ᵐ p ∂μ, P p.1 :=
  ae_mono hdom (Measure.ae_smul_measure (Measure.quasiMeasurePreserving_fst.ae hP) _)

/-- An almost-everywhere fit recovers the entire retained original mass. No
measurability of the fit event or normalization of either law is required. -/
theorem original_mass_of_ae_event {Ω : Type*} [MeasurableSpace Ω]
    (μ ρ : Measure Ω) (hdom : μ ≤ ρ) (E : Set Ω) (hE : ∀ᵐ ω ∂μ, ω ∈ E) :
    μ Set.univ ≤ ρ E := by
  have heq : μ Set.univ = μ E := by
    apply measure_congr
    filter_upwards [hE] with ω hω
    simp only [Set.mem_univ, hω]
  rw [heq]
  exact hdom E

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
