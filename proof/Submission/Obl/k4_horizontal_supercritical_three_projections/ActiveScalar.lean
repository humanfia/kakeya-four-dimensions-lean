import Submission.Obl.k4_horizontal_supercritical_three_projections.RawInterface
import Submission.Obl.k4_horizontal_supercritical_three_projections.NormalizedScalar
import Submission.Obl.k4_horizontal_supercritical_three_projections.Ensemble

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open Set MeasureTheory
open Submission.Obl.k4_fixed_budget_quadratic_recovery

/-- Raw original-chart caps give the precise normalized scalar input on any
measurable subchart, with all losses spent before calling the scalar theorem. -/
theorem raw_chart_scalar_admissible {α : Type} [MeasurableSpace α]
    {N K d s₀ Dexp depth e₀ M ξ η : ℝ} (hN : 0 < N)
    (ν : Measure α) [IsProbabilityMeasure ν] (ζ μ : Measure (α × ℝ)) (π : Measure ℝ)
    (b : α → Fin 6 → ℝ) (hb : Measurable b)
    (hraw : RawChartData N K d s₀ Dexp depth e₀ M ξ b μ π)
    (P Q β : ℤ) (G : Set α) (hG : MeasurableSet G) (hG₀ : ν G ≠ 0)
    (hsub : G ⊆ chartSet b K (N ^ (-e₀)) (N ^ (-Dexp)) (N ^ (-M)) P Q β)
    (hζ : ζ ≤ μ) (hdom : ζ ≤ ENNReal.ofReal (N ^ η) • (ν.prod volume))
    (hsupp : ζ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (hcoeff : ∀ l ∈ G, ∀ i,
      |Parent.projectedCoefficients ((P : ℝ) * N ^ (-Dexp)) ((Q : ℝ) * N ^ (-Dexp))
        (N ^ (-Dexp)) (b l) i| ≤ N ^ η)
    (hc₁ : N ^ (-(1 : ℝ)) ≤
      chartWeight π (N ^ (-M)) (N ^ (-Dexp)) ![β, P, Q] / (ν G).toReal)
    (hc₂ : chartWeight π (N ^ (-M)) (N ^ (-Dexp)) ![β, P, Q] / (ν G).toReal ≤ N ^ (1 : ℝ))
    (hpure : N ^ ξ ≤ N ^ η)
    (hsupport : N ^ ξ ≤ N ^ η *
      (chartWeight π (N ^ (-M)) (N ^ (-Dexp)) ![β, P, Q] / (ν G).toReal)⁻¹) :
    ScalarAdmissible N η d depth (20 * s₀) 1 1 s₀
      (chartWeight π (N ^ (-M)) (N ^ (-Dexp)) ![β, P, Q] / (ν G).toReal)
      (ProbabilityTheory.cond ν G)
      (padCoefficients G (fun l => Parent.projectedCoefficients
        ((P : ℝ) * N ^ (-Dexp)) ((Q : ℝ) * N ^ (-Dexp)) (N ^ (-Dexp)) (b l)))
      (chartLaw ν ζ G) := by
  let D := N ^ (-Dexp)
  let χ := N ^ (-M)
  let σ := N ^ (-(20 * s₀))
  let a := N ^ (-depth)
  let W := chartWeight π χ D ![β, P, Q]
  let bs := fun l => Parent.projectedCoefficients ((P : ℝ) * D) ((Q : ℝ) * D) D (b l)
  let y := fun l t => (b l 1 - (Q : ℝ) * D) / D - 2 * t * ((b l 0 - (P : ℝ) * D) / D)
  let x := fun l t => b l 2 + t * b l 5
  let z := fun p : α × ℝ => ![⌊p.2 / σ⌋, ⌊y p.1 p.2 / σ⌋]
  have hb' : Measurable bs := Parent.measurable_projectedCoefficients hb _ _ _
  have hy (l t) : scalarY (bs l) t = y l t := by
    change bs l 0 + t * bs l 1 = _
    exact Parent.projectedCoefficients_y _ _ _ _ _
  have hx (l t) : scalarX (bs l) t = x l t :=
    Parent.projectedCoefficients_x _ _ _ _ _
  have hz (p : α × ℝ) : scalarCell (bs p.1) p.2 σ = z p := by
    change ![⌊p.2 / σ⌋, ⌊scalarY (bs p.1) p.2 / σ⌋] = _
    rw [hy]
  have hW : 0 ≤ W := by dsimp [W, chartWeight]; positivity
  obtain ⟨hchart, hp, ha, ht⟩ := hraw P Q β
  apply normalized_scalar_admissible hN ν ζ μ G hG hG₀ hζ bs hb' hdom hsupp
    hcoeff hc₁ hc₂
  · intro r q j hr hrs
    have hcap : μ {p | p.1 ∈ G ∧ scalarCell (bs p.1) p.2 σ = q ∧
        ⌊scalarX (bs p.1) p.2 / N ^ (-r)⌋ = j} ≤
        ENNReal.ofReal (N ^ ξ * σ ^ 2 * (N ^ (-r)) ^ d * W) := by
      apply le_trans (measure_mono ?_) (hp r q j hr hrs)
      intro p hp'
      refine ⟨hsub hp'.1, ?_, ?_⟩
      · simpa only [hz] using hp'.2.1
      · simpa only [hx] using hp'.2.2
    apply hcap.trans
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpure (sq_nonneg _))
        (by positivity)) hW)
  · obtain ⟨F, hcard, hF⟩ := ht
    refine ⟨F, hcard.trans (mul_le_mul_of_nonneg_right hsupport (by positivity)), ?_⟩
    filter_upwards [hF] with p hp' hpG
    change (scalarCell (bs p.1) p.2 σ, ⌊scalarX (bs p.1) p.2 / a⌋) ∈ F
    rw [hz, hx]
    exact hp' (hsub hpG)
  · intro r q j v hr hrs
    have hcap : μ {p | p.1 ∈ G ∧ scalarCell (bs p.1) p.2 σ = q ∧
        ⌊scalarX (bs p.1) p.2 / a⌋ = j ∧ ⌊bs p.1 1 / N ^ (-r)⌋ = v} ≤
        ENNReal.ofReal (N ^ ξ * σ ^ 2 * a ^ d * N ^ (-r) * W) := by
      apply le_trans (measure_mono ?_) (ha r q j v hr hrs)
      intro p hp'
      refine ⟨hsub hp'.1, ?_, ?_, hp'.2.2.2⟩
      · simpa only [hz] using hp'.2.1
      · simpa only [hx] using hp'.2.2.1
    simp only [neg_one_mul]
    apply hcap.trans
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpure (sq_nonneg _))
          (by positivity)) (by positivity)) hW)

end Submission.Obl.k4_horizontal_supercritical_three_projections
