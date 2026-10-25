/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/DirectionalCorrection.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.FiberGeometry
import Submission.Obl.k4_subcritical_corrected_scalar_charts.TimeMarginalFloor

/-! The quantitative directional correction. The hypotheses separate the original
whole-domain comparisons from the time-polynomial selection, so later incidence
restrictions never replace the earlier comparison witnesses. -/

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory

/-- Three square corners control both spatial slopes of an endpoint predictor. -/
theorem predictor_slopes_of_corners {h : Fin 6 → ℝ} {t p q D E : ℝ} (hD : 0 < D)
    (h0 : |parameterPredictor h t p q| ≤ E)
    (h1 : |parameterPredictor h t (p + D) q| ≤ E)
    (h2 : |parameterPredictor h t p (q + D)| ≤ E) :
    |h 2 + h 3 * t| ≤ 2 * E / D ∧ |h 4 + h 5 * t| ≤ 2 * E / D := by
  exact Submission.Lib.K4FullTimeLayers.affine_square_slopes
    (a := h 0 + h 1 * t) (b := h 2 + h 3 * t) (c := h 4 + h 5 * t)
    (p := p) (q := q) hD h0 h1 h2

/-- A product-square norm bounds the fiber derivative, uniformly over unit time. -/
theorem fiberDerivative_of_square_norm {h : Fin 6 → ℝ} {p q D E t : ℝ}
    (hD : 0 < D) (ht : t ∈ Icc (0 : ℝ) 1)
    (hnorm : ∀ p' ∈ Icc p (p + D), ∀ q' ∈ Icc q (q + D),
      |parameterPredictor h t p' q'| ≤ E) :
    |fiberDerivative h t| ≤ 6 * E / D := by
  have hp : p ∈ Icc p (p + D) := ⟨le_rfl, by linarith⟩
  have hq : q ∈ Icc q (q + D) := ⟨le_rfl, by linarith⟩
  have hpD : p + D ∈ Icc p (p + D) := ⟨by linarith, le_rfl⟩
  have hqD : q + D ∈ Icc q (q + D) := ⟨by linarith, le_rfl⟩
  obtain ⟨hb, hc⟩ := predictor_slopes_of_corners hD
    (hnorm p hp q hq) (hnorm (p + D) hpD q hq) (hnorm p hp (q + D) hqD)
  have hE : 0 ≤ E := (abs_nonneg _).trans (hnorm p hp q hq)
  have hr : 0 ≤ 2 * E / D := by positivity
  calc
    |fiberDerivative h t| = |(h 2 + h 3 * t) + 2 * t * (h 4 + h 5 * t)| := by
      unfold fiberDerivative
      congr 1
      ring
    _ ≤ |h 2 + h 3 * t| + |2 * t * (h 4 + h 5 * t)| := abs_add_le _ _
    _ = |h 2 + h 3 * t| + 2 * t * |h 4 + h 5 * t| := by
      norm_num only [abs_mul, abs_of_nonneg ht.1, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * E / D + 2 * 1 * (2 * E / D) := by
      exact add_le_add hb (mul_le_mul
        (mul_le_mul_of_nonneg_left ht.2 (by norm_num)) hc (abs_nonneg _) (by norm_num))
    _ = 6 * E / D := by ring

/-- A fine full-time comparison and a true child-box horizontal comparison give
the power-small error in the shared quadratic time row. -/
theorem directional_signal_comparison {L0 Lb : Fin 4 → ℝ} {H0 Hb : Fin 6 → ℝ}
    {v t r E₁ E₂ : ℝ} (hr : 0 ≤ r)
    (htrue : |(L0 2 + t * L0 3) - (Lb 2 + t * Lb 3)| ≤ E₁)
    (hfull : |fiberDerivative (horizontalLift Lb v - Hb) t| ≤ E₂) :
    |r * (L0 2 + t * L0 3 - fiberDerivative H0 t) -
      r * fiberDerivative (Hb - H0) t| ≤ r * (E₁ + E₂) := by
  rw [fiberDerivative_sub, horizontalLift_fiberDerivative] at hfull
  rw [fiberDerivative_sub]
  calc
    _ = |r * (((L0 2 + t * L0 3) - (Lb 2 + t * Lb 3)) +
        ((Lb 2 + t * Lb 3) - fiberDerivative Hb t))| := by congr 1; ring
    _ = r * |((L0 2 + t * L0 3) - (Lb 2 + t * Lb 3)) +
        ((Lb 2 + t * Lb 3) - fiberDerivative Hb t)| := by
      rw [abs_mul, abs_of_nonneg hr]
    _ ≤ r * (E₁ + E₂) := mul_le_mul_of_nonneg_left
      ((abs_add_le _ _).trans (add_le_add htrue hfull)) hr

/-- Coefficients of the scaled fiber derivative as a quadratic time polynomial. -/
noncomputable def directionalTimeCoefficients (r : ℝ) (h : Fin 6 → ℝ) : Fin 3 → ℝ :=
  ![r * h 2, r * (h 3 + 2 * h 4), 2 * r * h 5]

theorem directionalTimeCoefficients_eval (r : ℝ) (h : Fin 6 → ℝ) (t : ℝ) :
    (quadraticTimePolynomial (directionalTimeCoefficients r h)).eval t =
      r * fiberDerivative h t := by
  rw [quadraticTimePolynomial_eval]
  dsimp [directionalTimeCoefficients, fiberDerivative]
  ring

/-- Choose the correction from one trajectory and retain all paired incidences
where its time polynomial fits the shared signal. No coefficient bound on the
unselected endpoint rows is assumed. -/
theorem exists_directional_correction_of_mass {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (ρ : Measure (α × ℝ))
    (Hb : α → Fin 6 → ℝ) (H0 : Fin 6 → ℝ) (r : ℝ) (signal : ℝ → ℝ)
    {C m K δ : ℝ} (hC : 0 < C) (hm : 0 < m) (hmC : m ≤ C)
    (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hdom : ρ ≤ ENNReal.ofReal C • (ν.prod volume))
    {E : Set (α × ℝ)} (hE : MeasurableSet E)
    (hmass : ENNReal.ofReal m ≤ ρ E) (hsub : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hsignal : ∀ p ∈ E, |signal p.2| ≤ K)
    (hfit : ∀ p ∈ E,
      |r * fiberDerivative (Hb p.1 - H0) p.2 - signal p.2| ≤ δ) :
    ∃ β : Fin 3 → ℝ,
      (∀ i, |β i| ≤ 17 * (96 * C / m) ^ 2 * (K + δ)) ∧
      ENNReal.ofReal (m ^ 2 / (8 * C)) ≤
        ρ {p | p ∈ E ∧ |signal p.2 - fiberDerivative (fiberCorrection β) p.2| ≤ δ} := by
  let b : α → Fin 3 → ℝ := fun l => directionalTimeCoefficients r (Hb l - H0)
  have hb (p : α × ℝ) (hp : p ∈ E) :
      |(quadraticTimePolynomial (b p.1)).eval p.2 - signal p.2| ≤ δ := by
    simpa only [b, directionalTimeCoefficients_eval] using hfit p hp
  obtain ⟨l, hcoeff, hret⟩ := exists_shared_time_polynomial_of_mass ν ρ b signal
    hC hm hmC hK hδ hdom hE hmass hsub hsignal hb
  refine ⟨b l, hcoeff, hret.trans (measure_mono ?_)⟩
  intro p hp
  refine ⟨hp.1, ?_⟩
  simpa only [quadraticTimePolynomial_eval, fiberDerivative_correction, abs_sub_comm] using hp.2

end Submission.Obl.k4_subcritical_corrected_scalar_charts
