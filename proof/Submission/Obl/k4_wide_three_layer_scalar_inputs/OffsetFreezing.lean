import Submission.Obl.k4_subcritical_corrected_scalar_charts.QuadraticVariation
import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Set MvPolynomial Filter
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction
open Submission.Obl.k4_fixed_budget_quadratic_recovery

noncomputable section

/-- A long moving-strip bound freezes a projected difference on any short
physical domain. The transverse distance is measured in the same moving chart. -/
theorem moving_strip_freezing (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2)
    {E D u p t₀ Y₀ t Y q W : ℝ} (hD : 0 < D)
    (hbox : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |eval ![t, u - t * p + D * w] G| ≤ E)
    (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hY₀ : |Y₀ - u + t₀ * p| ≤ D) (hY : |Y - u + t * p| ≤ D)
    (hdt : |t - t₀| ≤ q) (hdY : |(Y - Y₀) + p * (t - t₀)| ≤ W) :
    |eval ![t, Y] G - eval ![t₀, Y₀] G| ≤ 32 * E * (q + W / D) := by
  obtain ⟨c, hc⟩ := isQuad2_affine_second (isQuad2_eval G hG) u (-p) D
  have hcform : ∀ t w, eval ![t, u - t * p + D * w] G = quadraticValue c t w := by
    intro t w
    convert hc t w using 1 <;> congr 2 <;> ring
  have heval (r V : ℝ) : eval ![r, V] G =
      quadraticValue c r ((V - u + r * p) / D) := by
    rw [← hcform]
    congr 2
    field_simp
    ring
  have hnorm : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |quadraticValue c t w| ≤ E := by
    simpa only [← hcform] using hbox
  have hw (r V : ℝ) (hV : |V - u + r * p| ≤ D) :
      (V - u + r * p) / D ∈ Icc (-1 : ℝ) 1 := by
    have h := abs_le.mp hV
    constructor
    · apply (le_div_iff₀ hD).mpr
      linarith [h.1]
    · apply (div_le_iff₀ hD).mpr
      linarith [h.2]
  rw [heval, heval]
  apply Submission.Obl.k4_subcritical_corrected_scalar_charts.quadratic_short_domain_freezing
    hnorm ht₀ (hw t₀ Y₀ hY₀) ht (hw t Y hY) hdt
  rw [← sub_div, show (Y - u + t * p) - (Y₀ - u + t₀ * p) =
    (Y - Y₀) + p * (t - t₀) by ring, abs_div, abs_of_pos hD]
  exact div_le_div_of_nonneg_right hdY hD.le

/-- Subtracting the frozen constant transfers the finer projected fit
onto its coarse predictor without changing the physical residual units. -/
theorem fine_fit_after_freezing {X G₀ Gi D E F : ℝ}
    (hfit : |X - Gi| ≤ E) (hfreeze : |Gi - G₀ - D| ≤ F) :
    |X - G₀ - D| ≤ E + F := by
  have heq : X - G₀ - D = (X - Gi) + (Gi - G₀ - D) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hfit hfreeze)

/-- The strict wide inequalities absorb the full-strip comparison loss
and make its variation smaller than either finer accuracy. -/
theorem eventually_wide_freezing {N : ℕ → ℝ}
    (hNt : Tendsto N atTop atTop) {d κ s₀ s u η : ℝ}
    (hu : 0 < u) (hη : η ≤ u / 10)
    (hwide : (10 / (1 - d) + 3) * u < 2 * κ * (s - s₀))
    (hblock : (10 / (1 - d) + 3) * u < κ * s) :
    ∀ᶠ k in atTop,
      32 * N k ^ (η + (10 / (1 - d)) * u) *
        (N k ^ (-κ * s + η) + N k ^ (-2 * κ * (s - s₀) + 2 * η)) ≤
          N k ^ (-u) := by
  have ha : 2 * η + (10 / (1 - d)) * u - κ * s < -u := by nlinarith
  have hb : 3 * η + (10 / (1 - d)) * u - 2 * κ * (s - s₀) < -u := by nlinarith
  have h1 := hNt.eventually (eventually_const_mul_rpow_le 64 ha)
  have h2 := hNt.eventually (eventually_const_mul_rpow_le 64 hb)
  filter_upwards [h1, h2, hNt.eventually (eventually_gt_atTop (0 : ℝ))] with k hk1 hk2 hNk
  have hsplit : 32 * N k ^ (η + (10 / (1 - d)) * u) *
      (N k ^ (-κ * s + η) + N k ^ (-2 * κ * (s - s₀) + 2 * η)) =
      (64 * N k ^ (2 * η + (10 / (1 - d)) * u - κ * s) +
        64 * N k ^ (3 * η + (10 / (1 - d)) * u - 2 * κ * (s - s₀))) / 2 := by
    rw [mul_add, mul_assoc 32, mul_assoc 32, ← Real.rpow_add hNk, ← Real.rpow_add hNk]
    have heq1 : (η + (10 / (1 - d)) * u) + (-κ * s + η) =
        2 * η + (10 / (1 - d)) * u - κ * s := by ring
    have heq2 : (η + (10 / (1 - d)) * u) + (-2 * κ * (s - s₀) + 2 * η) =
        3 * η + (10 / (1 - d)) * u - 2 * κ * (s - s₀) := by ring
    rw [heq1, heq2]
    ring
  rw [hsplit]
  linarith

/-- The same strict power gaps absorb any fixed constant introduced by
strip enlargement or key-coordinate transport. -/
theorem eventually_wide_freezing_with_constant {N : ℕ → ℝ}
    (hNt : Tendsto N atTop atTop) (C : ℝ) {d κ s₀ s u η : ℝ}
    (hu : 0 < u) (hη : η ≤ u / 10)
    (hwide : (10 / (1 - d) + 3) * u < 2 * κ * (s - s₀))
    (hblock : (10 / (1 - d) + 3) * u < κ * s) :
    ∀ᶠ k in atTop,
      C * N k ^ (η + (10 / (1 - d)) * u) *
        (N k ^ (-κ * s + η) + N k ^ (-2 * κ * (s - s₀) + 2 * η)) ≤
          N k ^ (-u) := by
  have ha : 2 * η + (10 / (1 - d)) * u - κ * s < -u := by nlinarith
  have hb : 3 * η + (10 / (1 - d)) * u - 2 * κ * (s - s₀) < -u := by nlinarith
  have h1 := hNt.eventually (eventually_const_mul_rpow_le (2 * C) ha)
  have h2 := hNt.eventually (eventually_const_mul_rpow_le (2 * C) hb)
  filter_upwards [h1, h2, hNt.eventually (eventually_gt_atTop (0 : ℝ))] with k hk1 hk2 hNk
  have hsplit : C * N k ^ (η + (10 / (1 - d)) * u) *
      (N k ^ (-κ * s + η) + N k ^ (-2 * κ * (s - s₀) + 2 * η)) =
      ((2 * C) * N k ^ (2 * η + (10 / (1 - d)) * u - κ * s) +
        (2 * C) * N k ^ (3 * η + (10 / (1 - d)) * u - 2 * κ * (s - s₀))) / 2 := by
    rw [mul_add, mul_assoc C, mul_assoc C, ← Real.rpow_add hNk, ← Real.rpow_add hNk]
    have heq1 : (η + (10 / (1 - d)) * u) + (-κ * s + η) =
        2 * η + (10 / (1 - d)) * u - κ * s := by ring
    have heq2 : (η + (10 / (1 - d)) * u) + (-2 * κ * (s - s₀) + 2 * η) =
        3 * η + (10 / (1 - d)) * u - 2 * κ * (s - s₀) := by ring
    rw [heq1, heq2]
    ring
  rw [hsplit]
  linarith

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
