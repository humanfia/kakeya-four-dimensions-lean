import Submission.Obl.k4_horizontal_strict_parameter_step.ChartCoordinates
import Submission.Obl.k4_horizontal_strict_parameter_step.FirstJet.Statement

/-! Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at d50c59d5b1367f287a76eef33f4c400a8e312ee2,
file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/ChartMixedGeometry.lean`.
The namespace and internal imports are changed to o272. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set

noncomputable section

/-- The normalized mixed test is an original physical graph band in a smaller
static parameter square. The trajectory and prior remain unchanged. -/
theorem chartCoordinates_mixed_test {α : Type*} {A : Set α}
    {b : α → Fin 6 → ℝ} {h : Fin 6 → ℝ} {a D p₀ q₀ t x₀ r w : ℝ}
    {l : α} {y₀ : Fin 2 → ℝ} (ha : 0 < a) (hD : 0 < D) (hl : l ∈ A)
    (hx : |chartCoordinates A b h a D p₀ q₀ l 2 +
      t * chartCoordinates A b h a D p₀ q₀ l 3 - x₀| ≤ 2 * w)
    (hy0 : |chartCoordinates A b h a D p₀ q₀ l 0 - y₀ 0| ≤ r)
    (hy1 : |chartCoordinates A b h a D p₀ q₀ l 1 - y₀ 1| ≤ r) :
    |b l 0 - (p₀ + D * y₀ 0)| ≤ D * r ∧
      |b l 1 - (q₀ + D * y₀ 1)| ≤ D * r ∧
      |b l 2 + t * b l 5 - (predictor h t (b l 0) (b l 1) + a * x₀)| ≤
        2 * a * w := by
  classical
  have hscalar := chartCoordinates_scalar (b := b) h ha.ne' D p₀ q₀ hl t
  rw [hscalar] at hx
  have hstatic0 : chartCoordinates A b h a D p₀ q₀ l 0 = (b l 0 - p₀) / D := by
    simp only [chartCoordinates, piecewise_eq_of_mem _ _ _ hl, Matrix.cons_val_zero]
  have hstatic1 : chartCoordinates A b h a D p₀ q₀ l 1 = (b l 1 - q₀) / D := by
    simp only [chartCoordinates, piecewise_eq_of_mem _ _ _ hl, Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [hstatic0] at hy0
  rw [hstatic1] at hy1
  have hscale (R x c z : ℝ) (hR : 0 < R) :
      |x - (c + R * z)| = R * |(x - c) / R - z| := by
    calc
      _ = |R * ((x - c) / R - z)| := by
        congr 1
        field_simp
        ring
      _ = _ := by rw [abs_mul, abs_of_pos hR]
  refine ⟨?_, ?_, ?_⟩
  · rw [hscale D (b l 0) p₀ (y₀ 0) hD]
    exact mul_le_mul_of_nonneg_left hy0 hD.le
  · rw [hscale D (b l 1) q₀ (y₀ 1) hD]
    exact mul_le_mul_of_nonneg_left hy1 hD.le
  · rw [hscale a (b l 2 + t * b l 5) (predictor h t (b l 0) (b l 1)) x₀ ha]
    exact (mul_le_mul_of_nonneg_left hx ha.le).trans_eq (by ring)

/-- The physical cap of the original chart law gives its normalized integrated
mixed cap at arbitrary centers. This is compatible with conditioning by the
original assignment mass and with all later event restrictions. -/
theorem chartCoordinates_integrated_mixed_cap {α : Type*} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) {A : Set α} {b : α → Fin 6 → ℝ} (h : Fin 6 → ℝ)
    {a D p₀ q₀ r w B : ℝ} (ha : 0 < a) (hD : 0 < D)
    (hsupport : ∀ᵐ p ∂μ, p.1 ∈ A) (I : Set ℝ) (x₀ : ℝ) (y₀ : Fin 2 → ℝ)
    (hcap : μ {p | p.2 ∈ I ∧ |b p.1 0 - (p₀ + D * y₀ 0)| ≤ D * r ∧
      |b p.1 1 - (q₀ + D * y₀ 1)| ≤ D * r ∧
      |b p.1 2 + p.2 * b p.1 5 -
        (predictor h p.2 (b p.1 0) (b p.1 1) + a * x₀)| ≤ 2 * a * w} ≤
          ENNReal.ofReal B) :
    μ {p | p.2 ∈ I ∧
      |chartCoordinates A b h a D p₀ q₀ p.1 2 +
        p.2 * chartCoordinates A b h a D p₀ q₀ p.1 3 - x₀| ≤ 2 * w ∧
      |chartCoordinates A b h a D p₀ q₀ p.1 0 - y₀ 0| ≤ r ∧
      |chartCoordinates A b h a D p₀ q₀ p.1 1 - y₀ 1| ≤ r} ≤ ENNReal.ofReal B := by
  apply (measure_mono_ae ?_).trans hcap
  filter_upwards [hsupport] with p hp he
  have hh := chartCoordinates_mixed_test ha hD hp he.2.1 he.2.2.1 he.2.2.2
  exact ⟨he.1, hh.1, hh.2.1, hh.2.2⟩

/-- Original numerator floors pay for the static area and hidden scale in
mixed caps. The smaller spatial and scalar widths are independent. -/
theorem mixed_reference_cancellation {C B a D r w χ τ d : ℝ}
    (hC : 0 ≤ C) (ha : 0 < a) (hD : 0 ≤ D) (hr : 0 ≤ r)
    (hw : 0 < w) (hχ : 0 ≤ χ) (hτ : 0 ≤ τ) (hd : d ≤ 1)
    (hχr : χ ≤ r * D) (hbudget : C * a ^ d * D ^ 2 ≤ B) :
    4200 * (C * (2 * a * w) ^ d) * τ * (r * D + χ) * (2 * (r * D) + χ) ≤
      (50400 * B * r ^ 2 * w ^ d) * τ := by
  have htwo : (2 : ℝ) ^ d ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num) hd
  have hpower : (2 * a * w) ^ d ≤ 2 * a ^ d * w ^ d := by
    rw [Real.mul_rpow (by positivity) hw.le, Real.mul_rpow (by norm_num) ha.le]
    gcongr
  have harea : (r * D + χ) * (2 * (r * D) + χ) ≤ 6 * (r ^ 2 * D ^ 2) := by
    calc
      _ ≤ (2 * (r * D)) * (3 * (r * D)) := by gcongr <;> linarith
      _ = _ := by ring
  calc
    _ = (4200 * τ) * (C * (2 * a * w) ^ d) *
        ((r * D + χ) * (2 * (r * D) + χ)) := by ring
    _ ≤ (4200 * τ) * (C * (2 * a ^ d * w ^ d)) * (6 * (r ^ 2 * D ^ 2)) := by
      gcongr
    _ = 50400 * (C * a ^ d * D ^ 2) * r ^ 2 * w ^ d * τ := by ring
    _ ≤ _ := by gcongr

end

end Submission.Obl.k4_horizontal_strict_parameter_step
