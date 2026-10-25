/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at a653e9614f679c1b36a9606abd448afbd7b87d1f, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeFineNumerics.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Mathlib

namespace Submission.Obl.k4_horizontal_strict_parameter_step

/-- A single numerical mesh error bounds both shared jitter and corner
reconstruction errors for every actual predictor in the comparison menu. -/
theorem comparison_roundoff_common {K B D χ δ : ℝ}
    (hK : 1 ≤ K) (hB : 0 ≤ B) (hD : 0 < D) (hD1 : D ≤ 1)
    (hχ : 0 ≤ χ) (hδ : 0 ≤ δ) :
    (2 * (4 * B) * δ + (6 * (4 * B) / D) * (χ + (3 * K + 1) * δ) ≤
      (200 * B / D) * (χ + K * δ)) ∧
    (2 * B * δ + (8 * B / D) * (3 * χ + (4 * (3 * K) + 5) * δ) ≤
      (200 * B / D) * (χ + K * δ)) := by
  have hK0 : 0 ≤ K := by linarith
  have hBD : B * δ * D ≤ B * δ * K :=
    mul_le_mul_of_nonneg_left (hD1.trans hK) (mul_nonneg hB hδ)
  have hBK : B * δ ≤ B * δ * K := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hK (mul_nonneg hB hδ)
  have hBχ : 0 ≤ B * χ := mul_nonneg hB hχ
  have hBδK : 0 ≤ B * δ * K := mul_nonneg (mul_nonneg hB hδ) hK0
  have heq : (200 * B / D) * (χ + K * δ) = (200 * B * (χ + K * δ)) / D := by ring
  rw [heq]
  constructor
  · apply (le_div_iff₀ hD).mpr
    calc
      _ = 8 * B * δ * D + 24 * B * (χ + (3 * K + 1) * δ) := by field_simp; ring
      _ ≤ _ := by nlinarith
  · apply (le_div_iff₀ hD).mpr
    calc
      _ = 2 * B * δ * D + 8 * B * (3 * χ + (12 * K + 5) * δ) := by field_simp; ring
      _ ≤ _ := by nlinarith

/-- Resolving the finest original mixed scale supplies every comparison mesh
inequality at once. In particular it resolves all larger matching tolerances. -/
theorem finest_mesh_control {K B D χ δ a ζ q : ℝ}
    (hK : 1 ≤ K) (hB : 1 ≤ B) (hD : 0 < D) (hD1 : D ≤ 1)
    (hχ : 0 < χ) (hδ : 0 < δ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1)
    (hDq : D ≤ q ^ 2)
    (hfine : (200 * B / D) * (χ + K * δ) ≤ a * ζ) :
    χ ≤ ζ * D ∧ 4 * K * δ ≤ ζ * D ∧ δ ≤ 1 ∧ δ ≤ q ∧
      2 * χ + (3 * (3 * K) + 4) * δ ≤ D ∧
      2 * (4 * B) * δ + (6 * (4 * B) / D) * (χ + (3 * K + 1) * δ) ≤ a * ζ ∧
      2 * B * δ + (8 * B / D) * (3 * χ + (4 * (3 * K) + 5) * δ) ≤ a * ζ := by
  have hK0 : 0 ≤ K := by linarith
  have hB0 : 0 ≤ B := by linarith
  have heq : (200 * B / D) * (χ + K * δ) = (200 * B * (χ + K * δ)) / D := by ring
  have hf : 200 * B * (χ + K * δ) ≤ a * ζ * D := by
    rw [heq] at hfine
    exact (div_le_iff₀ hD).mp hfine
  have haD : a * ζ * D ≤ ζ * D := by
    have hh := mul_le_mul_of_nonneg_right ha1 (mul_nonneg hζ.le hD.le)
    nlinarith
  have hχB : 200 * χ ≤ 200 * B * χ := by
    have hh := mul_le_mul_of_nonneg_right hB hχ.le
    nlinarith
  have hδB : 200 * K * δ ≤ 200 * B * (K * δ) := by
    have hh := mul_le_mul_of_nonneg_right hB (mul_nonneg hK0 hδ.le)
    nlinarith
  have hχsmall : 200 * χ ≤ ζ * D := by
    have hh : 0 ≤ B * K * δ := by positivity
    nlinarith
  have hδsmall : 200 * K * δ ≤ ζ * D := by
    have hh : 0 ≤ B * χ := by positivity
    nlinarith
  have hδK : δ ≤ K * δ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hK hδ.le
  have hζD : ζ * D ≤ D := by nlinarith
  have hδD : δ ≤ D := by nlinarith
  have hδq : δ ≤ q := hδD.trans (hDq.trans (by nlinarith))
  obtain ⟨hc, hj⟩ := comparison_roundoff_common hK hB0 hD hD1 hχ.le hδ.le
  refine ⟨?_, ?_, hδD.trans hD1, hδq, ?_, hc.trans hfine, hj.trans hfine⟩ <;> nlinarith

/-- The old baseline's mixed tests use the same finest mesh budget, since its
whole-square norm is smaller than the common comparison-menu bound. -/
theorem baseline_roundoff_of_common {K P B D χ δ a ζ : ℝ}
    (hK : 1 ≤ K) (hP : 0 ≤ P) (hPB : P ≤ B) (hD : 0 < D) (hD1 : D ≤ 1)
    (hχ : 0 ≤ χ) (hδ : 0 ≤ δ) (haζ : 0 ≤ a * ζ)
    (hfine : (200 * B / D) * (χ + K * δ) ≤ a * ζ) :
    8 * P * δ + (24 * P / D) * (χ + (3 * K + 1) * δ) ≤ 2 * a * ζ := by
  have hB : 0 ≤ B := hP.trans hPB
  have hc := (comparison_roundoff_common hK hB hD hD1 hχ hδ).1.trans hfine
  calc
    _ ≤ 2 * (4 * B) * δ + (6 * (4 * B) / D) * (χ + (3 * K + 1) * δ) := by
      have hK0 : 0 ≤ K := by linarith
      calc
        _ ≤ 8 * B * δ + (24 * B / D) * (χ + (3 * K + 1) * δ) := by gcongr
        _ = _ := by ring
    _ ≤ a * ζ := hc
    _ ≤ _ := by nlinarith

end Submission.Obl.k4_horizontal_strict_parameter_step
