/- Adapted within this LOT tree from o218/x0764, commit 57a9c674add438aa35f784b08ec4154ae5ff1920,
Submission/Obl/k4_horizontal_endpoint_wide_return/Wide/MixedTerm.lean. -/
import Mathlib
import Submission.Lib.K4PolynomialRemez

set_option linter.unusedVariables false

/-!
# Removing the mixed term of a bilinear field along a third direction

Last part of the "common coefficient field" step of the wide-interval proposition (paper
`prop:wide-interval`): a bilinear interpolant `β₀ + β₁ x + β₂ y + m x y` that agrees to `E` with
an affine function of time along a line `t ↦ (x₀ + t a₁, y₀ + t a₂)` on a set of times of measure
`≥ η` in `[0,1]` has `|m a₁ a₂| ≤ 8 (24/η)² E` (Remez, lib `K4PolynomialRemez`, and the second
difference of a quadratic).  When the line's direction has both basis components bounded below
by a reciprocal subpower, this bounds the mixed coefficient `m`.
-/

namespace Submission.Obl.k4_horizontal_wide_interval_return

open MeasureTheory Polynomial

/-- The leading coefficient of a quadratic bounded on `[0,1]`. -/
theorem quadratic_leading_le {c₀ c₁ c₂ E : ℝ}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, |c₀ + c₁ * t + c₂ * t ^ 2| ≤ E) : |c₂| ≤ 8 * E := by
  have h0 : |c₀| ≤ E := by simpa using h 0 (by norm_num)
  have h1 : |c₀ + c₁ + c₂| ≤ E := by simpa using h 1 (by norm_num)
  have hh : |c₀ + c₁ / 2 + c₂ / 4| ≤ E := by
    have := h (1 / 2) (by norm_num)
    have e : c₀ + c₁ * (1 / 2) + c₂ * (1 / 2) ^ 2 = c₀ + c₁ / 2 + c₂ / 4 := by ring
    rwa [e] at this
  have heq : c₂ = 2 * (c₀ + (c₀ + c₁ + c₂)) - 4 * (c₀ + c₁ / 2 + c₂ / 4) := by ring
  rw [heq]
  calc |2 * (c₀ + (c₀ + c₁ + c₂)) - 4 * (c₀ + c₁ / 2 + c₂ / 4)|
      ≤ |2 * (c₀ + (c₀ + c₁ + c₂))| + |4 * (c₀ + c₁ / 2 + c₂ / 4)| := abs_sub _ _
    _ = 2 * |c₀ + (c₀ + c₁ + c₂)| + 4 * |c₀ + c₁ / 2 + c₂ / 4| := by
        rw [abs_mul, abs_mul]; norm_num
    _ ≤ 2 * (|c₀| + |c₀ + c₁ + c₂|) + 4 * |c₀ + c₁ / 2 + c₂ / 4| := by
        gcongr; exact abs_add_le _ _
    _ ≤ 2 * (E + E) + 4 * E := by gcongr
    _ = 8 * E := by ring

/-- **Mixed term along a third line.** -/
theorem mixed_term_le {β₀ β₁ β₂ m x₀ y₀ a₁ a₂ φ₀ φ₁ E η : ℝ} (S : Set ℝ) (hη : 0 < η)
    (hη1 : η ≤ 1) (hE : 0 ≤ E) (hS : S ⊆ Set.Icc (0 : ℝ) 1)
    (hmass : ENNReal.ofReal η ≤ volume S)
    (hfit : ∀ t ∈ S, |(β₀ + β₁ * (x₀ + t * a₁) + β₂ * (y₀ + t * a₂) +
      m * (x₀ + t * a₁) * (y₀ + t * a₂)) - (φ₀ + φ₁ * t)| ≤ E) :
    |m * a₁ * a₂| ≤ 8 * ((24 / η) ^ 2 * E) := by
  -- the difference is a quadratic in time
  set c₀ := β₀ + β₁ * x₀ + β₂ * y₀ + m * x₀ * y₀ - φ₀ with hc₀
  set c₁ := β₁ * a₁ + β₂ * a₂ + m * (x₀ * a₂ + y₀ * a₁) - φ₁ with hc₁
  set c₂ := m * a₁ * a₂ with hc₂
  have hform : ∀ t, (β₀ + β₁ * (x₀ + t * a₁) + β₂ * (y₀ + t * a₂) +
      m * (x₀ + t * a₁) * (y₀ + t * a₂)) - (φ₀ + φ₁ * t) = c₀ + c₁ * t + c₂ * t ^ 2 := by
    intro t; simp only [hc₀, hc₁, hc₂]; ring
  let p : Polynomial ℝ := Polynomial.C c₀ + Polynomial.C c₁ * X + Polynomial.C c₂ * X ^ 2
  have hpeval : ∀ t, p.eval t = c₀ + c₁ * t + c₂ * t ^ 2 := by
    intro t; simp [p]
  have hpdeg : p.natDegree ≤ 2 := by
    simp only [p]
    refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
    · simp
    · exact (natDegree_C_mul_le _ _).trans (by simp)
    · exact (natDegree_C_mul_le _ _).trans (by simp)
  have hremez := Submission.Lib.K4PolynomialRemez.polynomial_remez_unit p 2 hpdeg S hη hη1 hE hS
    hmass (by intro t ht; rw [hpeval, ← hform]; exact hfit t ht)
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, |c₀ + c₁ * t + c₂ * t ^ 2| ≤ (24 / η) ^ 2 * E := by
    intro t ht
    have := hremez t ht
    rw [hpeval] at this
    calc |c₀ + c₁ * t + c₂ * t ^ 2| ≤ (8 * ((2 : ℕ) + 1 : ℝ) / η) ^ 2 * E := this
      _ = (24 / η) ^ 2 * E := by norm_num
  exact quadratic_leading_le hbound

end Submission.Obl.k4_horizontal_wide_interval_return
