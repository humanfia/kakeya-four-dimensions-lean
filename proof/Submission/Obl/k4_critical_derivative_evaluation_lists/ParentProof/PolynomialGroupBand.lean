/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, PolynomialGroupBand.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.NativeGroupBand

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory Set
open scoped ENNReal

/-- A quadratic band with quadratic coefficient at most its thickness is
paid for by the same original joint caps and unchanged external palette. -/
theorem original_native_group_polynomial_band_cap_window
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) (U : Set Y)
    (b : Y → Fin 6 → ℝ) (time : Y → ℝ) (velocity : Y → ℤ) (j : ℤ)
    (δ r H D K m C d c₀ c₁ c₂ : ℝ) (palette : ℝ≥0∞) (p : Fin 3 → ℝ)
    (hδ : 0 < δ) (hr : 0 < r) (hH : 0 ≤ H) (hK : 4 ≤ K) (hC : 0 ≤ C)
    (hδD : K * δ ≤ D) (hmesh : 3 * δ ≤ r)
    (hp₀ : |p 0| ≤ K) (hp₂ : |p 2| ≤ K) (hc₁ : |c₁| ≤ K) (hc₂ : |c₂| ≤ r)
    (ht : ∀ y ∈ U, |time y - m| ≤ H / 2)
    (hunit : ∀ y ∈ U, |time y| ≤ 1)
    (hb₀ : ∀ y ∈ U, |b y 0 - p 0| ≤ D) (hb₁ : ∀ y ∈ U, |b y 1 - p 1| ≤ D)
    (hv : ∀ y ∈ U, |b y 3 - p 2| ≤ D) (hdef : ∀ y ∈ U, |b y 4 + b y 0| ≤ D)
    (hband : ∀ y ∈ U,
      |b y 2 + time y * b y 5 - (c₀ + c₁ * time y + c₂ * (time y) ^ 2)| ≤ 3 * r)
    (hvel : ∀ y ∈ U, velocity y = j)
    (hcap : ∀ (q : Fin 3 → ℤ) (n : ℤ),
      μ {y | (fun e => ⌊nativeHorizontalPoint (b y) (time y) e / δ⌋) = q ∧
        ⌊(b y 2 + time y * b y 5) / r⌋ = n ∧ velocity y = j} ≤
        ENNReal.ofReal (C * δ ^ 3 * r ^ d) * palette) :
    μ U ≤ ENNReal.ofReal (1440 * C * K * (H + δ) * D ^ 2 * r ^ d) * palette := by
  let L : Fin 4 → ℝ := ![c₀, c₁, 0, 0]
  have hK0 : 0 ≤ K := by linarith
  have hL : ∀ e : Fin 3, |L e.succ| ≤ K := by
    intro e
    fin_cases e
    · exact hc₁
    · simpa [L] using hK0
    · simpa [L] using hK0
  have heq (b : Fin 6 → ℝ) (t : ℝ) :
      affineBaseValue L (nativeHorizontalPoint b t) = c₀ + t * c₁ := by
    simp [affineBaseValue, L, Fin.sum_univ_succ, nativeHorizontalPoint]
    ring
  apply original_group_band_joint_cap μ U (fun y => nativeHorizontalPoint (b y) (time y))
    (fun y => b y 2 + time y * b y 5) velocity j δ r (H + δ) D K (m - H / 2)
    C (r ^ d) palette p L hδ hr (by linarith) hC (Real.rpow_nonneg hr.le _)
    (by linarith) hδD hmesh hp₀ hp₂ hL
  · intro y hy
    have hh := abs_le.mp (ht y hy)
    change time y ∈ Icc (m - H / 2) (m - H / 2 + (H + δ))
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  · intro y hy
    exact (native_initial_group_geometry (b y) p (time y) D (hunit y hy)
      (hb₀ y hy) (hb₁ y hy) (hv y hy) (hdef y hy)).1
  · intro y hy
    exact (native_initial_group_geometry (b y) p (time y) D (hunit y hy)
      (hb₀ y hy) (hb₁ y hy) (hv y hy) (hdef y hy)).2
  · intro y hy
    rw [heq]
    have hquad : |c₂ * (time y) ^ 2| ≤ r := by
      rw [abs_mul, abs_pow]
      exact (mul_le_mul hc₂ (pow_le_one₀ (abs_nonneg _) (hunit y hy))
        (sq_nonneg _) hr.le).trans_eq (mul_one _)
    calc
      _ = |(b y 2 + time y * b y 5 -
          (c₀ + c₁ * time y + c₂ * (time y) ^ 2)) + c₂ * (time y) ^ 2| := by congr 1; ring
      _ ≤ |b y 2 + time y * b y 5 - (c₀ + c₁ * time y + c₂ * (time y) ^ 2)| +
          |c₂ * (time y) ^ 2| := abs_add_le _ _
      _ ≤ 3 * r + r := add_le_add (hband y hy) hquad
      _ ≤ K * r := by nlinarith
  · exact hvel
  · exact hcap

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
