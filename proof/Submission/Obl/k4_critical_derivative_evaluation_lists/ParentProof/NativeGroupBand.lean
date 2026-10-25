/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, NativeGroupBand.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.GroupBandGrid
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.NativeRowField

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory Set
open scoped ENNReal

theorem native_initial_group_geometry
    (b : Fin 6 → ℝ) (p : Fin 3 → ℝ) (t D : ℝ) (ht : |t| ≤ 1)
    (hb₀ : |b 0 - p 0| ≤ D) (hb₁ : |b 1 - p 1| ≤ D)
    (hv : |b 3 - p 2| ≤ D) (hdef : |b 4 + b 0| ≤ D) :
    |nativeHorizontalPoint b t 1 - p 0 - t * p 2| ≤ 2 * D ∧
      |nativeHorizontalPoint b t 2 - p 1 + t * p 0| ≤ 3 * D := by
  have hm (x : ℝ) (hx : |x| ≤ D) : |t * x| ≤ D := by
    rw [abs_mul]
    exact (mul_le_mul ht hx (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  constructor
  · change |b 0 + t * b 3 - p 0 - t * p 2| ≤ 2 * D
    calc
      _ = |(b 0 - p 0) + t * (b 3 - p 2)| := by congr 1; ring
      _ ≤ |b 0 - p 0| + |t * (b 3 - p 2)| := abs_add_le _ _
      _ ≤ D + D := add_le_add hb₀ (hm _ hv)
      _ = _ := by ring
  · change |b 1 + t * b 4 - p 1 + t * p 0| ≤ 3 * D
    calc
      _ = |(b 1 - p 1) + t * (b 4 + b 0) - t * (b 0 - p 0)| := by congr 1; ring
      _ ≤ |b 1 - p 1| + |t * (b 4 + b 0)| + |t * (b 0 - p 0)| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ D + D + D := add_le_add (add_le_add hb₁ (hm _ hdef)) (hm _ hb₀)
      _ = _ := by ring

/-- A native group in one true time window and one affine hidden band is
bounded directly by the ORIGINAL finite-mesh joint caps and external palette. -/
theorem original_native_affine_group_band_cap
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) (U : Set Y)
    (b : Y → Fin 6 → ℝ) (time : Y → ℝ) (velocity : Y → ℤ) (j : ℤ)
    (δ r H D K t₀ C d c₀ c₁ : ℝ) (palette : ℝ≥0∞) (p : Fin 3 → ℝ)
    (hδ : 0 < δ) (hr : 0 < r) (hK : 3 ≤ K) (hC : 0 ≤ C)
    (hδH : δ ≤ H) (hδD : K * δ ≤ D) (hmesh : 3 * δ ≤ r)
    (hp₀ : |p 0| ≤ K) (hp₂ : |p 2| ≤ K) (hc₁ : |c₁| ≤ K)
    (ht : ∀ y ∈ U, time y ∈ Icc t₀ (t₀ + H))
    (hunit : ∀ y ∈ U, |time y| ≤ 1)
    (hb₀ : ∀ y ∈ U, |b y 0 - p 0| ≤ D) (hb₁ : ∀ y ∈ U, |b y 1 - p 1| ≤ D)
    (hv : ∀ y ∈ U, |b y 3 - p 2| ≤ D) (hdef : ∀ y ∈ U, |b y 4 + b y 0| ≤ D)
    (hband : ∀ y ∈ U, |b y 2 + time y * b y 5 - c₀ - time y * c₁| ≤ 3 * r)
    (hvel : ∀ y ∈ U, velocity y = j)
    (hcap : ∀ (q : Fin 3 → ℤ) (n : ℤ),
      μ {y | (fun e => ⌊nativeHorizontalPoint (b y) (time y) e / δ⌋) = q ∧
        ⌊(b y 2 + time y * b y 5) / r⌋ = n ∧ velocity y = j} ≤
        ENNReal.ofReal (C * δ ^ 3 * r ^ d) * palette) :
    μ U ≤ ENNReal.ofReal (1440 * C * K * H * D ^ 2 * r ^ d) * palette := by
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
    (fun y => b y 2 + time y * b y 5) velocity j δ r H D K t₀ C (r ^ d) palette p L
    hδ hr (by linarith) hC (Real.rpow_nonneg hr.le _) hδH hδD hmesh hp₀ hp₂ hL ht
  · intro y hy
    exact (native_initial_group_geometry (b y) p (time y) D (hunit y hy)
      (hb₀ y hy) (hb₁ y hy) (hv y hy) (hdef y hy)).1
  · intro y hy
    exact (native_initial_group_geometry (b y) p (time y) D (hunit y hy)
      (hb₀ y hy) (hb₁ y hy) (hv y hy) (hdef y hy)).2
  · intro y hy
    rw [heq]
    have hh : |b y 2 + time y * b y 5 - (c₀ + time y * c₁)| ≤ 3 * r := by
      simpa only [sub_add_eq_sub_sub] using hband y hy
    exact hh.trans (mul_le_mul_of_nonneg_right hK hr.le)
  · exact hvel
  · exact hcap

/-- A window shorter than the original mesh is enlarged once; the counted
mass is still the original measure, and the cost is H+delta. -/
theorem original_native_group_band_cap_window
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) (U : Set Y)
    (b : Y → Fin 6 → ℝ) (time : Y → ℝ) (velocity : Y → ℤ) (j : ℤ)
    (δ r H D K m C d c₀ c₁ : ℝ) (palette : ℝ≥0∞) (p : Fin 3 → ℝ)
    (hδ : 0 < δ) (hr : 0 < r) (hH : 0 ≤ H) (hK : 3 ≤ K) (hC : 0 ≤ C)
    (hδD : K * δ ≤ D) (hmesh : 3 * δ ≤ r)
    (hp₀ : |p 0| ≤ K) (hp₂ : |p 2| ≤ K) (hc₁ : |c₁| ≤ K)
    (ht : ∀ y ∈ U, |time y - m| ≤ H / 2)
    (hunit : ∀ y ∈ U, |time y| ≤ 1)
    (hb₀ : ∀ y ∈ U, |b y 0 - p 0| ≤ D) (hb₁ : ∀ y ∈ U, |b y 1 - p 1| ≤ D)
    (hv : ∀ y ∈ U, |b y 3 - p 2| ≤ D) (hdef : ∀ y ∈ U, |b y 4 + b y 0| ≤ D)
    (hband : ∀ y ∈ U, |b y 2 + time y * b y 5 - c₀ - time y * c₁| ≤ 3 * r)
    (hvel : ∀ y ∈ U, velocity y = j)
    (hcap : ∀ (q : Fin 3 → ℤ) (n : ℤ),
      μ {y | (fun e => ⌊nativeHorizontalPoint (b y) (time y) e / δ⌋) = q ∧
        ⌊(b y 2 + time y * b y 5) / r⌋ = n ∧ velocity y = j} ≤
        ENNReal.ofReal (C * δ ^ 3 * r ^ d) * palette) :
    μ U ≤ ENNReal.ofReal (1440 * C * K * (H + δ) * D ^ 2 * r ^ d) * palette := by
  apply original_native_affine_group_band_cap μ U b time velocity j δ r (H + δ) D K
    (m - H / 2) C d c₀ c₁ palette p hδ hr hK hC (by linarith) hδD hmesh hp₀ hp₂ hc₁
  · intro y hy
    have hh := abs_le.mp (ht y hy)
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  · exact hunit
  · exact hb₀
  · exact hb₁
  · exact hv
  · exact hdef
  · exact hband
  · exact hvel
  · exact hcap

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
