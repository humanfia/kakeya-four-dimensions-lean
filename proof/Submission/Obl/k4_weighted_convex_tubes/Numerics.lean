import Submission.Obl.k4_weighted_convex_tubes.Basic

namespace Submission.Obl.k4_weighted_convex_tubes

open MeasureTheory Set Filter
open scoped Topology

noncomputable def scale (D : ℕ) : ℝ := 1 / (100 * (D : ℝ))

theorem scale_pos {D : ℕ} (hD : 1 ≤ D) : 0 < scale D := by
  have : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  unfold scale
  positivity

theorem scale_le {D : ℕ} (hD : 1 ≤ D) : scale D ≤ 1 / 100 := by
  have hd : (1 : ℝ) ≤ D := by exact_mod_cast hD
  unfold scale
  exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)

theorem scale_sq {D : ℕ} (_hD : 1 ≤ D) :
    scale D ^ 2 = 1 / (10000 * (D : ℝ) ^ 2) := by
  unfold scale
  ring

theorem scale_sq_le {D : ℕ} (hD : 1 ≤ D) :
    scale D ^ 2 ≤ 1 / (D : ℝ) ^ 2 := by
  rw [scale_sq hD]
  have hd : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [sq_pos_of_pos hd]

theorem scale_rpow_inv {D : ℕ} (hD : 1 ≤ D) (ε : ℝ) :
    scale D ^ ε * ((100 : ℝ) ^ ε * (D : ℝ) ^ ε) = 1 := by
  have hd : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  unfold scale
  rw [one_div, Real.inv_rpow (by positivity),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 100) hd.le]
  exact inv_mul_cancel₀ (by positivity)

theorem eventual_dense {α η c r₀ : ℝ} (hα : 0 < α) (hη : 0 < η)
    (hηα : 2 * η ≤ α) (hc : 0 < c) (hr₀ : 0 < r₀) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ D : ℕ, N ≤ D →
      scale D ≤ r₀ ∧
      scale D ^ α * scale D ^ 2 ≤ c * (D : ℝ) ^ (-η) / (D : ℝ) ^ 2 := by
  have hlim : Tendsto (fun D : ℕ => (D : ℝ) ^ (-η)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hη).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hlim.eventually_le_const hc)
  let N := max 1 (max N₁ ⌈1 / (100 * r₀)⌉₊)
  have hN : 1 ≤ N := le_max_left _ _
  refine ⟨N, hN, fun D hND => ?_⟩
  have hD : 1 ≤ D := hN.trans hND
  have hd1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hd : (0 : ℝ) < D := by linarith
  have hD₁ : N₁ ≤ D := (le_max_left _ _).trans ((le_max_right _ _).trans hND)
  have hD₂ : ⌈1 / (100 * r₀)⌉₊ ≤ D :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hND)
  have hnum : 1 / (100 * r₀) ≤ (D : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hD₂)
  have hr : scale D ≤ r₀ := by
    unfold scale
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 100 * D)]
    have := (div_le_iff₀ (by positivity : 0 < 100 * r₀)).mp hnum
    nlinarith
  refine ⟨hr, ?_⟩
  have hscale : scale D ≤ (D : ℝ)⁻¹ := by
    unfold scale
    rw [← one_div]
    exact one_div_le_one_div_of_le hd (by linarith)
  have hrpow : scale D ^ α ≤ (D : ℝ) ^ (-α) := by
    calc
      _ ≤ ((D : ℝ)⁻¹) ^ α := Real.rpow_le_rpow (scale_pos hD).le hscale hα.le
      _ = _ := by rw [Real.inv_rpow hd.le, Real.rpow_neg hd.le]
  have hpow : (D : ℝ) ^ (-α) ≤ c * (D : ℝ) ^ (-η) := by
    calc
      _ ≤ (D : ℝ) ^ (-η + -η) :=
        Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
      _ = (D : ℝ) ^ (-η) * (D : ℝ) ^ (-η) := Real.rpow_add hd _ _
      _ ≤ c * (D : ℝ) ^ (-η) :=
        mul_le_mul_of_nonneg_right (hN₁ D hD₁) (Real.rpow_nonneg hd.le _)
  calc
    _ ≤ (c * (D : ℝ) ^ (-η)) * (1 / (D : ℝ) ^ 2) :=
      mul_le_mul (hrpow.trans hpow) (scale_sq_le hD) (sq_nonneg _) (by positivity)
    _ = _ := by ring

theorem density_reciprocal {D : ℕ} (hD : 1 ≤ D) {c η V : ℝ} (hc : 0 < c)
    (hdense : c * (D : ℝ) ^ (-η) / (D : ℝ) ^ 2 ≤ V) :
    1 / (D : ℝ) ^ 2 ≤ ((D : ℝ) ^ η / c) * V := by
  have hd : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hp : 0 < (D : ℝ) ^ η := Real.rpow_pos_of_pos hd _
  have hh := mul_le_mul_of_nonneg_left hdense (div_nonneg hp.le hc.le)
  rw [Real.rpow_neg hd.le] at hh
  have heq : ((D : ℝ) ^ η / c) * (c * ((D : ℝ) ^ η)⁻¹ / (D : ℝ) ^ 2) =
      1 / (D : ℝ) ^ 2 := by field_simp
  rwa [heq] at hh

end Submission.Obl.k4_weighted_convex_tubes
