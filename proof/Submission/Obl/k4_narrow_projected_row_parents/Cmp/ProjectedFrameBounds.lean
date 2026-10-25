/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/ProjectedFrameBounds.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.ProjectedDomainBudget
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetJets

/-! Bounds of the actual common frame in a projected label's normalized strip. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain

open Metric Set
open Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

noncomputable section

theorem projected_common_coefficients {H β q χ g m t u v : ℝ}
    (hH : 1 ≤ H) (hβ : 0 < β) (hq : 0 < q) (hq1 : q ≤ 1) (hg : 0 < g) (hm : 0 < m)
    (hqg : q * g ≤ m) (hmβ : m ≤ β) (b : Fin 6 → ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfit : ∀ r ∈ Icc (0 : ℝ) 1, |b 1 + r * b 4 - u - r * v| ≤ H * β) :
    |((code q χ g m b t) 4 : ℝ) * m - u - timeCenter q (code q χ g m b t) * v| ≤ 2 * H * β ∧
    |100 * q * (((code q χ g m b t) 3 : ℝ) * g - v)| ≤ 300 * H * β ∧
    |100 * m| ≤ 100 * H * β := by
  let c := code q χ g m b t
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hβH : β ≤ H * β := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hH hβ.le
  have ht₀ := timeCenter_mem_unit (χ := χ) (g := g) (m := m) hq b ht
  have hposition : |b 1 + timeCenter q c * b 4 - (c 4 : ℝ) * m| ≤ m := by
    simpa [c, code, timeCenter, mul_assoc] using
      Submission.Lib.K4VelocityStrips.midpoint_floor_center_bound hm (b 1 + timeCenter q c * b 4)
  have hslope := projected_velocity_error b hfit
  have hround : |(c 3 : ℝ) * g - b 4| ≤ g := by
    simpa [c, code, abs_sub_comm] using
      Submission.Lib.K4VelocityStrips.midpoint_floor_center_bound hg (b 4)
  have hraw : |(c 3 : ℝ) * g - v| ≤ g + 2 * (H * β) := by
    have hid : (c 3 : ℝ) * g - v = ((c 3 : ℝ) * g - b 4) + (b 4 - v) := by ring
    rw [hid]
    exact (abs_add_le _ _).trans (add_le_add hround hslope)
  refine ⟨?_, ?_, ?_⟩
  · have hid : (c 4 : ℝ) * m - u - timeCenter q c * v =
        ((c 4 : ℝ) * m - (b 1 + timeCenter q c * b 4)) +
          (b 1 + timeCenter q c * b 4 - u - timeCenter q c * v) := by ring
    change |(c 4 : ℝ) * m - u - timeCenter q c * v| ≤ _
    rw [hid]
    have hpos' : |(c 4 : ℝ) * m - (b 1 + timeCenter q c * b 4)| ≤ m := by
      simpa only [abs_sub_comm] using hposition
    have hh := (abs_add_le _ _).trans (add_le_add hpos' (hfit _ ht₀))
    linarith only [hh, hmβ, hβH]
  · change |100 * q * ((c 3 : ℝ) * g - v)| ≤ _
    rw [abs_mul, abs_of_pos (by positivity : 0 < 100 * q)]
    calc
      _ ≤ 100 * q * (g + 2 * (H * β)) := mul_le_mul_of_nonneg_left hraw (by positivity)
      _ = (200 * H * β) * q + 100 * (q * g) := by ring
      _ ≤ (200 * H * β) * 1 + 100 * m :=
        add_le_add (mul_le_mul_of_nonneg_left hq1 (by positivity))
          (mul_le_mul_of_nonneg_left hqg (by norm_num))
      _ ≤ 300 * H * β := by nlinarith only [hmβ, hβH]
  · rw [abs_of_pos (by positivity : 0 < 100 * m)]
    nlinarith only [hmβ, hβH]

/-- The real strip coordinate remains bounded on the entire complex comparison
ball, using the explicit coefficient bounds above. -/
theorem normalized_strip_coordinate_bound {H β A₀ A₁ A₂ : ℝ}
    (hH : 1 ≤ H) (hβ : 0 < β)
    (h₀ : |A₀| ≤ 2 * H * β) (h₁ : |A₁| ≤ 300 * H * β) (h₂ : |A₂| ≤ 100 * H * β)
    (z₀ z₂ : ℂ) (hz₀ : ‖z₀‖ ≤ 4) (hz₂ : ‖z₂‖ ≤ 4) :
    ‖((((A₀ : ℂ) + (A₁ : ℂ) * z₀ + (A₂ : ℂ) * z₂) / (β : ℂ) + 1) / 2)‖ ≤ 1000 * H := by
  have hH0 : 0 ≤ H := (zero_le_one : (0 : ℝ) ≤ 1).trans hH
  have hnorm : ‖(A₀ : ℂ) + (A₁ : ℂ) * z₀ + (A₂ : ℂ) * z₂‖ ≤ 1602 * H * β := by
    calc
      _ ≤ ‖(A₀ : ℂ)‖ + ‖(A₁ : ℂ) * z₀‖ + ‖(A₂ : ℂ) * z₂‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = |A₀| + |A₁| * ‖z₀‖ + |A₂| * ‖z₂‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 2 * H * β + (300 * H * β) * 4 + (100 * H * β) * 4 := by
        exact add_le_add (add_le_add h₀ (mul_le_mul h₁ hz₀ (norm_nonneg _) (by positivity)))
          (mul_le_mul h₂ hz₂ (norm_nonneg _) (by positivity))
      _ = _ := by ring
  have hdiv : ‖((A₀ : ℂ) + (A₁ : ℂ) * z₀ + (A₂ : ℂ) * z₂) / (β : ℂ)‖ ≤ 1602 * H := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ]
    exact (div_le_iff₀ hβ).mpr (by nlinarith only [hnorm])
  rw [norm_div, Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have h := norm_add_le (((A₀ : ℂ) + (A₁ : ℂ) * z₀ + (A₂ : ℂ) * z₂) / (β : ℂ)) 1
  rw [norm_one] at h
  linarith only [h, hdiv, hH]

def complexTime (q : ℝ) (c : Code) (z : EuclideanSpace ℂ (Fin 3)) : ℂ :=
  (timeCenter q c : ℂ) + (100 * q : ℝ) * z 0

def complexMinor (q g m : ℝ) (c : Code) (z : EuclideanSpace ℂ (Fin 3)) : ℂ :=
  ((c 4 : ℝ) * m : ℝ) + (100 * q * ((c 3 : ℝ) * g) : ℝ) * z 0 + (100 * m : ℝ) * z 2

/-- Both variables of the normalized projected polynomial remain in a complex
box of radius1000H on the full common ball4, at every actual projected incidence. -/
theorem projected_common_complex_box {H β q χ g m t u v : ℝ}
    (hH : 1 ≤ H) (hβ : 0 < β) (hq : 0 < q) (hq1 : q ≤ 1) (hg : 0 < g) (hm : 0 < m)
    (hqg : q * g ≤ m) (hmβ : m ≤ β) (b : Fin 6 → ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfit : ∀ r ∈ Icc (0 : ℝ) 1, |b 1 + r * b 4 - u - r * v| ≤ H * β)
    (z : EuclideanSpace ℂ (Fin 3)) (hz : ‖z‖ ≤ 4) :
    ‖complexTime q (code q χ g m b t) z‖ ≤ 1000 * H ∧
    ‖((complexMinor q g m (code q χ g m b t) z - (u : ℂ) -
      complexTime q (code q χ g m b t) z * (v : ℂ)) / (β : ℂ) + 1) / 2‖ ≤ 1000 * H := by
  let c := code q χ g m b t
  have hz₀ : ‖z 0‖ ≤ 4 := (PiLp.norm_apply_le z 0).trans hz
  have hz₂ : ‖z 2‖ ≤ 4 := (PiLp.norm_apply_le z 2).trans hz
  have ht₀ := timeCenter_mem_unit (χ := χ) (g := g) (m := m) hq b ht
  constructor
  · change ‖(timeCenter q c : ℂ) + (100 * q : ℝ) * z 0‖ ≤ _
    have htime : |timeCenter q c| ≤ 1 := by rw [abs_of_nonneg ht₀.1]; exact ht₀.2
    have h := norm_add_le (timeCenter q c : ℂ) ((100 * q : ℝ) * z 0)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h
    norm_num [abs_of_pos hq] at h
    have hmul : 100 * q * ‖z 0‖ ≤ 400 := by
      calc
        _ ≤ 100 * 1 * 4 := mul_le_mul (mul_le_mul_of_nonneg_left hq1 (by norm_num)) hz₀
          (norm_nonneg _) (by norm_num)
        _ = _ := by norm_num
    push_cast
    linarith only [h, htime, hmul, hH]
  · obtain ⟨h₀, h₁, h₂⟩ := projected_common_coefficients hH hβ hq hq1 hg hm hqg hmβ b ht hfit
    have h := normalized_strip_coordinate_bound hH hβ h₀ h₁ h₂ (z 0) (z 2) hz₀ hz₂
    convert h using 1
    congr 3
    dsimp [complexMinor, complexTime, c]
    push_cast
    ring

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain
