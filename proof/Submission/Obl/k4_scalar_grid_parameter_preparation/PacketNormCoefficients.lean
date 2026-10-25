/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/PacketNormCoefficients.lean -/
import Submission.Obl.k4_fixed_budget_quadratic_recovery.QuadraticCoefficients

/-! The adapted packet norm bounds ordinary coefficients after both affine frame changes. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

open Set
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction
open Submission.Obl.k4_fixed_budget_quadratic_recovery

def swapScalarQuadraticCoefficients (c : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![c 0,c 2,c 1,c 5,c 4,c 3]

theorem quadraticValue_swap (c : Fin 6 → ℝ) (t y : ℝ) :
    quadraticValue (swapScalarQuadraticCoefficients c) t y = quadraticValue c y t := by
  simp [swapScalarQuadraticCoefficients, quadraticValue]
  ring

theorem swapScalarQuadraticCoefficients_bound (c : Fin 6 → ℝ) (H : ℝ)
    (hc : ∀ i, |c i| ≤ H) : ∀ i, |swapScalarQuadraticCoefficients c i| ≤ H := by
  intro i
  fin_cases i <;> exact hc _

theorem isQuad2_swap {f : ℝ → ℝ → ℝ} (hf : IsQuad2 f) : IsQuad2 (fun t y => f y t) := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨swapScalarQuadraticCoefficients c, ?_⟩
  intro t y
  change f y t = quadraticValue (swapScalarQuadraticCoefficients c) t y
  rw [quadraticValue_swap]
  exact hc y t

/-- A packet norm controls its physical coefficients by a fixed power of its inverse
time length. The coarse bound suffices to choose the internal gradient-freezing mesh. -/
theorem packet_norm_scalar_coefficients (F : MvPolynomial (Fin 2) ℝ)
    (hF : F.totalDegree ≤ 2) (K t₀ h u v : ℝ) (hK : 1 ≤ K)
    (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) 1) (hh : 0 < h) (hh₁ : h ≤ 1)
    (huv : |u| + |v| ≤ K)
    (hbound : ∀ t ∈ Set.Icc t₀ (t₀ + h), ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |MvPolynomial.eval ![t, u + t * v + h * z] F| ≤ K) :
    ∃ c : Fin 6 → ℝ,
      (∀ t y, MvPolynomial.eval ![t,y] F = quadraticValue c t y) ∧
      ∀ i, |c i| ≤ 200 * K * (2 * K / h) ^ 4 := by
  have htime : IsQuad2 (fun s y => MvPolynomial.eval ![t₀ + h * s,y] F) := by
    have hf := isQuad2_swap (isQuad2_affine_second
      (isQuad2_swap (isQuad2_eval F hF)) t₀ 0 h)
    simpa only [mul_zero, add_zero] using hf
  obtain ⟨q, hq⟩ := isQuad2_affine_second htime (u + t₀ * v) (h * v) h
  change ∀ s z, MvPolynomial.eval ![t₀ + h * s, u + t₀ * v + s * (h * v) + h * z] F =
    quadraticValue q s z at hq
  have hqbound : ∀ i, |q i| ≤ 8 * K := quadratic_coefficients_bound (by
    intro s hs z hz
    rw [← hq]
    have ht : t₀ + h * s ∈ Set.Icc t₀ (t₀ + h) := by
      constructor <;> nlinarith [mul_nonneg hh.le hs.1, mul_nonneg hh.le (sub_nonneg.mpr hs.2)]
    have he : u + t₀ * v + s * (h * v) + h * z = u + (t₀ + h * s) * v + h * z := by ring
    rw [he]
    exact hbound _ ht z hz)
  let R := 2 * K / h
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hR : 1 ≤ R := (one_le_div hh).mpr (by linarith)
  have hKR : K ≤ R := by
    apply (le_div_iff₀ hh).mpr
    nlinarith
  have ht₀abs : |t₀| ≤ 1 := by rw [abs_of_nonneg ht₀.1]; exact ht₀.2
  have hcenter : |u + t₀ * v| ≤ K := by
    calc
      _ ≤ |u| + |t₀| * |v| := by simpa only [abs_mul] using abs_add_le u (t₀ * v)
      _ ≤ |u| + 1 * |v| := add_le_add le_rfl (mul_le_mul_of_nonneg_right ht₀abs (abs_nonneg _))
      _ ≤ K := by simpa only [one_mul] using huv
  have hhinv : |h⁻¹| ≤ R := by
    rw [abs_of_nonneg (inv_nonneg.mpr hh.le)]
    simpa only [one_div] using div_le_div_of_nonneg_right (by linarith : 1 ≤ 2 * K) hh.le
  have huR : |(u + t₀ * v) / h| ≤ R := by
    rw [abs_div, abs_of_pos hh]
    exact div_le_div_of_nonneg_right (hcenter.trans (by linarith)) hh.le
  have hvR : |(h * v) / h| ≤ R := by
    rw [mul_div_cancel_left₀ _ hh.ne']
    exact (by linarith [abs_nonneg u] : |v| ≤ K).trans hKR
  let q₁ := undoQuadraticFrame q (u + t₀ * v) (h * v) h
  have hq₁ : ∀ i, |q₁ i| ≤ 5 * (8 * K) * R ^ 2 :=
    undoQuadraticFrame_bound (by positivity) hR hqbound huR hvR hhinv
  have hq₁form (s y : ℝ) : MvPolynomial.eval ![t₀ + h * s,y] F = quadraticValue q₁ s y := by
    let z := (y - (u + t₀ * v) - s * (h * v)) / h
    have he : u + t₀ * v + s * (h * v) + h * z = y := by dsimp [z]; field_simp; ring
    calc
      _ = MvPolynomial.eval ![t₀ + h * s, u + t₀ * v + s * (h * v) + h * z] F := by rw [he]
      _ = quadraticValue q s z := hq s z
      _ = _ := undoQuadraticFrame_value q (u + t₀ * v) (h * v) hh.ne' s y
  have htR : |t₀ / h| ≤ R := by
    rw [abs_div, abs_of_pos hh]
    exact div_le_div_of_nonneg_right (ht₀abs.trans (by linarith)) hh.le
  let q₂ := swapScalarQuadraticCoefficients q₁
  have hq₂ := swapScalarQuadraticCoefficients_bound q₁ _ hq₁
  let q₃ := undoQuadraticFrame q₂ t₀ 0 h
  have hq₃ : ∀ i, |q₃ i| ≤ 5 * (5 * (8 * K) * R ^ 2) * R ^ 2 :=
    undoQuadraticFrame_bound (by positivity) hR hq₂ htR (by simp; linarith) hhinv
  refine ⟨swapScalarQuadraticCoefficients q₃, ?_, ?_⟩
  · intro t y
    have ht : t₀ + h * ((t - t₀) / h) = t := by field_simp; ring
    rw [quadraticValue_swap]
    calc
      _ = quadraticValue q₁ ((t - t₀) / h) y := by
        have hf := hq₁form ((t - t₀) / h) y
        rwa [ht] at hf
      _ = quadraticValue q₂ y ((t - t₀) / h) := (quadraticValue_swap q₁ y _).symm
      _ = quadraticValue q₃ y t := by
        simpa only [mul_zero, sub_zero] using undoQuadraticFrame_value q₂ t₀ 0 hh.ne' y t
  · intro i
    have hb := swapScalarQuadraticCoefficients_bound q₃ _ hq₃ i
    convert hb using 1
    dsimp [R]
    ring

end Submission.Obl.k4_scalar_grid_parameter_preparation
