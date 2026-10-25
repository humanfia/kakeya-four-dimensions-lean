/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/FieldFreezing.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.PacketNormCoefficients
import Submission.Obl.k4_scalar_grid_parameter_preparation.PolynomialLipschitz
import Submission.Obl.k4_scalar_grid_parameter_preparation.FieldVelocityForecast
import Submission.Obl.k4_fixed_budget_quadratic_recovery.QuadraticPolynomial

/-! Quantitative variation of packet gradients on an explicitly chosen internal grid. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

open Set MvPolynomial
open Submission.Obl.k4_fixed_budget_quadratic_recovery

theorem packet_norm_polynomial_coefficients (F : MvPolynomial (Fin 2) ℝ)
    (hF : F.totalDegree ≤ 2) (K t₀ h u v : ℝ) (hK : 1 ≤ K)
    (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) 1) (hh : 0 < h) (hh₁ : h ≤ 1)
    (huv : |u| + |v| ≤ K)
    (hbound : ∀ t ∈ Set.Icc t₀ (t₀ + h), ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |MvPolynomial.eval ![t, u + t * v + h * z] F| ≤ K) :
    ∀ b, |F.coeff b| ≤ 1200 * K * (2 * K / h) ^ 4 := by
  obtain ⟨c, hc, hcb⟩ := packet_norm_scalar_coefficients F hF K t₀ h u v hK ht₀ hh hh₁ huv hbound
  rw [polynomial_eq_of_quadratic_values hc]
  intro b
  have hb := quadraticPolynomial_coeff_bound (by positivity : 0 ≤ 200 * K * (2 * K / h) ^ 4) hcb b
  convert hb using 1
  ring

theorem binary_gradient_variation_bound (F : MvPolynomial (Fin 2) ℝ) (hF : F.totalDegree ≤ 2)
    (B R δ : ℝ) (hB : 0 ≤ B) (hR : 1 ≤ R) (hc : ∀ b, |F.coeff b| ≤ B)
    (x y : Fin 2 → ℝ) (hx : ∀ i, |x i| ≤ R) (hy : ∀ i, |y i| ≤ R)
    (hxy : dist x y ≤ δ) (e : Fin 2) :
    |eval x (pderiv e F) - eval y (pderiv e F)| ≤ 162 * B * R ^ 4 * δ := by
  have hd : (pderiv e F).totalDegree ≤ 2 :=
    (Submission.Obl.k4_quadratic_slope_volume.totalDegree_pderiv_le F e).trans
      ((Nat.sub_le _ _).trans hF)
  have hcoeff : ∀ b, |(pderiv e F).coeff b| ≤ 3 * B := by
    have hb := pderiv_coefficients_bound F 2 hF hB hc e
    norm_num at hb
    exact hb
  have hb := binary_polynomial_lipschitz (pderiv e F) 2 hd (by positivity) hR hcoeff x y hx hy
  have hnum : 54 * (3 * B) * R ^ 4 = 162 * B * R ^ 4 := by ring
  norm_num only [Nat.cast_ofNat] at hb
  rw [hnum] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hxy (by positivity))

/-- A fine grid is chosen using a numerical budget; the field-freezing hypothesis
in the steep-field estimate is then a theorem about the actual packet polynomial. -/
theorem binary_gradient_freezing_on_grid (F : MvPolynomial (Fin 2) ℝ)
    (hF : F.totalDegree ≤ 2) (B R δ : ℝ) (hB : 0 ≤ B) (hR : 1 ≤ R) (hδ : 0 < δ)
    (hc : ∀ b, |F.coeff b| ≤ B) (hbudget : 162 * B * R ^ 4 * δ ≤ 1)
    (x y : Fin 2 → ℝ) (hx : ∀ i, |x i| ≤ R) (hy : ∀ i, |y i| ≤ R)
    (hcode : (fun i => (⌊x i / δ⌋ : ℤ)) = (fun i => (⌊y i / δ⌋ : ℤ))) :
    ∀ e, |eval x (pderiv e F) - eval y (pderiv e F)| ≤ 1 := by
  have hd : dist x y ≤ δ := by
    apply (dist_pi_le_iff hδ.le).mpr
    intro i
    exact scalarVelocityBin_diameter_le hδ (q := ⌊x i / δ⌋) rfl (congrFun hcode i).symm
  intro e
  exact (binary_gradient_variation_bound F hF B R δ hB hR hc x y hx hy hd e).trans hbudget

end Submission.Obl.k4_scalar_grid_parameter_preparation
