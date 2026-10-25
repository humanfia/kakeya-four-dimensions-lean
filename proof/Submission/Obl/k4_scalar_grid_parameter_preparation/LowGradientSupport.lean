/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/LowGradientSupport.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.PhysicalSupportCover
import Submission.Obl.k4_scalar_grid_parameter_preparation.QuadraticEndpointGradient

/-! Quadratic packet support counts on the retained low-gradient points themselves. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

open Set MvPolynomial

theorem physical_grid_cover_of_quadratic_graph (S : Set (Fin 3 → ℝ))
    (F : MvPolynomial (Fin 2) ℝ) (hF : F.totalDegree ≤ 2)
    (ξ h A K L t₀ y₀ : ℝ) (hξ : 0 < ξ) (hξh : ξ ≤ h)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (htime : ∀ p ∈ S, p 0 ∈ Set.Icc t₀ (t₀ + h))
    (hY : ∀ p ∈ S, |p 1 - y₀| ≤ A * h)
    (hfit : ∀ p ∈ S, |p 2 - eval ![p 0,p 1] F| ≤ K * ξ)
    (hgrad : ∀ p ∈ S, ∀ e, |eval ![p 0,p 1] (pderiv e F)| ≤ L) :
    (physicalScalarGridTag ξ '' S).Finite ∧
      ((physicalScalarGridTag ξ '' S).ncard : ℝ) ≤
        4 * (4 * A + 2) * (4 * (L + K) + 2) * (h / ξ) ^ 2 := by
  have hhidden : ∀ p ∈ S, ∀ p' ∈ S,
      (⌊p 0 / ξ⌋ : ℤ) = ⌊p' 0 / ξ⌋ → (⌊p 1 / ξ⌋ : ℤ) = ⌊p' 1 / ξ⌋ →
        dist (p 2) (p' 2) ≤ (2 * (L + K)) * ξ := by
    intro p hp p' hp' ht hy
    have ht' : |p 0 - p' 0| ≤ ξ := by
      exact scalarVelocityBin_diameter_le hξ (q := ⌊p 0 / ξ⌋) rfl ht.symm
    have hy' : |p 1 - p' 1| ≤ ξ := by
      exact scalarVelocityBin_diameter_le hξ (q := ⌊p 1 / ξ⌋) rfl hy.symm
    have hdiff : |eval ![p 0,p 1] F - eval ![p' 0,p' 1] F| ≤ 2 * L * ξ := by
      have hd := quadratic_difference_le_endpoint_gradients F hF
        ![p' 0,p' 1] ![p 0,p 1] L (hgrad p' hp') (hgrad p hp)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hd
      exact hd.trans ((mul_le_mul_of_nonneg_left (add_le_add ht' hy') hL).trans_eq (by ring))
    rw [Real.dist_eq]
    calc
      _ ≤ |p 2 - eval ![p 0,p 1] F| +
          (|eval ![p 0,p 1] F - eval ![p' 0,p' 1] F| +
            |eval ![p' 0,p' 1] F - p' 2|) :=
        (abs_sub_le (p 2) (eval ![p 0,p 1] F) (p' 2)).trans
          (add_le_add le_rfl (abs_sub_le (eval ![p 0,p 1] F) (eval ![p' 0,p' 1] F) (p' 2)))
      _ ≤ K * ξ + (2 * L * ξ + K * ξ) := add_le_add (hfit p hp)
        (add_le_add hdiff (by simpa only [abs_sub_comm] using hfit p' hp'))
      _ = _ := by ring
  have h := physical_grid_cover_of_base_fibers S ξ h A (2 * (L + K)) t₀ y₀
    hξ hξh hA (by positivity) htime hY hhidden
  convert h using 2 <;> ring

/-- The moving packet base has side `O(K*h)`, so the low-gradient physical graph
uses only a polynomial factor times `(h/ξ)^2` cells. -/
theorem physical_grid_cover_of_quadratic_packet (S : Set (Fin 3 → ℝ))
    (F : MvPolynomial (Fin 2) ℝ) (hF : F.totalDegree ≤ 2)
    (ξ h K L t₀ u v : ℝ) (hξ : 0 < ξ) (hξh : ξ ≤ h) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hv : |v| ≤ K)
    (htime : ∀ p ∈ S, p 0 ∈ Set.Icc t₀ (t₀ + h))
    (hY : ∀ p ∈ S, |p 1 - u - p 0 * v| ≤ K * h)
    (hfit : ∀ p ∈ S, |p 2 - eval ![p 0,p 1] F| ≤ K * ξ)
    (hgrad : ∀ p ∈ S, ∀ e, |eval ![p 0,p 1] (pderiv e F)| ≤ L) :
    (physicalScalarGridTag ξ '' S).Finite ∧
      ((physicalScalarGridTag ξ '' S).ncard : ℝ) ≤
        4 * (8 * K + 2) * (4 * (L + K) + 2) * (h / ξ) ^ 2 := by
  have hh : 0 < h := hξ.trans_le hξh
  have hY' : ∀ p ∈ S, |p 1 - (u + t₀ * v)| ≤ (2 * K) * h := by
    intro p hp
    have ht : |p 0 - t₀| ≤ h := by
      rw [abs_of_nonneg (sub_nonneg.mpr (htime p hp).1)]
      linarith [(htime p hp).2]
    calc
      _ = |(p 1 - u - p 0 * v) + (p 0 - t₀) * v| := by congr 1; ring
      _ ≤ |p 1 - u - p 0 * v| + |p 0 - t₀| * |v| := by
        simpa only [abs_mul] using abs_add_le (p 1 - u - p 0 * v) ((p 0 - t₀) * v)
      _ ≤ K * h + h * K := add_le_add (hY p hp) (mul_le_mul ht hv (abs_nonneg _) hh.le)
      _ = _ := by ring
  have h := physical_grid_cover_of_quadratic_graph S F hF ξ h (2 * K) K L t₀ (u + t₀ * v)
    hξ hξh (by positivity) hK hL htime hY' hfit hgrad
  convert h using 2 <;> ring

/-- The packet's time length may be smaller than its thickness by the original
loss factor. Inflating the comparison base by that factor costs only `K^2`. -/
theorem physical_grid_cover_of_quadratic_packet_at_rate (S : Set (Fin 3 → ℝ))
    (F : MvPolynomial (Fin 2) ℝ) (hF : F.totalDegree ≤ 2)
    (ξ h K L t₀ u v : ℝ) (hξ : 0 < ξ) (hh : 0 < h)
    (hξh : ξ ≤ K * h) (hK : 1 ≤ K) (hL : 0 ≤ L) (hv : |v| ≤ K)
    (htime : ∀ p ∈ S, p 0 ∈ Set.Icc t₀ (t₀ + h))
    (hY : ∀ p ∈ S, |p 1 - u - p 0 * v| ≤ K * h)
    (hfit : ∀ p ∈ S, |p 2 - eval ![p 0,p 1] F| ≤ K * ξ)
    (hgrad : ∀ p ∈ S, ∀ e, |eval ![p 0,p 1] (pderiv e F)| ≤ L) :
    (physicalScalarGridTag ξ '' S).Finite ∧
      ((physicalScalarGridTag ξ '' S).ncard : ℝ) ≤
        4 * K ^ 2 * (8 * K + 2) * (4 * (L + K) + 2) * (h / ξ) ^ 2 := by
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hKh : h ≤ K * h := by nlinarith
  have hc := physical_grid_cover_of_quadratic_packet S F hF ξ (K * h) K L t₀ u v
    hξ hξh hK₀ hL hv (fun p hp => ⟨(htime p hp).1, by linarith [(htime p hp).2]⟩)
    (fun p hp => (hY p hp).trans (mul_le_mul_of_nonneg_left hKh hK₀)) hfit hgrad
  convert hc using 2 <;> ring

end Submission.Obl.k4_scalar_grid_parameter_preparation
