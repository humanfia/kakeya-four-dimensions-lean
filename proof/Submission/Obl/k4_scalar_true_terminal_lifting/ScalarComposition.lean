import Submission.Obl.k4_scalar_true_terminal_lifting.Theta
import Submission.Obl.k4_scalar_true_terminal_lifting.DyadicComposition

namespace Submission.Obl.k4_scalar_true_terminal_lifting

open MvPolynomial Set
open k4_scalar_linear_critical_extremizers.Split

/-- The affine map on time and visible position induced by a parent chart. -/
noncomputable def chartBaseSubstitution (t₀ dt u v J : ℝ) :
    Fin 2 → MvPolynomial (Fin 2) ℝ :=
  ![C dt⁻¹ * (X 0 - C t₀), C J⁻¹ * (X 1 - C u - C v * X 0)]

/-- Add the parent potential to the rescaled child potential. -/
noncomputable def composedPotential (P₀ P₁ : MvPolynomial (Fin 2) ℝ)
    (t₀ dt u v J s : ℝ) : MvPolynomial (Fin 2) ℝ :=
  P₀ + C s * bind₁ (chartBaseSubstitution t₀ dt u v J) P₁

theorem chartBaseSubstitution_eval (t₀ dt u v J t Y : ℝ) :
    (fun e => eval ![t, Y] (chartBaseSubstitution t₀ dt u v J e)) =
      ![(t - t₀) / dt, (Y - u - t * v) / J] := by
  funext e
  fin_cases e <;> simp [chartBaseSubstitution, div_eq_inv_mul, mul_comm]

theorem chartBaseSubstitution_degree (t₀ dt u v J : ℝ) (e : Fin 2) :
    (chartBaseSubstitution t₀ dt u v J e).totalDegree ≤ 1 := by
  fin_cases e
  · exact theta_deg_C_mul _ (theta_deg_sub (theta_deg_X _ le_rfl) (theta_deg_C _))
  · exact theta_deg_C_mul _ (theta_deg_sub
      (theta_deg_sub (theta_deg_X _ le_rfl) (theta_deg_C _))
      (theta_deg_C_mul _ (theta_deg_X _ le_rfl)))

theorem composedPotential_eval (P₀ P₁ : MvPolynomial (Fin 2) ℝ)
    (t₀ dt u v J s t Y : ℝ) :
    eval ![t, Y] (composedPotential P₀ P₁ t₀ dt u v J s) =
      eval ![t, Y] P₀ + s * eval ![(t - t₀) / dt, (Y - u - t * v) / J] P₁ := by
  simp only [composedPotential, map_add, map_mul, eval_C, theta_eval_bind₁,
    chartBaseSubstitution_eval]

theorem composedPotential_degree {P₀ P₁ : MvPolynomial (Fin 2) ℝ}
    (hP₀ : P₀.totalDegree ≤ 2) (hP₁ : P₁.totalDegree ≤ 2)
    (t₀ dt u v J s : ℝ) :
    (composedPotential P₀ P₁ t₀ dt u v J s).totalDegree ≤ 2 := by
  apply theta_deg_add hP₀
  apply theta_deg_C_mul
  exact (theta_totalDegree_bind₁_le _ P₁ 1
    (chartBaseSubstitution_degree t₀ dt u v J)).trans (by simpa using hP₁)

noncomputable def composedCenter (t₀ dt u₀ J₀ u₁ v₁ : ℝ) : ℝ :=
  u₀ + J₀ * u₁ - J₀ * (t₀ / dt) * v₁

noncomputable def composedSlope (dt v₀ J₀ v₁ : ℝ) : ℝ := v₀ + J₀ * v₁ / dt

/-- Visible residuals multiply by the parent transverse scale. -/
theorem composed_visible_residual
    (θ : (ℕ × (Fin 5 → ℝ)) → (ℕ × (Fin 5 → ℝ)))
    (t₀ dt u₀ v₀ J₀ u₁ v₁ : ℝ) (hJ₀ : J₀ ≠ 0)
    (hy : ∀ l t, y (θ l) ((t - t₀) / dt) = (y l t - u₀ - t * v₀) / J₀)
    (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) :
    y l t - composedCenter t₀ dt u₀ J₀ u₁ v₁ -
        t * composedSlope dt v₀ J₀ v₁ =
      J₀ * (y (θ l) ((t - t₀) / dt) - u₁ - ((t - t₀) / dt) * v₁) := by
  rw [hy]
  simp only [composedCenter, composedSlope, div_eq_mul_inv]
  field_simp [hJ₀]
  ring

/-- Hidden residuals multiply by the parent hidden scale. -/
theorem composed_hidden_residual
    (θ : (ℕ × (Fin 5 → ℝ)) → (ℕ × (Fin 5 → ℝ)))
    (P₀ P₁ : MvPolynomial (Fin 2) ℝ) (t₀ dt u₀ v₀ J₀ s : ℝ) (hs : s ≠ 0)
    (hy : ∀ l t, y (θ l) ((t - t₀) / dt) = (y l t - u₀ - t * v₀) / J₀)
    (hx : ∀ l t, x (θ l) ((t - t₀) / dt) =
      (x l t - eval ![t, y l t] P₀) / s)
    (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) :
    x l t - eval ![t, y l t] (composedPotential P₀ P₁ t₀ dt u₀ v₀ J₀ s) =
      s * (x (θ l) ((t - t₀) / dt) -
        eval ![(t - t₀) / dt, y (θ l) ((t - t₀) / dt)] P₁) := by
  rw [composedPotential_eval, hy, hx]
  field_simp
  ring

/-- Both whole-interval fits lift directly, with the child visible error and
the additive hidden scales. No pointwise fit of the parent is used here. -/
theorem composed_chart_fits
    (θ : (ℕ × (Fin 5 → ℝ)) → (ℕ × (Fin 5 → ℝ)))
    (P₀ P₁ : MvPolynomial (Fin 2) ℝ) (t₀ dt u₀ v₀ J₀ u₁ v₁ J₁ : ℝ)
    {N r L₀ L₁ ε : ℝ} (hN : 0 < N) (hJ₀ : 0 < J₀) (hL : L₁ = L₀ - r)
    (hy : ∀ l t, y (θ l) ((t - t₀) / dt) = (y l t - u₀ - t * v₀) / J₀)
    (hx : ∀ l t, x (θ l) ((t - t₀) / dt) =
      (x l t - eval ![t, y l t] P₀) / N ^ (-r))
    (l : ℕ × (Fin 5 → ℝ)) (t : ℝ)
    (hfit : |y (θ l) ((t - t₀) / dt) - u₁ - ((t - t₀) / dt) * v₁| ≤ N ^ ε * J₁ ∧
      |x (θ l) ((t - t₀) / dt) -
        eval ![(t - t₀) / dt, y (θ l) ((t - t₀) / dt)] P₁| ≤ N ^ ε * N ^ (-L₁)) :
    |y l t - composedCenter t₀ dt u₀ J₀ u₁ v₁ - t * composedSlope dt v₀ J₀ v₁| ≤
        N ^ ε * (J₀ * J₁) ∧
      |x l t - eval ![t, y l t] (composedPotential P₀ P₁ t₀ dt u₀ v₀ J₀ (N ^ (-r)))| ≤
        N ^ ε * N ^ (-L₀) := by
  constructor
  · rw [composed_visible_residual θ t₀ dt u₀ v₀ J₀ u₁ v₁ hJ₀.ne' hy, abs_mul,
      abs_of_pos hJ₀]
    exact (mul_le_mul_of_nonneg_left hfit.1 hJ₀.le).trans_eq (by ring)
  · have hs := Real.rpow_pos_of_pos hN (-r)
    rw [composed_hidden_residual θ P₀ P₁ t₀ dt u₀ v₀ J₀ (N ^ (-r)) hs.ne' hy hx,
      abs_mul, abs_of_pos hs]
    apply (mul_le_mul_of_nonneg_left hfit.2 hs.le).trans_eq
    calc
      N ^ (-r) * (N ^ ε * N ^ (-L₁)) = N ^ ε * N ^ (-r + -L₁) := by
        rw [Real.rpow_add hN]
        ring
      _ = N ^ ε * N ^ (-L₀) := by rw [hL]; congr 2; ring

end Submission.Obl.k4_scalar_true_terminal_lifting
