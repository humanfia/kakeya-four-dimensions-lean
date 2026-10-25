import Submission.Obl.k4_scalar_conditional_crop_worlds.Definitions
import Submission.Obl.k4_dyadic_crop_worlds.Main

open MeasureTheory Finset

namespace Submission.Obl.k4_scalar_conditional_crop_worlds

/-- Relative prior weighting cancels conditional normalization, and division by a retained
prior mass at most one only increases the retained incidence mass. -/
lemma weighted_mass_ge {w : ℕ} (p S ω : Fin w → ℝ) (mass : Fin w → ENNReal)
    {ρ T : ℝ} (hp : ∀ γ, 0 < p γ) (hS : ∀ γ, 0 ≤ S γ)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hω : ∀ γ, ω γ = p γ / ρ)
    (hMass : ∀ γ, ENNReal.ofReal (p γ) * mass γ = ENNReal.ofReal (S γ))
    (hTmass : T⁻¹ ≤ ∑ γ, S γ) :
    ENNReal.ofReal T⁻¹ ≤ ∑ γ, ENNReal.ofReal (ω γ) * mass γ := by
  have hterm : ∀ γ, ENNReal.ofReal (ω γ) * mass γ = ENNReal.ofReal (S γ / ρ) := by
    intro γ
    have hp0 : ENNReal.ofReal (p γ) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hp γ
    have heq : mass γ = (ENNReal.ofReal (p γ))⁻¹ * ENNReal.ofReal (S γ) := by
      calc mass γ = (ENNReal.ofReal (p γ))⁻¹ * (ENNReal.ofReal (p γ) * mass γ) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hp0 ENNReal.ofReal_ne_top, one_mul]
        _ = _ := by rw [hMass γ]
    rw [hω γ, heq]
    exact k4_dyadic_crop_worlds.weighted_term (hp γ) (hS γ)
  rw [Finset.sum_congr rfl (fun γ _ => hterm γ),
    ← ENNReal.ofReal_sum_of_nonneg (fun γ _ => div_nonneg (hS γ) hρ0.le), ← Finset.sum_div]
  exact ENNReal.ofReal_le_ofReal (hTmass.trans
    (le_div_self (Finset.sum_nonneg fun γ _ => hS γ) hρ0 hρ1))

end Submission.Obl.k4_scalar_conditional_crop_worlds
