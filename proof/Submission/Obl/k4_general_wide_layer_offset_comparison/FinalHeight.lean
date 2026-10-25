import Submission.Obl.k4_contact_affine_residual_candidate_transfer.Subpower
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open Filter
open Submission.Obl.k4_contact_affine_residual_candidate_transfer

/-- The final height pays the original geometry, the finite counting budget,
and simultaneous renewal without changing the fiber radius afterward. -/
def comparisonHeight (K B h R : ℝ) : ℝ := 2 + K + B + 4 * h * R

theorem comparisonHeight_spec {K B h R : ℝ}
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hh : 0 ≤ h) (hR : 0 ≤ R) :
    2 ≤ comparisonHeight K B h R ∧ K ≤ comparisonHeight K B h R ∧
      B ≤ comparisonHeight K B h R ∧ 4 * h * R ≤ comparisonHeight K B h R := by
  have hp : 0 ≤ 4 * h * R := by positivity
  dsimp only [comparisonHeight]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Every intrinsic subpower budget may be paid before the whole-fiber
comparison, with one final height still below every positive scale power. -/
theorem comparisonHeight_subpower {N K B h R : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : Small N K) (hB : Small N B) (hh : Small N h) (hR : Small N R) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      comparisonHeight (K k) (B k) (h k) (R k) ≤ N k ^ ε := by
  have h4 := Small.const hNt (by norm_num : (0 : ℝ) ≤ 4)
  have h2 := Small.const hNt (by norm_num : (0 : ℝ) ≤ 2)
  have hN0 : ∀ k, 0 ≤ N k := fun k => zero_le_one.trans (hN k)
  have hprod := (h4.mul hN0 hh).mul hN0 hR
  exact (((h2.add hNt hK).add hNt hB).add hNt hprod).2

/-- A power-small original exception costs an arbitrarily small fixed
fraction of a dense source with an intrinsic subpower mass denominator. -/
theorem eventually_power_loss_le_inverse {N H : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hH : ∀ k, 1 ≤ H k)
    (hHs : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε)
    {c A : ℝ} (hc : 0 < c) (hA : 0 < A) :
    ∀ᶠ k in atTop, N k ^ (-c) ≤ (A * H k)⁻¹ := by
  have hs := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hH hHs 1 (a := -c) (b := 0) (by linarith) (A := A) hA.le
  filter_upwards [hs] with k hk
  have hden : 0 < A * H k := mul_pos hA (zero_lt_one.trans_le (hH k))
  rw [inv_eq_one_div, le_div_iff₀ hden]
  calc
    N k ^ (-c) * (A * H k) = A * H k * N k ^ (-c) := by ring
    _ ≤ 1 := by simpa only [pow_one, Real.rpow_zero] using hk.le

end Submission.Obl.k4_general_wide_layer_offset_comparison
