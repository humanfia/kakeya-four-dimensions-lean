-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/ShiftBudget.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.AffineResidual
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ModelScales
import Submission.Obl.k4_discrete_of_terminal_charts.Horizon

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover

open Filter MvPolynomial
open Submission.Obl.k4_stable_native_signal_oscillation

/-- A bounded affine residual controls both shifted base parts at the
native reciprocal width. -/
theorem shifted_value_budget {K a H : ℝ} (hK : 0 ≤ K) (ha : 0 < a)
    (ha1 : a ≤ 1) (hH : 1 ≤ H) :
    K * a + H * K + H ^ 2 / 2 * (K / a) ≤ 8 * K * H ^ 2 / a ∧
      K + (K / a) * H ≤ 8 * K * H ^ 2 / a := by
  have hH0 : 0 ≤ H := by linarith
  have hH2 : 1 ≤ H ^ 2 := one_le_pow₀ hH
  have hHH : H ≤ H ^ 2 := by nlinarith [sq_nonneg (H - 1)]
  have ha2 : a ^ 2 ≤ H ^ 2 := (pow_le_one₀ ha.le ha1).trans hH2
  have hHa : H * a ≤ H ^ 2 := (mul_le_of_le_one_right hH0 ha1).trans hHH
  have haH : a ≤ H ^ 2 := ha1.trans hH2
  have h1 := mul_le_mul_of_nonneg_left ha2 hK
  have h2 := mul_le_mul_of_nonneg_left hHa hK
  have h3 := mul_le_mul_of_nonneg_left haH hK
  have h4 := mul_le_mul_of_nonneg_left hHH hK
  have hpos : 0 ≤ K * H ^ 2 := by positivity
  constructor
  · apply (le_div_iff₀ ha).mpr
    have heq : (K * a + H * K + H ^ 2 / 2 * (K / a)) * a =
        K * a ^ 2 + K * (H * a) + K * H ^ 2 / 2 := by field_simp
    rw [heq]
    nlinarith
  · apply (le_div_iff₀ ha).mpr
    have heq : (K + (K / a) * H) * a = K * a + K * H := by field_simp
    rw [heq]
    nlinarith

namespace Model

variable {α : Type*} [MeasurableSpace α] (p : Model α)

/-- A subpower coarse residual gives a fixed shallow budget for the shifted
base parts of every label test, with no coefficient bound on its predictor. -/
theorem eventually_shifted_base_values (hp : p.Valid)
    (H : ℕ → ℝ) (hH : ∀ k, 1 ≤ H k)
    (hHsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ p.N k ^ ε)
    {s : ℝ} (hs : 0 < s) :
    ∀ᶠ k in atTop, ∀ (a₀ : ℝ), p.a k s ≤ a₀ → a₀ ≤ 1 →
      ∀ (L : Fin 4 → ℝ) (F : MvPolynomial (Fin 4) ℝ), F.totalDegree ≤ 2 →
      ∀ v : Fin 4 → ℝ,
      |eval v F| ≤ p.K k * a₀ → |eval v (pderiv 3 F)| ≤ p.K k →
      |eval v (pderiv 3 (pderiv 3 F))| ≤ p.K k / a₀ →
      |eval v (Submission.Lib.K4ContactNormalization.affineBase L) - v 3| ≤ H k →
      |eval (Fin.init v) (restrictBase (translatedTest L F))| ≤ p.N k ^ (2 * s) ∧
      |eval (Fin.init v) (restrictBase (pderiv 3 (translatedTest L F)))| ≤
        p.N k ^ (2 * s) := by
  have hN : ∀ k, 1 ≤ p.N k := fun k => by linarith [hp.N_ge k]
  have hNpos := Valid.N_pos p hp
  have hK0 := fun k => (Valid.K_pos p hp k).le
  have hH0 : ∀ k, 0 ≤ H k := fun k => by linarith [hH k]
  have hpow := Submission.Obl.k4_discrete_of_terminal_charts.subpower_pow hN hH0 hHsub 2
  have hprod := Submission.Obl.k4_discrete_of_terminal_charts.subpower_mul hNpos
    hK0 (fun k => sq_nonneg (H k)) hp.K_sub hpow
  have hbudget := Submission.Obl.k4_discrete_of_terminal_charts.subpower_mul hNpos
    (fun _ => (by norm_num : (0 : ℝ) ≤ 8))
    (fun k => mul_nonneg (hK0 k) (sq_nonneg (H k)))
    (Submission.Obl.k4_discrete_of_terminal_charts.subpower_const hp.N_lim 8) hprod
  filter_upwards [hbudget s hs] with k hk
  intro a₀ ha₀ ha₁ L F hF v hv hf hc hclose
  have ha := Valid.a_pos p hp k s
  have ha₀pos : 0 < a₀ := ha.trans_le ha₀
  have h := affine_shift_base_value_bounds L F hF v (hK0 k) ha₀pos (hH0 k)
    hv hf hc hclose
  have hraw := shifted_value_budget (hK0 k) ha₀pos ha₁ (hH k)
  have hbound : 8 * p.K k * H k ^ 2 / a₀ ≤ p.N k ^ (2 * s) := by
    calc
      _ ≤ 8 * p.K k * H k ^ 2 / p.a k s :=
        div_le_div_of_nonneg_left
          (mul_nonneg (mul_nonneg (by norm_num) (hK0 k)) (sq_nonneg _)) ha ha₀
      _ ≤ p.N k ^ s / p.a k s := by
        apply div_le_div_of_nonneg_right _ ha.le
        simpa only [mul_assoc] using hk
      _ = _ := by
        rw [a, div_eq_mul_inv, show -s = -(s) by ring, Real.rpow_neg (hNpos k).le,
          inv_inv, ← Real.rpow_add (hNpos k)]
        congr 1
        ring
  exact ⟨h.1.trans (hraw.1.trans hbound), h.2.trans (hraw.2.trans hbound)⟩

end Model
end Submission.Obl.k4_contact_fine_labels_from_coarse_cover
