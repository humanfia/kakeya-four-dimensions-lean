-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/FineMesh.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ModelScales
import Submission.Obl.k4_discrete_of_terminal_charts.Horizon

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model

open Filter

variable {α : Type*} [MeasurableSpace α] (p : Model α)

/-- A fixed fine native mesh absorbs every calibrated shallow base part,
including an arbitrary subpower affine residual. -/
theorem eventually_fine_freezing_mesh (hp : p.Valid)
    (H : ℕ → ℝ) (hH : ∀ k, 1 ≤ H k)
    (hHsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ p.N k ^ ε)
    {s : ℝ} (hs : 0 < s) :
    ∀ᶠ k in atTop,
      216 * p.N k ^ (40 * s) * (2 * p.K k) ^ 2 * (1 + H k) *
        p.N k ^ (-100 * s) ≤ p.a k s ∧
      216 * p.N k ^ (40 * s) * (2 * p.K k) ^ 2 * (1 + H k) *
        p.N k ^ (-100 * s) ≤ (2 * p.K k)⁻¹ := by
  have hN : ∀ k, 1 ≤ p.N k := fun k => by linarith [hp.N_ge k]
  have hNpos := Valid.N_pos p hp
  have hK0 := fun k => (Valid.K_pos p hp k).le
  have hH0 : ∀ k, 0 ≤ H k := fun k => by linarith [hH k]
  have hpow := Submission.Obl.k4_discrete_of_terminal_charts.subpower_pow hN hK0 hp.K_sub 3
  have hprod := Submission.Obl.k4_discrete_of_terminal_charts.subpower_mul hNpos
    (fun k => pow_nonneg (hK0 k) 3) hH0 hpow hHsub
  have hbudget := Submission.Obl.k4_discrete_of_terminal_charts.subpower_mul hNpos
    (fun _ => (by norm_num : (0 : ℝ) ≤ 3456))
    (fun k => mul_nonneg (pow_nonneg (hK0 k) 3) (hH0 k))
    (Submission.Obl.k4_discrete_of_terminal_charts.subpower_const hp.N_lim 3456) hprod
  filter_upwards [hbudget s hs] with k hk
  have hNk : 0 ≤ p.N k := (hNpos k).le
  have hKk : 0 ≤ p.K k := hK0 k
  have hHk : 0 ≤ H k := hH0 k
  let V := 216 * p.N k ^ (40 * s) * (2 * p.K k) ^ 2 * (1 + H k) *
    p.N k ^ (-100 * s)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hfactor : 1728 * p.K k ^ 3 * (1 + H k) ≤ 3456 * p.K k ^ 3 * H k := by
    nlinarith [mul_nonneg (show 0 ≤ 1728 * p.K k ^ 3 by positivity)
      (show 0 ≤ H k - 1 by linarith [hH k])]
  have hscaled : V * (2 * p.K k) ≤ p.N k ^ (-59 * s) := by
    calc
      _ = (1728 * p.K k ^ 3 * (1 + H k)) *
          (p.N k ^ (40 * s) * p.N k ^ (-100 * s)) := by dsimp [V]; ring
      _ ≤ (3456 * p.K k ^ 3 * H k) *
          (p.N k ^ (40 * s) * p.N k ^ (-100 * s)) :=
        mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ = (3456 * p.K k ^ 3 * H k) * p.N k ^ (-60 * s) := by
        rw [← Real.rpow_add (hNpos k)]; congr 2; ring
      _ ≤ p.N k ^ s * p.N k ^ (-60 * s) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa only [mul_assoc] using hk
      _ = _ := by rw [← Real.rpow_add (hNpos k)]; congr 1; ring
  constructor
  · apply (le_mul_of_one_le_right hV (show 1 ≤ 2 * p.K k by linarith [hp.K_ge k])).trans
    apply hscaled.trans
    exact Real.rpow_le_rpow_of_exponent_le (hN k) (by linarith)
  · rw [inv_eq_one_div]
    apply (le_div_iff₀ (show 0 < 2 * p.K k by linarith [hp.K_ge k])).mpr
    apply hscaled.trans
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le (hN k) (show -59 * s ≤ 0 by linarith)

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model
