/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/LightThresholds.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.EntryBudget
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.MatchingVolume

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open MeasureTheory Set Metric

noncomputable def lightThreshold {Fr : Type*} (ρ : Fr → ℝ) (ζ r X : ℝ)
    (l : Fr × (Fin 3 → ℤ)) : ℝ := (ρ l.1 + ζ) * (2 * r) ^ 3 * X ^ (-8 : ℝ)

theorem lightThreshold_pos {Fr : Type*} {ρ : Fr → ℝ} (hρ : ∀ f, 0 ≤ ρ f)
    {ζ r X : ℝ} (hζ : 0 < ζ) (hr : 0 < r) (hX : 0 < X) (l : Fr × (Fin 3 → ℤ)) :
    0 < lightThreshold ρ ζ r X l := by
  have := hρ l.1
  unfold lightThreshold
  positivity

theorem sum_lightThreshold_le {m J : ℕ} (frame : Fin m → Fin J) (ρ : Fin J → ℝ)
    {ζ r X : ℝ} (hρ : ∀ f, 0 ≤ ρ f) (hζ : 0 ≤ ζ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hX : 1 ≤ X) (hbudget : (∑ i, ρ (frame i)) ≤ X ^ 2)
    (hcount : (m : ℝ) * ζ ≤ 1) :
    (∑ i : Fin m × ↥(gridBox (r / 2) (1 / 8)) × Bool,
      lightThreshold ρ ζ r X (frame i.1, i.2.1.val)) ≤ 5324 * X ^ (-6 : ℝ) := by
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hsum : (∑ i : Fin m, (ρ (frame i) + ζ)) ≤ 2 * X ^ 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hone : 1 ≤ X ^ 2 := one_le_pow₀ hX
    linarith
  have heq : (∑ i : Fin m × ↥(gridBox (r / 2) (1 / 8)) × Bool,
      lightThreshold ρ ζ r X (frame i.1, i.2.1.val)) =
      2 * (((gridBox (r / 2) (1 / 8)).card : ℝ) * (2 * r) ^ 3) * X ^ (-8 : ℝ) *
        (∑ i : Fin m, (ρ (frame i) + ζ)) := by
    simp only [Fintype.sum_prod_type, lightThreshold, Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_bool, Fintype.card_coe, nsmul_eq_mul, Nat.cast_mul,
      Nat.cast_ofNat]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  calc _ ≤ 2 * 1331 * X ^ (-8 : ℝ) * (2 * X ^ 2) := by
          apply mul_le_mul
          · apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hXpos.le _)
            exact mul_le_mul_of_nonneg_left (matching_grid_weight hr hr1) (by norm_num)
          · exact hsum
          · exact Finset.sum_nonneg (fun i _ => add_nonneg (hρ _) hζ)
          · positivity
    _ = 5324 * X ^ (-6 : ℝ) := by
      rw [← Real.rpow_two X]
      have hh : X ^ (-8 : ℝ) * X ^ (2 : ℝ) = X ^ (-6 : ℝ) := by
        rw [← Real.rpow_add hXpos]
        norm_num
      calc _ = 5324 * (X ^ (-8 : ℝ) * X ^ (2 : ℝ)) := by ring
        _ = _ := by rw [hh]

namespace NormalizationStep.TestedSample

variable {cv : Prop} {lam Nk : ℝ} {Wk : ℕ}
  {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure Trajectory}
  {Ek : Fin Wk → Set Incidence} {Bk : Fin Wk → ℝ}
  {L dc a h : ℝ} {M D : ℕ} {ε : ℝ}
  (s : TestedSample cv lam Nk Wk ωk νk Ek Bk L dc a h M D ε)

theorem count_inverse_power (hNk : 0 < Nk) : (s.m : ℝ) * Nk ^ (-(M : ℝ)) ≤ 1 := by
  rw [Real.rpow_neg hNk.le, Real.rpow_natCast]
  calc _ ≤ Nk ^ M * (Nk ^ M)⁻¹ := mul_le_mul_of_nonneg_right s.hm (by positivity)
    _ = 1 := mul_inv_cancel₀ (by positivity)

theorem light_threshold_budget (hω : ∀ γ, 0 ≤ ωk γ) (hωsum : ∑ γ, ωk γ = 1)
    (hNk : 1 ≤ Nk) (ha : 0 < a) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (∑ i : Fin s.m × ↥(gridBox (r / 2) (1 / 8)) × Bool,
      lightThreshold s.sourceCeiling (Nk ^ (-(M : ℝ))) r (Nk ^ a)
        (s.frame i.1, i.2.1.val)) ≤ 5324 * (Nk ^ a) ^ (-6 : ℝ) := by
  have hNkpos : 0 < Nk := zero_lt_one.trans_le hNk
  apply sum_lightThreshold_le s.frame s.sourceCeiling
    (s.sourceCeiling_nonneg hω hNkpos.le) (Real.rpow_nonneg hNkpos.le _) hr hr1
    (Real.one_le_rpow hNk ha.le) _ (s.count_inverse_power hNkpos)
  have hb := s.sum_sourceCeiling_le hω hωsum hNkpos
  rw [← Real.rpow_mul_natCast hNkpos.le a 2]
  convert hb using 1
  congr 1
  push_cast
  ring

end NormalizationStep.TestedSample

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
