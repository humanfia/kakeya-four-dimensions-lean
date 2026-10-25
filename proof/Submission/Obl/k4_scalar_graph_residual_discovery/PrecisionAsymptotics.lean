import Submission.Obl.k4_scalar_graph_residual_discovery.PrecisionKernel
import Submission.Obl.k4_scalar_graph_residual_discovery.BlockPowers

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Filter
open Submission.Obl.k4_scalar_marked_coefficient_smoothing
open Submission.Obl.k4_profile_density_bounds

/-- All geometric precision fields follow from strict fixed scale gaps
and a polynomial envelope. The coarse exponent is also the first-grid
terminal exponent, so it can be an integer on every preparation mesh. -/
theorem eventually_precision_of_envelope {N U H Hg R Q : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop) (hU : Subpower N U)
    (hH : ∀ k, 0 ≤ H k) (hHg : ∀ k, 0 ≤ Hg k) (hR : ∀ k, 0 ≤ R k)
    {A e a C L B : ℝ} (hA : 0 ≤ A) (p : ℕ)
    (hgapρ : e - a < -C) (hgapz : e - L < -a - C) (hgapb : e - B < -a - C)
    (haL : a ≤ L) (haB : a ≤ B)
    (hbound : ∀ᶠ k in atTop,
      precisionEnvelope (H k) (Hg k) (R k) (Q k) ≤ A * U k ^ p * N k ^ e) :
    ∀ᶠ k in atTop,
      (1 + 3 * (H k + 1)) * N k ^ (-B) ≤ N k ^ (-a) * N k ^ (-C) ∧
      (Hg k * N k ^ (-L) + R k *
        (N k ^ (-a) + 2 * N k ^ (-B) + N k ^ (-a)) * (1 + H k)) *
        (N k ^ (-a) + 2 * N k ^ (-B)) + 2 * (1 + 2 * Hg k) * N k ^ (-B) ≤
          N k ^ (-a) * N k ^ (-C) ∧
      4 * Q k ^ 2 * N k ^ (-a) + Hg k * N k ^ (-L) / N k ^ (-a) +
        2 * (H k + 1) * N k ^ (-B) / N k ^ (-a) ≤ N k ^ (-C) ∧
      2 * (R k * (N k ^ (-a) + 2 * N k ^ (-B) + N k ^ (-a)) +
        4 * Q k ^ 2 * N k ^ (-a)) + (1 + 2 * Hg k) * N k ^ (-B) / N k ^ (-a) ≤
          N k ^ (-C) := by
  have h10A : 0 ≤ 10 * A := by positivity
  filter_upwards [hbound,
    eventually_subpower_mul_rpow_lt hN hNt hU.1 hU.2 p hgapρ h10A,
    eventually_subpower_mul_rpow_lt hN hNt hU.1 hU.2 p hgapz h10A,
    eventually_subpower_mul_rpow_lt hN hNt hU.1 hU.2 p hgapb h10A]
      with k hk hρ hz hb
  have hNp : 0 < N k := zero_lt_one.trans_le (hN k)
  have hprod : N k ^ (-a) * N k ^ (-C) = N k ^ (-a - C) := by
    simpa only [sub_eq_add_neg] using (Real.rpow_add hNp (-a) (-C)).symm

  have hterm (v : ℝ) :
      10 * (precisionEnvelope (H k) (Hg k) (R k) (Q k) * N k ^ (-v)) ≤
        (10 * A) * U k ^ p * N k ^ (e - v) := by
    calc
      _ ≤ 10 * ((A * U k ^ p * N k ^ e) * N k ^ (-v)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hNp.le _)) (by norm_num)
      _ = _ := by rw [sub_eq_add_neg, Real.rpow_add hNp]; ring
  apply precision_kernel (hH k) (hHg k) (hR k) (Real.rpow_pos_of_pos hNp _)
    (Real.rpow_nonneg hNp.le _) (Real.rpow_nonneg hNp.le _) (Real.rpow_nonneg hNp.le _)
    (Real.rpow_le_rpow_of_exponent_le (hN k) (neg_le_neg haB))
    (Real.rpow_le_rpow_of_exponent_le (hN k) (neg_le_neg haL))
  · have hh := (hterm a).trans hρ.le
    linarith
  · have hh := (hterm B).trans hb.le
    rw [← hprod] at hh
    linarith
  · have hh := (hterm L).trans hz.le
    rw [← hprod] at hh
    linarith

/-- The same envelope controls both errors transferred to the original
row. Only the fixed scale gap and original subpower bounds enter here. -/
theorem eventually_row_graph_margins_of_envelope {N U K h H Hg R Q : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hU : Subpower N U) (hK : Subpower N K)
    (hH : ∀ k, 0 ≤ H k) (hHg : ∀ k, 0 ≤ Hg k) (hR : ∀ k, 0 ≤ R k)
    {A e a L κ β : ℝ} (hA : 0 ≤ A) (p : ℕ) (hβ : 0 < β)
    (hgapρ : e - a < -κ * β) (hgapz : e - L < -κ * β)
    (hscale : ∀ᶠ k in atTop, N k ^ (-κ) / K k ≤ h k)
    (hbound : ∀ᶠ k in atTop,
      precisionEnvelope (H k) (Hg k) (R k) (Q k) ≤ A * U k ^ p * N k ^ e) :
    ∀ᶠ k in atTop, Hg k * N k ^ (-L) ≤ h k ^ β ∧
      4 * Q k ^ 2 * N k ^ (-a) ≤ h k ^ β := by
  filter_upwards [hbound,
    eventually_monomial_le_block_rpow hN hNt hU hK hβ hgapρ hA p hscale,
    eventually_monomial_le_block_rpow hN hNt hU hK hβ hgapz hA p hscale]
      with k hk hρ hz
  have hNp : 0 < N k := zero_lt_one.trans_le (hN k)
  have hHR : 0 ≤ (1 + H k) * R k := mul_nonneg (by linarith [hH k]) (hR k)
  have hG : Hg k ≤ precisionEnvelope (H k) (Hg k) (R k) (Q k) := by
    dsimp only [precisionEnvelope]
    nlinarith only [hH k, hHg k, hHR, sq_nonneg (Q k)]
  have hQ : 4 * Q k ^ 2 ≤ precisionEnvelope (H k) (Hg k) (R k) (Q k) := by
    dsimp only [precisionEnvelope]
    nlinarith only [hH k, hHg k, hHR, sq_nonneg (Q k)]
  have hterm (v : ℝ) :
      precisionEnvelope (H k) (Hg k) (R k) (Q k) * N k ^ (-v) ≤
        A * U k ^ p * N k ^ (e - v) := by
    calc
      _ ≤ (A * U k ^ p * N k ^ e) * N k ^ (-v) :=
        mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hNp.le _)
      _ = _ := by rw [sub_eq_add_neg, Real.rpow_add hNp]; ring
  exact ⟨((mul_le_mul_of_nonneg_right hG (Real.rpow_nonneg hNp.le _)).trans
      (hterm L)).trans hz,
    ((mul_le_mul_of_nonneg_right hQ (Real.rpow_nonneg hNp.le _)).trans (hterm a)).trans hρ⟩

end Submission.Obl.k4_scalar_graph_residual_discovery
