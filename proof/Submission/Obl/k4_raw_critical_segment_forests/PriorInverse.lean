import Submission.Obl.k4_raw_critical_segment_forests.Saturation
import Submission.Obl.k4_raw_critical_segment_forests.Widths

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- Supplied prepared parents already have polynomially positive full priors;
no selection or change of parent labels is required. -/
theorem PreparedParent.prior_inverse {p : Data} (hp : Valid p) {k M D : ℕ}
    {r ε κ : ℝ} {a : Atlas p k} (ha : PreparedParent p M D r ε κ a) (hε : ε ≤ 1)
    (b : Fin a.C) :
    (p.ν k (a.γ b) (a.A b)).toReal⁻¹ ≤ p.N k ^ (2 * M + ⌈max (p.f r) 0⌉₊ + 1) := by
  have hN := hp.scale_pos k
  have hN1 := hp.scale_ge_one k
  have hκ : 0 < κ := lt_of_lt_of_le zero_lt_one ha.1
  have hc := ha.2.2.2.2.1.2.2.1 b
  have hdetpos : 0 < |Matrix.det (a.Q b)| := abs_pos.mpr hc.1
  have hκN : κ ≤ p.N k := ha.2.2.1.trans
    ((Real.rpow_le_rpow_of_exponent_le hN1 hε).trans_eq (Real.rpow_one _))
  have hsum : (∑ i : Fin 2, ∑ j : Fin 2, |(a.Q b)⁻¹ i j|) ≤ p.N k ^ M := by
    apply le_trans ?_ hc.2.2.1
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      le_add_of_nonneg_left (abs_nonneg ((a.Q b) i j))
  have hdetInv := (abs_det_le_entry_sum_sq (a.Q b)⁻¹).trans
    (pow_le_pow_left₀ (by positivity) hsum 2)
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', abs_inv] at hdetInv
  have hs := ha.prior_saturation hp b
  have hlow : 0 < p.N k ^ (-p.f r) * |Matrix.det (a.Q b)| / κ := by positivity
  have hpowinv : (p.N k ^ (-p.f r))⁻¹ = p.N k ^ (p.f r) := by
    rw [← Real.rpow_neg hN.le, neg_neg]
  have hsq : (p.N k ^ M) ^ 2 = p.N k ^ (2 * (M : ℝ)) := by
    rw [← Real.rpow_natCast (p.N k ^ M) 2, ← Real.rpow_natCast (p.N k) M,
      ← Real.rpow_mul hN.le]
    congr 1
    ring
  calc
    _ ≤ (p.N k ^ (-p.f r) * |Matrix.det (a.Q b)| / κ)⁻¹ := inv_anti₀ hlow hs.2.1
    _ = κ * p.N k ^ (p.f r) * |Matrix.det (a.Q b)|⁻¹ := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, hpowinv]
      ring
    _ ≤ p.N k * p.N k ^ (p.f r) * (p.N k ^ M) ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hκN (Real.rpow_nonneg hN.le _))
        hdetInv (by positivity) (by positivity)
    _ = p.N k ^ (p.f r + 2 * (M : ℝ) + 1) := by
      rw [hsq]
      nth_rw 1 [← Real.rpow_one (p.N k)]
      rw [← Real.rpow_add hN, ← Real.rpow_add hN]
      congr 1
      ring
    _ ≤ _ := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le hN1
      have hceil : p.f r ≤ (⌈max (p.f r) 0⌉₊ : ℝ) :=
        (le_max_left _ _).trans (Nat.le_ceil _)
      push_cast
      linarith only [hceil]

end
end Submission.Obl.k4_raw_critical_segment_forests
