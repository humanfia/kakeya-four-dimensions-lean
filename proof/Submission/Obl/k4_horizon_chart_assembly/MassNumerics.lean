import Mathlib

namespace Submission.Obl.k4_horizon_chart_assembly

/-- The original mass floor survives the three explicit residual terms. -/
theorem retained_mass_ge_inverse {K κ M S b s α : ℝ}
    (hK : 0 < K) (hκ : 2 * K ≤ κ) (hM : K⁻¹ ≤ M)
    (hbound : M ≤ S + b + s + α * M)
    (hb : b ≤ K⁻¹ / 8) (hs : s ≤ K⁻¹ / 8) (hα : α ≤ 1 / 4) : κ⁻¹ ≤ S := by
  have hM₀ : 0 ≤ M := (inv_nonneg.mpr hK.le).trans hM
  have hαM := mul_le_mul_of_nonneg_right hα hM₀
  have hS : K⁻¹ / 2 ≤ S := by nlinarith
  have hκ₀ : 0 < κ := (mul_pos (by norm_num) hK).trans_le hκ
  have hi : κ⁻¹ ≤ (2 * K)⁻¹ := (inv_le_inv₀ hκ₀ (by positivity)).mpr hκ
  calc
    _ ≤ (2 * K)⁻¹ := hi
    _ = K⁻¹ / 2 := by ring
    _ ≤ S := hS

/-- The same final mass calculation for finite original incidence masses. -/
theorem ennreal_retained_mass_ge_inverse {K κ : ℝ} {M S b s α : ENNReal}
    (hK : 0 < K) (hκ : 2 * K ≤ κ) (hMfin : M ≠ ⊤) (hSfin : S ≠ ⊤)
    (hM : ENNReal.ofReal K⁻¹ ≤ M)
    (hbound : M ≤ S + b + s + α * M)
    (hb : b ≤ ENNReal.ofReal (K⁻¹ / 8))
    (hs : s ≤ ENNReal.ofReal (K⁻¹ / 8)) (hα : α ≤ ENNReal.ofReal (1 / 4)) :
    ENNReal.ofReal κ⁻¹ ≤ S := by
  have hbfin : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have hsfin : s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs
  have hαfin : α ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hα
  have hMreal : K⁻¹ ≤ M.toReal := (ENNReal.ofReal_le_iff_le_toReal hMfin).mp hM
  have hbreal : b.toReal ≤ K⁻¹ / 8 := ENNReal.toReal_le_of_le_ofReal (by positivity) hb
  have hsreal : s.toReal ≤ K⁻¹ / 8 := ENNReal.toReal_le_of_le_ofReal (by positivity) hs
  have hαreal : α.toReal ≤ (1 : ℝ) / 4 := ENNReal.toReal_le_of_le_ofReal (by norm_num) hα
  have hreal := ENNReal.toReal_mono (by finiteness) hbound
  rw [ENNReal.toReal_add (a := S + b + s) (b := α * M) (by finiteness) (by finiteness),
    ENNReal.toReal_add (a := S + b) (b := s) (by finiteness) hsfin,
    ENNReal.toReal_add hSfin hbfin, ENNReal.toReal_mul] at hreal
  exact (ENNReal.ofReal_le_iff_le_toReal hSfin).mpr
    (retained_mass_ge_inverse hK hκ hMreal hreal hbreal hsreal hαreal)

end Submission.Obl.k4_horizon_chart_assembly
