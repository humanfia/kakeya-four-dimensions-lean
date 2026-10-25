import Submission.Obl.k4_scalar_mesh_block_reduction.Uniformity
import Submission.Obl.k4_quadratic_atlas_normalization.MassSelection

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement

open Filter

lemma normalization_loss_subpower (N ε : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k)
    (hNt : Tendsto N atTop atTop) (hε : ∀ k, 0 ≤ ε k) (hεt : Tendsto ε atTop (nhds 0)) :
    (∀ k, 1 ≤ 8 * N k ^ ε k) ∧
      ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, 8 * N k ^ ε k ≤ N k ^ η := by
  obtain ⟨hbase, hsub⟩ := k4_scalar_mesh_block_reduction.subpower_of_vanishing_exponent
    N ε (fun k => by linarith [hN k]) hε hεt
  refine ⟨(fun k => by nlinarith [hbase k]), ?_⟩
  intro η hη
  have hhalf : 0 < η / 2 := by positivity
  have hc : ∀ᶠ k in atTop, (8 : ℝ) ≤ N k ^ (η / 2) :=
    ((tendsto_rpow_atTop hhalf).comp hNt).eventually (eventually_ge_atTop 8)
  filter_upwards [hsub (η / 2) hhalf, hc] with k hk hkc
  calc
    8 * N k ^ ε k ≤ N k ^ (η / 2) * N k ^ (η / 2) := by
      exact mul_le_mul hkc hk (Real.rpow_nonneg (by linarith [hN k]) _) (by positivity)
    _ = N k ^ η := by
      rw [← Real.rpow_add (by linarith [hN k])]
      congr 1
      ring

/-- The exact coefficient-volume factor is polynomially bounded on a chart. -/
lemma coefficient_volume_factor_bound {N ε h dt J δ : ℝ}
    (hN : 1 ≤ N) (hε : ε ≤ 1) (hdt : 0 < dt) (hdt1 : dt ≤ 1)
    (hdtinv : dt⁻¹ ≤ N ^ (h + ε)) (hJ : 0 ≤ J) (hJfit : J ≤ N ^ ε * dt)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    J ^ 2 * δ ^ 3 / dt ^ 4 ≤ N ^ (4 * h + 6) := by
  have hN0 : 0 < N := by linarith
  have hJN : J ≤ N := by
    calc
      J ≤ N ^ ε * dt := hJfit
      _ ≤ N ^ ε * 1 := mul_le_mul_of_nonneg_left hdt1 (Real.rpow_nonneg hN0.le _)
      _ = N ^ ε := mul_one _
      _ ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN hε
      _ = N := Real.rpow_one _
  have hdinv : dt⁻¹ ≤ N ^ (h + 1) := hdtinv.trans
    (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
  have hδpow : δ ^ 3 ≤ 1 := pow_le_one₀ hδ hδ1
  calc
    J ^ 2 * δ ^ 3 / dt ^ 4 = J ^ 2 * δ ^ 3 * (dt⁻¹) ^ 4 := by rw [div_eq_mul_inv, inv_pow]
    _ ≤ N ^ 2 * 1 * (N ^ (h + 1)) ^ 4 := by gcongr
    _ = N ^ (4 * h + 6) := by
      rw [mul_one, ← Real.rpow_natCast N 2, ← Real.rpow_natCast (N ^ (h + 1)) 4,
        ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
      congr 1
      ring

/-- A polynomial prior-mass cut also bounds every normalized density height. -/
lemma normalized_prior_height_bound {N ε h dt J δ mass M Q : ℝ}
    (hN : 1 ≤ N) (hε : ε ≤ 1) (hdt : 0 < dt) (hdt1 : dt ≤ 1)
    (hdtinv : dt⁻¹ ≤ N ^ (h + ε)) (hJ : 0 ≤ J) (hJfit : J ≤ N ^ ε * dt)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmass : N ^ (-Q) ≤ mass) :
    N ^ M * (J ^ 2 * δ ^ 3 / dt ^ 4) / mass ≤ N ^ (M + 4 * h + 6 + Q) := by
  have hN0 : 0 < N := by linarith
  have hm0 : 0 < mass := (Real.rpow_pos_of_pos hN0 _).trans_le hmass
  have hminv : mass⁻¹ ≤ N ^ Q := by
    have h := inv_anti₀ (Real.rpow_pos_of_pos hN0 (-Q)) hmass
    simpa only [Real.rpow_neg hN0.le, inv_inv] using h
  have hc := coefficient_volume_factor_bound hN hε hdt hdt1 hdtinv hJ hJfit hδ hδ1
  calc
    N ^ M * (J ^ 2 * δ ^ 3 / dt ^ 4) / mass =
        N ^ M * (J ^ 2 * δ ^ 3 / dt ^ 4) * mass⁻¹ := div_eq_mul_inv _ _
    _ ≤ N ^ M * N ^ (4 * h + 6) * N ^ Q := by gcongr
    _ = N ^ (M + 4 * h + 6 + Q) := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1
      ring

lemma normalization_format_count_bound {N a b : ℝ} (hN : 2 ≤ N) :
    N ^ a + N ^ b ≤ N ^ (max a b + 1) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  calc
    N ^ a + N ^ b ≤ N ^ max a b + N ^ max a b :=
      add_le_add (Real.rpow_le_rpow_of_exponent_le hN1 (le_max_left a b))
        (Real.rpow_le_rpow_of_exponent_le hN1 (le_max_right a b))
    _ = 2 * N ^ max a b := by ring
    _ ≤ N * N ^ max a b := mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hN0.le _)
    _ = N ^ (max a b + 1) := by rw [Real.rpow_add hN0, Real.rpow_one]; ring

lemma power_pruning_budget {N ε : ℝ} (hN : 2 ≤ N) (hε : ε ≤ 1) (hNε : 2 ≤ N ^ ε) :
    N ^ (-2 : ℝ) ≤ N ^ (-ε) / 2 ∧ N ^ (-2 * ε) ≤ N ^ (-ε) / 2 := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hinv : N ^ (-1 : ℝ) ≤ 1 / 2 := by
    rw [Real.rpow_neg hN0.le, Real.rpow_one]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hN
  have hsmall : N ^ (ε - 2) ≤ 1 / 2 :=
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : ε - 2 ≤ (-1 : ℝ))).trans hinv
  have hneg : N ^ (-ε) ≤ 1 / 2 := by
    rw [Real.rpow_neg hN0.le]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hNε
  constructor
  · calc
      N ^ (-2 : ℝ) = N ^ (-ε) * N ^ (ε - 2) := by
        rw [← Real.rpow_add hN0]
        congr 1
        ring
      _ ≤ N ^ (-ε) * (1 / 2) := mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hN0.le _)
      _ = _ := by ring
  · calc
      N ^ (-2 * ε) = N ^ (-ε) * N ^ (-ε) := by
        rw [← Real.rpow_add hN0]
        congr 1
        ring
      _ ≤ N ^ (-ε) * (1 / 2) := mul_le_mul_of_nonneg_left hneg (Real.rpow_nonneg hN0.le _)
      _ = _ := by ring

lemma retain_power_mass_after_prior_cut {N ε : ℝ}
    (hN : 2 ≤ N) (hε : ε ≤ 1) (hNε : 2 ≤ N ^ ε)
    (mass retained deleted : ENNReal) (hlower : ENNReal.ofReal (N ^ (-ε)) ≤ mass)
    (hcover : mass ≤ retained + deleted) (hdeleted : deleted ≤ ENNReal.ofReal (N ^ (-2 : ℝ))) :
    ENNReal.ofReal (N ^ (-2 * ε)) ≤ retained := by
  have hb := power_pruning_budget hN hε hNε
  have hhalf := k4_quadratic_atlas_normalization.retain_half_mass mass retained deleted
    (N ^ (-ε)) (Real.rpow_nonneg (by linarith [hN]) _) hlower hcover
    (hdeleted.trans (ENNReal.ofReal_le_ofReal hb.1))
  exact (ENNReal.ofReal_le_ofReal hb.2).trans hhalf

end Submission.Obl.k4_scalar_normalized_exact_refinement
