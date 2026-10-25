-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.ScaleBudget.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_cover_refinement.Arithmetic

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

/-- A dyadic scale index costs an arbitrarily small power of the fine scale. -/
lemma dyadic_index_bound {u δ : ℝ} (hu : 0 < u) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {L : ℕ} (hscale : δ ≤ ((2 : ℝ) ^ L)⁻¹) :
    (L + 1 : ℝ) ≤ (1 + 1 / (u * Real.log 2)) * δ ^ (-u) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (2 : ℝ) ^ L ≤ δ⁻¹ := by
    have hh := (inv_le_inv₀ (by positivity : 0 < ((2 : ℝ) ^ L)⁻¹) hδ).mpr hscale
    simpa only [inv_inv] using hh
  have hlog := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ L) hpow
  rw [Real.log_pow] at hlog
  have hupper := Real.log_le_rpow_div (inv_pos.mpr hδ).le hu
  have hrpow : (δ⁻¹) ^ u = δ ^ (-u) := by rw [Real.inv_rpow hδ.le, Real.rpow_neg hδ.le]
  rw [hrpow] at hupper
  have hL : (L : ℝ) ≤ δ ^ (-u) / (u * Real.log 2) := by
    apply (le_div_iff₀ (mul_pos hu hlog2)).mpr
    have hh := (le_div_iff₀ hu).mp (hlog.trans hupper)
    nlinarith
  have hunit : 1 ≤ δ ^ (-u) := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      (show -u ≤ 0 by linarith)
  calc
    (L + 1 : ℝ) ≤ δ ^ (-u) / (u * Real.log 2) + δ ^ (-u) := add_le_add hL hunit
    _ = _ := by ring

/-- Uniform absorption of the number of dyadic scales. -/
theorem exists_dyadic_index_cutoff {u : ℝ} (hu : 0 < u) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → δ ≤ d →
      ∀ L : ℕ, δ ≤ ((2 : ℝ) ^ L)⁻¹ → (L + 1 : ℝ) ≤ δ ^ (-2 * u) := by
  have hC : 0 < 1 + 1 / (u * Real.log 2) := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  obtain ⟨d, hd, hb⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
    hu (inv_pos.mpr hC)
  refine ⟨d, hd, fun δ hδ hδ1 hδd L hL => ?_⟩
  have hc : 1 + 1 / (u * Real.log 2) ≤ δ ^ (-u) := by
    rw [Real.rpow_neg hδ.le]
    have hh := (inv_le_inv₀ (inv_pos.mpr hC) (Real.rpow_pos_of_pos hδ u)).mpr (hb δ hδ hδd)
    simpa only [inv_inv] using hh
  calc
    (L + 1 : ℝ) ≤ (1 + 1 / (u * Real.log 2)) * δ ^ (-u) :=
      dyadic_index_bound hu hδ hδ1 hL
    _ ≤ δ ^ (-u) * δ ^ (-u) := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hδ.le _)
    _ = δ ^ (-2 * u) := by rw [← Real.rpow_add hδ]; congr 1; ring

/-- Choose the cinematic strip width dyadically while preserving the original tube radius. -/
lemma exists_dyadic_strip_scale {δ : ℝ} (hδ : 0 < δ) (hsmall : δ < 1 / 208) :
    ∃ L : ℕ, 3 ≤ L ∧ 13 * δ ≤ ((2 : ℝ) ^ L)⁻¹ ∧ ((2 : ℝ) ^ L)⁻¹ < 26 * δ := by
  have ht : 0 < 13 * δ := by positivity
  have ht1 : 13 * δ ≤ 1 := by linarith
  obtain ⟨L, hlo, hhi⟩ := exists_nat_pow_near_of_lt_one ht ht1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have he (k : ℕ) : (1 / 2 : ℝ) ^ k = ((2 : ℝ) ^ k)⁻¹ := by simp
  have hwidth : ((2 : ℝ) ^ L)⁻¹ < 26 * δ := by
    rw [pow_succ, he] at hlo
    linarith
  have hL : 3 ≤ L := by
    by_contra h
    have hL2 : L ≤ 2 := by omega
    have hside : (1 / 4 : ℝ) ≤ ((2 : ℝ) ^ L)⁻¹ := by
      have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hL2
      have hh := (inv_le_inv₀ (by positivity) (by positivity)).mpr hp
      norm_num at hh
      exact hh
    linarith
  exact ⟨L, hL, by rwa [he] at hhi, hwidth⟩

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
