-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab.FinalAux.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Slab.Params

/-!
# Auxiliary estimates for the final bookkeeping
-/

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab

open Set Metric MeasureTheory
open scoped ENNReal

lemma cube_count_le {σ ε₁ δ s ρc k n : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hε₁ : 0 < ε₁)
    (hε₁1 : ε₁ < 1 / 2) (hδ : 0 < δ) (hρc : 0 < ρc) (hρcs : ρc ≤ 16 * s) (hk : 0 < k)
    (hn : 0 ≤ n) :
    8 * (ρc ^ (2 - σ - ε₁) * k) * (δ ^ (-ε₁) * (n / k)) ≤ 2048 * s ^ (2 - σ - ε₁) * δ ^ (-ε₁) * n := by
  have hs : 0 < s := by linarith
  have hx : 0 ≤ 2 - σ - ε₁ := by linarith
  have h1 : ρc ^ (2 - σ - ε₁) ≤ (16 * s) ^ (2 - σ - ε₁) := Real.rpow_le_rpow hρc.le hρcs hx
  have h2 : (16 * s) ^ (2 - σ - ε₁) = 16 ^ (2 - σ - ε₁) * s ^ (2 - σ - ε₁) :=
    Real.mul_rpow (by norm_num) hs.le
  have h3 : (16 : ℝ) ^ (2 - σ - ε₁) ≤ 256 := by
    calc (16 : ℝ) ^ (2 - σ - ε₁) ≤ 16 ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 256 := by norm_num
  have hδε : 0 < δ ^ (-ε₁) := Real.rpow_pos_of_pos hδ _
  have e : 8 * (ρc ^ (2 - σ - ε₁) * k) * (δ ^ (-ε₁) * (n / k)) =
      8 * ρc ^ (2 - σ - ε₁) * δ ^ (-ε₁) * n := by field_simp
  rw [e]
  have hsx : 0 ≤ s ^ (2 - σ - ε₁) := Real.rpow_nonneg hs.le _
  have h4 : ρc ^ (2 - σ - ε₁) ≤ 256 * s ^ (2 - σ - ε₁) :=
    (h1.trans_eq h2).trans (mul_le_mul_of_nonneg_right h3 hsx)
  have h5 : 8 * ρc ^ (2 - σ - ε₁) * δ ^ (-ε₁) * n ≤ 8 * (256 * s ^ (2 - σ - ε₁)) * δ ^ (-ε₁) * n := by
    apply mul_le_mul_of_nonneg_right _ hn
    apply mul_le_mul_of_nonneg_right _ hδε.le
    exact mul_le_mul_of_nonneg_left h4 (by norm_num)
  calc 8 * ρc ^ (2 - σ - ε₁) * δ ^ (-ε₁) * n ≤ 8 * (256 * s ^ (2 - σ - ε₁)) * δ ^ (-ε₁) * n := h5
    _ = 2048 * s ^ (2 - σ - ε₁) * δ ^ (-ε₁) * n := by ring

lemma shadingHeightMeasure_mono {n : ℕ} {Y Z : Fin n → Set Space} (hZY : ∀ i, Z i ⊆ Y i)
    (H : Set ℝ) : Reg.shadingHeightMeasure Z H ≤ Reg.shadingHeightMeasure Y H := by
  unfold Reg.shadingHeightMeasure
  rw [Measure.coe_finsetSum, Measure.coe_finsetSum, Finset.sum_apply, Finset.sum_apply]
  apply Finset.sum_le_sum
  intro i _
  exact Measure.le_iff'.mp (Measure.map_mono (Measure.restrict_mono (hZY i) le_rfl)
    (by fun_prop)) H

lemma heightMass_total {n : ℕ} {Y : Fin n → Set Space} (hY : ∀ i, Y i ⊆ ball (0 : Space) 1) :
    heightMass Y (Icc (-1) 1) = ∑ i, volume (Y i) := by
  unfold heightMass
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply inter_eq_left.mpr
  intro p hp
  have h := abs_coord_lt_one (hY i hp) 2
  exact ⟨by linarith [(abs_lt.mp h).1], by linarith [(abs_lt.mp h).2]⟩

/-- The final mass comparison. -/
lemma final_mass {δ ρ s εl ε₁ ε n M S : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hs : 0 < s)
    (hεl : 0 ≤ εl) (hn : 0 ≤ n)
    (hS : S ≤ 384 * n * δ ^ 2) (hM : δ ^ ε₁ * n * δ ^ 2 ≤ M)
    (hs1 : ρ * δ ^ ε₁ / 64 ≤ s) (hs2 : δ / 64 ≤ s)
    (hkey : 73728 * 64 ^ εl * δ ^ (ε - εl - 3 / 2 * ε₁) ≤ 1) :
    δ ^ ε * S ≤ s ^ εl * Real.sqrt s / (24 * Real.sqrt ρ) * M := by
  have hρp : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have hsp : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hδe : 0 < δ ^ ε₁ := Real.rpow_pos_of_pos hδ _
  -- `s ^ εl ≥ (δ / 64) ^ εl`
  have h1 : (δ / 64) ^ εl ≤ s ^ εl := Real.rpow_le_rpow (by positivity) hs2 hεl
  have h1' : (δ / 64) ^ εl = δ ^ εl / 64 ^ εl := Real.div_rpow hδ.le (by norm_num) _
  -- `√s / √ρ ≥ δ ^ (ε₁/2) / 8`
  have h2 : Real.sqrt (δ ^ ε₁) / 8 ≤ Real.sqrt s / Real.sqrt ρ := by
    rw [le_div_iff₀ hρp, Real.le_sqrt (by positivity) hs.le, mul_pow, div_pow,
      Real.sq_sqrt hδe.le, Real.sq_sqrt hρ.le]
    nlinarith
  have h2' : Real.sqrt (δ ^ ε₁) = δ ^ (ε₁ / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hδ.le]; congr 1; ring
  rw [h2'] at h2
  -- assemble
  have hpos : 0 ≤ δ ^ (ε₁ / 2) := Real.rpow_nonneg hδ.le _
  have hlow : δ ^ εl / 64 ^ εl * (δ ^ (ε₁ / 2) / 8) * (δ ^ ε₁ * n * δ ^ 2) / 24 ≤
      s ^ εl * Real.sqrt s / (24 * Real.sqrt ρ) * M := by
    have e : s ^ εl * Real.sqrt s / (24 * Real.sqrt ρ) * M =
        s ^ εl * (Real.sqrt s / Real.sqrt ρ) * M / 24 := by field_simp
    rw [e]
    gcongr
    · rw [← h1']; exact h1
  refine le_trans ?_ hlow
  -- `δ ^ ε * S ≤ ...`
  have h64 : 0 < (64 : ℝ) ^ εl := Real.rpow_pos_of_pos (by norm_num) _
  have hkey' : 73728 * 64 ^ εl * δ ^ ε ≤ δ ^ εl * δ ^ (3 / 2 * ε₁) := by
    have e : δ ^ ε = δ ^ (ε - εl - 3 / 2 * ε₁) * (δ ^ εl * δ ^ (3 / 2 * ε₁)) := by
      rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]; congr 1; ring
    rw [e]
    have hprod : 0 ≤ δ ^ εl * δ ^ (3 / 2 * ε₁) := by positivity
    calc 73728 * 64 ^ εl * (δ ^ (ε - εl - 3 / 2 * ε₁) * (δ ^ εl * δ ^ (3 / 2 * ε₁)))
        = (73728 * 64 ^ εl * δ ^ (ε - εl - 3 / 2 * ε₁)) * (δ ^ εl * δ ^ (3 / 2 * ε₁)) := by ring
      _ ≤ 1 * (δ ^ εl * δ ^ (3 / 2 * ε₁)) := mul_le_mul_of_nonneg_right hkey hprod
      _ = _ := one_mul _
  have hsplit : δ ^ (3 / 2 * ε₁) = δ ^ (ε₁ / 2) * δ ^ ε₁ := by
    rw [← Real.rpow_add hδ]; congr 1; ring
  have hS' : δ ^ ε * S ≤ δ ^ ε * (384 * n * δ ^ 2) :=
    mul_le_mul_of_nonneg_left hS (Real.rpow_nonneg hδ.le _)
  refine hS'.trans ?_
  have : δ ^ ε * (384 * n * δ ^ 2) * (73728 * 64 ^ εl) =
      384 * n * δ ^ 2 * (73728 * 64 ^ εl * δ ^ ε) := by ring
  have h3 : δ ^ ε * (384 * n * δ ^ 2) * (73728 * 64 ^ εl) ≤
      384 * n * δ ^ 2 * (δ ^ εl * δ ^ (3 / 2 * ε₁)) := by
    rw [this]; exact mul_le_mul_of_nonneg_left hkey' (by positivity)
  have e2 : δ ^ εl / 64 ^ εl * (δ ^ (ε₁ / 2) / 8) * (δ ^ ε₁ * n * δ ^ 2) / 24 =
      384 * n * δ ^ 2 * (δ ^ εl * δ ^ (3 / 2 * ε₁)) / (73728 * 64 ^ εl) := by
    rw [hsplit]; field_simp; ring
  rw [e2, le_div_iff₀ (by positivity)]
  exact h3

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab
