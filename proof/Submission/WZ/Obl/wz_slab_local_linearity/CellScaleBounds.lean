-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CellScaleBounds.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.PowerIdentities

namespace WangZahlLot.Obl.wz_slab_local_linearity

lemma cell_layer_scale {ρ : ℝ} {M : ℕ} (hρ : 0 < ρ)
    (hMlo : 1 / Real.sqrt ρ ≤ (M : ℝ)) (hMhi : (M : ℝ) ≤ 2 / Real.sqrt ρ) :
    Real.sqrt ρ ≤ (M : ℝ) * ρ ∧ (M : ℝ) * ρ ≤ 2 * Real.sqrt ρ := by
  have hs := Real.sqrt_pos.mpr hρ
  have hs2 := Real.sq_sqrt hρ.le
  have hlo : 1 ≤ (M : ℝ) * Real.sqrt ρ := (div_le_iff₀ hs).mp hMlo
  have hhi : (M : ℝ) * Real.sqrt ρ ≤ 2 := (le_div_iff₀ hs).mp hMhi
  have he : (M : ℝ) * ρ = ((M : ℝ) * Real.sqrt ρ) * Real.sqrt ρ := by
    calc (M : ℝ) * ρ = (M : ℝ) * (Real.sqrt ρ) ^ 2 := by rw [hs2]
      _ = ((M : ℝ) * Real.sqrt ρ) * Real.sqrt ρ := by ring
  rw [he]
  exact ⟨by simpa only [one_mul] using mul_le_mul_of_nonneg_right hlo hs.le,
    mul_le_mul_of_nonneg_right hhi hs.le⟩

lemma cell_scale_bounds {ρ κ : ℝ} {M : ℕ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hκ : 0 < κ) (hκsmall : κ ≤ 1 / 1000)
    (hMlo : 1 / Real.sqrt ρ ≤ (M : ℝ)) (hMhi : (M : ℝ) ≤ 2 / Real.sqrt ρ) :
    0 < Real.sqrt ρ / 1000 ∧ Real.sqrt ρ / 1000 < 1 ∧
    8 * (Real.sqrt ρ / 1000) * (M * ρ) / ρ + 1 ≤ 100 / κ ∧
    12 * (Real.sqrt ρ / 1000) / (κ / 8 * (M * ρ)) + 1 ≤ 100 / κ ∧
    κ / 8 * ρ / (M * ρ) ≤ Real.sqrt ρ / 1000 ∧
    48 * (M * ρ) * (Real.sqrt ρ / 1000) ≤ ρ := by
  have hs := Real.sqrt_pos.mpr hρ
  have hs2 := Real.sq_sqrt hρ.le
  have hs1 : Real.sqrt ρ ≤ 1 := by nlinarith
  have hκ1 : κ ≤ 1 := by linarith
  obtain ⟨hslow, hshigh⟩ := cell_layer_scale hρ hMlo hMhi
  have hMρ : 0 < (M : ℝ) * ρ := hs.trans_le hslow
  refine ⟨by positivity, by linarith, ?_, ?_, ?_, ?_⟩
  · have h100 : 100 ≤ 100 / κ := by rw [le_div_iff₀ hκ]; linarith
    calc 8 * (Real.sqrt ρ / 1000) * (M * ρ) / ρ + 1
        ≤ 8 * (Real.sqrt ρ / 1000) * (2 * Real.sqrt ρ) / ρ + 1 := by gcongr
      _ = 16 / 1000 + 1 := by field_simp; nlinarith [hs2]
      _ ≤ 100 / κ := by linarith
  · have hden : 0 < κ / 8 * Real.sqrt ρ := by positivity
    calc 12 * (Real.sqrt ρ / 1000) / (κ / 8 * (M * ρ)) + 1
        ≤ 12 * (Real.sqrt ρ / 1000) / (κ / 8 * Real.sqrt ρ) + 1 := by gcongr
      _ = (96 / 1000) / κ + 1 := by field_simp; ring
      _ ≤ 100 / κ := by
        apply (le_div_iff₀ hκ).mpr
        have he : ((96 / 1000) / κ + 1) * κ = 96 / 1000 + κ := by field_simp
        rw [he]
        linarith
  · calc κ / 8 * ρ / (M * ρ) ≤ κ / 8 * ρ / Real.sqrt ρ :=
          div_le_div_of_nonneg_left (by positivity) hs hslow
      _ = κ * Real.sqrt ρ / 8 := by field_simp; nlinarith [hs2]
      _ ≤ Real.sqrt ρ / 1000 := by nlinarith
  · calc 48 * (M * ρ) * (Real.sqrt ρ / 1000)
        ≤ 48 * (2 * Real.sqrt ρ) * (Real.sqrt ρ / 1000) := by gcongr
      _ = (96 / 1000) * ρ := by nlinarith [hs2]
      _ ≤ ρ := by linarith

lemma cell_entropy_lower {ρ ε ε' : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hε : ε' ≤ ε) (hε1 : ε' < 1) :
    ρ ^ ((ε - 1) / 2) ≤ (Real.sqrt ρ / 1000) ^ (ε' - 1) := by
  have hs := Real.sqrt_pos.mpr hρ
  calc ρ ^ ((ε - 1) / 2) ≤ ρ ^ ((ε' - 1) / 2) :=
        Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by linarith)
    _ = (Real.sqrt ρ) ^ (ε' - 1) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hρ.le]
        congr 1
        ring
    _ ≤ (Real.sqrt ρ / 1000) ^ (ε' - 1) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)

lemma cell_ad_budgets {ρ η τ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ) (hκ1 : ρ ^ η ≤ 1)
    (hbudget : 12000 * ρ ^ (-2 * η) ≤ ρ ^ (-τ / 2)) :
    11 ≤ (Real.sqrt ρ / 1000) ^ (-τ) ∧
    12000 / (ρ ^ η) ^ 2 ≤ (Real.sqrt ρ / 1000) ^ (-τ) ∧
    6 * ρ ^ (-η) ≤ (Real.sqrt ρ / 1000) ^ (-τ) := by
  have hs := Real.sqrt_pos.mpr hρ
  have hκ : 0 < ρ ^ η := Real.rpow_pos_of_pos hρ _
  have he : 12000 / (ρ ^ η) ^ 2 = 12000 * ρ ^ (-2 * η) := by
    rw [rpow_nat_power hρ, div_eq_mul_inv, ← Real.rpow_neg hρ.le]
    congr 2
    norm_num
    ring
  have hδ : ρ ^ (-τ / 2) ≤ (Real.sqrt ρ / 1000) ^ (-τ) := by
    calc ρ ^ (-τ / 2) = (Real.sqrt ρ) ^ (-τ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hρ.le]
          congr 1
          ring
      _ ≤ (Real.sqrt ρ / 1000) ^ (-τ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have hn5 : 12000 / (ρ ^ η) ^ 2 ≤ (Real.sqrt ρ / 1000) ^ (-τ) := by
    rw [he]
    exact hbudget.trans hδ
  refine ⟨?_, hn5, ?_⟩
  · apply le_trans _ hn5
    rw [le_div_iff₀ (sq_pos_of_pos hκ)]
    nlinarith
  · apply le_trans _ hn5
    rw [Real.rpow_neg hρ.le, ← div_eq_mul_inv, div_le_div_iff₀ hκ (sq_pos_of_pos hκ)]
    nlinarith

end WangZahlLot.Obl.wz_slab_local_linearity
