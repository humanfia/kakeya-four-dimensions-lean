-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.SmallPowers.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.ScaleDyadic

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

lemma constant_power_bound {C ν : ℝ} (hC : 0 < C) (hν : 0 < ν) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → C ≤ δ ^ (-ν) := by
  refine ⟨C ^ (-ν⁻¹), Real.rpow_pos_of_pos hC _, ?_⟩
  intro δ hδ hδd
  have hh := Real.rpow_le_rpow_of_nonpos hδ hδd (neg_nonpos.mpr hν.le)
  rw [← Real.rpow_mul hC.le, show -ν⁻¹ * -ν = 1 by field_simp, Real.rpow_one] at hh
  exact hh

lemma dyadic_size_log_bound {M a : ℝ} (ha : 0 < a) (haM : a ≤ M) :
    (Scale.dyExp M a : ℝ) + 1 ≤ Real.log (M / a) / Real.log 2 + 1 := by
  have hlog : 0 ≤ Real.logb 2 (M / a) :=
    Real.logb_nonneg (by norm_num) ((one_le_div ha).mpr haM)
  have hn : (Scale.dyExp M a : ℝ) ≤ Real.log (M / a) / Real.log 2 := Nat.floor_le hlog
  linarith

/-- A dyadic scale count, including the factor two needed for half-mass
selection, is uniformly smaller than any prescribed negative power. -/
theorem dyadic_size_power_bound {M k ν : ℝ} (hM : 1 ≤ M) (hk : 0 < k) (hν : 0 < ν) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → δ ≤ d →
      2 * ((Scale.dyExp M (δ ^ k) : ℝ) + 1) ≤ δ ^ (-ν) := by
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let e := ν / (2 * k)
  have he : 0 < e := by dsimp [e]; positivity
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C := 2 * (M ^ e / (e * Real.log 2) + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨d, hd, hbound⟩ := constant_power_bound hC (half_pos hν)
  refine ⟨d, hd, ?_⟩
  intro δ hδ hδ1 hδd
  have hδk : 0 < δ ^ k := Real.rpow_pos_of_pos hδ _
  have hδkM : δ ^ k ≤ M := (Real.rpow_le_one hδ.le hδ1 hk.le).trans hM
  have hs := dyadic_size_log_bound hδk hδkM
  have hl := Real.log_le_rpow_div (div_pos hM0 hδk).le he
  have hpow : (M / δ ^ k) ^ e = M ^ e * δ ^ (-(ν / 2)) := by
    rw [Real.div_rpow hM0.le hδk.le, ← Real.rpow_mul hδ.le]
    have hke : k * e = ν / 2 := by dsimp [e]; field_simp
    rw [hke, Real.rpow_neg hδ.le, div_eq_mul_inv]
  have hone : 1 ≤ δ ^ (-(ν / 2)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hpoly : 2 * ((Scale.dyExp M (δ ^ k) : ℝ) + 1) ≤ C * δ ^ (-(ν / 2)) := by
    have hh := div_le_div_of_nonneg_right hl hlog.le
    rw [hpow] at hh
    dsimp [C]
    have hh' : Real.log (M / δ ^ k) / Real.log 2 ≤
        M ^ e / (e * Real.log 2) * δ ^ (-(ν / 2)) := by
      convert hh using 1 <;> field_simp <;> ring
    nlinarith
  calc
    _ ≤ C * δ ^ (-(ν / 2)) := hpoly
    _ ≤ δ ^ (-(ν / 2)) * δ ^ (-(ν / 2)) :=
      mul_le_mul_of_nonneg_right (hbound δ hδ hδd) (Real.rpow_nonneg hδ.le _)
    _ = _ := by rw [← Real.rpow_add hδ]; congr 1; ring

/-- The elementary logarithmic aspect-ratio loss is also subpower. -/
theorem logarithm_power_bound {M ν : ℝ} (hM : 1 ≤ M) (hν : 0 < ν) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → δ ≤ d →
      1 + Real.log (M / δ) ≤ δ ^ (-ν) := by
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let C := 1 + M ^ (ν / 2) / (ν / 2)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨d, hd, hbound⟩ := constant_power_bound hC (half_pos hν)
  refine ⟨d, hd, ?_⟩
  intro δ hδ hδ1 hδd
  have hl := Real.log_le_rpow_div (div_pos hM0 hδ).le (half_pos hν)
  rw [Real.div_rpow hM0.le hδ.le] at hl
  have hone : 1 ≤ δ ^ (-(ν / 2)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hpoly : 1 + Real.log (M / δ) ≤ C * δ ^ (-(ν / 2)) := by
    dsimp [C]
    rw [Real.rpow_neg hδ.le]
    rw [Real.rpow_neg hδ.le] at hone
    nlinarith [show M ^ (ν / 2) / δ ^ (ν / 2) / (ν / 2) =
      M ^ (ν / 2) / (ν / 2) * (δ ^ (ν / 2))⁻¹ by ring]
  calc
    _ ≤ C * δ ^ (-(ν / 2)) := hpoly
    _ ≤ δ ^ (-(ν / 2)) * δ ^ (-(ν / 2)) :=
      mul_le_mul_of_nonneg_right (hbound δ hδ hδd) (Real.rpow_nonneg hδ.le _)
    _ = _ := by rw [← Real.rpow_add hδ]; congr 1; ring

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
