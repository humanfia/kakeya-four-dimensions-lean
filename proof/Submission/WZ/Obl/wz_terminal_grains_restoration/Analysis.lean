-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_terminal_grains_restoration.Analysis.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Small-scale numerical facts for o149
-/

namespace WangZahlLot.Obl.wz_terminal_grains_restoration

noncomputable section

/-- Every constant lies below `δ^(-ε)` for small `δ`. -/
theorem const_le_rpow_neg {ε : ℝ} (hε : 0 < ε) (K : ℝ) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → K ≤ δ ^ (-ε) := by
  have hM : 0 < max K 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨(max K 1) ^ (-(1 / ε)), by positivity, ?_, ?_⟩
  · exact Real.rpow_le_one_of_one_le_of_nonpos (le_max_right _ _)
      (by have := one_div_pos.2 hε; linarith)
  · intro δ hδ hδd
    calc K ≤ max K 1 := le_max_left _ _
      _ = ((max K 1) ^ (-(1 / ε))) ^ (-ε) := by
          rw [← Real.rpow_mul hM.le]
          have : -(1 / ε) * -ε = 1 := by field_simp
          rw [this, Real.rpow_one]
      _ ≤ δ ^ (-ε) := Real.rpow_le_rpow_of_nonpos hδ hδd (by linarith)

/-- `δ^(-a) = (δ⁻¹)^a`. -/
theorem rpow_neg_eq_inv_rpow {δ : ℝ} (hδ : 0 < δ) (a : ℝ) : δ ^ (-a) = δ⁻¹ ^ a := by
  rw [Real.rpow_neg hδ.le, Real.inv_rpow hδ.le]

/-- The number of dyadic classes up to `C₀ δ^(-3)`, squared, is below `δ^(-h/4)` for small `δ`. -/
theorem log_class_bound {h : ℝ} (hh : 0 < h) (C₀ : ℝ) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → ∀ n : ℕ, (n : ℝ) ≤ C₀ * δ ^ (-(3:ℝ)) →
      ((Nat.log 2 n : ℝ) + 1) ^ 2 ≤ δ ^ (-(h / 4)) := by
  set C := max C₀ 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  have hCpos : 0 < C := lt_of_lt_of_le one_pos hC1
  set ε := h / 16 with hεdef
  have hε : 0 < ε := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC1
  set K := (Real.log C + 3 / ε) / Real.log 2 + 1 with hKdef
  have hK : 0 ≤ K := by positivity
  obtain ⟨d, hd, hd1, hdK⟩ := const_le_rpow_neg (ε := h / 8) (by positivity) (K ^ 2)
  refine ⟨d, hd, hd1, ?_⟩
  intro δ hδ hδd n hn
  have hδ1 : δ ≤ 1 := hδd.trans hd1
  set u := δ⁻¹ with hudef
  have hu1 : 1 ≤ u := by rw [hudef]; exact one_le_inv₀ hδ |>.2 hδ1
  have hupos : 0 < u := lt_of_lt_of_le one_pos hu1
  have hgoal : δ ^ (-(h / 4)) = u ^ (h / 8) * u ^ (h / 8) := by
    rw [rpow_neg_eq_inv_rpow hδ, ← Real.rpow_add hupos]
    congr 1; ring
  have hKu : K ^ 2 ≤ u ^ (h / 8) := by
    have := hdK δ hδ hδd
    rwa [rpow_neg_eq_inv_rpow hδ] at this
  have huε : 1 ≤ u ^ ε := Real.one_le_rpow hu1 hε.le
  -- the main estimate `L + 1 ≤ K u^ε`
  have hL : (Nat.log 2 n : ℝ) + 1 ≤ K * u ^ ε := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      simp only [Nat.log_zero_right, CharP.cast_eq_zero, zero_add]
      have : 1 ≤ K := by
        rw [hKdef]
        have : 0 ≤ (Real.log C + 3 / ε) / Real.log 2 := by positivity
        linarith
      calc (1 : ℝ) ≤ K := this
        _ = K * 1 := (mul_one K).symm
        _ ≤ K * u ^ ε := mul_le_mul_of_nonneg_left huε hK
    · set L := Nat.log 2 n with hLdef
      have hpow : 2 ^ L ≤ n := Nat.pow_log_le_self 2 hnpos.ne'
      have hnreal : (2 : ℝ) ^ L ≤ (n : ℝ) := by exact_mod_cast hpow
      have hn' : (n : ℝ) ≤ C * u ^ (3:ℝ) := by
        calc (n : ℝ) ≤ C₀ * δ ^ (-(3:ℝ)) := hn
          _ ≤ C * δ ^ (-(3:ℝ)) := by
              gcongr
              exact le_max_left _ _
          _ = C * u ^ (3:ℝ) := by rw [rpow_neg_eq_inv_rpow hδ]
      have hlogL : (L : ℝ) * Real.log 2 ≤ Real.log C + 3 * Real.log u := by
        have h2L : (0 : ℝ) < 2 ^ L := by positivity
        calc (L : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ L) := (Real.log_pow 2 L).symm
          _ ≤ Real.log (C * u ^ (3:ℝ)) := Real.log_le_log h2L (hnreal.trans hn')
          _ = Real.log C + 3 * Real.log u := by
              rw [Real.log_mul hCpos.ne' (by positivity), Real.log_rpow hupos]
      have hlogu : Real.log u ≤ u ^ ε / ε := Real.log_le_rpow_div hupos.le hε
      have hL' : (L : ℝ) ≤ (Real.log C + 3 * (u ^ ε / ε)) / Real.log 2 := by
        rw [le_div_iff₀ hlog2]
        nlinarith
      calc (L : ℝ) + 1 ≤ (Real.log C + 3 * (u ^ ε / ε)) / Real.log 2 + 1 := by linarith
        _ ≤ (Real.log C * u ^ ε + 3 * (u ^ ε / ε)) / Real.log 2 + 1 * u ^ ε := by
            gcongr
            · nlinarith
            · linarith
        _ = K * u ^ ε := by
            rw [hKdef]
            field_simp
  have hsq : ((Nat.log 2 n : ℝ) + 1) ^ 2 ≤ K ^ 2 * u ^ (h / 8) := by
    have h0 : 0 ≤ (Nat.log 2 n : ℝ) + 1 := by positivity
    calc ((Nat.log 2 n : ℝ) + 1) ^ 2 ≤ (K * u ^ ε) ^ 2 := pow_le_pow_left₀ h0 hL 2
      _ = K ^ 2 * u ^ (h / 8) := by
          rw [mul_pow, ← Real.rpow_natCast (u ^ ε) 2, ← Real.rpow_mul hupos.le]
          congr 2
          rw [hεdef]; push_cast; ring
  rw [hgoal]
  calc ((Nat.log 2 n : ℝ) + 1) ^ 2 ≤ K ^ 2 * u ^ (h / 8) := hsq
    _ ≤ u ^ (h / 8) * u ^ (h / 8) := by
        gcongr

end

end WangZahlLot.Obl.wz_terminal_grains_restoration
