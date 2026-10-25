-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.CaseAPowers.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.CaseAContradiction
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.WindowNumerics

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

variable {r s ε₀ ε κ : ℝ} {n : ℕ} {P : Finset E2} {D S J₀ : Finset (E2 × E2)}
  {cls : E2 × E2 → E2 × E2} {J₁ : ℕ → Finset (E2 × E2)}
  {tb : ℕ → E2 × E2 → E2 × E2}

/-- The class count entering the quadratic and degree estimates has an
explicit small-power loss. -/
theorem HighConfig.winZ_le_power
    (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    {ℓ ν w : ℝ} {KY : ℕ} (hr1 : r ≤ 1) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hw : 0 < w) (hw26 : 26 * w ≤ 1)
    (hpin : pinConst w (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY ≤
      r ^ (-2 * ε - ν)) :
    winZ r s ε (r ^ ℓ) (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY
      (S.image cls).card w ≤
      (5200 * nearTubeConst) * r ^ (-(10 * ε + 2 * s + ε₀ + ℓ * s + ν)) := by
  classical
  have hr := H.fail.r_pos
  have hsub : S.image cls ⊆ J₀ := by
    intro j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    exact H.cls_mem q (H.sub hq)
  have hlines : ((S.image cls).card : ℝ) ≤ r ^ (-(2 * s) - ε₀) :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (H.fail.few_lines J₀ H.lines_sub H.lines_sep).le
  have hquad : quadConst r s ε (r ^ (-ε)) (r ^ ℓ) ≤
      5200 * r ^ (-3 * ε - 3 * ε - ℓ * s) :=
    tubeConst_le_power hr hr1 hs1 hε
  have hCn := nearTubeConst_pos
  have hquad0 := quadConst_nonneg (s := s) (ε := ε) hr
    (Real.rpow_nonneg hr.le (-ε)) (Real.rpow_pos_of_pos hr ℓ)
  have hpin0 : 0 ≤ pinConst w (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY :=
    pinConst_nonneg' hw hw26 (by positivity)
  unfold winZ
  calc
    _ ≤ (r ^ (-ε)) ^ 2 *
        ((5200 * r ^ (-3 * ε - 3 * ε - ℓ * s)) * r ^ (-(2 * s) - ε₀)) *
        (nearTubeConst * r ^ (-2 * ε - ν)) := by gcongr
    _ = (5200 * nearTubeConst) * ((r ^ (-ε)) ^ (2 : ℕ) *
        r ^ (-3 * ε - 3 * ε - ℓ * s) * r ^ (-(2 * s) - ε₀) * r ^ (-2 * ε - ν)) := by ring
    _ = _ := by
      congr 1
      rw [← Real.rpow_mul_natCast hr.le, ← Real.rpow_add hr,
        ← Real.rpow_add hr, ← Real.rpow_add hr]
      congr 1
      norm_num
      ring

/-- Power bookkeeping for the quadratic constant of the selected tube. -/
theorem winK0J_le_power {r s ε d u Z C : ℝ}
    (hr : 0 < r) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hZ : Z ≤ C * r ^ (-(10 * ε + 2 * s + u))) :
    winK0J r s ε d Z ≤
      (64 * C * arcTubeConst ^ (4 : ℕ) * 98 ^ (2 : ℕ) * 36) *
        r ^ (-(26 * ε + u + 2 * d)) := by
  have hAC : 0 < arcTubeConst := by unfold arcTubeConst; norm_num
  have h3 : (3 : ℝ) ^ s ≤ 3 := by
    calc (3 : ℝ) ^ s ≤ 3 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
      _ = 3 := Real.rpow_one _
  unfold winK0J
  calc
    _ ≤ 64 * (C * r ^ (-(10 * ε + 2 * s + u))) *
        ((r ^ (-ε)) ^ 2 * arcTubeConst) ^ 4 * (2 * (49 * r ^ (-ε))) ^ 2 *
        (2 * r ^ (-ε) * 3) ^ 2 / ((r ^ (ε + d)) ^ 2 * (r ^ (ε - s)) ^ 2) := by
          gcongr
    _ = (64 * C * arcTubeConst ^ (4 : ℕ) * 98 ^ (2 : ℕ) * 36) *
        ((r ^ (-ε)) ^ (12 : ℕ) * r ^ (-(10 * ε + 2 * s + u)) /
          ((r ^ (ε + d)) ^ (2 : ℕ) * (r ^ (ε - s)) ^ (2 : ℕ))) := by ring
    _ = _ := by
      congr 1
      repeat rw [← Real.rpow_mul_natCast hr.le]
      rw [← Real.rpow_add hr, ← Real.rpow_add hr, ← Real.rpow_sub hr]
      congr 1
      norm_num
      ring

/-- Power bookkeeping for the projection-cover exponent of the selected tube. -/
theorem winC2_le_power {r s ε d u Z C : ℝ}
    (hr : 0 < r) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hZ : Z ≤ C * r ^ (-(10 * ε + 2 * s + u))) :
    winC2 r s ε d Z ≤
      (96 * C * arcTubeConst ^ (3 : ℕ) * 98 ^ (2 : ℕ)) *
        r ^ (-(24 * ε + u + 3 * d)) := by
  have hAC : 0 < arcTubeConst := by unfold arcTubeConst; norm_num
  have h3 : (3 : ℝ) ^ s ≤ 3 := by
    calc (3 : ℝ) ^ s ≤ 3 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
      _ = 3 := Real.rpow_one _
  have h2 : (2 : ℝ) ^ s ≤ 2 := by
    calc (2 : ℝ) ^ s ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
      _ = 2 := Real.rpow_one _
  unfold winC2
  calc
    _ ≤ 8 * (C * r ^ (-(10 * ε + 2 * s + u))) *
        ((r ^ (-ε)) ^ 2 * arcTubeConst) ^ 3 * (2 * (49 * r ^ (-ε))) ^ 2 *
        (2 * r ^ (-ε) * 3) * (2 * r ^ (-(ε + d))) /
          ((r ^ (ε + d)) ^ 2 * (r ^ (ε - s)) ^ 2) := by gcongr
    _ = (96 * C * arcTubeConst ^ (3 : ℕ) * 98 ^ (2 : ℕ)) *
        ((r ^ (-ε)) ^ (9 : ℕ) * r ^ (-(10 * ε + 2 * s + u)) * r ^ (-(ε + d)) /
          ((r ^ (ε + d)) ^ (2 : ℕ) * (r ^ (ε - s)) ^ (2 : ℕ))) := by ring
    _ = _ := by
      congr 1
      repeat rw [← Real.rpow_mul_natCast hr.le]
      rw [← Real.rpow_add hr, ← Real.rpow_add hr, ← Real.rpow_add hr, ← Real.rpow_sub hr]
      congr 1
      norm_num
      ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
