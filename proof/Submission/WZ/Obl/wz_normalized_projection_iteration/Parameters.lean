-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_iteration.Parameters.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_iteration.Grid

namespace WangZahlLot.Obl.wz_normalized_projection_iteration

/-- Polynomial packing makes the occupancy regularization loss a small power of the scale. -/
theorem packing_negative_power {δ P τ : ℝ} (hδ : 0 < δ) (hP : 0 < P) (hτ : 0 < τ)
    {n : ℕ} (hn : 0 < n) (hpack : (n : ℝ) * δ ^ 6 ≤ P) :
    P ^ (-τ) * δ ^ (6 * τ) ≤ (n : ℝ) ^ (-τ) := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnle : (n : ℝ) ≤ P / δ ^ 6 := (le_div_iff₀ (by positivity)).mpr hpack
  have hh := Real.rpow_le_rpow_of_nonpos hnr hnle (by linarith : -τ ≤ 0)
  convert hh using 1
  rw [Real.div_rpow hP.le (by positivity : 0 ≤ δ ^ 6), div_eq_mul_inv,
    ← Real.rpow_neg (by positivity : 0 ≤ δ ^ 6), neg_neg,
    ← Real.rpow_natCast_mul hδ.le]
  norm_num

/-- Choose all small-scale cutoffs before the family and the intermediate radius. -/
theorem coarse_parameters {P a β : ℝ} (hP : 0 < P) (ha : 0 < a) (hβ : 0 < β) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ d0 : ℝ, 0 < d0 ∧
    ∀ δ r : ℝ, 0 < δ → δ ≤ d0 → δ ≤ r → r ≤ δ ^ a →
    ∀ n : ℕ, 0 < n → (n : ℝ) * δ ^ 6 ≤ P →
      r ≤ (1 / 100000 : ℝ) ∧
      147456 * r ^ β ≤ δ ^ (8 * κ) ∧
      768 * (4800 : ℝ) ^ 3 * δ ^ (-κ) ≤ δ ^ (8 * κ) * r ^ (-β) ∧
      (linePalette : ℝ) * δ ^ (8 * κ) ≤
        δ ^ κ * ((1 - (2 : ℝ) ^ (-κ)) / 2) * (n : ℝ) ^ (-κ) := by
  let κ := a * β / 20
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hgapD : 0 < a * β - 8 * κ := by dsimp [κ]; nlinarith [mul_pos ha hβ]
  have hgapF : 0 < a * β - 9 * κ := by dsimp [κ]; nlinarith [mul_pos ha hβ]
  let c : ℝ := (1 - (2 : ℝ) ^ (-κ)) / 2
  have hc : 0 < c := by
    have hh := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
      (by linarith : -κ < 0)
    dsimp [c]
    linarith
  have hK : (0 : ℝ) < linePalette := by norm_num [linePalette]
  obtain ⟨dR, hdR, hR⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
    ha (by norm_num : (0 : ℝ) < 1 / 100000)
  obtain ⟨dD, hdD, hD⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
    hgapD (by norm_num : (0 : ℝ) < 1 / 147456)
  obtain ⟨dF, hdF, hF⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
    hgapF (by norm_num : (0 : ℝ) < 1 / (768 * 4800 ^ 3))
  obtain ⟨dM, hdM, hM⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
    hκ (by positivity : 0 < c * P ^ (-κ) / (linePalette : ℝ))
  refine ⟨κ, hκ, min dR (min dD (min dF dM)),
    lt_min hdR (lt_min hdD (lt_min hdF hdM)), ?_⟩
  intro δ r hδ hd hδr hra n hn hpack
  have hr : 0 < r := hδ.trans_le hδr
  have hdR' := hd.trans (min_le_left _ _)
  have hdD' := hd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdF' := hd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hdM' := hd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hpowD := hD δ hδ hdD'
  have hpowF := hF δ hδ hdF'
  have hpowM := (le_div_iff₀ hK).mp (hM δ hδ hdM')
  have hrpow : r ^ β ≤ δ ^ (a * β) := by
    rw [Real.rpow_mul hδ.le]
    exact Real.rpow_le_rpow hr.le hra hβ.le
  refine ⟨hra.trans (hR δ hδ hdR'), ?_, ?_, ?_⟩
  · calc
      147456 * r ^ β ≤ 147456 * δ ^ (a * β) := by gcongr
      _ = (147456 * δ ^ (a * β - 8 * κ)) * δ ^ (8 * κ) := by
        rw [mul_assoc, ← Real.rpow_add hδ]
        congr 2
        ring
      _ ≤ 1 * δ ^ (8 * κ) := by gcongr; linarith
      _ = _ := one_mul _
  · apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hr β)).mp
    calc
      (768 * 4800 ^ 3 * δ ^ (-κ)) * r ^ β ≤
          (768 * 4800 ^ 3 * δ ^ (-κ)) * δ ^ (a * β) := by gcongr
      _ = (768 * 4800 ^ 3 * δ ^ (a * β - 9 * κ)) * δ ^ (8 * κ) := by
        simp only [mul_assoc]
        rw [← Real.rpow_add hδ, ← Real.rpow_add hδ,
          show -κ + a * β = a * β - 9 * κ + 8 * κ by ring]
      _ ≤ 1 * δ ^ (8 * κ) := by gcongr; linarith
      _ = (δ ^ (8 * κ) * r ^ (-β)) * r ^ β := by
        rw [mul_assoc, ← Real.rpow_add hr, neg_add_cancel, Real.rpow_zero]
        ring
  · have hnneg := packing_negative_power hδ hP hκ hn hpack
    calc
      (linePalette : ℝ) * δ ^ (8 * κ) =
          (δ ^ κ * (linePalette : ℝ)) * δ ^ (7 * κ) := by
        rw [show 8 * κ = κ + 7 * κ by ring, Real.rpow_add hδ]
        ring
      _ ≤ (c * P ^ (-κ)) * δ ^ (7 * κ) := by gcongr
      _ = δ ^ κ * c * (P ^ (-κ) * δ ^ (6 * κ)) := by
        rw [mul_assoc, ← show κ + 6 * κ = 7 * κ by ring, Real.rpow_add hδ]
        ring
      _ ≤ δ ^ κ * c * (n : ℝ) ^ (-κ) :=
        mul_le_mul_of_nonneg_left hnneg (by positivity)

end WangZahlLot.Obl.wz_normalized_projection_iteration
