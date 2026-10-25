-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.SecondFillingParameters.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/SecondFillingParameters.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 commit be976b9, SecondFillingParameters.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_move_two_long_grains_gain.Core
import Submission.WZ.Obl.wz_horizontal_tube_exclusion.Vertical

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

/-- Any strict exponent reserve pays the second Córdoba filling uniformly
over the old tube radius and the growing packet angle. -/
theorem second_filling_parameters {β t s u ε L C : ℝ}
    (hβ : 0 < β) (hs : 0 < s) (hst : s ≤ t)
    (hgap : 3 * u + s < ε) (hL : 0 < L) (hC : 0 < C) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧ ∀ δ d θ : ℝ,
      0 < δ → δ ≤ d₀ → δ ≤ d → δ ^ (-t) * d ≤ θ → θ ≤ 1 →
      d ≤ θ * δ ^ s ∧ θ * δ ^ s ≤ 1 ∧
      8 * ((θ * δ ^ s) / θ) ^ β < 1 ∧
      (1000000000 * L * d ^ 5 * (1 + Real.log (1 / d))) *
          (δ ^ ε * (C * d * θ)) ≤
        (δ ^ u * d ^ 2) ^ 3 * (θ * δ ^ s) := by
  obtain ⟨d₁, hd₁, Hangle⟩ := WangZahlLot.Obl.wz_move_two_long_grains_gain.small_rpow
    (mul_pos hs hβ) (K := 1 / 16) (by norm_num)
  obtain ⟨d₂, hd₂, Hlog⟩ :=
    WangZahlLot.Obl.wz_horizontal_tube_exclusion.exists_log_power_comparison
      (1000000000 * L * C) (B := 1) (by norm_num) hgap
  refine ⟨min d₁ (min d₂ (1 / 100)), by positivity,
    (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro δ d θ hδ hδ0 hδd hgrow hθ1
  have hd : 0 < d := hδ.trans_le hδd
  have hθ : 0 < θ := (mul_pos (Real.rpow_pos_of_pos hδ _) hd).trans_le hgrow
  have hδ1 : δ ≤ 1 :=
    (hδ0.trans ((min_le_right _ _).trans (min_le_right _ _))).trans (by norm_num)
  have hδsp : 0 < δ ^ s := Real.rpow_pos_of_pos hδ _
  have hδs1 : δ ^ s ≤ 1 := Real.rpow_le_one hδ.le hδ1 hs.le
  have hlow : d ≤ θ * δ ^ s := by
    have hp : 1 ≤ δ ^ (s - t) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
    calc
      d ≤ δ ^ (s - t) * d := by nlinarith
      _ = δ ^ s * (δ ^ (-t) * d) := by
        rw [← mul_assoc, ← Real.rpow_add hδ]
        congr 2
      _ ≤ δ ^ s * θ := mul_le_mul_of_nonneg_left hgrow hδsp.le
      _ = _ := mul_comm _ _
  refine ⟨hlow, ?_, ?_, ?_⟩
  · calc
      _ ≤ (1 : ℝ) * 1 := mul_le_mul hθ1 hδs1 hδsp.le zero_le_one
      _ = _ := one_mul _
  · have he : ((θ * δ ^ s) / θ) ^ β = δ ^ (s * β) := by
      rw [mul_div_cancel_left₀ _ hθ.ne', ← Real.rpow_mul hδ.le]
    rw [he]
    have hh := Hangle δ hδ (hδ0.trans (min_le_left _ _))
    linarith
  · have hlog : Real.log (1 / d) ≤ Real.log (1 / δ) :=
      Real.log_le_log (by positivity) (one_div_le_one_div_of_le hδ hδd)
    have hh : (1000000000 * L * C) * (1 + Real.log (1 / δ)) * δ ^ ε ≤
        δ ^ (3 * u + s) := by
      simpa only [one_mul] using Hlog δ hδ
        (hδ0.trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hpow : (δ ^ u) ^ 3 * δ ^ s = δ ^ (3 * u + s) := by
      rw [← Real.rpow_natCast (δ ^ u) 3, ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
      congr 1
      norm_num
      ring
    calc
      _ = ((1000000000 * L * C) * (1 + Real.log (1 / d)) * δ ^ ε) *
          (d ^ 6 * θ) := by ring
      _ ≤ ((1000000000 * L * C) * (1 + Real.log (1 / δ)) * δ ^ ε) *
          (d ^ 6 * θ) := by gcongr
      _ ≤ δ ^ (3 * u + s) * (d ^ 6 * θ) :=
        mul_le_mul_of_nonneg_right hh (by positivity)
      _ = _ := by rw [← hpow]; ring

/-- A small power loss in the containing prism's short width is paid by
the same amount of density exponent reserve. -/
theorem second_filling_width_parameters {β t s u ε vLoss L C : ℝ}
    (hβ : 0 < β) (hs : 0 < s) (hst : s ≤ t)
    (hgap : 3 * u + s + vLoss < ε) (hL : 0 < L) (hC : 0 < C) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧ ∀ δ d θ : ℝ,
      0 < δ → δ ≤ d₀ → δ ≤ d → δ ^ (-t) * d ≤ θ → θ ≤ 1 →
      d ≤ θ * δ ^ s ∧ θ * δ ^ s ≤ 1 ∧
      8 * ((θ * δ ^ s) / θ) ^ β < 1 ∧
      (1000000000 * L * d ^ 5 * (1 + Real.log (1 / d))) *
          (δ ^ ε * (C * δ ^ (-vLoss) * d * θ)) ≤
        (δ ^ u * d ^ 2) ^ 3 * (θ * δ ^ s) := by
  obtain ⟨d₀, hd₀, hd₀1, H⟩ := second_filling_parameters (u := u) (ε := ε - vLoss)
    hβ hs hst (by linarith) hL hC
  refine ⟨d₀, hd₀, hd₀1, ?_⟩
  intro δ d θ hδ hδ0 hδd hgrow hθ1
  obtain ⟨hr, hr1, hang, hnum⟩ := H δ d θ hδ hδ0 hδd hgrow hθ1
  refine ⟨hr, hr1, hang, ?_⟩
  have hp : δ ^ (ε - vLoss) = δ ^ ε * δ ^ (-vLoss) := by
    rw [← Real.rpow_add hδ]
    congr 1
  rw [hp] at hnum
  convert hnum using 1 <;> ring

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
