-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.LocalAlternative.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.LocalCover
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.ImprovementTransfer

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (exists_rotation)

attribute [local irreducible] normalize

set_option maxHeartbeats 800000 in
lemma local_alternative {σ ω : ℝ} (hσ : 0 ≤ σ) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hP : OneScaleAlternative σ ω) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ α κ : ℝ, 0 < α ∧ 0 < κ ∧ ∃ η₀ c : ℝ, 0 < η₀ ∧ 0 < c ∧ c ≤ 1 ∧
      ∀ η r s : ℝ, 0 < η → η ≤ η₀ → 0 < s → s ≤ c * r → r ≤ 1 →
      ∀ y w : Space, ‖w‖ = 1 →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space), Fibre r s η y w x v Y →
      ENNReal.ofReal (κ * (s / r) ^ (ω - α) * (n * s ^ 2) * (n * (s / r)) ^ (-σ)) ≤ volume (⋃ i, Y i) ∨
        FibreCover r s ζ coverScale ω y w x v Y := by
  let τ := ζ / 100
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨α₀, hα₀, κ₀, hκ₀, ηP, hηP, HP⟩ := hP τ hτ
  let θ := min ηP (min 1 (min (α₀ / 4) τ))
  have hθ : 0 < θ := lt_min hηP (lt_min zero_lt_one (lt_min (by positivity) hτ))
  have hθηP : θ ≤ ηP := min_le_left _ _
  have hθ1 : θ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hθα : θ ≤ α₀ / 2 := by
    have hh : θ ≤ α₀ / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hθτ : θ ≤ τ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨ηN, cN, hηN, hcN, hcN1, HN⟩ := normalize_with_power_loss hθ
  obtain ⟨q, cP, hq, hτq, hcP, hcP100, HC⟩ := cover_parameters hζ hω
  let η₀ := min ηN τ
  let c := min cN cP
  have hη₀ : 0 < η₀ := lt_min hηN hτ
  have hc : 0 < c := lt_min hcN hcP
  have hc1 : c ≤ 1 := (min_le_left _ _).trans hcN1
  refine ⟨α₀ / 2, improvementConstant κ₀ ω α₀ σ, by positivity,
    improvementConstant_pos hκ₀, η₀, c, hη₀, hc, hc1, ?_⟩
  intro η r s hη hη0 hs hsr hr1 y w hw n x v Y hF
  have hr : 0 < r := (mul_pos_iff_of_pos_left hc).mp (hs.trans_le hsr)
  have hsrN : s ≤ cN * r := hsr.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hr.le)
  have hηN' : η ≤ ηN := hη0.trans (min_le_left _ _)
  have hητ : η ≤ τ := hη0.trans (min_le_right _ _)
  obtain ⟨e, hew⟩ := exists_rotation hw
  obtain ⟨hr', M, j, z, u, hj, hA, hforward, hmid, hcard, hselected⟩ :=
    HN η r s hη hηN' hs hsrN hr1 y w e hw hew n x v Y hF
  have hsr' : s ≤ r := hsr.trans (mul_le_of_le_one_left hr.le hc1)
  have hs100 : s ≤ 1 / 100 := calc
    s ≤ c * r := hsr
    _ ≤ c := by nlinarith only [mul_le_mul_of_nonneg_left hr1 hc.le]
    _ ≤ cP := min_le_right _ _
    _ ≤ 1 / 100 := hcP100
  have hδ : 0 < s / r := div_pos hs hr
  have hδcP : s / r ≤ cP := ((div_le_iff₀ hr).mpr hsr).trans (min_le_right _ _)
  obtain ⟨hsmall, hqsmall, hrsmall, hmasssmall, herrorsmall⟩ := HC (s / r) hδ hδcP
  have hd : 0 < normalizedRadius r s := normalizedRadius_pos hr hs
  have hd100 : normalizedRadius r s ≤ 1 / 100 := (normalizedRadius_le hr hsr').trans (by norm_num)
  have hd1 : normalizedRadius r s ≤ 1 := hd100.trans (by norm_num)
  have hcount : (normalizedRadius r s) ^ (-θ) ≤ (normalizedRadius r s) ^ (-ηP) :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hθηP)
  have hAP := admissible_mono hd hd1 hθηP hcount hcount hA
  rcases HP (normalizedRadius r s) hd hd100 M z u
    (fun i => normalize e y w r hr '' Y (j i)) hAP with hQ | hG
  · exact Or.inl (local_improvement_of_normalized hσ hθα hκ₀ hr hs hsr' e y w
      hF.1 hA.1 j hj Y hcard hQ)
  · right
    apply local_cover_of_normalized hζ hω hω1 hθ1 hθτ hη hητ hr hr1 hs hsr' hs100 hq hτq
      (by simpa only [radius_eq_ratio] using hsmall)
      (by simpa only [radius_eq_ratio] using hqsmall)
      (by simpa only [radius_eq_ratio] using hrsmall)
      (by simpa only [radius_eq_ratio] using hmasssmall)
      (by simpa only [radius_eq_ratio] using herrorsmall)
      hw e hew x v Y hF j hj z u hA hforward hmid hselected hG

end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
