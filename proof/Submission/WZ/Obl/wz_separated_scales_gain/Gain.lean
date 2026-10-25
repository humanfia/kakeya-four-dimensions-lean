-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_scales_gain.Gain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_scales_gain.Parameters
import Submission.WZ.Obl.wz_separated_scales_gain.FiniteProduct

namespace WangZahlLot.Obl.wz_separated_scales_gain

open MeasureTheory Set
open WangZahlLot.Obl.wz_nonflat_factored_improvement

/-- Combine the harmless positive power losses into a single exponent. -/
theorem loss_power_identity {δ : ℝ} (hδ : 0 < δ) (η ν t ζ₂ u e a H W : ℝ) :
    a * (δ ^ η) ^ 3 * (δ ^ ν) ^ 2 * (δ ^ t) ^ 4 * (δ ^ (-ζ₂))⁻¹ ^ 4 *
      δ ^ (u + e) * H * W =
    a * δ ^ (u + (e + 3 * η + 2 * ν + 4 * t + 4 * ζ₂)) * H * W := by
  have hpow : (δ ^ η) ^ 3 * (δ ^ ν) ^ 2 * (δ ^ t) ^ 4 * (δ ^ (-ζ₂))⁻¹ ^ 4 *
      δ ^ (u + e) = δ ^ (u + (e + 3 * η + 2 * ν + 4 * t + 4 * ζ₂)) := by
    apply Real.log_injOn_pos (by change (0 : ℝ) < _; positivity)
      (by change (0 : ℝ) < _; positivity)
    simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_inv, Real.log_pow]
    ring
  calc
    _ = a * ((δ ^ η) ^ 3 * (δ ^ ν) ^ 2 * (δ ^ t) ^ 4 * (δ ^ (-ζ₂))⁻¹ ^ 4 *
        δ ^ (u + e)) * H * W := by ring
    _ = _ := by rw [hpow]

/-- The separated middle scales provide a fixed improvement over the outer exponent. -/
theorem separated_gain {σ ω u ζ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 2)
    (hω : 0 < ω) (hgap : ω < u) (hD : EstimateD σ ω) (hE : EstimateE σ u)
    (hζ : 0 < ζ) : SeparatedGain σ u ζ := by
  let e := ζ * (u - ω) / 8
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨A, ηF, ηM, ηO, hA, hηF, hηM, hηO, H⟩ :=
    finite_three_scale_product hσ0.le hσ1 (hω.trans hgap).le hD hE he
  obtain ⟨ζ₀, η, ν, t, d, K, hζ₀, hη, hν, ht, hd, hd1, hK, hloss, HP⟩ :=
    choose_separated_parameters hζ he hηF hηM hηO
  let α := ζ * (u - ω) / 2
  have hα : 0 < α := by dsimp [α]; positivity
  refine ⟨α, hα, ζ₀, hζ₀, ?_⟩
  intro ζ₂ hζ₂ hζ₂0 ε hε
  have hK0 : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
  refine ⟨A / K ^ 5, by positivity, η, hη, d, hd, ?_⟩
  intro δ hδ hδd n x v Y hn hv hB hover hYm hYT _htotal hind hSB
  have hδ1 : δ ≤ 1 := hδd.trans hd1
  obtain ⟨τ, ρ, hτ, hρ, hsep, hbound⟩ := H δ (δ ^ η) (δ ^ ν) (δ ^ t) ζ ζ₂
    hδ hδ1 (Real.rpow_pos_of_pos hδ η) (Real.rpow_le_one hδ.le hδ1 hη.le)
    (Real.rpow_pos_of_pos hδ ν) (Real.rpow_pos_of_pos hδ t) (Real.rpow_le_one hδ.le hδ1 ht.le)
    hζ₂.le K hK (fun τ ρ hδτ hτρ hρ1 hsep => HP ζ₂ δ τ ρ hζ₂ hζ₂0 hδ hδd hδτ hτρ hρ1 hsep)
    n x v Y hn hv hB hover hYm hYT hind hSB
  rw [loss_power_identity hδ] at hbound
  apply (ENNReal.ofReal_le_ofReal ?_).trans hbound
  apply separated_target_le_product hδ hδ1 hτ hρ hsep (sub_nonneg.mpr hgap.le)
    (by positivity) (by positivity)
  dsimp [α, e] at *
  linarith

end WangZahlLot.Obl.wz_separated_scales_gain
