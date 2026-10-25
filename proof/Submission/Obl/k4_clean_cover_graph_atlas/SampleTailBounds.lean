import Submission.Obl.k4_clean_cover_graph_atlas.SampleScales

namespace Submission.Obl.k4_clean_cover_graph_atlas

/-- A cubic overlap budget accommodates the integer rounding in the number
of observation domains. -/
theorem cube_list_budget {N κ σ β C : ℝ} (hN : 1 ≤ N) (hκ : 0 ≤ κ) (hκN : κ ≤ N ^ σ)
    (hC : 0 ≤ C) (hσβ : σ ≤ β / 4) (hβ : 0 < β)
    (hNK : (C + 1) ^ (1 / (β / 4)) ≤ N) : C * κ ^ 3 ≤ N ^ β := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hκ3 : κ ^ 3 ≤ N ^ (3 * σ) := by
    calc
      _ ≤ (N ^ σ) ^ (3 : ℕ) := by gcongr
      _ = _ := by rw [← Real.rpow_mul_natCast hNpos.le]; congr 1; ring
  have habs := rpow_absorb hN (by linarith : 1 ≤ C + 1) (by positivity : 0 < β / 4)
    hNK (show 3 * σ + β / 4 ≤ β by linarith)
  exact (mul_le_mul (by linarith : C ≤ C + 1) hκ3 (by positivity) (by linarith)).trans habs

/-- The sum of the comparison jet widths is bounded by a fixed constant,
uniformly over late samples and all smaller matching slacks. -/
theorem sample_jet_budget {ι : Type*} [Fintype ι] (upper : ι → ℝ)
    {Rg M εg lower : ℝ} (hupper : ∀ a, 0 ≤ upper a)
    (hR : 1 ≤ Rg) (hM : 0 ≤ M) (hM1 : M ≤ 1) (hε : 0 ≤ εg) (hlower : 0 < lower) :
    0 ≤ (∑ a, upper a * (M * Rg ^ (-εg))) / lower ∧
      (∑ a, upper a * (M * Rg ^ (-εg))) / lower ≤ (∑ a, upper a) / lower := by
  have htail : Rg ^ (-εg) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hR (by linarith)
  have htail0 : 0 ≤ Rg ^ (-εg) := Real.rpow_nonneg (zero_le_one.trans hR) _
  have hscale : M * Rg ^ (-εg) ≤ 1 :=
    (mul_le_mul hM1 htail htail0 zero_le_one).trans_eq (mul_one 1)
  refine ⟨div_nonneg (Finset.sum_nonneg fun a _ => mul_nonneg (hupper a) (mul_nonneg hM htail0)) hlower.le,
    div_le_div_of_nonneg_right ?_ hlower.le⟩
  calc
    _ = (∑ a, upper a) * (M * Rg ^ (-εg)) := (Finset.sum_mul ..).symm
    _ ≤ (∑ a, upper a) * 1 := mul_le_mul_of_nonneg_left hscale (Finset.sum_nonneg fun a _ => hupper a)
    _ = _ := mul_one _

/-- The exponent of the total original cap fits the pair-error budget. -/
theorem sample_pair_exponent_le {Cs : ℕ} {Cd Crem ρ gain L ε σ τ δ₀ εG : ℝ}
    (hCd : 0 ≤ Cd) (hCrem : 0 ≤ Crem) (hρ : 0 ≤ ρ) (hgain : 0 ≤ gain) (hL : 0 ≤ L)
    (hε : 0 ≤ ε) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (hδρ : δ₀ ≤ ρ * gain)
    (hεG : 0 ≤ εG)
    (hbud : expMult Cs Cd Crem * slackTot ρ gain L ε σ τ ≤ εG * gain * L / 8) :
    ((12 * ρ * gain + 5 * δ₀) * L + 12 * ε + τ) + 6 * σ ≤ εG * gain * L / 4 := by
  have hS : 0 ≤ slackTot ρ gain L ε σ τ := by unfold slackTot; positivity
  have hsmall := slack_small hCd hCrem hS hbud
  have hbound : ((12 * ρ * gain + 5 * δ₀) * L + 12 * ε + τ) + 6 * σ ≤
      17 * slackTot ρ gain L ε σ τ := by
    unfold slackTot
    nlinarith [mul_le_mul_of_nonneg_right hδρ hL, mul_nonneg (mul_nonneg hρ hgain) hL]
  nlinarith [mul_nonneg (mul_nonneg hεG hgain) hL]

end Submission.Obl.k4_clean_cover_graph_atlas
