-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_estimate_equivalence.Starting.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_estimate_equivalence.Packing
import Submission.WZ.Obl.wz_estimate_equivalence.Elementary
import Submission.WZ.Obl.wz_estimate_equivalence.Coefficients

namespace WangZahlLot.Obl.wz_estimate_equivalence

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- A uniform starting estimate from parameter packing and the average shading density. -/
theorem e_seven {σ : ℝ} (hσ : 0 ≤ σ) (hσmax : σ ≤ 2 / 3) : E σ 7 := by
  intro ε hε
  let C : ℝ := 160 ^ 6
  have hC : 0 < C := by norm_num [C]
  refine ⟨C⁻¹, inv_pos.mpr hC, ε, hε, ?_⟩
  intro δ hδ hδmax m l hm hl n x v Y hn hv hT hsep hY hYT hdens hK hF
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hδ1 : δ ≤ 1 := le_trans hδmax (by norm_num)
  have hpack : (n : ℝ) * δ ^ 6 ≤ C := tube_card_bound hδ hδmax hv hT hsep
  have hB : δ ≤ (n : ℝ) * δ := by nlinarith
  have hpow : ((n : ℝ) * δ) ^ (-σ) ≤ δ ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos hδ hB (neg_nonpos.mpr hσ)
  have hscale : δ ^ ((7 : ℝ) + ε) * δ ^ (-σ) ≤ δ ^ (6 + ε) := by
    rw [← Real.rpow_add hδ]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hexp : δ ^ (6 + ε) = δ ^ 6 * δ ^ ε := by
    rw [Real.rpow_add hδ]
    norm_num
  have hcoef : C⁻¹ * δ ^ ((7 : ℝ) + ε) * ((n : ℝ) * δ ^ 2) *
      ((n : ℝ) * δ) ^ (-σ) ≤ δ ^ ε * δ ^ 2 := by
    calc
      C⁻¹ * δ ^ ((7 : ℝ) + ε) * ((n : ℝ) * δ ^ 2) *
          ((n : ℝ) * δ) ^ (-σ) ≤
          C⁻¹ * δ ^ ((7 : ℝ) + ε) * ((n : ℝ) * δ ^ 2) * δ ^ (-σ) := by gcongr
      _ = C⁻¹ * (δ ^ ((7 : ℝ) + ε) * δ ^ (-σ)) * ((n : ℝ) * δ ^ 2) := by ring
      _ ≤ C⁻¹ * δ ^ (6 + ε) * ((n : ℝ) * δ ^ 2) := by gcongr
      _ = (δ ^ ε * δ ^ 2) * (C⁻¹ * ((n : ℝ) * δ ^ 6)) := by rw [hexp]; ring
      _ ≤ (δ ^ ε * δ ^ 2) * (C⁻¹ * C) := by gcongr
      _ = δ ^ ε * δ ^ 2 := by rw [inv_mul_cancel₀ hC.ne', mul_one]
  have hdens' : ENNReal.ofReal ((δ ^ ε * δ ^ 2) * (n : ℝ)) ≤
      Finset.sum Finset.univ (fun i : Fin n => volume (Y i)) := by
    convert hdens using 1
    congr 1
    ring
  have hU := average_density_le_union hn Y (by positivity) hdens'
  refine (ENNReal.ofReal_le_ofReal ?_).trans hU
  exact (general_coefficient_le hσ hσmax (inv_nonneg.mpr hC.le)
    (Real.rpow_nonneg hδ.le _) (by positivity) (by positivity) hm hl).trans hcoef

/-- The starting exponent is independent of the input estimate. -/
theorem e_starting {σ : ℝ} (hσ : 0 ≤ σ) (hσmax : σ ≤ 1 / 2) :
    ∃ ω₀ : ℝ, E σ ω₀ := ⟨7, e_seven hσ (by linarith)⟩

end WangZahlLot.Obl.wz_estimate_equivalence
