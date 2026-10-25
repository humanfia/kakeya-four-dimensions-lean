import Submission.Obl.k4_raw_critical_segment_forests.Forest
import Submission.Obl.k4_finite_width_output_exclusion.Interfaces
import Submission.Obl.k4_quadratic_atlas_normalization.ChartMonotonicity

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

def Forest.reslack {p : Data} {k : ℕ} (a : Forest p k) (κ : ℝ) : Forest p k :=
  {a with κ := κ}

/-- Polynomial complexity and the common slack can be enlarged throughout a
forest without changing its labels, its parents, or any assignment. -/
lemma Forest.Core.mono {p : Data} (hp : Valid p) {k M M' D D' m : ℕ}
    {r : ℕ → ℝ} {a : Forest p k} {κ : ℝ}
    (ha : a.Core M D m r) (hM : M ≤ M') (hD : D ≤ D') (hκ : a.κ ≤ κ) :
    (a.reslack κ).Core M' D' m r := by
  obtain ⟨hκ1, hKκ, hC, hmass, hsep, hchart⟩ := ha
  have hκpos : 0 < a.κ := by linarith
  have hNpos : 0 < p.N k := hp.scale_pos k
  have hκκ : ENNReal.ofReal (κ⁻¹) ≤ ENNReal.ofReal (a.κ⁻¹) :=
    ENNReal.ofReal_le_ofReal (inv_anti₀ hκpos hκ)
  refine ⟨hκ1.trans hκ, hKκ.trans hκ,
    hC.trans (pow_le_pow_right₀ (hp.scale_ge_one k) hM),
    fun i hi => hκκ.trans (hmass i hi), hsep, ?_⟩
  intro b
  obtain ⟨hlev, hj, hc, hpar⟩ := hchart b
  refine ⟨hlev, hj, ?_, hpar⟩
  apply k4_quadratic_atlas_normalization.chart_mono
    (hp.scale_ge_one k) hM hD hκpos hκ (hp.B_pos k (a.γ b)).le hc
  intro hfloor
  apply le_trans ?_ hfloor
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_left (by positivity)
    (mul_pos (by positivity) hκpos)
    (mul_le_mul_of_nonneg_left hκ (by positivity))

end
end Submission.Obl.k4_raw_critical_segment_forests
