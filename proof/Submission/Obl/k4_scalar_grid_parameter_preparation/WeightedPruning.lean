/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/WeightedPruning.lean -/
import Submission.Obl.k4_quadratic_atlas_normalization.MassSelection

/-! Uniform world losses preserve the original weighted inverse-mass floor. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

theorem weighted_retained_mass_of_uniform_loss {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : ι → Measure Ω) (w : ι → ℝ≥0∞) (E : ι → Set Ω)
    (m ε : ℝ) (hm : 0 ≤ m) (hε : 0 ≤ ε) (hbudget : ε ≤ m / 2)
    (hw : (∑ i, w i) ≤ 1)
    (hmass : ENNReal.ofReal m ≤ ∑ i, w i * μ i Set.univ)
    (hloss : ∀ i, μ i (E i)ᶜ ≤ ENNReal.ofReal ε) :
    ENNReal.ofReal (m / 2) ≤ ∑ i, w i * μ i (E i) := by
  let loss : ℝ≥0∞ := ENNReal.ofReal ε
  have hdeleted : (∑ i, w i * μ i (E i)ᶜ) ≤ loss := by
    calc
      _ ≤ ∑ i, w i * loss := Finset.sum_le_sum fun i hi =>
        mul_le_mul le_rfl (hloss i) bot_le bot_le
      _ = (∑ i, w i) * loss := (Finset.sum_mul _ _ _).symm
      _ ≤ 1 * loss := mul_le_mul hw le_rfl bot_le bot_le
      _ = loss := one_mul _
  have hcover := Submission.Obl.k4_quadratic_atlas_normalization.weighted_mass_le_retained_add_deleted
    μ w (fun _ => Set.univ) E (fun i => (E i)ᶜ) (fun i => by
      rw [Set.union_compl_self])
  have htotal : ENNReal.ofReal m ≤ (∑ i, w i * μ i (E i)) + loss :=
    hmass.trans (hcover.trans (add_le_add le_rfl hdeleted))
  have hnum : ENNReal.ofReal (m / 2) + loss ≤ ENNReal.ofReal m := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  exact (ENNReal.add_le_add_iff_right (show loss ≠ ⊤ from ENNReal.ofReal_ne_top)).mp
    (hnum.trans htotal)

theorem weighted_retained_mass_lower {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : ι → Measure Ω) (w : ι → ℝ≥0∞) (E : ι → Set Ω)
    (K : ℝ) (hK : 0 < K) (hw : (∑ i, w i) ≤ 1)
    (hmass : ENNReal.ofReal (1 / K) ≤ ∑ i, w i * μ i Set.univ)
    (hloss : ∀ i, μ i (E i)ᶜ ≤ ENNReal.ofReal (3 / (100 * K))) :
    ENNReal.ofReal (1 / (2 * K)) ≤ ∑ i, w i * μ i (E i) := by
  have hbudget : 3 / (100 * K) ≤ (1 / K) / 2 := by
    rw [div_div]
    apply (div_le_div_iff₀ (by positivity : 0 < 100 * K) (by positivity : 0 < K * 2)).mpr
    nlinarith
  simpa only [div_div, mul_comm] using weighted_retained_mass_of_uniform_loss μ w E
    (1 / K) (3 / (100 * K)) (by positivity) (by positivity) hbudget hw hmass hloss

/-- Real world weights are passed through exactly as in the frozen mixture. -/
theorem original_weighted_retained_mass_lower {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : ι → Measure Ω) (ω : ι → ℝ) (E : ι → Set Ω)
    (K : ℝ) (hK : 0 < K) (hω : ∀ i, 0 ≤ ω i) (hsum : (∑ i, ω i) = 1)
    (hmass : ENNReal.ofReal K⁻¹ ≤ ∑ i, ENNReal.ofReal (ω i) * μ i Set.univ)
    (hloss : ∀ i, μ i (E i)ᶜ ≤ ENNReal.ofReal (3 / (100 * K))) :
    ENNReal.ofReal (1 / (2 * K)) ≤ ∑ i, ENNReal.ofReal (ω i) * μ i (E i) := by
  have hω' : (∑ i, ENNReal.ofReal (ω i)) ≤ 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi => hω i), hsum]
    norm_num
  exact weighted_retained_mass_lower μ (fun i => ENNReal.ofReal (ω i)) E K hK hω'
    (by simpa only [one_div] using hmass) hloss

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
