import Submission.Obl.k4_general_parent_wide_layer_candidates.Lists.PoolFinal
import Submission.Obl.k4_general_parent_wide_layer_candidates.Lists.ScalarBounds

/-!
# Scalar readiness from native velocity lists

The general-parent analogue of accepted o248
(`k4_wide_velocity_lists_scalar_preparation`, files `AssemblyCore.lean` and
`Preparation.lean`): original native caps integrated over scalar residual cells give
the Scalar cap tests, and palette pooling over deep original labels, split by the
deep native-signal confinement, gives one terminal list on a dense submeasure.
-/

namespace Submission.Obl.k4_general_parent_wide_layer_candidates

open MeasureTheory Set Filter

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α]

/-- Exact density and a single smaller incoming loss turn a pooled law into
Scalar readiness, with all final budgets fixed before the losses are requested. -/
theorem scalarReadiness_of_pooling {p : Parent α} (h : p.Valid)
    {r v m : ℝ} (hexp : p.ListExponents r v m)
    (frames : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, Nonempty (p.ListFrame k r v m ε))
    (pooling : Pooling p r v m) : p.ScalarReadiness := by
  obtain ⟨hr, hv, _hvr, hm, hℓm, hU⟩ := hexp
  have hm0 : 0 < m := by linarith
  have hκ := h.rate_pos
  have hκ1 := h.rate_le_one
  have h3m : m ≤ 3 * m / p.κ := by
    rw [le_div_iff₀ hκ]
    nlinarith
  have hrU : r ≤ p.U := by linarith
  have hrvU : r + v ≤ p.U := by linarith
  have hrvm : r + v < m := by linarith
  have hdr : 0 ≤ p.d * r := mul_nonneg h.dimension_nonneg hr.le
  refine ⟨r, v, m, p.d * r + 1, p.S, m / 2, max 1 (m / 10), hr, hv,
    hrvU, hrvm, (by linarith), h.palette_pos, (by positivity), (by linarith),
    le_max_left _ _, ?_⟩
  obtain ⟨ε₀, hε₀, pooling⟩ := pooling
  intro η hη
  let ε := min (η / 8) ε₀
  have hε : 0 < ε := lt_min (by positivity) hε₀
  have hεη8 : ε ≤ η / 8 := min_le_left _ _
  have hεε₀ : ε ≤ ε₀ := min_le_right _ _
  have hεη : ε ≤ η := by linarith
  have hN1 : ∀ k, 1 ≤ p.N k := fun k => by linarith [h.scale k]
  have hcardCost := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit h.subpower.1 h.subpower.2 1
    (show 2 * ε < η by linarith) (show (0 : ℝ) ≤ 216 by norm_num)
  have hmassCost := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    h.scale_limit (show -η < -ε by linarith) (2 : ℝ)
  filter_upwards [frames ε hε, pooling ε hε hεε₀, h.eventually_scalar_bounds hr hv hm hℓm hrU hη,
    hcardCost, hmassCost] with k hf hp caps hcardCost hmassCost
  have hN : 0 < p.N k := by linarith [h.scale k]
  obtain ⟨f⟩ := hf
  obtain ⟨law, hle, hmass, terminal, hcard, hterminal⟩ := hp f
  apply f.ready_of_submeasure h hr hεη law hle ((caps ε f).mono hle) _ terminal _ hterminal
  · apply le_trans (ENNReal.ofReal_le_ofReal ?_) hmass
    linarith
  · have hcost : 216 * p.K k * p.N k ^ (2 * ε) ≤ p.N k ^ η := by
      simpa only [pow_one] using hcardCost.le
    exact hcard.trans (mul_le_mul_of_nonneg_right hcost (by positivity))

/-- **Scalar readiness from native velocity lists.** Velocity-wise residual
lists at fixed list exponents, together with the deep native-signal confinement,
give a complete Scalar input on a dense submeasure of every incoming frame. -/
theorem scalarReadiness_of_lists {α : Type} [MeasurableSpace α] (p : Parent α)
    (h : p.Valid) {r v m : ℝ} (hexp : p.ListExponents r v m)
    (frames : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, Nonempty (p.ListFrame k r v m ε))
    (hconf : p.DeepConfinement r v m) : p.ScalarReadiness :=
  scalarReadiness_of_pooling h hexp frames (h.pooling hexp hconf)

/-- Velocity lists at arbitrarily small exponents and deep native-signal
confinement at every admissible list exponent with enough room below `U` give
Scalar readiness. -/
theorem scalarReadiness_of_velocityLists {α : Type} [MeasurableSpace α] (p : Parent α)
    (h : p.Valid)
    (hconf : ∃ Λ : ℝ, 0 < Λ ∧ ∀ r v m, p.ListExponents r v m → Λ * m ≤ p.U →
      p.DeepConfinement r v m)
    (hl : p.VelocityLists) : p.ScalarReadiness := by
  obtain ⟨Λ, hΛ, hconf⟩ := hconf
  obtain ⟨r, v, m, hexp, hmU, frames⟩ := hl (p.U / Λ) (div_pos h.depth_pos hΛ)
  have hΛm : Λ * m ≤ p.U := by
    rw [le_div_iff₀ hΛ] at hmU
    linarith
  exact p.scalarReadiness_of_lists h hexp frames (hconf r v m hexp hΛm)

end Parent

end

end Submission.Obl.k4_general_parent_wide_layer_candidates
