/- Inlined from LOT tree g-oai-074, obligation o250, session x0879,
commit 525ce8d3c8ed1d02854b5f6c797e220d2ac13ddd, file Submission/Obl/k4_horizontal_wide_interval_return/Core/IndexFacts.lean.
Namespace/imports renamed; the referenced goodSet definition is included. -/
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core.LayerCaps

/-!
# Facts at one index of a valid model

Measurability, finiteness, the horizontal relation `|b₄ + b₀| ≤ N^-e₀` and the good set
(unit time, horizontal relation, bounded hidden value) hold eventually for a valid model.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core

open MeasureTheory Set Filter

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- The original unit-time good set. -/
def goodSet (b : α → Fin 6 → ℝ) (ζ₀ Kb : ℝ) : Set (α × ℝ) :=
  {p | p.2 ∈ Icc (0 : ℝ) 1 ∧ |b p.1 4 + b p.1 0| ≤ ζ₀ ∧ |hidden b p| ≤ Kb}

theorem index_facts (cfg : Data α) (hv : cfg.Valid) :
    ∀ᶠ k in atTop, Measurable (cfg.b k) ∧ cfg.ρ k ≤ cfg.μ k ∧ IsFiniteMeasure (cfg.μ k) ∧
      IsFiniteMeasure (cfg.π k) ∧
      (∀ᵐ p ∂cfg.μ k, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀)) ∧
      cfg.μ k (goodSet (cfg.b k) (cfg.N k ^ (-cfg.e₀)) (cfg.K k))ᶜ = 0 := by
  have hU := hv.range_pos
  set R : ℝ := 2 + 1 / cfg.U with hR
  have hR1 : 1 < R := by rw [hR]; have : 0 < 1 / cfg.U := by positivity
                         linarith
  have hRU : R⁻¹ ≤ cfg.U := by
    rw [hR, inv_le_comm₀ (by positivity) hU]
    have : 1 / cfg.U ≤ 2 + 1 / cfg.U := by linarith
    simpa [one_div] using this
  filter_upwards [hv.prepared R hR1] with k hk
  obtain ⟨hb, hν, hπ, hμle, hρμ, hsupp, hρmass, -, -, hX⟩ := hv.basic k
  have hprep := hk cfg.U hRU le_rfl
  obtain ⟨-, -, -, -, hlab, hcover, -⟩ := hprep
  -- finiteness
  have hμfin : IsFiniteMeasure (cfg.μ k) := by
    constructor
    have h1 : cfg.μ k univ ≤ cfg.μ k (univ ×ˢ Icc (0 : ℝ) 1) +
        cfg.μ k (univ ×ˢ Icc (0 : ℝ) 1)ᶜ := by
      rw [← measure_union disjoint_compl_right ((MeasurableSet.univ.prod measurableSet_Icc).compl),
        union_compl_self]
    rw [hsupp, add_zero] at h1
    refine h1.trans_lt (lt_of_le_of_lt (hμle _) ?_)
    rw [Measure.smul_apply, Measure.prod_prod, Real.volume_Icc, measure_univ]
    simp
  -- a label exists, giving the horizontal relation
  have hne : 0 < cfg.n k cfg.U := by
    by_contra h0
    push_neg at h0
    have hn : cfg.n k cfg.U = 0 := by omega
    have hzero : cfg.μ k univ = 0 := by
      have hF : ∀ᵐ p ∂cfg.μ k, False := hcover.mono fun p hp => by
        obtain ⟨i, -⟩ := hp
        have := i.2
        omega
      have : cfg.μ k = 0 := ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp hF)
      rw [this, Measure.coe_zero, Pi.zero_apply]
    have hK : 0 < cfg.K k := by linarith [hv.loss_lower k]
    have : ENNReal.ofReal (cfg.K k)⁻¹ ≤ 0 := hρmass.trans ((hρμ univ).trans hzero.le)
    have hpos : 0 < ENNReal.ofReal (cfg.K k)⁻¹ := ENNReal.ofReal_pos.mpr (inv_pos.mpr hK)
    exact absurd this (not_le.mpr hpos)
  obtain ⟨-, -, -, -, -, -, -, -, hhor⟩ := hlab ⟨0, hne⟩
  obtain ⟨hP, hhor, -⟩ := hhor rfl
  refine ⟨hb, hρμ, hμfin, inferInstance, hhor, ?_⟩
  -- the good set
  have hsupp' : ∀ᵐ p ∂cfg.μ k, p.2 ∈ Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    refine measure_mono_null (fun p hp => ?_) hsupp
    simp only [mem_compl_iff, mem_prod, mem_univ, true_and]
    exact hp
  have hae : ∀ᵐ p ∂cfg.μ k, p ∈ goodSet (cfg.b k) (cfg.N k ^ (-cfg.e₀)) (cfg.K k) := by
    filter_upwards [hsupp', hhor, hX] with p hp1 hp2 hp3
    refine ⟨hp1, hp2, ?_⟩
    have := (hp3.1 p.2 hp1).1
    rw [hP] at this
    simpa [Data.x, hidden] using this
  exact ae_iff.mp hae

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core
