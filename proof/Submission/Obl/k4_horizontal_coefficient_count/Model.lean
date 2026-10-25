import Submission.Obl.k4_critical_switching_state_preparation.PreparedModel
import Submission.Obl.k4_horizontal_coefficient_count.Sequence
import Submission.Obl.k4_horizontal_coefficient_count.Bounded

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set Filter

/-- The accepted critical-preparation data type stores the same four
horizontal hypotheses; the rate condition belongs to the validity record. -/
abbrev InputData (α : Type) [MeasurableSpace α] :=
  Submission.Obl.k4_critical_switching_state_preparation.Data α

structure Subcritical {α : Type} [MeasurableSpace α] (cfg : InputData α) : Prop where
  scale : ∀ k, 2 ≤ cfg.N k
  scale_limit : Tendsto cfg.N atTop atTop
  subpower : (∀ k, 1 ≤ cfg.K k) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, cfg.K k ≤ cfg.N k ^ ε
  dimension_nonneg : 0 ≤ cfg.d
  dimension_lt_one : cfg.d < 1
  rate_pos : 0 < cfg.κ
  rate_le_one : cfg.κ ≤ 1
  transverse_pos : 0 < cfg.ℓ
  palette_pos : 0 < cfg.S
  palette_le_one : cfg.S ≤ 1
  depth_pos : 0 < cfg.U
  defect_pos : 0 < cfg.e₀
  subcritical_rate : 2 * cfg.κ < 1
  horizontal_rate : cfg.ℓ = cfg.κ
  basic : cfg.Basic
  caps : cfg.Caps
  atlas : cfg.Atlas
  nested : cfg.Nested

namespace Subcritical

variable {α : Type} [MeasurableSpace α] {cfg : InputData α} (h : Subcritical cfg)

include h

theorem residual_mass_le (k : ℕ) : cfg.ρ k univ ≤ ENNReal.ofReal (cfg.K k) := by
  letI : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  exact ((h.basic k).2.2.2.2.1 univ).trans
    (current_total_mass_le (cfg.ν k) (cfg.μ k)
      (h.basic k).2.2.2.1 (h.basic k).2.2.2.2.2.1)

theorem residual_time (k : ℕ) : cfg.ρ k (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 :=
  le_antisymm (((h.basic k).2.2.2.2.1 _).trans_eq (h.basic k).2.2.2.2.2.1) bot_le

theorem residual_floor (k : ℕ) : ENNReal.ofReal ((cfg.K k)⁻¹) ≤ cfg.ρ k univ :=
  (h.basic k).2.2.2.2.2.2.1

end Subcritical

/-- The only remaining analytic input: one heavy coefficient cover at
each depth in the fixed reconstruction buffer. -/
def RawEngine : Prop :=
  ∀ (α : Type) [MeasurableSpace α] (cfg : InputData α), Subcritical cfg →
    ∀ s : ℝ, 0 < s → 2 * s < cfg.U → 100 * s < cfg.e₀ →
      ∀ ε : ℝ, 0 < ε → HeavyCoverAt cfg.N cfg.d cfg.e₀ 1 2 s ε cfg.ρ cfg.π cfg.b

end Submission.Obl.k4_horizontal_coefficient_count
