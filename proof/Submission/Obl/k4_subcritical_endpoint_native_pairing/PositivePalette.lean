import Submission.Obl.k4_two_velocity_row_list_completion.MeasureTable

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing

open MeasureTheory

/-- Original joint cell caps ensure that every occupied palette bin has a
positive original weight, even when its marginal mass is arbitrarily small. -/
theorem ae_positive_palette_of_cell_caps {Ω Γ V : Type*} [MeasurableSpace Ω]
    [Countable Γ] [Countable V] (μ : Measure Ω) (cell : Ω → Γ) (control : Ω → V)
    (weight : V → ENNReal) (B : ENNReal)
    (hcap : ∀ c v, μ {p | cell p = c ∧ control p = v} ≤ B * weight v) :
    ∀ᵐ p ∂μ, 0 < weight (control p) := by
  filter_upwards [Submission.Obl.k4_two_velocity_row_list_completion.ae_record_mass_ne_zero
    μ (fun p => (cell p, control p))] with p hp
  apply pos_iff_ne_zero.mpr
  intro hz
  have hc := hcap (cell p) (control p)
  rw [hz, mul_zero] at hc
  apply hp
  simpa only [Prod.mk.injEq] using le_antisymm hc bot_le

end Submission.Obl.k4_subcritical_endpoint_native_pairing
