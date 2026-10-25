import Submission.Obl.k4_wide_velocity_lists_scalar_preparation.Model

namespace Submission.Obl.k4_wide_velocity_lists_scalar_preparation

open MeasureTheory Set Filter

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The original parent facts used to integrate a scalar residual cell. -/
structure ParentGeometry (cfg : Data α) (k : ℕ) (r : ℝ) : Prop where
  prior_lower : ∀ i : Fin (cfg.n k r), ENNReal.ofReal
    ((cfg.N k ^ (-r)) ^ cfg.d * (((2 : ℝ) ^ cfg.T k r)⁻¹) ^ 2 *
      cfg.N k ^ (-cfg.ℓ * r) / cfg.K k) ≤ cfg.ν k (cfg.A k r i)
  fitted_subset : ∀ i, cfg.B k r i ⊆ cfg.A k r i
  coefficient_bound : ∀ i e, |cfg.c k r i e| ≤ cfg.K k
  transverse : ∀ i l, l ∈ cfg.A k r i →
    ∀ t ∈ Submission.Obl.k4_critical_conditional_row_preparation.Data.I
      (cfg.T k r) (cfg.j k r i),
    |cfg.x k l t 2 - cfg.c k r i 2 - t * cfg.c k r i 3 -
      cfg.c k r i 4 * cfg.x k l t 1| ≤
      cfg.K k * ((2 : ℝ) ^ cfg.T k r)⁻¹ * cfg.N k ^ (-cfg.ℓ * r)

theorem Valid.eventually_parent_geometry (h : Valid cfg)
    {r : ℝ} (hr : 0 < r) (hrU : r ≤ cfg.U) :
    ∀ᶠ k in atTop, ParentGeometry cfg k r := by
  let R := 2 + r⁻¹
  have hR : 1 < R := by dsimp [R]; linarith [inv_pos.mpr hr]
  have hRr : R⁻¹ ≤ r := by
    apply (inv_le_comm₀ (by linarith : 0 < R) hr).mpr
    dsimp [R]
    linarith
  filter_upwards [h.atlas R hR] with k hk
  have a := hk r hRr hrU
  refine ⟨?_, (fun i => (a.2.2.1 i).2.2),
    (fun i e => (a.2.2.2.2.1 i).2.2.2.1 e), ?_⟩
  · intro i
    simpa only [zpow_neg, zpow_natCast] using (a.2.2.2.2.1 i).1
  · intro i l hl t ht
    simpa only [zpow_neg, zpow_natCast] using
      ((a.2.2.2.2.1 i).2.2.2.2.2.1 l hl t ht).2.1

end Data

end

end Submission.Obl.k4_wide_velocity_lists_scalar_preparation
