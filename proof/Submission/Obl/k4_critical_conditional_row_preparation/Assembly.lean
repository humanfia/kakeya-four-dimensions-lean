import Submission.Obl.k4_critical_conditional_row_preparation.Normalize

namespace Submission.Obl.k4_critical_conditional_row_preparation
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace Data
variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- Uniform physical preparation suffices for the exact fixed-depth conclusion. -/
theorem preparation_of_physical (h : cfg.Valid)
    (hphysical : ∀ s η : ℝ, 0 < s → 1000 * s < cfg.U → 1000 * s < cfg.e₀ → 0 < η →
      ∀ᶠ k in atTop, ∀ source : Measure (α × ℝ), source ≤ cfg.ρ k →
        ENNReal.ofReal (cfg.N k ^ (-(η / 100))) ≤ source univ →
        Nonempty (cfg.PhysicalPreparation k s η source)) :
    ∀ s : ℝ, 0 < s → 1000 * s < cfg.U → 1000 * s < cfg.e₀ → s < 1 →
      (∀ η : ℝ, 0 < η → ∃ᶠ k in atTop, cfg.ListAt k s η) →
      ∀ η : ℝ, 0 < η → ∃ᶠ k in atTop, cfg.ConditionalAt k s η := by
  intro s hs hsU hse _ hlist η hη
  have hsU' : s ≤ cfg.U := by linarith
  have hlate : ∀ᶠ k in atTop, cfg.ListAt k s (η / 100) → cfg.ConditionalAt k s η := by
    filter_upwards [hphysical s η hs hsU hse hη, h.eventually_assignment_level hs hsU',
      h.eventually_pruning_losses η hη, h.eventually_palette_interval_cap (200 * s) η (by positivity) hη,
      h.eventually_clipped_joint_cell_cap s (200 * s) η hs (by positivity) hη]
      with k hprep a hcost hpal hjoint
    rintro ⟨source, lists, hsource, hmass, hcard, hlists⟩
    obtain ⟨p⟩ := hprep source hsource hmass
    apply p.to_conditionalAt h a hs.le hη hcost.2.1 hpal
      (hjoint a p.index p.current p.current_le_parent) (lists p.index)
    · intro q v
      exact (hcard p.index q v).trans (Real.rpow_le_rpow_of_exponent_le
        (by linarith [h.scale k]) (by linarith))
    · exact hlists p.index
  exact ((hlist (η / 100) (by positivity)).and_eventually hlate).mono (fun _ hk => hk.2 hk.1)

end Data
end
end Submission.Obl.k4_critical_conditional_row_preparation
