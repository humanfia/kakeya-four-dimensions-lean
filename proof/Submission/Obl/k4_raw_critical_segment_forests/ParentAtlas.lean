import Submission.Obl.k4_raw_critical_segment_forests.Layers
import Submission.Obl.k4_raw_critical_segment_forests.NestedInterface
import Submission.Obl.k4_coarsened_outer_horizon_composition.Finish

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- Key an own-depth list by the terminal, finer observation. -/
def finerLists {p : Data} {k : ℕ} (a : Atlas p k) (r : ℝ) : Atlas p k :=
  { a with
    lst := fun γ o => a.lst γ (Submission.Lib.K4Homogenization.coarsenObservation (p.N k) r p.L o) }

lemma knownAt_finer_of_trueDepth {p : Data} (hp : Valid p) {k M D : ℕ}
    {a : Atlas p k} {κ r : ℝ} (hr : r ≤ p.L)
    (ha : TrueDepth a M D κ r)
    (hlst : ∀ γ o, ((a.lst γ o).card : ℝ) ≤ κ)
    (hmem : ∀ b z, z ∈ a.F b → b ∈ a.lst (a.γ b)
      (obs (p.B k (a.γ b)) (δ (p.N k) r) z)) :
    (finerLists a r).KnownAt M D κ r := by
  dsimp only [finerLists, Atlas.KnownAt, Atlas.Regular]
  obtain ⟨hC, hsep, hchart, hmass⟩ := ha
  refine ⟨⟨hC, hsep, ?_, hmass⟩, fun γ o => hlst γ _⟩
  intro b
  apply k4_coarsened_outer_horizon_composition.chart_extra_mono (hc := hchart b)
  intro _ z hz
  have heq := congrFun (k4_coarsened_outer_horizon_composition.obs_factorization
    (hp.scale_ge_one k) hr (p.B k (a.γ b))) z
  change obs (p.B k (a.γ b)) (δ (p.N k) r) z =
    Submission.Lib.K4Homogenization.coarsenObservation (p.N k) r p.L
      (obs (p.B k (a.γ b)) (δ (p.N k) p.L) z) at heq
  change b ∈ a.lst (a.γ b)
    (Submission.Lib.K4Homogenization.coarsenObservation (p.N k) r p.L
      (obs (p.B k (a.γ b)) (δ (p.N k) p.L) z))
  rw [← heq]
  exact hmem b z hz

end
end Submission.Obl.k4_raw_critical_segment_forests
