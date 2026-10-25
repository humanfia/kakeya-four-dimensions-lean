/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NamedAncestry.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeLevel
import Submission.Obl.k4_subcritical_corrected_scalar_charts.WitnessInheritance

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory Filter
open Submission.Obl.k4_critical_intercept_concentration.Data

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- A named original parent occurring at an original child incidence is the
actual frozen ancestor, almost everywhere. Thus the ENTIRE child assignment
and time block inherit that named parent's estimates. -/
theorem NativeLevel.named_ancestry_ae (h : cfg.Prepared) {k : ℕ} {s₀ s : ℝ}
    (parent : cfg.NativeLevel k s₀) (child : cfg.NativeLevel k s)
    (hnested : ∀ ic : Fin (cfg.n k s), ∃ ip : Fin (cfg.n k s₀),
      cfg.A k s ic ⊆ cfg.A k s₀ ip ∧
      I (cfg.T k s) (cfg.j k s ic) ⊆ I (cfg.T k s₀) (cfg.j k s₀ ip)) :
    ∀ᵐ p ∂cfg.μ k, ∀ (ic : Fin (cfg.n k s)) (ip : Fin (cfg.n k s₀)),
      p.1 ∈ cfg.B k s ic → p.2 ∈ I (cfg.T k s) (cfg.j k s ic) →
      p.1 ∈ cfg.B k s₀ ip → p.2 ∈ I (cfg.T k s₀) (cfg.j k s₀ ip) →
      cfg.A k s ic ⊆ cfg.A k s₀ ip ∧
        I (cfg.T k s) (cfg.j k s ic) ⊆ I (cfg.T k s₀) (cfg.j k s₀ ip) := by
  let : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  filter_upwards [true_assignments_ae_unique (cfg.ν k) (cfg.μ k)
    (ENNReal.ofReal (cfg.K k)) (h.basic k).2.2.2.1 (cfg.T k s₀) (cfg.j k s₀)
    (cfg.A k s₀) parent.assignments.disjoint] with p hp
  intro ic ip hci hct hpi hpt
  obtain ⟨jp, hA, hI⟩ := hnested ic
  have heq : ip = jp := hp ip jp (parent.assignments.fitted_subset ip hpi) hpt
    (hA (child.assignments.fitted_subset ic hci)) (hI hct)
  simpa only [heq] using And.intro hA hI

/-- At every fixed pair of increasing depths, the original atlas supplies
named ancestry for every pair of genuine stored native levels. -/
theorem Prepared.eventually_named_ancestry (h : cfg.Prepared) {s₀ s : ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ < s) (hsU : s ≤ cfg.U) :
    ∀ᶠ k in atTop, ∀ (parent : cfg.NativeLevel k s₀) (child : cfg.NativeLevel k s),
      ∀ᵐ p ∂cfg.μ k, ∀ (ic : Fin (cfg.n k s)) (ip : Fin (cfg.n k s₀)),
        p.1 ∈ cfg.B k s ic → p.2 ∈ I (cfg.T k s) (cfg.j k s ic) →
        p.1 ∈ cfg.B k s₀ ip → p.2 ∈ I (cfg.T k s₀) (cfg.j k s₀ ip) →
        cfg.A k s ic ⊆ cfg.A k s₀ ip ∧
          I (cfg.T k s) (cfg.j k s ic) ⊆ I (cfg.T k s₀) (cfg.j k s₀ ip) := by
  filter_upwards [h.eventually_nested hs₀ hs hsU] with k hk
  intro parent child
  exact parent.named_ancestry_ae h child hk

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
