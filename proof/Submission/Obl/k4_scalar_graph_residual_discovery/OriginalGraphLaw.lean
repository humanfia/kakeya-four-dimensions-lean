/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit f3582cb1, file OriginalGraphLaw.lean.
   Helper namespace and imports renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.Model

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory

namespace ScalarData

/-- Prepared and graph laws agree on every later retained event. Graph
palette caps are applied only to the graph law; original global floors
may be transported using this equality, with no renormalization. -/
theorem original_graph_restrict_eq (D : ScalarData) (k : ℕ) (g : Fin (D.W k))
    {E₀ Eg R : Set ScalarIncidence} (hREg : R ⊆ Eg) (hEgE₀ : Eg ⊆ E₀) :
    ((D.ρ k g).restrict E₀).restrict R = ((D.ρ k g).restrict Eg).restrict R := by
  rw [Measure.restrict_restrict_of_subset (hREg.trans hEgE₀),
    Measure.restrict_restrict_of_subset hREg]

/-- The equality includes every retained entry, even if the entry itself
is not measurable; measurability of the retained event suffices. -/
theorem original_graph_measure_on_retained (D : ScalarData) (k : ℕ) (g : Fin (D.W k))
    {E₀ Eg R : Set ScalarIncidence} (hR : MeasurableSet R)
    (hREg : R ⊆ Eg) (hEgE₀ : Eg ⊆ E₀) (A : Set ScalarIncidence) :
    (D.ρ k g).restrict E₀ (R ∩ A) = (D.ρ k g).restrict Eg (R ∩ A) := by
  have hh := congrArg (fun ν : Measure ScalarIncidence => ν A)
    (D.original_graph_restrict_eq k g hREg hEgE₀)
  simpa only [Measure.restrict_apply' hR, inter_comm] using hh

end ScalarData

end Submission.Obl.k4_scalar_graph_residual_discovery
