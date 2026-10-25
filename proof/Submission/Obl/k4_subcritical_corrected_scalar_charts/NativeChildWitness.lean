/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeChildWitness.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeOriginalCaps
import Submission.Obl.k4_subcritical_corrected_scalar_charts.WitnessInheritance

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory
open scoped ENNReal
open Submission.Obl.k4_critical_intercept_concentration.Data

noncomputable section

theorem affineField_sub (L M : Fin 4 → ℝ) (z : Fin 3 → ℝ) :
    affineField (L - M) z = affineField L z - affineField M z := by
  simp only [affineField, Pi.sub_apply]
  ring

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- Every full original child witness lies near its genuine parent's affine
entry as well as its own. The current endpoint law plays no role in this fact. -/
theorem NativeLevel.child_parent_difference_ae (h : cfg.Prepared)
    {k : ℕ} {s₀ s : ℝ} (parent : cfg.NativeLevel k s₀) (child : cfg.NativeLevel k s)
    (ip : Fin (cfg.n k s₀)) (ic : Fin (cfg.n k s))
    (hA : cfg.A k s ic ⊆ cfg.A k s₀ ip)
    (hI : I (cfg.T k s) (cfg.j k s ic) ⊆ I (cfg.T k s₀) (cfg.j k s₀ ip)) :
    ∀ᵐ p ∂(cfg.μ k).restrict (cfg.B k s ic ×ˢ I (cfg.T k s) (cfg.j k s ic)),
      |affineField (child.L ic - parent.L ip) (originalBase (cfg.b k p.1) p.2)| ≤
        cfg.K k * (cfg.N k ^ (-s) + cfg.N k ^ (-s₀)) := by
  let : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  have hp := nested_assignment_parent_mem (cfg.ν k) (cfg.μ k) (ENNReal.ofReal (cfg.K k))
    (h.basic k).2.2.2.1 (cfg.T k s₀) (cfg.j k s₀) (cfg.A k s₀) (cfg.B k s₀)
    parent.assignments.disjoint parent.assignments.fitted_subset parent.assignments.covers
    (cfg.B k s ic) (I (cfg.T k s) (cfg.j k s ic)) ip
    ((child.assignments.fitted_subset ic).trans hA) hI
  have hE : MeasurableSet (cfg.B k s ic ×ˢ I (cfg.T k s) (cfg.j k s ic)) :=
    (child.fitted_measurable ic).prod measurableSet_Icc
  filter_upwards [ae_restrict_of_ae hp, ae_restrict_mem hE] with p hp hpE
  have hpB := hp hpE.1 hpE.2
  have hc := child.fit ic p.1 hpE.1 p.2 hpE.2
  have hpa := parent.fit ip p.1 hpB p.2 (hI hpE.2)
  rw [affineField_sub]
  change |affineField (child.L ic) (originalBase (cfg.b k p.1) p.2) -
    affineField (parent.L ip) (originalBase (cfg.b k p.1) p.2)| ≤ _
  have hc' : |(cfg.b k p.1 2 + p.2 * cfg.b k p.1 5) -
      affineField (child.L ic) (originalBase (cfg.b k p.1) p.2)| ≤ cfg.K k * cfg.N k ^ (-s) := hc
  have hp' : |(cfg.b k p.1 2 + p.2 * cfg.b k p.1 5) -
      affineField (parent.L ip) (originalBase (cfg.b k p.1) p.2)| ≤ cfg.K k * cfg.N k ^ (-s₀) := hpa
  exact (abs_sub_le _ (cfg.b k p.1 2 + p.2 * cfg.b k p.1 5) _).trans
    ((add_le_add (by simpa only [abs_sub_comm] using hc') hp').trans_eq (by ring))

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
