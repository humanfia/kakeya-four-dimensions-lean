import Submission.Obl.k4_unbounded_geometric_packet_reduction.SupportGrid
import Submission.Obl.k4_unbounded_geometric_packet_reduction.SupportNumerics
import Submission.Obl.k4_unbounded_geometric_packet_reduction.SupportCaps

namespace Submission.Obl.k4_unbounded_geometric_packet_reduction

open MeasureTheory

noncomputable section

/-- Restricting only the analytical packet law to the native oscillation
pieces supplies Q0's full projected scalar law on the same original prior. -/
theorem OscillationPieces.projected_law
    {N χ η d s m S U : ℝ} {C Cpart : ℕ} {R : Fin C → ENNReal}
    {μ : Fin C → Measure Inc} {ν : Fin C → Measure Traj}
    {b : Fin C → Traj → Fin 5 → ℝ}
    (o : OscillationPieces N χ d s m C Cpart R μ b)
    (hcaps : ∀ a, ScalarCaps N χ d s m S U (ν a) (μ a) (b a))
    (hN : 2 ≤ N) (hK : 2 ≤ N ^ χ) (hm : 0 ≤ m) (hχη : χ ≤ η)
    (hχ : χ * ((2 * Cpart + 12 : ℕ) : ℝ) ≤ η) :
    ∀ a, ProjectedScalarLaw N η d s m S U (ν a)
      ((μ a).restrict (⋃ e, ⋃ i, o.piece a e i)) (b a) := by
  have hNp : 0 < N := by linarith
  obtain ⟨F, hF⟩ := o.finite_support hNp (fun a => (hcaps a).2.2.2.2.1)
  intro a
  have hgood : MeasurableSet (⋃ e, ⋃ i, o.piece a e i) :=
    MeasurableSet.iUnion (fun e => MeasurableSet.iUnion (o.measurable a e))
  apply (hcaps a).complete_of_support (by linarith) hχη Measure.restrict_le_self
  refine ⟨F a, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (hF a).1 (sq_nonneg _)).trans
      (support_grid_target_bound Cpart hN hK hm hχ)
  · have hunit : ∀ᵐ p ∂μ a, p.2 ∈ Set.Icc (0 : ℝ) 1 := by
      rw [ae_iff]
      have heq : {p : Inc | p.2 ∉ Set.Icc (0 : ℝ) 1} =
          (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ := by ext p; simp
      rw [heq]
      exact (hcaps a).2.2.2.1
    filter_upwards [ae_restrict_mem hgood,
      hunit.filter_mono (ae_mono Measure.restrict_le_self)] with p hp ht
    exact (hF a).2 p hp ht

end
end Submission.Obl.k4_unbounded_geometric_packet_reduction
