/-
Adapted from this LOT tree o198, session x0691, commit 9816360a0a6a894f89615acd484d1584ad77897e,
Submission/Obl/k4_balanced_native_packet_transport/WindowSelection.lean (namespace renamed to
Submission.Obl.k4_uncapped_native_capping). Existing source attributions below are retained.
-/
import Submission.Obl.k4_uncapped_native_capping.WindowTransport
import Submission.Obl.k4_uncapped_native_capping.WeightedDomination

namespace Submission.Obl.k4_uncapped_native_capping

open MeasureTheory Set
noncomputable section

theorem WindowCertificate.weight_pos
    {N χ d s m : ℝ} {C : ℕ} {R : Fin C → ENNReal}
    {μ : Fin C → Measure Inc} {b : Fin C → Traj → Fin 5 → ℝ}
    (h : WindowCertificate N χ d s m C R μ b) (i : Fin C) : 0 < R i := by
  obtain ⟨J, w, Λ, P, S, tag, A, z, hw, hN, href, hA, _⟩ := h
  exact (hA i).1

/-- Analytical deletion preserves the same shared certificate and budgets. -/
theorem WindowCertificate.mono
    {N χ d s m : ℝ} {C : ℕ} {R : Fin C → ENNReal}
    {μ μ' : Fin C → Measure Inc} {b : Fin C → Traj → Fin 5 → ℝ}
    (h : WindowCertificate N χ d s m C R μ b) (hμ : ∀ i, μ' i ≤ μ i) :
    WindowCertificate N χ d s m C R μ' b := by
  apply h.transport id (fun _ => id) (fun _ => measurable_id) R μ' b
    (fun _ => univ) (fun _ => MeasurableSet.univ) (fun _ => by simp)
    h.weight_pos
    (fun A _ => Finset.sum_le_sum (fun i _ => mul_le_mul' le_rfl (hμ i (A i))))
    (fun _ => 0) (fun _ => 0) (fun _ => 1) (fun _ => by norm_num)
  · intro i p _
    simp only [id_eq, one_mul, zero_add, and_self]
  · intro i p _
    rfl

/-- Removing whole packets changes no reference laws, signal values or windows. -/
theorem WindowCertificate.reindex
    {N χ d s m : ℝ} {C C' : ℕ} {R : Fin C → ENNReal}
    {μ : Fin C → Measure Inc} {b : Fin C → Traj → Fin 5 → ℝ}
    (h : WindowCertificate N χ d s m C R μ b) (e : Fin C' ↪ Fin C) :
    WindowCertificate N χ d s m C' (R ∘ e) (μ ∘ e) (b ∘ e) := by
  have hdom := weighted_pullback_domination_of_disjoint e (fun _ => id)
    (fun _ => measurable_id) R μ (R ∘ e) (μ ∘ e) (fun _ => univ)
    (fun _ => MeasurableSet.univ)
    (fun i j hne heq => False.elim (hne (e.injective heq)))
    (fun i => by simp only [Function.comp_apply, Measure.map_id, Measure.restrict_univ]; rfl)
  apply h.transport e (fun _ => id) (fun _ => measurable_id)
    (R ∘ e) (μ ∘ e) (b ∘ e)
    (fun _ => univ) (fun _ => MeasurableSet.univ) (fun _ => by simp)
    (fun i => h.weight_pos (e i)) hdom
    (fun _ => 0) (fun _ => 0) (fun _ => 1) (fun _ => by norm_num)
  · intro i p _
    simp only [id_eq, Function.comp_apply, one_mul, zero_add, and_self]
  · intro i p _
    rfl

end
end Submission.Obl.k4_uncapped_native_capping
