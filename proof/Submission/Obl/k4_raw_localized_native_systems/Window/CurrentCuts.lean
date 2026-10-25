import Submission.Obl.k4_raw_localized_native_systems.Window.LongWitnesses
import Submission.Obl.k4_fixed_menu_density_pruning.CandidatePruning

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- Cutting disjoint current events by a common-world analytical event costs
only the unchanged original-world exceptional mass. -/
theorem current_common_cut_loss {p : Data} {k C : ℕ}
    (γC : Fin C → Fin (p.W k)) (FC : Fin C → Set Point)
    (hFC : ∀ a, MeasurableSet (FC a)) (hFCE : ∀ a, FC a ⊆ p.E k (γC a))
    (hdisj : ∀ a a', a ≠ a' → γC a = γC a' → Disjoint (FC a) (FC a'))
    (Keep : Fin (p.W k) → Set Point) :
    (∑ a, ENNReal.ofReal (p.ω k (γC a)) * priorMass p k (γC a) (FC a \ Keep (γC a))) ≤
      ∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ (Keep γ)ᶜ := by
  have heq (a : Fin C) : selected p k (γC a) (FC a \ Keep (γC a)) =
      priorMass p k (γC a) (FC a \ Keep (γC a)) := by
    rw [selected, Measure.restrict_eq_self _ (sdiff_subset.trans (hFCE a))]
  have hh := k4_fixed_menu_density_pruning.weighted_candidate_exception_le
    (selected p k) (fun γ => ENNReal.ofReal (p.ω k γ)) γC FC (fun γ => (Keep γ)ᶜ) hFC hdisj
  simpa only [← sdiff_eq, heq] using hh

theorem rawSupportSet_mono_current {p : Data} {k C : ℕ} (W : Atlas p k)
    (H : Fin W.C → Set Point) (Compat : Fin C → Fin W.C → Prop)
    {F F' : Fin C → Set Point} (hF : ∀ a, F' a ⊆ F a) (a : Fin C) :
    rawSupportSet W H Compat F' a ⊆ rawSupportSet W H Compat F a :=
  fun _ hz => ⟨hF a hz.1, hz.2⟩

/-- Add the loss of an analytical current cutoff to the loss of a subsequent
good subset, while continuing to measure the original formatted events. -/
theorem current_omission_split {p : Data} {k C : ℕ}
    (γC : Fin C → Fin (p.W k)) (F F' G : Fin C → Set Point) :
    (∑ a, ENNReal.ofReal (p.ω k (γC a)) * priorMass p k (γC a) (F a \ G a)) ≤
      (∑ a, ENNReal.ofReal (p.ω k (γC a)) * priorMass p k (γC a) (F a \ F' a)) +
        ∑ a, ENNReal.ofReal (p.ω k (γC a)) * priorMass p k (γC a) (F' a \ G a) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  rw [← mul_add]
  apply mul_le_mul' le_rfl
  apply le_trans (measure_mono (show F a \ G a ⊆ (F a \ F' a) ∪ (F' a \ G a) by
    intro z hz
    by_cases hz' : z ∈ F' a
    · exact Or.inr ⟨hz', hz.2⟩
    · exact Or.inl ⟨hz.1, hz'⟩))
  exact measure_union_le _ _

end
end Submission.Obl.k4_raw_localized_native_systems.Window
