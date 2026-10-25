import Submission.Obl.k4_scalar_candidate_original_return.Defs
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Basic
import Submission.Obl.k4_scalar_normalized_exact_refinement.Mass

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Set
open scoped ENNReal

/-- Domination keeps each world's original weight. Clipping each label to the
original event costs no original mass, even without old-selected support. -/
lemma dominated_original_success {p : Code} (hp : Exact p) (k : ℕ) {m : ℕ}
    (ρ : Fin (W p k) → Measure Inc) (hρ : ∀ g, ρ g ≤ mu p k g)
    (γ : Fin m → Fin (W p k)) (C : Fin m → Set Inc) :
    (∑ g, ENNReal.ofReal (ω p k g) * ρ g {q | ∃ i, γ i = g ∧ q ∈ C i}) ≤
      ∑ i, ENNReal.ofReal (ω p k (γ i)) * mu p k (γ i) (E p k (γ i) ∩ C i) := by
  apply (k4_scalar_normalized_exact_refinement.weighted_union_le_sum ρ
    (fun g => ENNReal.ofReal (ω p k g)) γ C).trans
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply (hρ (γ i) (C i)).trans_eq
  apply measure_congr
  have hE : ∀ᵐ q ∂mu p k (γ i), q ∈ E p k (γ i) :=
    ae_restrict_mem (k4_scalar_true_atlas_terminal_lists.Exact.event_measurable hp k (γ i))
  filter_upwards [hE] with q hq
  simp only [mem_inter_iff, hq, true_and]

end Submission.Obl.k4_scalar_candidate_original_return
