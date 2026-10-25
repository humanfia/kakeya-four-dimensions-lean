/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/PreparedComparisonDeletion.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.PreparedComparisonAt

/-! Accounting for the original native exception before the comparison. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open MeasureTheory Set
open Submission.Obl.k4_general_parent_projected_layers

noncomputable section

/-- A native exception smaller than the current source leaves a positive source
to which the comparison applies, under the unchanged original law. -/
theorem comparison_source_outside_exception {X : Type*} [MeasurableSpace X]
    {μ ζ : Measure X} (hζ : ζ ≤ μ) {E : Set X} (hE : MeasurableSet E)
    (hsmall : μ E < ζ univ) :
    ζ.restrict Eᶜ ≤ μ ∧ (ζ.restrict Eᶜ) univ ≠ 0 ∧ (ζ.restrict Eᶜ) E = 0 := by
  refine ⟨Measure.restrict_le_self.trans hζ, ?_, ?_⟩
  · intro hz
    have hz' : ζ Eᶜ = 0 := by simpa using hz
    have htotal : ζ univ = ζ E := by
      simpa only [hz', add_zero] using (measure_add_measure_compl hE (μ := ζ)).symm
    exact (not_lt_of_ge (hζ E)) (htotal ▸ hsmall)
  · rw [Measure.restrict_apply hE]
    simp

/-- The native exception, the original-reference pruning and the matching loss
are charged once each against the source before any deletion. -/
theorem PreparedComparison.mass_budget_before_deletion
    {α : Type} [MeasurableSpace α] {p : Parameters} {a : PreparedModel α} {k : ℕ}
    {s H q χ m aTable Fprune Llist ε C Λ : ℝ} {L : ProjLayer α}
    {ζ : Measure (α × ℝ)} {assign : α × ℝ → Fin (a.n k s)}
    {g : Fin (a.n k s) → Bool → EuclideanSpace ℂ (Fin 3) → ℂ}
    {E : Set (α × ℝ)} (hE : MeasurableSet E) {nativeLoss : ENNReal}
    (hbad : ζ E ≤ nativeLoss)
    (cmp : PreparedComparison p a k s H q χ m aTable Fprune Llist ε C Λ L
      (ζ.restrict Eᶜ) assign g) :
    cmp.law ≤ ζ ∧
      ζ univ ≤ cmp.law univ + nativeLoss +
        ENNReal.ofReal (commonComparisonReference p k s H aTable / Fprune) +
        ENNReal.ofReal (C * (6 * commonNativeCapConstant (p.K k)) * Λ ^ (-ε) *
          commonComparisonReference p k s H aTable) := by
  refine ⟨cmp.le.trans Measure.restrict_le_self, ?_⟩
  have hmass := add_le_add cmp.mass_budget hbad
  have htotal : ζ univ = (ζ.restrict Eᶜ) univ + ζ E := by
    simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter, add_comm]
      using (measure_add_measure_compl hE (μ := ζ)).symm
  rw [htotal]
  convert hmass using 1
  ac_rfl

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
