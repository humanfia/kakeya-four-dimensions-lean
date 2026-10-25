-- Adapted from this LOT tree, obligation o254, branch x0898, commit f25a0cc9, file Submission/Obl/k4_general_parent_wide_layer_candidates/Native/DomainLawAssembly.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
/- Adapted from this LOT tree, obligation o200, session x0934, commit 3ef9d3b45123d3245f500a2dc2bd85270a8fff3d,
   Submission/Obl/k4_finite_projected_horizontal_candidates/DomainLawAssembly.lean. Original source attributions are retained below. -/
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.MeshPairLaw

/-! Assemble prepared laws on a finite common-domain partition. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Preparing the two colors separately inside each domain gives one global
submeasure. Its restriction to a domain is exactly that domain's prepared law. -/
theorem assemble_domain_submeasures {Ω Q : Type*} [MeasurableSpace Ω]
    [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (μ : Measure Ω) (code : Ω → Q) (hcode : Measurable code)
    (law : Q → Measure Ω) (hdom : ∀ q, law q ≤ codePieces μ code q) :
    (∑ q, law q) ≤ μ ∧ ∀ q, (∑ j, law j).restrict {p | code p = q} = law q := by
  classical
  have hmem (q : Q) : ∀ᵐ p ∂law q, code p = q :=
    (ae_restrict_mem (hcode (measurableSet_singleton q))).filter_mono (ae_mono (hdom q))
  constructor
  · calc
      _ ≤ ∑ q, codePieces μ code q := Finset.sum_le_sum fun q _ => hdom q
      _ = μ := codePieces_sum μ code hcode
  · intro q
    have hrestr (j : Q) : (law j).restrict {p | code p = q} = if j = q then law q else 0 := by
      by_cases hj : j = q
      · subst j
        rw [ite_eq_left rfl]
        exact Measure.restrict_eq_self_of_ae_mem (hmem q)
      · rw [ite_eq_right hj]
        apply Measure.restrict_eq_zero.mpr
        have hnot : ∀ᵐ p ∂law j, p ∉ {p | code p = q} :=
          (hmem j).mono fun p hp hq => hj (hp.symm.trans hq)
        exact compl_mem_ae_iff.mp hnot
    change Measure.restrictₗ {p | code p = q} (∑ j, law j) = law q
    rw [map_sum]
    simp only [Measure.restrictₗ_apply, hrestr]
    simp

/-- Local pruning losses add through the original partition. Their charge is
the sum of original reference weights, without a factor for the domain count. -/
theorem assembled_domain_mass_budget {Ω Q : Type*} [MeasurableSpace Ω]
    [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (μ : Measure Ω) (code : Ω → Q) (hcode : Measurable code)
    (law : Q → Measure Ω) (loss : Q → ℝ≥0∞)
    (hbudget : ∀ q, codePieces μ code q univ ≤ law q univ + loss q) :
    μ univ ≤ (∑ q, law q) univ + ∑ q, loss q := by
  calc
    _ = (∑ q, codePieces μ code q) univ :=
      congrArg (fun ν : Measure Ω => ν univ) (codePieces_sum μ code hcode).symm
    _ = ∑ q, codePieces μ code q univ := Measure.finsetSum_apply _ _ _
    _ ≤ ∑ q, (law q univ + loss q) := Finset.sum_le_sum fun q _ => hbudget q
    _ = (∑ q, law q) univ + ∑ q, loss q := by
      rw [Finset.sum_add_distrib, Measure.finsetSum_apply]

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
