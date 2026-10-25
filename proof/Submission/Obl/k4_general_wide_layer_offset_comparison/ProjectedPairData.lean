import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedComparisonOffsets

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ProjectedPairData.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial

noncomputable section

namespace ProjectedComparisonFrame

variable {α : Type} [MeasurableSpace α] {p : Parent α} {k : ℕ} {sc sf m H h g b : ℝ}
    {σ : Measure (α × ℝ)} (f : ProjectedComparisonFrame p k sc sf m H h g b σ)

/-- The two actual finite selectors read original projected labels with
the SAME original bin and physical long domain. Their discrepancy is exactly
the pullback of the original fine-minus-coarse projected polynomials. -/
theorem original_pair_data_ae : ∀ᵐ ω ∂σ,
    ∃ (i : Fin f.coarse.count) (j : Fin f.fine.count),
      ω ∈ p.baseGood k ∧ ω.1 ∈ f.coarse.C i ∧ ω.1 ∈ f.fine.C j ∧
      f.coarse.tag i = f.fine.tag j ∧
      let D := p.domainCode k h g b ω
      f.differencePolynomial ω =
        projectedChartPolynomial (f.fine.G j) (domainTime h D) (32 * h)
          (domainIntercept h g b D) (domainVelocity g D) (32 * b) -
        projectedChartPolynomial (f.coarse.G i) (domainTime h D) (32 * h)
          (domainIntercept h g b D) (domainVelocity g D) (32 * b) := by
  filter_upwards [f.coarseAtlas.selected_source_ae, f.fineAtlas.selected_source_ae] with ω hc hf
  obtain ⟨ec, hsc, hc⟩ := hc
  obtain ⟨ef, hsf, hf⟩ := hf
  have hcode₀ := f.coarse.slicedEvent_code p f.coarseAtlas.valid f.coarseAtlas.domains ec.val hc.1
  have hcode₁ := f.fine.slicedEvent_code p f.fineAtlas.valid f.fineAtlas.domains ef.val hf.1
  have hD₀ : p.domainCode k h g b ω = ec.val.2.val := congrArg Prod.snd hcode₀
  have hD₁ : p.domainCode k h g b ω = ef.val.2.val := congrArg Prod.snd hcode₁
  refine ⟨ec.val.1, ef.val.1, hc.2, hc.1.1.1, hf.1.1.1,
    congrArg Prod.fst (hcode₀.symm.trans hcode₁), ?_⟩
  dsimp only
  rw [differencePolynomial, hsc, hsf]
  dsimp only [ProjectedLayer.SourceAtlas.polynomial, ProjectedLayer.sliceChart]
  rw [← hD₀, ← hD₁]

end ProjectedComparisonFrame
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
