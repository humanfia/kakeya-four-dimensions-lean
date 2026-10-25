import Submission.Obl.k4_general_wide_layer_offset_comparison.ActualWholeFiberOffsets
import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedPairData
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.DerivativeListPreparation

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ComparedProjectedOffsets.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set Filter MvPolynomial
open scoped ENNReal

noncomputable section

namespace ProjectedComparisonFrame

variable {α : Type} [MeasurableSpace α] {p : Parent α} {k : ℕ} {sc sf m H h g b : ℝ}
    {σ : Measure (α × ℝ)} (f : ProjectedComparisonFrame p k sc sf m H h g b σ)

def goodLaw (M : ℝ) : Measure (α × ℝ) := σ.restrict (f.bad M)ᶜ

theorem goodLaw_le (M : ℝ) : f.goodLaw M ≤ σ := Measure.restrict_le_self

/-- Delete the original discrepancy event without changing the mass
units. The mass-floor step is the accepted original-law deletion lemma. -/
theorem goodLaw_mass_floor {M target cost lower : ℝ}
    (htarget : 0 ≤ target) (hcost : 0 ≤ cost)
    (hlower : ENNReal.ofReal lower ≤ σ univ)
    (hbad : σ (f.bad M) ≤ ENNReal.ofReal cost) (hbudget : target + cost ≤ lower) :
    ENNReal.ofReal target ≤ f.goodLaw M univ := by
  apply Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.restrict_mass_after_deletion
    σ MeasurableSet.univ (f.bad_measurable M).compl (subset_univ _)
    (by simp) htarget hcost hlower
  · simpa using hbad
  · exact hbudget

end ProjectedComparisonFrame

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- Outside the original projected comparison event, the actual original
selectors carry canonical constant offsets on every true fiber they meet.
No new marginal floor, normalization or auxiliary pair law is used. -/
theorem eventually_projected_fiber_offsets (hp : p.Valid)
    {r u m C : ℝ} (hr : 0 < r) (hu : 0 < u) (hC : 0 ≤ C)
    (hm : (p.κ + p.ℓ) * r < m) (hgap : (C + 1 + p.ℓ) * u < p.κ * r)
    (H : ℕ → ℝ) (hH : ∀ k, 2 ≤ H k) (hKH : ∀ k, p.K k ≤ H k)
    (hHs : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ p.N k ^ ε) :
    ∀ᶠ k in atTop, ∀ sf h g b L : ℝ, ∀ σ : Measure (α × ℝ),
      ∀ f : ProjectedComparisonFrame p k r sf m L h g b σ,
      L ≤ H k → h * g = b → p.N k ^ (-p.ℓ * (r + u)) / H k ≤ b →
      g ≤ H k * p.N k ^ (-p.ℓ * r) →
      ∀ᵐ ω ∂f.goodLaw (4 * L * p.N k ^ (-r) * p.N k ^ (C * u)),
        ∃ (i : Fin f.coarse.count) (j : Fin f.fine.count),
          ω ∈ p.baseGood k ∧ ω.1 ∈ f.coarse.C i ∧ ω.1 ∈ f.fine.C j ∧
          f.coarse.tag i = f.fine.tag j ∧
          ∀ R : ℝ, p.AtDepth k r R → ∀ Q : Fin (p.n k r),
            ω.1 ∈ p.B k r Q → ω.2 ∈ block (p.T k r) (p.j k r Q) →
          ∀ t₀ ∈ block (p.T k r) (p.j k r Q),
            let z₀ := p.trueFiberPoint k r m Q (f.coarse.tag i) t₀
            let offset := eval ![z₀ 0, z₀ 2] (f.fine.G j) - eval ![z₀ 0, z₀ 2] (f.coarse.G i)
            ∀ z ∈ p.trueFiberBox k r m (H k) Q (f.coarse.tag i),
              |eval ![z 0, z 2] (f.fine.G j) - eval ![z 0, z 2] (f.coarse.G i) - offset| ≤
                p.N k ^ (-r - u) := by
  filter_upwards [p.eventually_wholeFiber_offsets hp hr hu hC hm hgap H hH hKH hHs] with k hk
  intro sf h g b L σ f hLH hmove hblo hghi
  let M := 4 * L * p.N k ^ (-r) * p.N k ^ (C * u)
  have hpairs : ∀ᵐ ω ∂f.goodLaw M, ∃ (i : Fin f.coarse.count) (j : Fin f.fine.count),
      ω ∈ p.baseGood k ∧ ω.1 ∈ f.coarse.C i ∧ ω.1 ∈ f.fine.C j ∧
      f.coarse.tag i = f.fine.tag j ∧
      let D := p.domainCode k h g b ω
      f.differencePolynomial ω =
        projectedChartPolynomial (f.fine.G j) (domainTime h D) (32 * h)
          (domainIntercept h g b D) (domainVelocity g D) (32 * b) -
        projectedChartPolynomial (f.coarse.G i) (domainTime h D) (32 * h)
          (domainIntercept h g b D) (domainVelocity g D) (32 * b) :=
    f.original_pair_data_ae.filter_mono (ae_mono (f.goodLaw_le M))
  have hgood : ∀ᵐ ω ∂f.goodLaw M, ω ∉ f.bad M :=
    ae_restrict_mem (f.bad_measurable M).compl
  filter_upwards [hpairs, hgood] with ω hpair hnot
  obtain ⟨i, j, hbase, hcoarse, hfine, htag, hpoly⟩ := hpair
  refine ⟨i, j, hbase, hcoarse, hfine, htag, ?_⟩
  intro R hat Q hl ht t₀ ht₀
  have hbins := ((f.coarseAtlas.valid.2.2.2.2.2.1 i).2.2.2.1 ω.1 hcoarse)
  apply hk R hat h g b f.time_pos f.slope_pos f.width_pos hmove hblo hghi Q
    (f.coarse.tag i) ω hl ht hbins.2.1 hbins.1 (f.coarse.G i) (f.fine.G j)
    (f.coarseAtlas.valid.2.2.2.2.2.1 i).2.1
    (f.fineAtlas.valid.2.2.2.2.2.1 j).2.1 ?_ t₀ ht₀
  intro y hy
  dsimp only at hpoly ⊢
  rw [← hpoly]
  apply (f.differencePolynomial_bound hnot y hy).trans
  dsimp only [M]
  have hN : 0 < p.N k := by linarith [hp.scale k]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLH (by norm_num)) (by positivity))
    (by positivity)

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
