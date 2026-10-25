import Submission.Obl.k4_general_wide_layer_offset_comparison.SmoothedProjectedAtlas
import Submission.Obl.k4_general_wide_layer_offset_comparison.AEComparison

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ProjectedMatchingLaw.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial
open scoped ENNReal

noncomputable section

/-- The literal two-color comparison law obtained from the unchanged
original source and its common tiny-cell jitter. All index identities and
both separate original priors are retained. -/
def projectedMatchingLaw {α : Type} [MeasurableSpace α]
    {p : Parent α} {A₀ A₁ : ProjectedLayer α}
    {k : ℕ} {s₀ s₁ m H h g b δ η B E : ℝ} {σ : Measure (α × ℝ)} [IsFiniteMeasure σ]
    (f₀ : A₀.SourceAtlas p k s₀ m H h g b σ)
    (f₁ : A₁.SourceAtlas p k s₁ m H h g b σ)
    (hbase : p.Basic) (hN : 0 < p.N k) (hK : 1 ≤ p.K k) (hH : 1 ≤ H)
    (hh : 0 < h) (hg : 0 < g) (hb : 0 < b) (hmove : h * g ≤ b)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8) (hη : 0 ≤ η) (hη1 : η ≤ 1) (hB : 0 ≤ B)
    (hcoeff₀ : ∀ i e, |(A₀.G i).coeff e| ≤ B)
    (hcoeff₁ : ∀ i e, |(A₁.G i).coeff e| ≤ B)
    (htime : (32 * h) * δ ≤ η)
    (htrans₀ : ∀ e : A₀.ActiveSlice p k h g b f₀.domains σ,
      (|domainVelocity g e.val.2.val| * (32 * h) + 32 * b) * δ ≤ η)
    (htrans₁ : ∀ e : A₁.ActiveSlice p k h g b f₁.domains σ,
      (|domainVelocity g e.val.2.val| * (32 * h) + 32 * b) * δ ≤ η)
    (hE : 0 < E)
    (herror₀ : H * p.N k ^ (-s₀) + 54 * B * (p.K k + 1) ^ 4 * η ≤ E)
    (herror₁ : H * p.N k ^ (-s₁) + 54 * B * (p.K k + 1) ^ 4 * η ≤ E)
    (Q : Finset (Fin 2 → ℤ))
    (hcover : ∀ᵐ ω ∂σ, meshCode2 δ (p.normalizedDomainBase k h g b ω) ∈ Q)
    (hcell₀ : f₀.CellCeiling δ Q) (hcell₁ : f₁.CellCeiling δ Q) :
    AEWeightComparison f₀.Index f₁.Index (Option ComparisonCode)
      ((α × ℝ) × EuclideanSpace ℝ (Fin 3)) := by
  have hZ := p.measurable_normalizedDomainBase hbase k h g b
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  refine
    { law := matchingMeshCoupling σ (p.normalizedDomainBase k h g b) δ Q
      lab₁ := f₀.key
      lab₂ := f₁.key
      φ₁ := f₀.sheet
      φ₂ := f₁.sheet
      src := fun z => f₀.selector z.1
      wit := fun z => f₁.selector z.1
      point := Prod.snd
      value := fun z => eval (p.x k z.1.1 z.1.2) (p.P k)
      error := E
      K := p.projectedComparisonDensity k H
      weight₁ := p.comparisonPrior k s₀ m h b
      weight₂ := p.comparisonPrior k s₁ m h b
      finite := matchingMeshCoupling_finite σ (p.normalizedDomainBase k h g b) hδ Q
      sheet₁ := f₀.isMatchSheet
      sheet₂ := f₁.isMatchSheet
      src_meas := fun i => (f₀.atom_measurable i).preimage measurable_fst
      wit_meas := fun i => (f₁.atom_measurable i).preimage measurable_fst
      point_meas := measurable_snd
      lab_eq := ?_
      point_mem := ?_
      error_pos := hE
      near_src := ?_
      near_wit := ?_
      K_nonneg := ?_
      weight₁_nonneg := fun c => (p.comparisonPrior_pos hN c).le
      weight₂_nonneg := fun c => (p.comparisonPrior_pos hN c).le
      density_src := ?_
      density_wit := ?_ }
  · have heq : ∀ᵐ ω ∂σ, f₀.key (f₀.selector ω) = f₁.key (f₁.selector ω) := by
      filter_upwards [f₀.key_ae, f₁.key_ae] with ω h₀ h₁
      exact h₀.trans h₁.symm
    exact matchingMeshCoupling_ae_original σ (p.normalizedDomainBase k h g b) hZ hδ Q hcover heq
  · exact matchingMeshCoupling_norm σ (p.normalizedDomainBase k h g b) hZ hδ hδsmall Q hcover
      (Filter.Eventually.of_forall (p.normalizedDomainBase_inner hh hg hb hmove))
  · exact (f₀.matching_near hbase hδ hη hη1 hK hB hh hb hcoeff₀ htime htrans₀ Q hcover).mono
      (fun _ hz => hz.trans herror₀)
  · exact (f₁.matching_near hbase hδ hη hη1 hK hB hh hb hcoeff₁ htime htrans₁ Q hcover).mono
      (fun _ hz => hz.trans herror₁)
  · dsimp [Parent.projectedComparisonDensity]
    positivity
  · exact f₀.matching_density hbase hδ hN hH0 hh hb Q hcover hcell₀
  · exact f₁.matching_density hbase hδ hN hH0 hh hb Q hcover hcell₁

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
