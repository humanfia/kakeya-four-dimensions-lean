import Submission.Obl.k4_general_wide_layer_offset_comparison.SmoothedProjectedAtlas
import Submission.Obl.k4_general_wide_layer_offset_comparison.ComparisonBandCaps

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ComparisonBandReturn.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial
open scoped ENNReal
open Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

noncomputable section

namespace ProjectedLayer.SourceAtlas

variable {α : Type} [MeasurableSpace α] {p : Parent α} {A Aq : ProjectedLayer α}
    {k : ℕ} {s sq m H h g b : ℝ} {σ : Measure (α × ℝ)}
    (f : A.SourceAtlas p k s m H h g b σ)
    (q : Aq.SourceAtlas p k sq m H h g b σ)

/-- The unused key has zero mass even after common-base smoothing. -/
theorem matching_key_none_null [IsFiniteMeasure σ] (hbase : p.Basic)
    {δ : ℝ} (hδ : 0 < δ) (Q : Finset (Fin 2 → ℤ))
    (hcover : ∀ᵐ ω ∂σ, meshCode2 δ (p.normalizedDomainBase k h g b ω) ∈ Q) :
    f.matchingLaw δ Q {z | f.key (f.selector z.1) = none} = 0 := by
  have hk := matchingMeshCoupling_ae_original σ (p.normalizedDomainBase k h g b)
    (p.measurable_normalizedDomainBase hbase k h g b) hδ Q hcover f.key_ae
  have hn : ∀ᵐ z ∂f.matchingLaw δ Q, f.key (f.selector z.1) ≠ none := by
    filter_upwards [hk] with z hz
    rw [hz]
    exact Option.some_ne_none _
  simpa only [not_not] using ae_iff.mp hn

/-- A queried band in the smoothed comparison law returns to a whole
ORIGINAL-source code band. Its mass is never divided by an individual
surviving pair or selector mass. -/
theorem matching_query_band_le [IsFiniteMeasure σ] (hbase : p.Basic) (hσ : σ ≤ p.μ k)
    {δ η B W : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hK : 1 ≤ p.K k) (hB : 0 ≤ B) (hh : 0 < h) (hb : 0 < b)
    (e : Aq.ActiveSlice p k h g b q.domains σ)
    (hcoeff : ∀ u, |(Aq.G e.val.1).coeff u| ≤ B)
    (htime : (32 * h) * δ ≤ η)
    (htrans : (|domainVelocity g e.val.2.val| * (32 * h) + 32 * b) * δ ≤ η)
    (herror : 54 * B * (p.K k + 1) ^ 4 * η ≤ W)
    (Q : Finset (Fin 2 → ℤ))
    (hcover : ∀ᵐ ω ∂σ, meshCode2 δ (p.normalizedDomainBase k h g b ω) ∈ Q) :
    f.matchingLaw δ Q {z | f.key (f.selector z.1) = q.key (some e) ∧
      ‖q.sheet (some e) (emb z.2) - (eval (p.x k z.1.1 z.1.2) (p.P k) : ℂ)‖ ≤ 2 * W} ≤
      σ (p.comparisonBand k m h g b (Aq.tag e.val.1) e.val.2.val (Aq.G e.val.1) (3 * W)) := by
  let E := p.comparisonBand k m h g b (Aq.tag e.val.1) e.val.2.val (Aq.G e.val.1) (3 * W)
  have hZ := p.measurable_normalizedDomainBase hbase k h g b
  have hgood : ∀ᵐ ω ∂σ, ω ∈ p.baseGood k :=
    (Parent.Basic.ae_baseGood p hbase k).filter_mono (ae_mono hσ)
  have horig := matchingMeshCoupling_ae_original σ (p.normalizedDomainBase k h g b)
    hZ hδ Q hcover (f.key_ae.and hgood)
  have hsub : {z | f.key (f.selector z.1) = q.key (some e) ∧
      ‖q.sheet (some e) (emb z.2) - (eval (p.x k z.1.1 z.1.2) (p.P k) : ℂ)‖ ≤ 2 * W}
      ≤ᵐ[f.matchingLaw δ Q] Prod.fst ⁻¹' E := by
    filter_upwards [horig, matchingMeshCoupling_close σ (p.normalizedDomainBase k h g b)
      hZ hδ Q] with z ho hc
    intro hz
    have hk := hz.1
    change f.key (f.selector z.1) = some (Aq.sliceComparisonCode e.val) at hk
    have hcode : p.comparisonCode k m h g b z.1 = (Aq.tag e.val.1, e.val.2.val) :=
      Option.some.inj (ho.1.symm.trans hk)
    have hv := p.projected_domain_jitter_variation hK hB hh hb hη hη1 (Aq.G e.val.1)
      ((q.valid.2.2.2.2.2.1 e.val.1).2.1) hcoeff ho.2 e.val.2.val (congrArg Prod.snd hcode)
      htime htrans (fun i => z.2 i) hc
    have hquery := hz.2
    change ‖polynomialMatchSheet (Aq.sliceChart h g b e.val) (emb z.2) -
      (eval (p.x k z.1.1 z.1.2) (p.P k) : ℂ)‖ ≤ 2 * W at hquery
    rw [polynomialMatchSheet_real, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hquery
    refine ⟨ho.2, hcode, ?_⟩
    calc
      _ ≤ |eval (p.x k z.1.1 z.1.2) (p.P k) - eval (fun i => z.2 i) (Aq.sliceChart h g b e.val)| +
          |eval (fun i => z.2 i) (Aq.sliceChart h g b e.val) -
            eval ![z.1.2, (p.x k z.1.1 z.1.2) 2] (Aq.G e.val.1)| := abs_sub_le _ _ _
      _ ≤ 2 * W + 54 * B * (p.K k + 1) ^ 4 * η :=
        add_le_add (by simpa only [abs_sub_comm] using hquery)
          (by simpa only [ProjectedLayer.sliceChart, abs_sub_comm] using hv)
      _ ≤ 3 * W := by linarith
  calc
    _ ≤ f.matchingLaw δ Q (Prod.fst ⁻¹' E) := measure_mono_ae hsub
    _ = σ E := by
      change matchingMeshCoupling σ (p.normalizedDomainBase k h g b) δ Q (Prod.fst ⁻¹' E) = σ E
      rw [← Measure.map_apply measurable_fst (p.measurableSet_comparisonBand hbase _ _ _ _ _ _ _ _ _),
        matchingMeshCoupling_fst σ (p.normalizedDomainBase k h g b) hZ hδ Q hcover]

end ProjectedLayer.SourceAtlas
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
