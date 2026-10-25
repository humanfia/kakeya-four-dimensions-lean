import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedSourceAtlas
import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedSliceDensities
import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedChartVariation

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/SmoothedProjectedAtlas.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial
open scoped ENNReal
open Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

noncomputable section

namespace ProjectedLayer.SourceAtlas

variable {α : Type} [MeasurableSpace α] {A : ProjectedLayer α} {p : Parent α}
    {k : ℕ} {s m H h g b : ℝ} {σ : Measure (α × ℝ)}
    (f : A.SourceAtlas p k s m H h g b σ)

/-- The smoothed base and the entire original source live in the same law.
The law is independent of which projected color labels the source. -/
def matchingLaw (_f : A.SourceAtlas p k s m H h g b σ) (δ : ℝ) (Q : Finset (Fin 2 → ℤ)) :
    Measure ((α × ℝ) × EuclideanSpace ℝ (Fin 3)) :=
  matchingMeshCoupling σ (p.normalizedDomainBase k h g b) δ Q

/-- Every actual projected chart remains close to the ORIGINAL native
signal after smoothing its base. -/
theorem matching_near [IsFiniteMeasure σ] (hbase : p.Basic)
    {δ η B : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hK : 1 ≤ p.K k) (hB : 0 ≤ B) (hh : 0 < h) (hb : 0 < b)
    (hcoeff : ∀ i e, |(A.G i).coeff e| ≤ B)
    (htime : (32 * h) * δ ≤ η)
    (htrans : ∀ e : A.ActiveSlice p k h g b f.domains σ,
      (|domainVelocity g e.val.2.val| * (32 * h) + 32 * b) * δ ≤ η)
    (Q : Finset (Fin 2 → ℤ))
    (hcover : ∀ᵐ ω ∂σ, meshCode2 δ (p.normalizedDomainBase k h g b ω) ∈ Q) :
    ∀ᵐ z ∂f.matchingLaw δ Q,
      ‖f.sheet (f.selector z.1) (emb z.2) -
        (eval (p.x k z.1.1 z.1.2) (p.P k) : ℂ)‖ ≤
          H * p.N k ^ (-s) + 54 * B * (p.K k + 1) ^ 4 * η := by
  have hZ := p.measurable_normalizedDomainBase hbase k h g b
  have horig := matchingMeshCoupling_ae_original σ (p.normalizedDomainBase k h g b)
    hZ hδ Q hcover f.selected_source_ae
  filter_upwards [horig, matchingMeshCoupling_close σ (p.normalizedDomainBase k h g b)
    hZ hδ Q] with z ho hc
  obtain ⟨e, hsel, he⟩ := ho
  have hcode : p.domainCode k h g b z.1 = e.val.2.val :=
    congrArg Prod.snd (A.slicedEvent_code p f.valid f.domains e.val he.1)
  have hv := p.projected_domain_jitter_variation hK hB hh hb hη hη1 (A.G e.val.1)
    ((f.valid.2.2.2.2.2.1 e.val.1).2.1) (hcoeff e.val.1) he.2 e.val.2.val hcode
    htime (htrans e) (fun i => z.2 i) hc
  have hs := A.slicedEvent_fit p f.valid f.domains e.val he.1
  rw [hsel]
  change ‖polynomialMatchSheet (A.sliceChart h g b e.val) (emb z.2) -
    (eval (p.x k z.1.1 z.1.2) (p.P k) : ℂ)‖ ≤ _
  rw [polynomialMatchSheet_real, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |eval (fun i => z.2 i) (A.sliceChart h g b e.val) -
          eval ![z.1.2, (p.x k z.1.1 z.1.2) 2] (A.G e.val.1)| +
        |eval ![z.1.2, (p.x k z.1.1 z.1.2) 2] (A.G e.val.1) -
          eval (p.x k z.1.1 z.1.2) (p.P k)| := abs_sub_le _ _ _
    _ ≤ 54 * B * (p.K k + 1) ^ 4 * η + H * p.N k ^ (-s) :=
      add_le_add (by simpa only [ProjectedLayer.sliceChart, abs_sub_comm] using hv)
        (by simpa only [abs_sub_comm] using hs)
    _ = _ := add_comm _ _

/-- The literal original-source mesh inequality, before any smoothing. -/
def CellCeiling (δ : ℝ) (Q : Finset (Fin 2 → ℤ)) : Prop :=
  ∀ e : A.ActiveSlice p k h g b f.domains σ, ∀ cell ∈ Q,
    σ {ω | meshCode2 δ (p.normalizedDomainBase k h g b ω) = cell ∧
      ω ∈ A.goodSliceEvent p k h g b f.domains e.val} ≤
      (ENNReal.ofReal (8400 * p.K k ^ 2 * p.N k ^ (-m) *
        (32 * h) * (32 * b) * (H * p.N k ^ (-s)) ^ p.d) *
        p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = A.tag e.val.1 0}) *
          ENNReal.ofReal (δ ^ 2)

/-- All selected index atoms have exact original-prior density ceilings,
including the null off-cover index. -/
theorem matching_density [IsFiniteMeasure σ] (hbase : p.Basic)
    {δ : ℝ} (hδ : 0 < δ) (hN : 0 < p.N k) (hH : 0 ≤ H)
    (hh : 0 < h) (hb : 0 < b) (Q : Finset (Fin 2 → ℤ))
    (hcover : ∀ᵐ ω ∂σ, meshCode2 δ (p.normalizedDomainBase k h g b ω) ∈ Q)
    (hcap : f.CellCeiling δ Q)
    (i : f.Index) (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : MeasurableSet U) :
    f.matchingLaw δ Q {z | f.selector z.1 = i ∧ z.2 ∈ U} ≤
      ENNReal.ofReal (p.projectedComparisonDensity k H *
        p.comparisonPrior k s m h b (f.key i)) * volume U := by
  cases i with
  | some e =>
    exact A.activeSlice_matching_density p hbase hN hH hh hb hδ f.domains σ
      f.disjoint_event f.measurable_event Q e (f.palette_positive e) (hcap e) U hU
  | none =>
    have hnull : f.matchingLaw δ Q (Prod.fst ⁻¹' {ω | f.selector ω = none}) = 0 := by
      rw [← Measure.map_apply measurable_fst (f.atom_measurable none),
        matchingLaw, matchingMeshCoupling_fst σ (p.normalizedDomainBase k h g b)
          (p.measurable_normalizedDomainBase hbase k h g b) hδ Q hcover]
      exact f.off_cover_null
    exact (measure_mono (fun _ hz => hz.1)).trans (hnull.le.trans zero_le)

end ProjectedLayer.SourceAtlas
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
