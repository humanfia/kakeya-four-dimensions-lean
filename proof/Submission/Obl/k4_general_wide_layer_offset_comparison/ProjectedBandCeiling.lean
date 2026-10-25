import Submission.Obl.k4_general_wide_layer_offset_comparison.ComparisonBandReturn
import Submission.Obl.k4_general_wide_layer_offset_comparison.ComparisonBandFactors

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ProjectedBandCeiling.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

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

/-- Every queried projected graph has the whole-law band ceiling measured
in the FINE original prior, whichever color supplied the query graph. -/
theorem query_band_ceiling [IsFiniteMeasure σ] (hbase : p.Basic) (hσ : σ ≤ p.μ k)
    {δ η B V r smax sf W : ℝ}
    (hN : 1 < p.N k) (hK : 1 ≤ p.K k) (hd : 0 ≤ p.d) (hd1 : p.d ≤ 1)
    (hH : 1 ≤ H) (hsmax : 0 ≤ smax) (hr : 0 ≤ r) (hB : 0 ≤ B)
    (hh : 0 < h) (hg : 0 < g) (hb : 0 < b) (hmove : h * g ≤ b)
    (hδ : 0 < δ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hV : 0 ≤ V) (hVg : p.K k + g ≤ V) (hVχ : p.K k + p.N k ^ (-m) ≤ V)
    (htime : (32 * h) * δ ≤ η)
    (htrans : ∀ e : Aq.ActiveSlice p k h g b q.domains σ,
      (|domainVelocity g e.val.2.val| * (32 * h) + 32 * b) * δ ≤ η)
    (hcoeff : ∀ i e, |(Aq.G i).coeff e| ≤ B)
    (hresolution : 54 * B * (p.K k + 1) ^ 4 * p.N k ^ (-r) ≤ p.N k ^ (-smax))
    (hdtime : p.N k ^ (-r) ≤ h)
    (hdχ : p.N k ^ (-r) ≤ 2 * p.N k ^ (-m)) (hdb : p.N k ^ (-r) ≤ 2 * b)
    (hmχ : V * p.N k ^ (-r) ≤ 2 * p.N k ^ (-m))
    (hmb : V * p.N k ^ (-r) ≤ 2 * b)
    (hW : 0 < W) (hmin : p.N k ^ (-smax) ≤ 3 * W)
    (herror : 54 * B * (p.K k + 1) ^ 4 * η ≤ W)
    (Q : Finset (Fin 2 → ℤ))
    (hcover : ∀ᵐ ω ∂σ, meshCode2 δ (p.normalizedDomainBase k h g b ω) ∈ Q)
    (hcap : ∀ t : ℝ, 0 ≤ t → t ≤ smax → ∀ (c : Fin 3 → ℤ) (j v₁ : ℤ),
      p.μ k {ω | p.z k (p.N k) r ω = c ∧
        ⌊eval (p.x k ω.1 ω.2) (p.P k) / (p.N k ^ (-t))⌋ = j ∧
        ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v₁} ≤
      ENNReal.ofReal (p.K k * p.N k ^ (-3 * r - p.d * t)) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v₁})
    (i : q.Index) :
    f.matchingLaw δ Q {z | f.key (f.selector z.1) = q.key i ∧
      ‖q.sheet i (emb z.2) - (eval (p.x k z.1.1 z.1.2) (p.P k) : ℂ)‖ ≤ 2 * W} ≤
      ENNReal.ofReal (p.projectedComparisonDensity k H *
        p.comparisonPrior k sf m h b (q.key i) * (W / p.N k ^ (-sf)) ^ p.d) := by
  cases i with
  | none =>
    have hz := f.matching_key_none_null hbase hδ Q hcover
    have hzero : f.matchingLaw δ Q {z | f.key (f.selector z.1) = q.key none ∧
        ‖q.sheet none (emb z.2) - (eval (p.x k z.1.1 z.1.2) (p.P k) : ℂ)‖ ≤ 2 * W} = 0 :=
      measure_mono_null (fun _ hp => hp.1) hz
    exact hzero.le.trans zero_le
  | some e =>
    have ha := Aq.activeSlice_anchor_bounds p q.valid (zero_lt_one.trans hN) hh hg hb σ e
    have hreturn := f.matching_query_band_le q hbase hσ hδ hη hη1 hK hB hh hb e
      (hcoeff e.val.1) htime (htrans e) herror Q hcover
    have hwhole := p.comparisonBand_cap hbase hN hK hd hsmax hr hB hh hg hb hmove hV
      hdtime hdχ hdb hmχ hmb (Aq.tag e.val.1) e.val.2.val
      (ha.2.2.2.trans hVχ) (ha.2.2.1.trans hVg) (Aq.G e.val.1)
      ((q.valid.2.2.2.2.2.1 e.val.1).2.1) (hcoeff e.val.1) hresolution
      (by positivity : 0 < 3 * W) hmin σ hσ hcap
    exact hreturn.trans (hwhole.trans
      (Aq.comparisonBand_factor p hbase (zero_lt_one.trans hN) hH hh hb hW hd hd1 e.val
        (q.palette_positive e)))

end ProjectedLayer.SourceAtlas
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
