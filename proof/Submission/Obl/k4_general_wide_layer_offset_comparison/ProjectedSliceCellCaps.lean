import Submission.Obl.k4_general_wide_layer_offset_comparison.SelectedProjectedSlices
import Submission.Obl.k4_general_wide_layer_offset_comparison.NormalizedBandCaps

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ProjectedSliceCellCaps.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial
open scoped ENNReal

noncomputable section

namespace ProjectedLayer

variable {α : Type} [MeasurableSpace α]

/-- The actual original source slices satisfy the normalized two-dimensional
cell ceiling needed by the matching lift. The signal and palette are both
kept at the original incidence; only the projected quadratic is resolved. -/
theorem activeSlice_cell_cap (A : ProjectedLayer α) (p : Parent α) (hbase : p.Basic)
    {k : ℕ} {s m H h g b r δ B V : ℝ} (hA : A.Valid p k s m H)
    (hN : 1 < p.N k) (hK : 1 ≤ p.K k) (hd : 0 ≤ p.d) (hs : 0 ≤ s)
    (hH : 1 ≤ H) (hr : 0 ≤ r) (hB : 0 ≤ B)
    (hh : 0 < h) (hg : 0 < g) (hb : 0 < b) (hδ : 0 < δ) (hV : 0 ≤ V)
    (hVg : p.K k + g ≤ V) (hVχ : p.K k + p.N k ^ (-m) ≤ V)
    (hcoeff : ∀ i e, |(A.G i).coeff e| ≤ B)
    (hresolution : 54 * B * (p.K k + 1) ^ 4 * p.N k ^ (-r) ≤ p.N k ^ (-s))
    (hdtime : p.N k ^ (-r) ≤ (32 * h) * δ)
    (hdχ : p.N k ^ (-r) ≤ 2 * p.N k ^ (-m))
    (hdb : p.N k ^ (-r) ≤ (32 * b) * δ)
    (hmχ : V * p.N k ^ (-r) ≤ 2 * p.N k ^ (-m))
    (hmb : V * p.N k ^ (-r) ≤ (32 * b) * δ)
    (D : Fin A.count → Finset (ℤ × ℤ × ℤ)) (σ : Measure (α × ℝ))
    (hσ : σ ≤ p.μ k) (e : A.ActiveSlice p k h g b D σ)
    (hcap : ∀ t : ℝ, 0 ≤ t → t ≤ s → ∀ (c : Fin 3 → ℤ) (j v₁ : ℤ),
      p.μ k {ω | p.z k (p.N k) r ω = c ∧
        ⌊eval (p.x k ω.1 ω.2) (p.P k) / (p.N k ^ (-t))⌋ = j ∧
        ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v₁} ≤
      ENNReal.ofReal (p.K k * p.N k ^ (-3 * r - p.d * t)) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v₁})
    (cell : Fin 2 → ℤ) :
    σ {ω | meshCode2 δ (p.normalizedDomainBase k h g b ω) = cell ∧
      ω ∈ A.goodSliceEvent p k h g b D e.val} ≤
      (ENNReal.ofReal (8400 * p.K k ^ 2 * p.N k ^ (-m) *
        (32 * h) * (32 * b) * (H * p.N k ^ (-s)) ^ p.d) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = A.tag e.val.1 0}) *
          ENNReal.ofReal (δ ^ 2) := by
  have hNp : 0 < p.N k := zero_lt_one.trans hN
  have hscale := Real.rpow_pos_of_pos hNp (-s)
  have hthick : 0 < H * p.N k ^ (-s) := mul_pos (zero_lt_one.trans_le hH) hscale
  have hmin : p.N k ^ (-s) ≤ H * p.N k ^ (-s) := by nlinarith
  have ha := A.activeSlice_anchor_bounds p hA hNp hh hg hb σ e
  apply p.normalized_band_cell_cap hbase hN hK hd hs hthick hmin hδ
    (by positivity) (by positivity) hV hdtime hdχ hdb hmχ hmb
    (domainTime h e.val.2.val) (domainIntercept h g b e.val.2.val)
    (domainVelocity g e.val.2.val) (A.tag e.val.1 1) (A.tag e.val.1 0)
    (ha.2.2.2.trans hVχ) (ha.2.2.1.trans hVg) (A.G e.val.1) σ hσ _ cell
  · intro ω hω
    have hc := A.slicedEvent_code p hA D e.val hω.2.1
    have hdomain : p.domainCode k h g b ω = e.val.2.val := congrArg Prod.snd hc
    refine ⟨hω.2.2.1, congrArg (fun c => c.1 1) hc,
      congrArg (fun c => c.1 0) hc, ?_⟩
    simpa only [p.normalizedDomainBase_on_code hdomain] using hω.1
  · intro ω hω
    exact A.slicedEvent_fit p hA D e.val hω.2.1
  · intro ω hω y hy
    exact p.projected_variation_on_good hN.le hK hr hB (A.G e.val.1)
      ((hA.2.2.2.2.2.1 e.val.1).2.1) (hcoeff e.val.1) hresolution hω.2.2 y hy
  · exact hcap

end ProjectedLayer
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
