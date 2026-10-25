/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/SharedTimePolynomial.lean`. Original attributions are retained below. -/
/- Adapted from this LOT tree, o202, session x0698, commit aacc14fa,
   `Submission/Obl/k4_horizontal_subcritical_rate_candidates/SharedTimePolynomial.lean`. Original imports of accepted libraries are retained. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.TimeRestoration
import Submission.Obl.k4_subcritical_corrected_scalar_charts.TimePolynomial

/-!
The shared-time selection in `prop:offcritical-wide`: one indexed trajectory locates a
quadratic, and all paired trajectories are restored at its witnessing times.
-/

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open MeasureTheory Set

lemma exists_shared_time_polynomial {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (ρ : Measure (α × ℝ))
    (b : α → Fin 3 → ℝ) (G : ℝ → ℝ)
    {C m c K δ : ℝ} (hC : 0 < C) (hm : 0 < m) (hmC : m ≤ C)
    (hc : 0 ≤ c) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hdom : ρ ≤ ENNReal.ofReal C • (ν.prod volume))
    {E : Set (α × ℝ)} {T₀ : Set ℝ} (hE : MeasurableSet E)
    (hmass : ENNReal.ofReal m ≤ ρ E)
    (hsub : E ⊆ univ ×ˢ (T₀ ∩ Icc (0 : ℝ) 1))
    (hrestore : ∀ T : Set ℝ, MeasurableSet T → T ⊆ T₀ →
      ENNReal.ofReal c * volume T ≤ ρ (E ∩ (univ ×ˢ T)))
    (hG : ∀ t ∈ T₀, |G t| ≤ K)
    (hfit : ∀ p ∈ E, |(quadraticTimePolynomial (b p.1)).eval p.2 - G p.2| ≤ δ) :
    ∃ l : α, (∀ i, |b l i| ≤ 17 * (48 * C / m) ^ 2 * (K + δ)) ∧
      ENNReal.ofReal (c * m / (2 * C)) ≤
        ρ {p | p ∈ E ∧ |(quadraticTimePolynomial (b l)).eval p.2 - G p.2| ≤ δ} := by
  have hsub₀ : E ⊆ univ ×ˢ T₀ := fun p hp => ⟨trivial, (hsub hp).2.1⟩
  obtain ⟨l, hTm, hTvol, hTmass⟩ :=
    exists_restored_time_witness ν ρ hC hm hc hdom hE hmass hsub₀ hrestore
  have hT₀ : Prod.mk l ⁻¹' E ⊆ T₀ := fun t ht => (hsub ht).2.1
  have hTI : Prod.mk l ⁻¹' E ⊆ Icc (0 : ℝ) 1 := fun t ht => (hsub ht).2.2
  have hη : 0 < m / (2 * C) := by positivity
  have hη1 : m / (2 * C) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  have hnorm (i : Fin 3) : |b l i| ≤ 17 * (24 / (m / (2 * C))) ^ 2 * (K + δ) :=
    timePolynomial_coeff_bound (b := b l) (G := G) hη hη1 hK hδ
    hTI hTvol (fun t ht => hG t (hT₀ ht)) (fun t ht => hfit (l, t) ht) i
  have hratio : (24 : ℝ) / (m / (2 * C)) = 48 * C / m := by
    field_simp
    ring
  refine ⟨l, ?_, hTmass.trans (measure_mono ?_)⟩
  · intro i
    simpa only [hratio] using hnorm i
  · intro p hp
    exact ⟨hp.1, hfit (l, p.2) hp.2.2⟩

end Submission.Obl.k4_subcritical_corrected_scalar_charts
