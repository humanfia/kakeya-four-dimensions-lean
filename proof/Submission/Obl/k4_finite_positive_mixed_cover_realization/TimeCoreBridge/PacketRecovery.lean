-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/PacketRecovery.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/PacketRecovery.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.MatchingRecovery
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.PosteriorBase
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.IncidenceRecovery

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MeasureTheory Set Finset
open Submission.Lib.K4OriginalLists

/-- Packet-level recovery at the original observation: every loss is precisely the
separated-pair error, and every finite jet bin is merged before lists are maximized. -/
theorem packet_original_lists {n : ℕ} {ι X Z : Type*} [Fintype ι]
    [MeasurableSpace X] [MeasurableSpace Z]
    (f : Fin n → Complex3 → ℂ) (jet : Fin n → ι → ℝ) (width : ι → ℝ)
    (hw : ∀ i, 0 < width i) (R M ε : ℝ)
    (hjet : ∀ a b, (∀ x : Real3, ‖x‖ ≤ (1 : ℝ) / 2 →
      ‖f a (emb x) - f b (emb x)‖ ≤ M * R ^ (-ε)) →
      ∀ i, |jet a i - jet b i| ≤ width i)
    (ρ : Measure X) (p : X → Fin n → ℝ)
    (hpmeas : ∀ a, Measurable (fun x => p x a))
    (hpint : ∀ a, Integrable (fun x => p x a) ρ) (hp : ∀ x a, 0 ≤ p x a)
    (μ : Fin n → Measure Z) (O : Z → X) (hO : Measurable O)
    (hlaw : ∀ a, ρ.withDensity (fun x => ENNReal.ofReal (p x a)) = (μ a).map O)
    (base : X → Real3) (hb : Measurable base) (lam : ℝ)
    (htotal : ∑ a, μ a univ ≤ ENNReal.ofReal lam)
    (hsupport : posteriorBasePairLaw ρ p base {q | ‖q.2‖ ≤ (1 : ℝ) / 2 ∧
      ‖f q.1.1 (emb q.2) - f q.1.2 (emb q.2)‖ ≤ M * R ^ (-1 + ε)}ᶜ = 0)
    (err : ENNReal)
    (hbad : posteriorBasePairLaw ρ p base (badPairs f f R M ε) ≤ err) :
    ∃ L : X → Finset (binLabels width jet), MeasurableLists L ∧
      (∀ x, (L x).card ≤ 7 ^ Fintype.card ι) ∧
      (∑ a, μ a univ) ≤
        (∑ a, μ a {z | mergedLabel width jet a ∈ L (O z)}) + err := by
  classical
  let s := binLabels width jet
  let label : Fin n → s := mergedLabel width jet
  let neighbors : s → Finset s := neighboringLabels s
  let ν := posteriorBasePairLaw ρ p base
  let E : Set ((Fin n × Fin n) × Real3) :=
    {q | ∀ i, |binVector width jet q.1.1 i - binVector width jet q.1.2 i| ≤ 1}
  let G : Set ((Fin n × Fin n) × X) := {q | label q.1.2 ∈ neighbors (label q.1.1)}
  have hneighbor (a b : Fin n) : label b ∈ neighbors (label a) ↔
      ∀ i, |binVector width jet a i - binVector width jet b i| ≤ 1 := by
    simp only [neighbors, neighboringLabels, Finset.mem_filter, Finset.mem_univ, true_and]
    change (∀ i, |binVector width jet b i - binVector width jet a i| ≤ 1) ↔ _
    constructor <;> intro h i <;> simpa only [abs_sub_comm] using h i
  have htotal_eq : ν univ = ∑ a, μ a univ := by
    dsimp only [ν]
    rw [posteriorBasePairLaw_univ ρ p hpmeas hp base hb]
    apply sum_congr rfl
    intro a _
    rw [hlaw a, Measure.map_apply hO MeasurableSet.univ, preimage_univ]
  have hmass_eq : ν E = posteriorPairLaw ρ p G := by
    calc
      _ = ν {q | label q.1.2 ∈ neighbors (label q.1.1)} := by
        congr 1
        ext q
        exact (hneighbor q.1.1 q.1.2).symm
      _ = _ := posteriorBasePairLaw_indices ρ p base hb
        (fun q => label q.2 ∈ neighbors (label q.1))
  have hcover : (∑ a, μ a univ) ≤ posteriorPairLaw ρ p G + err := by
    have hh : ν univ ≤ ν E + err :=
      (jet_neighbor_pair_cover f jet width hw R M ε hjet ν hsupport).trans
        (add_le_add le_rfl hbad)
    rwa [htotal_eq, hmass_eq] at hh
  have hfin : posteriorPairLaw ρ p G ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    rw [← hmass_eq]
    exact (measure_mono (subset_univ E)).trans ((le_of_eq htotal_eq).trans htotal)
  obtain ⟨L, hL, hLc, hsuccess⟩ := recover_original_incidence_lists ρ p hpmeas hpint hp
    μ O hO hlaw label neighbors (7 ^ Fintype.card ι)
    (card_neighboringLabels s) (posteriorPairLaw ρ p G).toReal
    (by rw [ENNReal.ofReal_toReal hfin])
  rw [ENNReal.ofReal_toReal hfin] at hsuccess
  exact ⟨L, hL, hLc, hcover.trans (add_le_add hsuccess le_rfl)⟩

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
