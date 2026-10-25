-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/OriginalCandidateCap.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.CandidateMarginal
import Submission.Obl.k4_clean_cover_graph_atlas.DensityCutoff

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory Set MvPolynomial

/-- The candidate base ceiling directly under the original incidence law, after the
pure observation-density tail has been removed. -/
theorem original_candidate_base_ceiling
    (μ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    {δ B U : ℝ} (hδ : 0 < δ) (hB : 0 < B) (hU : 0 < U)
    (hobs : Measurable (obs B δ))
    (g : (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal) (hg : Measurable g)
    (hlaw : μ.map (obs B δ) = (volume.prod Measure.count).withDensity g)
    (V : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (H : ENNReal)
    (hcut : ∀ p ∈ V, g (obs B δ p) ≤ H)
    (hfit : ∀ p ∈ V, |eval (x p.1 p.2) P| ≤ U * δ ∧
      B / U ≤ |eval (x p.1 p.2) (pderiv (3 : Fin 4) P)|)
    (A : Set (EuclideanSpace ℝ (Fin 3))) (hA : MeasurableSet A) :
    μ.restrict V {p | (obs B δ p).1 ∈ A} ≤
      (H * ENNReal.ofReal (16 * (1 + U ^ 2))) * volume A := by
  let ν := (μ.restrict V).map (obs B δ)
  have hcap : ν ≤ H • (volume.prod Measure.count) :=
    map_restrict_density_cutoff_le μ _ _ hobs g hg hlaw H V (fun p hp => hcut p hp)
  have hsupp : ν (polynomialBinSupport P (U * δ) (B / U) (δ / B))ᶜ = 0 := by
    apply map_restrict_compl_eq_zero μ _ hobs V _ (measurableSet_polynomialBinSupport P _ _ _)
    intro p hp
    exact original_obs_mem_candidate_support P hδ hB p (hfit p hp).1 (hfit p hp).2
  have hb := candidate_base_marginal P hP hδ hB hU ν H hcap hsupp A hA
  dsimp only [ν] at hb
  rw [Measure.map_apply hobs (hA.prod MeasurableSet.univ)] at hb
  simpa only [Set.preimage, mem_prod, mem_univ, and_true] using hb

end Submission.Obl.k4_clean_cover_graph_atlas
