-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/CleanCaps.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.CandidateMarginal
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.FiniteInterface
import Submission.Lib.K4ExactProblemOps.Coarsening

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4XInterface

/-- The exact continuous part of every original observation. -/
noncomputable def obsBase (p : (ℕ × (Fin 6 → ℝ)) × ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![p.2, (x p.1 p.2) 1, (x p.1 p.2) 2]

theorem measurable_obsBase : Measurable obsBase := by
  exact measurable_fst.comp (Submission.Lib.K4ExactProblemOps.measurable_obs 1 1)

theorem measurable_obs (B a : ℝ) : Measurable (obs B a) :=
  Submission.Lib.K4ExactProblemOps.measurable_obs B a

/-- A cleaned original observation cap gives the candidate's exact-base cap.
Only the supplied original measure is restricted; no density version is needed. -/
theorem candidate_base_map_cap
    (μ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    {δ B U : ℝ} (hδ : 0 < δ) (hB : 0 < B) (hU : 0 < U)
    (V : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (H : ENNReal)
    (hcap : (μ.restrict V).map (obs B δ) ≤ H • (volume.prod Measure.count))
    (hfit : ∀ p ∈ V, |eval (x p.1 p.2) P| ≤ U * δ ∧
      B / U ≤ |eval (x p.1 p.2) (pderiv (3 : Fin 4) P)|) :
    (μ.restrict V).map obsBase ≤ (H * ENNReal.ofReal (16 * (1 + U ^ 2))) • volume := by
  let S := polynomialBinSupport P (U * δ) (B / U) (δ / B)
  have hS : MeasurableSet S := measurableSet_polynomialBinSupport P _ _ _
  have hsupp : (μ.restrict V) ((obs B δ) ⁻¹' Sᶜ) = 0 := by
    rw [Measure.restrict_apply (hS.compl.preimage (measurable_obs B δ))]
    have he : ((obs B δ) ⁻¹' Sᶜ) ∩ V = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hp.1 (original_obs_mem_candidate_support P hδ hB p (hfit p hp.2).1 (hfit p hp.2).2)
    rw [he, measure_empty]
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.map_apply measurable_obsBase hA, Measure.smul_apply, smul_eq_mul]
  exact Submission.Lib.K4ListedExceptions.observation_base_marginal_bound
    (μ.restrict V) volume Measure.count (obs B δ) (measurable_obs B δ) S hS hsupp hcap
    (count_candidate_support P hP hδ hB hU) A hA

-- Adapted from this LOT tree o194/x0672, 69d09a7b, Outer.lean.
theorem delta_antitone {N r s : ℝ} (hN : 1 ≤ N) (hrs : r ≤ s) : δ N s ≤ δ N r := by
  unfold δ gδ
  apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  apply neg_le_neg
  apply Int.floor_mono
  apply div_le_div_of_nonneg_right _ (Real.log_pos one_lt_two).le
  exact mul_le_mul_of_nonneg_right hrs (Real.log_nonneg hN)

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
