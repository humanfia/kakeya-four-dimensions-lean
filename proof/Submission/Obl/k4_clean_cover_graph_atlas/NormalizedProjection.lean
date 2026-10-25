-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/NormalizedProjection.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.OriginalCandidateCap
import Submission.Obl.k4_clean_cover_graph_atlas.ProjectionMass
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.DensityTransport

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory Set

/-- The setwise original candidate estimate as a domination of base measures. -/
theorem original_candidate_base_law_le
    (μ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    {δ B U : ℝ} (hδ : 0 < δ) (hB : 0 < B) (hU : 0 < U)
    (hobs : Measurable (obs B δ))
    (g : (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal) (hg : Measurable g)
    (hlaw : μ.map (obs B δ) = (volume.prod Measure.count).withDensity g)
    (V : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (H : ENNReal)
    (hcut : ∀ p ∈ V, g (obs B δ p) ≤ H)
    (hfit : ∀ p ∈ V, |MvPolynomial.eval (x p.1 p.2) P| ≤ U * δ ∧
      B / U ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) P)|) :
    (μ.restrict V).map (fun p => (obs B δ p).1) ≤
      (H * ENNReal.ofReal (16 * (1 + U ^ 2))) • volume := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.map_apply hobs.fst hA]
  simpa only [Measure.smul_apply, smul_eq_mul, Set.preimage] using
    original_candidate_base_ceiling μ P hP hδ hB hU hobs g hg hlaw V H hcut hfit A hA

/-- Moving-frame normalization multiplies the original base ceiling by the exact
forward Jacobian; it never introduces an incidence-conditioned prior. -/
theorem normalized_base_law_le (μ : Measure (EuclideanSpace ℝ (Fin 3)))
    (H : ENNReal) (hcap : μ ≤ H • volume)
    (t0 q : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hq : 0 < q) (hQ : Q.det ≠ 0) :
    μ.map (Submission.Obl.k4_dyadic_crop_affine_laws.Framework.chartBaseEquiv
      t0 q c u Q hq.ne' hQ).symm ≤
      (H * ENNReal.ofReal (q * |Q.det|)) • volume := by
  let e := (Submission.Obl.k4_dyadic_crop_affine_laws.Framework.chartBaseEquiv
    t0 q c u Q hq.ne' hQ).symm
  calc
    _ ≤ (H • (volume : Measure (EuclideanSpace ℝ (Fin 3)))).map e :=
      Measure.map_mono hcap e.measurable
    _ = H • (volume : Measure (EuclideanSpace ℝ (Fin 3))).map e :=
      Measure.map_smul _ e.measurable.aemeasurable
    _ = _ := by
      rw [Submission.Obl.k4_dyadic_crop_affine_laws.Framework.map_chartBaseEquiv_symm
        t0 q c u Q hq hQ, smul_smul]

/-- A truncated original candidate of mass `m` has a quantitatively large
normalized projection. The denominator displays every density and Jacobian factor. -/
theorem normalized_candidate_projection_floor
    (μ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    {δ B U H m : ℝ} (hδ : 0 < δ) (hB : 0 < B) (hU : 0 < U) (hH : 0 < H)
    (hobs : Measurable (obs B δ))
    (g : (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal) (hg : Measurable g)
    (hlaw : μ.map (obs B δ) = (volume.prod Measure.count).withDensity g)
    (V : Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hcut : ∀ p ∈ V, g (obs B δ p) ≤ ENNReal.ofReal H)
    (hfit : ∀ p ∈ V, |MvPolynomial.eval (x p.1 p.2) P| ≤ U * δ ∧
      B / U ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) P)|)
    (hmass : ENNReal.ofReal m ≤ μ V)
    (t0 q : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hq : 0 < q) (hQ : Q.det ≠ 0)
    (E : Set (EuclideanSpace ℝ (Fin 3))) (hE : MeasurableSet E)
    (hsupport : ∀ p ∈ V,
      (Submission.Obl.k4_dyadic_crop_affine_laws.Framework.chartBaseEquiv
        t0 q c u Q hq.ne' hQ).symm (obs B δ p).1 ∈ E) :
    ENNReal.ofReal (m / (H * (16 * (1 + U ^ 2)) * (q * |Q.det|))) ≤ volume E := by
  let e := (Submission.Obl.k4_dyadic_crop_affine_laws.Framework.chartBaseEquiv
    t0 q c u Q hq.ne' hQ).symm
  let ν := ((μ.restrict V).map (fun p => (obs B δ p).1)).map e
  have hcap := normalized_base_law_le _ _
    (original_candidate_base_law_le μ P hP hδ hB hU hobs g hg hlaw V _ hcut hfit)
    t0 q c u Q hq hQ
  have hcoef : ENNReal.ofReal H * ENNReal.ofReal (16 * (1 + U ^ 2)) *
      ENNReal.ofReal (q * |Q.det|) =
      ENNReal.ofReal (H * (16 * (1 + U ^ 2)) * (q * |Q.det|)) := by
    rw [← ENNReal.ofReal_mul hH.le, ← ENNReal.ofReal_mul (by positivity)]
  rw [hcoef] at hcap
  have hdet : 0 < |Q.det| := abs_pos.mpr hQ
  apply projection_volume_floor ν volume E hE (by positivity) hcap
  · dsimp only [ν]
    rw [Measure.map_map e.measurable hobs.fst]
    exact map_restrict_compl_eq_zero μ _ (e.measurable.comp hobs.fst) V E hE hsupport
  · simpa only [ν, Measure.map_apply e.measurable MeasurableSet.univ,
      preimage_univ, Measure.map_apply hobs.fst MeasurableSet.univ,
      Measure.restrict_apply_univ] using hmass

end Submission.Obl.k4_clean_cover_graph_atlas
