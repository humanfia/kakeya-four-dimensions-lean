-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/LocalProjection.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/LocalProjection.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.NormalizedProjection

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MeasureTheory Set

/-- The common local comparison base, applied after the old moving frame. -/
noncomputable def localComparisonBase (a : EuclideanSpace ℝ (Fin 3)) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) := r⁻¹ • (x - a)

theorem measurable_localComparisonBase (a : EuclideanSpace ℝ (Fin 3)) (r : ℝ) :
    Measurable (localComparisonBase a r) := by unfold localComparisonBase; fun_prop

/-- Recentering and isotropic local normalization have the exact forward volume
factor r^3. The radius can be chosen independently of the original law. -/
theorem map_volume_localComparisonBase (a : EuclideanSpace ℝ (Fin 3)) {r : ℝ}
    (hr : 0 < r) : (volume : Measure (EuclideanSpace ℝ (Fin 3))).map (localComparisonBase a r) =
      ENNReal.ofReal (r ^ 3) • volume := by
  have he : localComparisonBase a r =
      (fun x : EuclideanSpace ℝ (Fin 3) => r⁻¹ • x) ∘ (fun x => x + -a) := by
    funext x
    simp only [localComparisonBase, Function.comp_apply, sub_eq_add_neg]
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop), map_add_right_eq_self,
    Measure.map_addHaar_smul volume (inv_ne_zero hr.ne')]
  simp only [finrank_euclideanSpace_fin, inv_pow, inv_inv, abs_of_nonneg (pow_nonneg hr.le 3)]

/-- Local normalization keeps the same incidence mass and multiplies its base
ceiling by exactly r^3. -/
theorem local_comparison_base_law_le (μ : Measure (EuclideanSpace ℝ (Fin 3)))
    (H : ENNReal) (hcap : μ ≤ H • volume) (a : EuclideanSpace ℝ (Fin 3)) {r : ℝ}
    (hr : 0 < r) : μ.map (localComparisonBase a r) ≤
      (H * ENNReal.ofReal (r ^ 3)) • volume := by
  calc
    _ ≤ (H • (volume : Measure (EuclideanSpace ℝ (Fin 3)))).map (localComparisonBase a r) :=
      Measure.map_mono hcap (measurable_localComparisonBase a r)
    _ = H • (volume : Measure (EuclideanSpace ℝ (Fin 3))).map (localComparisonBase a r) :=
      Measure.map_smul _ (measurable_localComparisonBase a r).aemeasurable
    _ = _ := by rw [map_volume_localComparisonBase a hr, smul_smul]

/-- The complete old moving-frame and local normalization cap for the original
base law, displaying its time, frame and local-radius factors. -/
theorem normalized_local_base_law_le (μ : Measure (EuclideanSpace ℝ (Fin 3)))
    (H : ENNReal) (hcap : μ ≤ H • volume)
    (t0 q : ℝ) (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (hq : 0 < q) (hQ : Q.det ≠ 0) (a : EuclideanSpace ℝ (Fin 3)) {r : ℝ} (hr : 0 < r) :
    μ.map ((localComparisonBase a r) ∘
      (Submission.Obl.k4_dyadic_crop_affine_laws.Framework.chartBaseEquiv
        t0 q c u Q hq.ne' hQ).symm) ≤
      (H * ENNReal.ofReal (q * |Q.det|) * ENNReal.ofReal (r ^ 3)) • volume := by
  rw [← Measure.map_map (measurable_localComparisonBase a r) (by fun_prop)]
  exact local_comparison_base_law_le _ _
    (normalized_base_law_le μ H hcap t0 q c u Q hq hQ) a hr

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
