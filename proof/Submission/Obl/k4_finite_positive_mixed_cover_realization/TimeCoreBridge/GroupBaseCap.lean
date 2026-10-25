-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/GroupBaseCap.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree o173/x0598, commit b7284666,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/GroupBaseCap.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.GroupCoords
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.LocalProjection

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MeasureTheory Set Submission.Lib.K4XInterface
open Submission.Obl.k4_dyadic_crop_affine_laws.Framework

/-- The packet coordinates read from an observation are exactly the accepted
moving-frame measurable equivalence's inverse. -/
theorem normBaseObs_eq_chartBaseEquiv_symm (T j : ℕ)
    (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0)
    (o : EuclideanSpace ℝ (Fin 3) × ℤ) :
    normBaseObs T j c u Q o =
      (chartBaseEquiv ((j : ℝ) / 2 ^ T) (1 / 2 ^ T) c u Q (by positivity) hQ).symm o.1 := by
  let e := chartBaseEquiv ((j : ℝ) / 2 ^ T) (1 / 2 ^ T) c u Q (by positivity) hQ
  let y : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![o.1 1, o.1 2]
  have hz : Matrix.toEuclideanLin Q (zcObs Q c u o) = y - c - o.1 0 • u :=
    toEuclideanLin_inv_cancel Q hQ _
  have hz' (k : Fin 2) : Q k 0 * (zcObs Q c u o) 0 + Q k 1 * (zcObs Q c u o) 1 =
      y k - c k - o.1 0 * u k := by
    have hh := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v k) hz
    simpa only [toEuclideanLin_apply_fin2, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] using hh
  have ht : (j : ℝ) / 2 ^ T + (1 / 2 ^ T) * (2 ^ T * o.1 0 - j) = o.1 0 := by
    field_simp
    ring
  have he : e (normBaseObs T j c u Q o) = o.1 := by
    rw [chartBaseEquiv_apply]
    ext k
    fin_cases k
    · change (j : ℝ) / 2 ^ T + (1 / 2 ^ T) * (2 ^ T * o.1 0 - j) = o.1 0
      exact ht
    · change c 0 + ((j : ℝ) / 2 ^ T + (1 / 2 ^ T) * (2 ^ T * o.1 0 - j)) * u 0 +
        Q 0 0 * (zcObs Q c u o) 0 + Q 0 1 * (zcObs Q c u o) 1 = o.1 1
      rw [ht]
      have hh := hz' 0
      change Q 0 0 * (zcObs Q c u o) 0 + Q 0 1 * (zcObs Q c u o) 1 =
        o.1 1 - c 0 - o.1 0 * u 0 at hh
      linarith
    · change c 1 + ((j : ℝ) / 2 ^ T + (1 / 2 ^ T) * (2 ^ T * o.1 0 - j)) * u 1 +
        Q 1 0 * (zcObs Q c u o) 0 + Q 1 1 * (zcObs Q c u o) 1 = o.1 2
      rw [ht]
      have hh := hz' 1
      change Q 1 0 * (zcObs Q c u o) 0 + Q 1 1 * (zcObs Q c u o) 1 =
        o.1 2 - c 1 - o.1 0 * u 1 at hh
      linarith
  calc
    _ = e.symm (e (normBaseObs T j c u Q o)) := (e.symm_apply_apply _).symm
    _ = _ := congrArg e.symm he

/-- The concrete comparison base of a group has the exact original-law ceiling
H*r^3*abs(det Q)/2^T, including its local radius, frame and time factors. -/
theorem original_group_base_law_le {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (O : Z → EuclideanSpace ℝ (Fin 3) × ℤ) (hO : Measurable O)
    {H : ℝ} (hH : 0 ≤ H)
    (hcap : μ.map (fun z => (O z).1) ≤ ENNReal.ofReal H • volume)
    (T j : ℕ) (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (hQ : Q.det ≠ 0) (v0 : EuclideanSpace ℝ (Fin 3)) {r : ℝ} (hr : 0 < r) :
    μ.map ((groupBase T j c u Q v0 r) ∘ O) ≤
      ENNReal.ofReal (H * r ^ 3 * |Q.det| / 2 ^ T) • volume := by
  have hq : 0 < (1 / (2 : ℝ) ^ T) := by positivity
  let e := chartBaseEquiv ((j : ℝ) / 2 ^ T) (1 / 2 ^ T) c u Q hq.ne' hQ
  have heq : (groupBase T j c u Q v0 r) ∘ O =
      ((localComparisonBase v0 r) ∘ e.symm) ∘ (fun z => (O z).1) := by
    funext z
    change r⁻¹ • (normBaseObs T j c u Q (O z) - v0) =
      r⁻¹ • (e.symm (O z).1 - v0)
    rw [normBaseObs_eq_chartBaseEquiv_symm T j c u Q hQ]
  rw [heq, ← Measure.map_map ((measurable_localComparisonBase v0 r).comp e.symm.measurable) hO.fst]
  have hc := normalized_local_base_law_le (μ.map (fun z => (O z).1)) (ENNReal.ofReal H) hcap
    ((j : ℝ) / 2 ^ T) (1 / 2 ^ T) c u Q hq hQ v0 hr
  have hcoef : ENNReal.ofReal H * ENNReal.ofReal ((1 / (2 : ℝ) ^ T) * |Q.det|) *
      ENNReal.ofReal (r ^ 3) = ENNReal.ofReal (H * r ^ 3 * |Q.det| / 2 ^ T) := by
    rw [← ENNReal.ofReal_mul hH, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [hcoef] at hc
  exact hc

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
