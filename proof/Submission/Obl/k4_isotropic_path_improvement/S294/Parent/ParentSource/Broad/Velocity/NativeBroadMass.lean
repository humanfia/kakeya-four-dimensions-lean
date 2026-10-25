-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Velocity.NativeBroadMass, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Velocity/NativeBroadMass.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Velocity/NativeBroadMass.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit d78c43c7c261;
-- source Submission/Obl/k4_isotropic_path_improvement/NativeBroadMass.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.CellBreadth
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.QuadraticVelocity

/-!
Apply the native Kakeya obstruction to precisely the genuinely broad
physical states, leaving all other state laws zero. The resulting moment
bounds their actual mass in one unchanged original incidence law.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity

open MeasureTheory Set
open SourceGeometry
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Filling
open scoped ENNReal
open Submission.Obl.k4_mk_grid_transfer

noncomputable section

variable {X : Type*} [MeasurableSpace X]

theorem anisotropic_native_broad_code_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : Type*} [MeasurableSpace X],
      ∀ (m : ℕ) (z : Fin m → Fin 4 → ℤ), Function.Injective z →
      ∀ (ν : Measure X) [IsFiniteMeasure ν]
        (P : X → MvPolynomial (Fin 4) ℝ) (p v : X → Fin 4 → ℝ)
        (A B D : X → ℝ) (s width K baseMesh fine ρ c M d : ℝ)
        (G : X × ℝ → ENNReal), Measurable G →
      ∀ [IsFiniteMeasure ((ν.prod volume).withDensity G)]
        (code : X × ℝ → Fin m), Measurable code →
      0 < K → 0 < baseMesh → baseMesh ≤ fine → 0 < ρ → 0 ≤ c →
      (∀ x, v x 0 = 1) →
      (∀ x t, MvPolynomial.eval (fun j => p x j + t * v x j) (P x) =
        A x * t ^ 2 + B x * t + D x) →
      (∀ x t, t ∈ Icc (0 : ℝ) 1 →
        |MvPolynomial.eval (fun j => p x j + t * v x j) (P x)| ≤ K) →
      Measurable (fun x => baseMesh⁻¹ • heightScale (baseMesh / fine) (nativePhysicalCurve (P x) (p x) (v x) s)) →
      Measurable (fun x => liftedVector (fun j => v x j.castSucc) (2 * A x * s + B x)) →
      8 * K * width ^ 2 < fine → 32 * K * width ≤ ρ / 2 →
      (∀ x t, G (x, t) ≤ ENNReal.ofReal K) →
      (∀ x t, G (x, t) ≠ 0 → |t - s| ≤ width ∧
        baseMesh⁻¹ • heightScale (baseMesh / fine) (nativePhysicalCurve (P x) (p x) (v x) t) ∈ latticeCell (z (code (x, t)))) →
      ν.real univ ≤ K * M / fine ^ ((2 : ℝ) / 3) →
      (m : ℝ) ≤ K * (fine ^ ((2 : ℝ) / 3) / baseMesh) ^ 3 * (fine ^ ((2 : ℝ) / 3) / fine) ^ d →
      (c * ρ / 4) ^ 4 *
        (((ν.prod volume).withDensity G).real {pt | cellBroad ((ν.prod volume).withDensity G) code
          (fun q => unitTangent (liftedVector (fun j => v q.1 j.castSucc)
            (2 * A q.1 * q.2 + B q.1))) ρ c (code pt)}) ^ 4 ≤
        256 * C ^ 3 * K ^ 9 * M ^ 4 * fine ^ ((1 - d) / 3) := by
  obtain ⟨C, hC, hbudget⟩ := anisotropic_native_broad_occupation_moment
  refine ⟨C, hC, ?_⟩
  intro X instX m z hz ν hν P p v A B D s width K baseMesh fine ρ c M d G hG hμ code hcode
    hK hbaseMesh hmesh hρ hc hv hquad hwhole ha hd hsmall hdir hceil hsupp hprior hcount
  classical
  let μ := (ν.prod volume).withDensity G
  let dir (q : X × ℝ) := unitTangent (liftedVector (fun j => v q.1 j.castSucc)
    (2 * A q.1 * q.2 + B q.1))
  let Broad (i : Fin m) := cellBroad μ code dir ρ c i
  let F (i : Fin m) := if Broad i then (code ⁻¹' {i}).indicator G else 0
  have hcell (i : Fin m) : MeasurableSet (code ⁻¹' {i}) := hcode (measurableSet_singleton i)
  have hF (i : Fin m) : Measurable (F i) := by
    dsimp only [F]
    split_ifs
    · exact hG.indicator (hcell i)
    · exact measurable_const
  have hlaw (i : Fin m) (hi : Broad i) :
      (ν.prod volume).withDensity (F i) = μ.restrict (code ⁻¹' {i}) := by
    dsimp only [F]
    rw [ite_eq_left hi, withDensity_indicator (hcell i), ← restrict_withDensity (hcell i) G]
  have hzero (i : Fin m) (hi : ¬ Broad i) : (ν.prod volume).withDensity (F i) = 0 := by
    simp only [F, ite_eq_right hi, withDensity_zero]
  have hbound (i : Fin m) (x : X) (t : ℝ) : F i (x, t) ≤ ENNReal.ofReal K := by
    dsimp only [F]
    split_ifs
    · exact (Set.indicator_le_self _ _ (x, t)).trans (hceil x t)
    · exact zero_le
  have hsupport (i : Fin m) (x : X) (t : ℝ) (ht : F i (x, t) ≠ 0) :
      |t - s| ≤ width ∧ baseMesh⁻¹ • heightScale (baseMesh / fine) (nativePhysicalCurve (P x) (p x) (v x) t) ∈ latticeCell (z i) := by
    have hi : Broad i := by
      by_contra hi
      simp only [F, ite_eq_right hi, Pi.zero_apply, ne_eq, not_true_eq_false] at ht
    have hxi : code (x, t) = i := by
      by_contra hxi
      simp only [F, ite_eq_left hi, Set.indicator_of_notMem (show (x, t) ∉ code ⁻¹' {i} from hxi), ne_eq, not_true_eq_false] at ht
    have hGpos : G (x, t) ≠ 0 := by
      intro h
      simp only [F, ite_eq_left hi, Set.indicator_of_mem (show (x, t) ∈ code ⁻¹' {i} from hxi), h, ne_eq, not_true_eq_false] at ht
    have h := hsupp x t hGpos
    simpa only [hxi] using h
  have hbroad (i : Fin m) : ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 4)), Module.finrank ℝ V < 4 →
      c * ((ν.prod volume).withDensity (F i)).real univ ≤
        ((ν.prod volume).withDensity (F i)).real {q | ρ ≤ Metric.infDist (dir q) (V : Set _)} := by
    by_cases hi : Broad i
    · rw [hlaw i hi]
      exact hi
    · rw [hzero i hi]
      simp
  have hsum : (∑ i, ((ν.prod volume).withDensity (F i)).real univ) =
      μ.real {q | Broad (code q)} := by
    have hpnt (i : Fin m) : ((ν.prod volume).withDensity (F i)).real univ =
        if Broad i then codeWeight μ code i else 0 := by
      by_cases hi : Broad i
      · rw [hlaw i hi, ite_eq_left hi]
        simp only [codeWeight, measureReal_def, Measure.restrict_apply_univ]
      · rw [hzero i hi, ite_eq_right hi]
        simp
    simp_rw [hpnt]
    exact sum_codeWeight_predicate μ code hcode Broad
  have h := hbudget m z hz ν P p v A B D s width K baseMesh fine ρ c M d F hF hK hbaseMesh hmesh hρ hc hv
    hquad hwhole ha hd hsmall hdir hbound hsupport hbroad hprior hcount
  rwa [hsum] at h

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
