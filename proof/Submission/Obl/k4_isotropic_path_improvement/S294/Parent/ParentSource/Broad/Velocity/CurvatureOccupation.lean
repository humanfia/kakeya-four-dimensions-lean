-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Velocity.CurvatureOccupation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Velocity/CurvatureOccupation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit 2f02dabfaa4891833d78772b63f6d98e404e9c6c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Velocity/CurvatureOccupation.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o265, Broad/Velocity/QuadraticVelocity.lean,
-- inherited on x1027 from o106/x0352, commit 5bf2ec7212f0.
-- Existing arbitrary-prior occupation budget is imported. Only the two
-- tangent estimates are changed to use the actual leading coefficient.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.QuadraticVelocity
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.CurvatureTubes

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4Homogenization
open Submission.Obl.k4_mk_grid_transfer

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- A support deficit bounds the original mass of broad physical cells.
The two remaining geometric inputs are the enclosing-cube prior cap and
the hereditary occupied-cell count. -/
theorem anisotropic_native_broad_occupation_moment_of_curvature :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : Type*} [MeasurableSpace X],
      ∀ (m : ℕ) (z : Fin m → Fin 4 → ℤ), Function.Injective z →
      ∀ (ν : Measure X) [IsFiniteMeasure ν]
        (P : X → MvPolynomial (Fin 4) ℝ) (p v : X → Fin 4 → ℝ)
        (A B D : X → ℝ) (s width K baseMesh fine ρ c M d : ℝ)
        (F : Fin m → X × ℝ → ℝ≥0∞),
      (∀ q, Measurable (F q)) → 0 < K → 0 < baseMesh → baseMesh ≤ fine → 0 < ρ → 0 ≤ c →
      (∀ x, v x 0 = 1) →
      (∀ x t, MvPolynomial.eval (fun j => p x j + t * v x j) (P x) =
        A x * t ^ 2 + B x * t + D x) →
      (∀ x, |A x| ≤ 8 * K) →
      Measurable (fun x => baseMesh⁻¹ • heightScale (baseMesh / fine) (nativePhysicalCurve (P x) (p x) (v x) s)) →
      Measurable (fun x => liftedVector (fun j => v x j.castSucc) (2 * A x * s + B x)) →
      8 * K * width ^ 2 < fine → 32 * K * width ≤ ρ / 2 →
      (∀ q x t, F q (x, t) ≤ ENNReal.ofReal K) →
      (∀ q x t, F q (x, t) ≠ 0 → |t - s| ≤ width ∧
        baseMesh⁻¹ • heightScale (baseMesh / fine) (nativePhysicalCurve (P x) (p x) (v x) t) ∈ latticeCell (z q)) →
      (∀ q : Fin m, ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 4)), Module.finrank ℝ V < 4 →
        c * ((ν.prod volume).withDensity (F q)).real univ ≤
          ((ν.prod volume).withDensity (F q)).real {pt |
            ρ ≤ Metric.infDist (unitTangent
              (liftedVector (fun j => v pt.1 j.castSucc) (2 * A pt.1 * pt.2 + B pt.1)))
                (V : Set _)}) →
      ν.real univ ≤ K * M / fine ^ ((2 : ℝ) / 3) →
      (m : ℝ) ≤ K * (fine ^ ((2 : ℝ) / 3) / baseMesh) ^ 3 * (fine ^ ((2 : ℝ) / 3) / fine) ^ d →
      (c * ρ / 4) ^ 4 * (∑ q : Fin m, ((ν.prod volume).withDensity (F q)).real univ) ^ 4 ≤
        256 * C ^ 3 * K ^ 9 * M ^ 4 * fine ^ ((1 - d) / 3) := by
  obtain ⟨C, hC, hbudget⟩ := anisotropic_broad_occupation_mass_power_bound
  refine ⟨C, hC, ?_⟩
  intro X instX m z hz ν hν P p v A B D s width K baseMesh fine ρ c M d F hF hK hbaseMesh hmesh hρ hc
    hv hquad hcurvature ha hd hsmall hdir hdensity hsupp hbroad hprior hcount
  have hfine : 0 < fine := hbaseMesh.trans_le hmesh
  let anchor (x : X) := baseMesh⁻¹ • heightScale (baseMesh / fine) (nativePhysicalCurve (P x) (p x) (v x) s)
  let e (x : X) := unitTangent (liftedVector (fun j => v x j.castSucc) (2 * A x * s + B x))
  have he : Measurable e := measurable_unitTangent hd
  have hcurve (x : X) (t : ℝ) : nativePhysicalCurve (P x) (p x) (v x) t =
      quadraticLift (fun j => p x j.castSucc) (fun j => v x j.castSucc) (A x) (B x) (D x) t := by
    simp only [nativePhysicalCurve, quadraticLift, hquad]
  have hunit (x : X) : ‖e x‖ = 1 := by
    apply norm_unitTangent
    exact norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one
      (norm_liftedVector_ge_one (fun j => v x j.castSucc) (2 * A x * s + B x) (hv x)))
  have hsets (q : Fin m) : MeasurableSet {x | latticePoint (z q) ∈ lineTube 3 (anchor x) (heightUnit (baseMesh / fine) (e x))} :=
    measurableSet_line_parameter_event 3 (latticePoint (z q)) ha ((measurable_heightUnit (baseMesh / fine)).comp he)
  have hduration (q : Fin m) (x : X) :
      incidenceDuration volume (F q) univ x ≤ ENNReal.ofReal (K * baseMesh) := by
    simpa only [incidenceDuration, Measure.restrict_univ] using
      cell_duration_le (fun t => heightScale (baseMesh / fine)
        (nativePhysicalCurve (P x) (p x) (v x) t)) (p x 0) K baseMesh hK.le hbaseMesh
        (by intro t; simp [heightScale, nativePhysicalCurve, liftedVector, hv x])
        (z q) (fun t => F q (x, t)) (hdensity q x) (fun t ht => (hsupp q x t ht).2)
  have htube (q : Fin m) (x : X) (t : ℝ) (ht : F q (x, t) ≠ 0) :
      latticePoint (z q) ∈ lineTube 3 (anchor x) (heightUnit (baseMesh / fine) (e x)) := by
    dsimp [anchor, e]
    rw [hcurve x s]
    apply anisotropic_quadratic_lattice_tangent_tube_of_curvature (fun j => p x j.castSucc)
      (fun j => v x j.castSucc) (A x) (B x) (D x) K width baseMesh fine s t
      hK.le hbaseMesh hfine (hv x) (hcurvature x) (hsupp q x t ht).1 hsmall (z q)
    rw [← hcurve x t]
    exact (hsupp q x t ht).2
  have hfixed (q : Fin m) : ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 4)),
      Module.finrank ℝ V < 4 → c * (occupationMarginal ν volume (F q)).real univ ≤
        (occupationMarginal ν volume (F q)).real {x | ρ / 2 ≤ Metric.infDist (e x) (V : Set _)} := by
    let μ := (ν.prod volume).withDensity (F q)
    have : IsFiniteMeasure (occupationMarginal ν volume (F q)) :=
      occupationMarginal_finite ν volume (hF q) (K * baseMesh)
        (Filter.Eventually.of_forall (hduration q))
    have : IsFiniteMeasure μ := by
      constructor
      rw [← occupationMarginal_univ ν volume (F q)]
      exact measure_lt_top _ _
    have hclose : ∀ᵐ pt ∂μ,
        ‖unitTangent (liftedVector (fun j => v pt.1 j.castSucc)
          (2 * A pt.1 * pt.2 + B pt.1)) - e pt.1‖ ≤ ρ / 2 := by
      apply (ae_withDensity_iff (hF q)).mpr
      apply Filter.Eventually.of_forall
      intro pt hpt
      exact ((quadratic_unit_tangent_change_of_curvature (fun j => v pt.1 j.castSucc)
        (A pt.1) (B pt.1) K s pt.2 (hv pt.1) (hcurvature pt.1)).trans
          (mul_le_mul_of_nonneg_left (hsupp q pt.1 pt.2 hpt).1 (by positivity))).trans hdir
    have h := map_fst_breadth_transfer μ (fun pt => unitTangent
      (liftedVector (fun j => v pt.1 j.castSucc) (2 * A pt.1 * pt.2 + B pt.1))) e
      he ρ (ρ / 2) c hclose (hbroad q)
    simpa only [occupationMarginal, μ, show ρ - ρ / 2 = ρ / 2 by ring] using h
  have h := hbudget m z hz ν volume F hF anchor e he hunit (ρ / 2) c K baseMesh fine M d
    (by positivity) hc hK hbaseMesh hmesh hsets (fun q => Filter.Eventually.of_forall (hduration q))
    htube hfixed hprior hcount
  simpa only [show c * (ρ / 2) / 2 = c * ρ / 4 by ring] using h

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
