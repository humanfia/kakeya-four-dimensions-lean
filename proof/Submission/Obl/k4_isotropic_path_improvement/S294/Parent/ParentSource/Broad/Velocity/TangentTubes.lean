-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Velocity.TangentTubes, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Velocity/TangentTubes.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Velocity/TangentTubes.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 5bf2ec7212f0;
-- source Submission/Obl/k4_isotropic_path_improvement/TangentTubes.lean.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry.QuadraticTangents
import Submission.Obl.k4_mk_grid_transfer.Grid

/-!
Affine tangent approximation of a native quadratic gives the exact
radius-three lattice tube incidence required by the Kakeya budget.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry

open Set
open Submission.Obl.k4_mk_grid_transfer

noncomputable section

def unitTangent {n : ℕ} (d : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  ‖d‖⁻¹ • d

theorem norm_unitTangent {n : ℕ} {d : EuclideanSpace ℝ (Fin n)} (hd : d ≠ 0) :
    ‖unitTangent d‖ = 1 := norm_smul_inv_norm hd

theorem measurable_unitTangent {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {d : Ω → EuclideanSpace ℝ (Fin n)} (hd : Measurable d) :
    Measurable (fun x => unitTangent (d x)) := (hd.norm.inv).smul hd

/-- Tube incidence is measurable jointly in the original line parameters. -/
theorem measurableSet_line_parameter_event {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (r : ℝ) (z : EuclideanSpace ℝ (Fin n))
    {a e : Ω → EuclideanSpace ℝ (Fin n)} (ha : Measurable a) (he : Measurable e) :
    MeasurableSet {x | z ∈ lineTube r (a x) (e x)} := by
  let U : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    ⋃ t : ℝ, {p | dist z (p.1 + t • p.2) < r}
  have hopen : IsOpen U := by
    apply isOpen_iUnion
    intro t
    exact isOpen_lt
      (continuous_const.dist (continuous_fst.add (continuous_snd.const_smul t)))
      continuous_const
  have hmeas := hopen.measurableSet.preimage (ha.prodMk he)
  have heq : {x | z ∈ lineTube r (a x) (e x)} = (fun x => (a x, e x)) ⁻¹' U := by
    ext x
    simp only [lineTube, Metric.mem_thickening_iff, Set.mem_preimage, U, Set.mem_iUnion,
      Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨w, ⟨t, rfl⟩, ht⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨a x + t • e x, ⟨t, rfl⟩, ht⟩
  rw [heq]
  exact hmeas

/-- Normalizing a tangent preserves velocity errors when its time component
ensures norm at least one. -/
theorem unitTangent_sub_bound {n : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (hu : 1 ≤ ‖u‖) (hv : v ≠ 0) :
    ‖unitTangent u - unitTangent v‖ ≤ 2 * ‖u - v‖ := by
  have hu0 : u ≠ 0 := norm_pos_iff.mp (by linarith : 0 < ‖u‖)
  have hrecU : ‖u‖ • unitTangent u = u := by
    simp only [unitTangent, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu0), one_smul]
  have hrecV : ‖v‖ • unitTangent v = v := by
    simp only [unitTangent, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
  have hscale : ‖u‖ * ‖unitTangent u - unitTangent v‖ ≤ 2 * ‖u - v‖ := by
    calc
      _ = ‖‖u‖ • (unitTangent u - unitTangent v)‖ := by simp [norm_smul]
      _ = ‖(u - v) + (‖v‖ - ‖u‖) • unitTangent v‖ := by
        congr 1
        rw [smul_sub, hrecU, sub_smul, hrecV]
        abel
      _ ≤ ‖u - v‖ + ‖(‖v‖ - ‖u‖) • unitTangent v‖ := norm_add_le _ _
      _ = ‖u - v‖ + |‖v‖ - ‖u‖| := by simp [norm_smul, Real.norm_eq_abs, norm_unitTangent hv]
      _ ≤ 2 * ‖u - v‖ := by
        have h := abs_norm_sub_norm_le v u
        rw [norm_sub_rev] at h
        linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hu) (norm_nonneg (unitTangent u - unitTangent v))]

theorem norm_liftedVector_ge_one (v : Fin 3 → ℝ) (q : ℝ) (hv : v 0 = 1) :
    1 ≤ ‖liftedVector v q‖ := by
  simpa [liftedVector, hv] using PiLp.norm_apply_le (liftedVector v q) 0

theorem norm_liftedVector_sub (v : Fin 3 → ℝ) (x y : ℝ) :
    ‖liftedVector v x - liftedVector v y‖ = |x - y| := by
  have heq : liftedVector v x - liftedVector v y =
      (x - y) • EuclideanSpace.single (3 : Fin 4) (1 : ℝ) := by
    ext j
    fin_cases j <;> simp [liftedVector]
  rw [heq]
  simp [norm_smul]

/-- Unit directions of bounded native quadratic trajectories vary by at
most `32*K` times the time displacement. -/
theorem quadratic_unit_tangent_change
    (v : Fin 3 → ℝ) (a b c K s t : ℝ) (hv : v 0 = 1)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |a * t ^ 2 + b * t + c| ≤ K) :
    ‖unitTangent (liftedVector v (2 * a * t + b)) -
      unitTangent (liftedVector v (2 * a * s + b))‖ ≤ 32 * K * |t - s| := by
  have hs : liftedVector v (2 * a * s + b) ≠ 0 :=
    norm_pos_iff.mp (by linarith [norm_liftedVector_ge_one v (2 * a * s + b) hv])
  have hunit := unitTangent_sub_bound (liftedVector v (2 * a * t + b))
    (liftedVector v (2 * a * s + b)) (norm_liftedVector_ge_one v _ hv) hs
  rw [norm_liftedVector_sub] at hunit
  have hdir := (quadratic_tangent_bounds a b c K h).2.1 s t
  nlinarith

/-- Normalize the full affine tangent without altering its line image. -/
theorem scaled_point_mem_tangent_tube {n : ℕ}
    (a d x : EuclideanSpace ℝ (Fin n)) (s b : ℝ) (hb : 0 < b) (hd : d ≠ 0)
    (herr : ‖x - a - s • d‖ < b) :
    b⁻¹ • x ∈ lineTube 1 (b⁻¹ • a) (unitTangent d) := by
  apply Metric.mem_thickening_iff.mpr
  refine ⟨b⁻¹ • (a + s • d), ?_, ?_⟩
  · refine ⟨b⁻¹ * s * ‖d‖, ?_⟩
    simp only [unitTangent, smul_smul, smul_add]
    congr 1
    congr 1
    field_simp
  · rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hb]
    have h := mul_lt_mul_of_pos_left herr (inv_pos.mpr hb)
    rw [inv_mul_cancel₀ hb.ne'] at h
    simpa only [sub_add_eq_sub_sub] using h

/-- Lattice incidence uses the accepted cell-radius and tube-enlargement
lemmas; the source point may lie anywhere in its half-open cube. -/
theorem lattice_cell_mem_tangent_tube {n : ℕ} (hn : 2 ≤ n) (hn4 : n ≤ 4)
    (a d x : EuclideanSpace ℝ (Fin n)) (s b : ℝ) (hb : 0 < b) (hd : d ≠ 0)
    (z : Fin n → ℤ) (hcell : b⁻¹ • x ∈ latticeCell z)
    (herr : ‖x - a - s • d‖ < b) :
    latticePoint z ∈ lineTube 3 (b⁻¹ • a) (unitTangent d) :=
  lineTube_mono_center (dist_latticePoint_lt_two hn hn4 z hcell)
    (scaled_point_mem_tangent_tube a d x s b hb hd herr)

/-- A physical quadratic portion of time radius `w` lies in the required
lattice tube once its quadratic remainder is smaller than `b`. -/
theorem quadraticLift_lattice_tangent_tube
    (p v : Fin 3 → ℝ) (a b c K width fine s t : ℝ)
    (hK : 0 ≤ K) (hfine : 0 < fine) (hv : v 0 = 1)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |a * t ^ 2 + b * t + c| ≤ K)
    (hdt : |t - s| ≤ width) (hsmall : 8 * K * width ^ 2 < fine)
    (z : Fin 4 → ℤ) (hcell : fine⁻¹ • quadraticLift p v a b c t ∈ latticeCell z) :
    latticePoint z ∈ lineTube 3 (fine⁻¹ • quadraticLift p v a b c s)
      (unitTangent (liftedVector v (2 * a * s + b))) := by
  have hd : liftedVector v (2 * a * s + b) ≠ 0 := by
    intro hzero
    have h0 := congrArg (fun x : EuclideanSpace ℝ (Fin 4) => x 0) hzero
    simp [liftedVector, hv] at h0
  apply lattice_cell_mem_tangent_tube (by decide) (by decide)
    (quadraticLift p v a b c s) (liftedVector v (2 * a * s + b))
    (quadraticLift p v a b c t) (t - s) fine hfine hd z hcell
  have hrem := quadraticLift_tangent_bound p v a b c K h s t
  have hsq := pow_le_pow_left₀ (abs_nonneg (t - s)) hdt 2
  exact (hrem.trans (mul_le_mul_of_nonneg_left hsq (by positivity))).trans_lt hsmall

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
