-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.SourceGeometry.PlaneGraph, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/SourceGeometry/PlaneGraph.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/SourceGeometry/PlaneGraph.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/SourceGeometry/PlaneGraph.lean.
-- Existing source attributions are preserved below.

/- Adapted from this LOT tree oai_074_kakeya_four_dimensions, obligation o106,
   session x0352, commit b976e86c1df62f72f3fa9d42b0a0c928d33ecc7d;
   original file Submission/Obl/k4_isotropic_path_improvement/PlaneGraph.lean.
   Existing source comments and attributions are preserved below. -/
import Submission.Obl.k4_real_conic_restoration.Coordinates
import Submission.Obl.k4_adapted_oscillation_tests.Glue

/-!
The last linear-algebra step of the physical velocity-graph argument.
A nearly containing plane is a bounded graph if its captured lifted
vectors have a conditioned basis of base projections.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry

open Matrix
open Submission.Obl.k4_real_conic_restoration

noncomputable section

/-- Three approximate normal equations control the base part of a normal. -/
theorem normal_base_bound
    (A : Matrix (Fin 3) (Fin 3) ℝ) (n w : Fin 3 → ℝ) (q K ε : ℝ)
    (hA : A.det ≠ 0)
    (hi : ∀ i j, |A⁻¹ i j| ≤ K) (hw : ∀ i, |w i| ≤ K)
    (herr : ∀ i, |(A *ᵥ n) i + q * w i| ≤ ε) :
    ∀ j, |n j| ≤ 3 * K * (ε + |q| * K) := by
  have hAn : ∀ i, |(A *ᵥ n) i| ≤ ε + |q| * K := by
    intro i
    calc
      |(A *ᵥ n) i| = |((A *ᵥ n) i + q * w i) - q * w i| := by congr 1; ring
      _ ≤ |(A *ᵥ n) i + q * w i| + |q * w i| := abs_sub _ _
      _ ≤ ε + |q| * K := by rw [abs_mul]; gcongr; exact herr i; exact hw i
  have h := vecMul_bound hAn (fun i j => hi j i)
  have heq : Matrix.vecMul (A *ᵥ n) A⁻¹.transpose = n := by
    rw [Matrix.vecMul_transpose, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), Matrix.one_mulVec]
  intro j
  rw [← heq]
  exact (h j).trans_eq (by ring)

/-- A normalized approximate normal has a nonnegligible final coordinate. -/
theorem final_normal_lower_bound
    (A : Matrix (Fin 3) (Fin 3) ℝ) (n w : Fin 3 → ℝ) (q K ε : ℝ)
    (hA : A.det ≠ 0) (hK : 1 ≤ K)
    (hi : ∀ i j, |A⁻¹ i j| ≤ K) (hw : ∀ i, |w i| ≤ K)
    (hn : 1 ≤ (∑ j, |n j|) + |q|)
    (herr : ∀ i, |(A *ᵥ n) i + q * w i| ≤ ε)
    (hsmall : 18 * K * ε ≤ 1) :
    1 ≤ 20 * K ^ 2 * |q| := by
  have hbase := normal_base_bound A n w q K ε hA hi hw herr
  have hsum := sum3_le hbase
  have hKsq : 1 ≤ K ^ 2 := by nlinarith
  have hupper : 1 ≤ 9 * K * ε + (9 * K ^ 2 + 1) * |q| := by nlinarith
  nlinarith [abs_nonneg q, mul_nonneg (sub_nonneg.mpr hKsq) (abs_nonneg q)]

/-- The plane row has polynomial size; all other normal residuals transfer
with the same reciprocal final-coordinate bound. -/
theorem exists_bounded_plane_row
    (A : Matrix (Fin 3) (Fin 3) ℝ) (n w : Fin 3 → ℝ) (q K ε : ℝ)
    (hA : A.det ≠ 0) (hK : 1 ≤ K) (hε : 0 ≤ ε)
    (hi : ∀ i j, |A⁻¹ i j| ≤ K) (hw : ∀ i, |w i| ≤ K)
    (hn : 1 ≤ (∑ j, |n j|) + |q|)
    (herr : ∀ i, |(A *ᵥ n) i + q * w i| ≤ ε)
    (hsmall : 18 * K * ε ≤ 1) :
    ∃ G : Fin 3 → ℝ, (∀ j, |G j| ≤ 7 * K ^ 2) ∧
      ∀ (v : Fin 3 → ℝ) (z δ : ℝ), |(∑ j, n j * v j) + q * z| ≤ δ →
        |z - ∑ j, G j * v j| ≤ 20 * K ^ 2 * δ := by
  have hK0 : 0 < K := by linarith
  have hq := final_normal_lower_bound A n w q K ε hA hK hi hw hn herr hsmall
  have hq0 : 0 < |q| := by nlinarith [sq_nonneg K]
  have hqn : q ≠ 0 := abs_pos.mp hq0
  have hinv : |q|⁻¹ ≤ 20 * K ^ 2 := (inv_le_iff_one_le_mul₀ hq0).mpr (by nlinarith)
  let G : Fin 3 → ℝ := fun j => -(n j) / q
  refine ⟨G, ?_, ?_⟩
  · intro j
    have hbase := normal_base_bound A n w q K ε hA hi hw herr j
    have hdiv := (div_le_div_of_nonneg_right hbase hq0.le)
    have heq : 3 * K * (ε + |q| * K) / |q| =
        3 * K * ε * |q|⁻¹ + 3 * K ^ 2 := by field_simp
    rw [heq] at hdiv
    have hprod := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ 3 * K * ε)
    have hsmall' := mul_le_mul_of_nonneg_right hsmall (pow_nonneg hK0.le 2)
    dsimp [G]
    rw [abs_div, abs_neg]
    nlinarith
  · intro v z δ hδ
    have hid : z - ∑ j, G j * v j = ((∑ j, n j * v j) + q * z) / q := by
      dsimp [G]
      simp only [div_mul_eq_mul_div, ← Finset.sum_div]
      field_simp
      rw [Finset.sum_neg_distrib]
      ring
    rw [hid, abs_div]
    calc
      |(∑ j, n j * v j) + q * z| / |q| ≤ δ / |q| :=
        div_le_div_of_nonneg_right hδ hq0.le
      _ ≤ 20 * K ^ 2 * δ := by
        rw [div_eq_mul_inv]
        nlinarith [mul_le_mul_of_nonneg_left hinv ((abs_nonneg _).trans hδ)]

/-- Entry/determinant conditioning suffices, without separate inverse data. -/
theorem exists_bounded_plane_row_of_det
    (A : Matrix (Fin 3) (Fin 3) ℝ) (n w : Fin 3 → ℝ) (q K ε : ℝ)
    (hK : 1 ≤ K) (hε : 0 ≤ ε)
    (hA : ∀ i j, |A i j| ≤ K) (hd : 1 ≤ K * |A.det|)
    (hw : ∀ i, |w i| ≤ K) (hn : 1 ≤ (∑ j, |n j|) + |q|)
    (herr : ∀ i, |(A *ᵥ n) i + q * w i| ≤ ε)
    (hsmall : 36 * K ^ 3 * ε ≤ 1) :
    ∃ G : Fin 3 → ℝ, (∀ j, |G j| ≤ 28 * K ^ 6) ∧
      ∀ (v : Fin 3 → ℝ) (z δ : ℝ), |(∑ j, n j * v j) + q * z| ≤ δ →
        |z - ∑ j, G j * v j| ≤ 80 * K ^ 6 * δ := by
  have hK0 : 0 < K := by linarith
  have hA0 : A.det ≠ 0 := by intro h; norm_num [h] at hd
  have hKsq : 1 ≤ K ^ 2 := by nlinarith
  have hKcube : K ≤ K ^ 3 := by
    nlinarith [mul_nonneg hK0.le (sub_nonneg.mpr hKsq)]
  obtain ⟨G, hG, hres⟩ := exists_bounded_plane_row A n w q (2 * K ^ 3) ε
    hA0 (by nlinarith) hε (inverse_entry_bound hK0 hA hd)
    (fun i => (hw i).trans (by nlinarith)) hn herr (by nlinarith)
  refine ⟨G, ?_, ?_⟩
  · intro j
    exact (hG j).trans_eq (by ring)
  · intro v z δ hδ
    exact (hres v z δ hδ).trans_eq (by ring)

/-- Unit Euclidean normals supply the normalization in the graph estimate. -/
theorem unit_normal_l1_lower (n : EuclideanSpace ℝ (Fin 4)) (hn : ‖n‖ = 1) :
    1 ≤ (∑ j : Fin 3, |n j.castSucc|) + |n 3| := by
  have h := Submission.Obl.k4_adapted_oscillation_tests.norm_apply_le_sum_abs
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 4))) (fun i => by simp) n
  change ‖n‖ ≤ ∑ j : Fin 4, |n j| at h
  rw [hn, Fin.sum_univ_castSucc] at h
  simpa only [show (Fin.last 3 : Fin 4) = 3 by decide] using h

/-- Plane distance controls a unit-normal residual. -/
theorem abs_inner_le_plane_distance
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : Submodule ℝ E) (n x : E) (hn : ‖n‖ = 1)
    (hortho : ∀ y ∈ V, inner ℝ n y = 0) :
    |inner ℝ n x| ≤ Metric.infDist x (V : Set E) := by
  apply (Metric.le_infDist ⟨0, V.zero_mem⟩).mpr
  intro y hy
  calc
    |inner ℝ n x| = |inner ℝ n (x - y)| := by rw [inner_sub_right, hortho y hy, sub_zero]
    _ ≤ ‖n‖ * ‖x - y‖ := abs_real_inner_le_norm _ _
    _ = dist x y := by rw [hn, one_mul, dist_eq_norm]

/-- Append the scalar velocity to the three base velocities. -/
def liftedVector (v : Fin 3 → ℝ) (z : ℝ) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![v 0, v 1, v 2, z]

theorem inner_liftedVector (n : EuclideanSpace ℝ (Fin 4)) (v : Fin 3 → ℝ) (z : ℝ) :
    inner ℝ n (liftedVector v z) = (∑ j : Fin 3, n j.castSucc * v j) + n 3 * z := by
  simp [liftedVector, PiLp.inner_apply, Fin.sum_univ_four, Fin.sum_univ_three, mul_comm]

/-- Every proper subspace has a unit normal. -/
theorem exists_unit_subspace_normal {d : ℕ} (V : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hV : Module.finrank ℝ V < d) :
    ∃ n : EuclideanSpace ℝ (Fin d), ‖n‖ = 1 ∧ ∀ y ∈ V, inner ℝ n y = 0 := by
  have hproper : V ≠ ⊤ := by
    intro h
    rw [h] at hV
    norm_num at hV
  have horth : Vᗮ ≠ ⊥ := fun h => hproper (Submodule.orthogonal_eq_bot_iff.mp h)
  obtain ⟨n, hnV, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot horth
  refine ⟨(‖n‖⁻¹ : ℝ) • n, norm_smul_inv_norm hn0, ?_⟩
  exact (V.mem_orthogonal' _).mp (Vᗮ.smul_mem _ hnV)

/-- A nearly containing proper plane with three transverse base projections
is a bounded row graph, with a quantitative distance-to-residual estimate. -/
theorem subspace_graph_row
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin 4))) (hV : Module.finrank ℝ V < 4)
    (A : Matrix (Fin 3) (Fin 3) ℝ) (w : Fin 3 → ℝ) (K ε : ℝ)
    (hK : 1 ≤ K) (hε : 0 ≤ ε)
    (hA : ∀ i j, |A i j| ≤ K) (hd : 1 ≤ K * |A.det|)
    (hw : ∀ i, |w i| ≤ K)
    (hnear : ∀ i, Metric.infDist (liftedVector (A i) (w i)) (V : Set _) ≤ ε)
    (hsmall : 36 * K ^ 3 * ε ≤ 1) :
    ∃ G : Fin 3 → ℝ, (∀ j, |G j| ≤ 28 * K ^ 6) ∧
      ∀ (v : Fin 3 → ℝ) (z : ℝ),
        |z - ∑ j, G j * v j| ≤
          80 * K ^ 6 * Metric.infDist (liftedVector v z) (V : Set _) := by
  obtain ⟨n, hn, hortho⟩ := exists_unit_subspace_normal V hV
  have herr (i : Fin 3) : |(A *ᵥ (fun j => n j.castSucc)) i + n 3 * w i| ≤ ε := by
    have h := (abs_inner_le_plane_distance V n (liftedVector (A i) (w i)) hn hortho).trans
      (hnear i)
    rw [inner_liftedVector] at h
    simpa only [Matrix.mulVec, dotProduct, mul_comm] using h
  obtain ⟨G, hG, hres⟩ := exists_bounded_plane_row_of_det A (fun j => n j.castSucc) w
    (n 3) K ε hK hε hA hd hw (unit_normal_l1_lower n hn) herr hsmall
  refine ⟨G, hG, ?_⟩
  intro v z
  apply hres
  rw [← inner_liftedVector]
  exact abs_inner_le_plane_distance V n _ hn hortho

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry
