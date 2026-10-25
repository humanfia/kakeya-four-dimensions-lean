/-
Adapted from: here:o204
Source: x0706, commit9bf14ed0, Submission/Obl/k4_uniform_sampled_isotropic_branches/AffineSupportVolume.lean.
The imported saturation, affine Jacobian, and signal-support APIs remain imports.
-/
import Submission.Lib.K4AffineMeshCaps.Transport

/-!
Occupied cells of a resolved affine cube have volume controlled by its
EXACT determinant, with no loss from its shear or eccentricity.
-/

namespace Submission.Lib.K4AffineCubeSupport

open MeasureTheory Set Matrix
open Submission.Lib.K4AffineMeshCaps

noncomputable section

def affineCube (M : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ) : Set (Fin 3 → ℝ) :=
  affineBase M b '' Icc 0 1

/-- The complete occupied mesh lies inside an enlarged native cube once
the mesh resolves each inverse row. -/
theorem affine_cube_mesh_saturation_subset
    (M : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ) (hM : M.det ≠ 0)
    {delta : ℝ} (hd : 0 < delta)
    (hresolve : ∀ i : Fin 3, (∑ j : Fin 3, |M⁻¹ i j| * delta) ≤ 1) :
    meshSaturation delta (affineCube M b) ⊆
      affineBase M⁻¹ (-(M⁻¹.mulVec b)) ⁻¹' Icc (-1 : Fin 3 → ℝ) 2 := by
  intro z hz
  obtain ⟨w, hw, hzw⟩ := meshSaturation_close hd (affineCube M b) hz
  obtain ⟨x, hx, rfl⟩ := hw
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have hinv : affineBase M⁻¹ (-(M⁻¹.mulVec b)) (affineBase M b x) = x := by
    simp [affineBase, Matrix.mulVec_add, Matrix.mulVec_mulVec, M.nonsing_inv_mul hMu, add_assoc]
  have hvar (i : Fin 3) : |affineBase M⁻¹ (-(M⁻¹.mulVec b)) z i - x i| ≤ 1 := by
    have hh := affineBase_coordinate_variation M⁻¹ (-(M⁻¹.mulVec b)) hzw i
    rw [hinv] at hh
    exact hh.trans (hresolve i)
  constructor
  · intro i
    have hh := (abs_le.mp (hvar i)).1
    have hxi : 0 ≤ x i := hx.1 i
    change -1 ≤ _
    linarith
  · intro i
    have hh := (abs_le.mp (hvar i)).2
    have hxi : x i ≤ 1 := hx.2 i
    change _ ≤ 2
    linarith

/-- This is the determinant estimate needed for raw fine-entry support
budgets. Conditioning enters only the resolution hypothesis, never its
volume constant. -/
theorem affine_cube_mesh_saturation_volume
    (M : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ) (hM : M.det ≠ 0)
    {delta : ℝ} (hd : 0 < delta)
    (hresolve : ∀ i : Fin 3, (∑ j : Fin 3, |M⁻¹ i j| * delta) ≤ 1) :
    volume (meshSaturation delta (affineCube M b)) ≤ ENNReal.ofReal (27 * |M.det|) := by
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have hN : (M⁻¹).det ≠ 0 := (M.isUnit_nonsing_inv_det hMu).ne_zero
  have hcube : (volume : Measure (Fin 3 → ℝ)) (Icc (-1 : Fin 3 → ℝ) 2) = ENNReal.ofReal 27 := by
    rw [Real.volume_Icc_pi]
    norm_num [Fin.prod_univ_succ]
  calc
    _ ≤ volume (affineBase M⁻¹ (-(M⁻¹.mulVec b)) ⁻¹' Icc (-1 : Fin 3 → ℝ) 2) :=
      measure_mono (affine_cube_mesh_saturation_subset M b hM hd hresolve)
    _ = ENNReal.ofReal |(M⁻¹).det|⁻¹ * ENNReal.ofReal 27 := by
      rw [volume_affineBase_preimage M⁻¹ (-(M⁻¹.mulVec b)) hN _ measurableSet_Icc, hcube]
    _ = _ := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', abs_inv, inv_inv,
        ← ENNReal.ofReal_mul (abs_nonneg _)]
      congr 1
      ring

/-- Coordinate boundedness gives finite occupied mesh support. -/
theorem finite_mesh_of_coordinate_bound (A : Set (Fin 3 → ℝ))
    {delta : ℝ} (hd : 0 < delta) (H : Fin 3 → ℝ) (hH : ∀ i, 0 ≤ H i)
    (hbound : ∀ x ∈ A, ∀ i, |x i| ≤ H i) : (baseMesh delta '' A).Finite := by
  classical
  choose F hF hmem using fun i : Fin 3 => interval_mesh_cover hd (hH i) 0
  let B := Fintype.piFinset F
  apply (B.finite_toSet).subset
  rintro z ⟨x, hx, rfl⟩
  exact Fintype.mem_piFinset.mpr (fun i => hmem i (x i) (by simpa only [sub_zero] using hbound x hx i))

theorem finite_mesh_affine_cube (M : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ)
    {delta : ℝ} (hd : 0 < delta) : (baseMesh delta '' affineCube M b).Finite := by
  apply finite_mesh_of_coordinate_bound _ hd (fun i => (∑ j : Fin 3, |M i j|) + |b i|)
    (by intro i; positivity)
  rintro z ⟨x, hx, rfl⟩ i
  simp only [affineBase, Pi.add_apply, Matrix.mulVec, dotProduct]
  calc
    _ ≤ |∑ j : Fin 3, M i j * x j| + |b i| := abs_add_le _ _
    _ ≤ (∑ j : Fin 3, |M i j * x j|) + |b i| :=
      add_le_add (Finset.abs_sum_le_sum_abs _ _) le_rfl
    _ ≤ (∑ j : Fin 3, |M i j|) + |b i| := by
      apply add_le_add _ le_rfl
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (hx.1 j)]
      exact mul_le_of_le_one_right (abs_nonneg _) (hx.2 j)

/-- The occupied saturation has exactly one full cube per occupied code. -/
theorem finite_occupied_mesh_volume (A : Set (Fin 3 → ℝ)) {delta : ℝ} (hd : 0 < delta)
    (hfin : (baseMesh delta '' A).Finite) :
    volume (meshSaturation delta A) = ENNReal.ofReal ((hfin.toFinset.card : ℝ) * delta ^ 3) := by
  classical
  let F := hfin.toFinset
  have hset : meshSaturation delta A = ⋃ q ∈ F, meshBox delta q := by
    ext z
    constructor
    · intro hz
      obtain ⟨q, hq⟩ := mem_iUnion.mp hz
      unfold selectedMeshCell at hq
      split_ifs at hq with hocc
      · exact mem_iUnion₂.mpr ⟨q, hfin.mem_toFinset.mpr hocc, hq⟩
      · exact hq.elim
    · intro hz
      obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.mp hz
      have hocc : ∃ x ∈ A, baseMesh delta x = q := hfin.mem_toFinset.mp hq
      apply mem_iUnion.mpr ⟨q, ?_⟩
      simpa only [selectedMeshCell, if_pos hocc] using hzq
  have hdisj : (F : Set (Fin 3 → ℤ)).PairwiseDisjoint (meshBox delta) :=
    fun q _ r _ hqr => meshBox_pairwiseDisjoint delta hqr
  rw [hset, measure_biUnion_finset hdisj (fun q _ => measurableSet_meshBox delta q)]
  simp_rw [volume_meshBox hd]
  rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]

/-- A finite cover of an arbitrarily sheared affine cube with its exact
determinant. No eccentricity is present in the cardinality constant. -/
theorem affine_cube_mesh_cover
    (M : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ) (hM : M.det ≠ 0)
    {delta : ℝ} (hd : 0 < delta)
    (hresolve : ∀ i : Fin 3, (∑ j : Fin 3, |M⁻¹ i j| * delta) ≤ 1) :
    ∃ F : Finset (Fin 3 → ℤ), (F.card : ℝ) * delta ^ 3 ≤ 27 * |M.det| ∧
      ∀ z ∈ affineCube M b, baseMesh delta z ∈ F := by
  classical
  have hfin := finite_mesh_affine_cube M b hd
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · have hh := affine_cube_mesh_saturation_volume M b hM hd hresolve
    rw [finite_occupied_mesh_volume _ hd hfin] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
  · intro z hz
    exact hfin.mem_toFinset.mpr ⟨z, hz, rfl⟩

end

end Submission.Lib.K4AffineCubeSupport
