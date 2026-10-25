/-
Adapted from: here:o204
Source: x0706, commit9bf14ed0, Submission/Obl/k4_uniform_sampled_isotropic_branches/AffineJointSupport.lean.
The imported saturation, affine Jacobian, and signal-support APIs remain imports.
-/
import Submission.Lib.K4AffineCubeSupport.Volume
import Submission.Lib.K4OriginalGeometricReference.JointSupport

/-! Fine affine cubes give determinant-accurate joint support at
INDEPENDENT base and signal meshes. -/

namespace Submission.Lib.K4AffineCubeSupport

open Set
open Submission.Lib.K4AffineMeshCaps
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells

noncomputable section

/-- The accepted fiber-oscillation support theorem attaches signal bins
to the determinant-accurate occupied base cover. -/
theorem affine_cube_joint_cover {X : Type*}
    (Z : X → Fin 3 → ℝ) (signal : X → ℝ) (A : Set X)
    (M : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ) (hM : M.det ≠ 0)
    {p s R : ℝ} (hp : 0 < p) (hs : 0 < s) (hR : 0 ≤ R)
    (hresolve : ∀ i : Fin 3, (∑ j : Fin 3, |M⁻¹ i j| * p) ≤ 1)
    (hpoint : ∀ x ∈ A, Z x ∈ affineCube M b)
    (hosc : ∀ x ∈ A, ∀ y ∈ A, baseCode p (Z x) = baseCode p (Z y) →
      |signal x - signal y| ≤ R * s) :
    ∃ F : Finset (Fin 4 → ℤ), (F.card : ℝ) * p ^ 3 ≤ 27 * (2 * R + 2) * |M.det| ∧
      ∀ x ∈ A, jointCode p s (Z x) (signal x) ∈ F := by
  classical
  obtain ⟨Base, hBase, hcover⟩ := affine_cube_mesh_cover M b hM hp hresolve
  have hbase (x : X) (hx : x ∈ A) : baseCode p (Z x) ∈ Base := hcover _ (hpoint x hx)
  obtain ⟨G, hG, hGcover⟩ := Submission.Lib.K4SignalMeshSupport.terminal_support_of_fiber_oscillation
    A (fun x => baseCode p (Z x)) signal Base hs hR hbase hosc
  let pack : (Fin 3 → ℤ) × ℤ → Fin 4 → ℤ := fun q => Fin.snoc q.1 q.2
  let F := G.image pack
  have hF : (F.card : ℝ) ≤ (Base.card : ℝ) * (2 * R + 2) :=
    (show (F.card : ℝ) ≤ (G.card : ℝ) by exact_mod_cast Finset.card_image_le).trans hG
  refine ⟨F, ?_, ?_⟩
  · calc
      _ ≤ ((Base.card : ℝ) * (2 * R + 2)) * p ^ 3 :=
        mul_le_mul_of_nonneg_right hF (by positivity)
      _ = (2 * R + 2) * ((Base.card : ℝ) * p ^ 3) := by ring
      _ ≤ (2 * R + 2) * (27 * |M.det|) :=
        mul_le_mul_of_nonneg_left hBase (by positivity)
      _ = _ := by ring
  · intro x hx
    exact Finset.mem_image.mpr ⟨(baseCode p (Z x), ⌊signal x / s⌋), hGcover x hx, rfl⟩

/-- A family pays the SUM of exact affine determinants, independent of
all chart eccentricities and of the signal/base mesh ratio. -/
theorem affine_joint_family_cover {I X : Type*} [Fintype I]
    (Z : X → Fin 3 → ℝ) (signal : X → ℝ) (A : I → Set X)
    (M : I → Matrix (Fin 3) (Fin 3) ℝ) (b : I → Fin 3 → ℝ)
    (hM : ∀ i, (M i).det ≠ 0)
    {p s R : ℝ} (hp : 0 < p) (hs : 0 < s) (hR : 0 ≤ R)
    (hrows : ∀ k : I, ∀ i : Fin 3, (∑ j : Fin 3, |(M k)⁻¹ i j| * p) ≤ 1)
    (hpoint : ∀ i x, x ∈ A i → Z x ∈ affineCube (M i) (b i))
    (hosc : ∀ i x, x ∈ A i → ∀ y, y ∈ A i → baseCode p (Z x) = baseCode p (Z y) →
      |signal x - signal y| ≤ R * s) :
    ∃ F : Finset (Fin 4 → ℤ),
      (F.card : ℝ) * p ^ 3 ≤ 27 * (2 * R + 2) * ∑ i : I, |(M i).det| ∧
      ∀ i x, x ∈ A i → jointCode p s (Z x) (signal x) ∈ F := by
  classical
  choose F hF hcover using fun i : I =>
    affine_cube_joint_cover Z signal (A i) (M i) (b i) (hM i) hp hs hR (hrows i)
      (hpoint i) (hosc i)
  let G := Finset.univ.biUnion F
  refine ⟨G, ?_, ?_⟩
  · calc
      _ ≤ (∑ i : I, (F i).card : ℝ) * p ^ 3 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast Finset.card_biUnion_le
      _ = ∑ i : I, ((F i).card : ℝ) * p ^ 3 := Finset.sum_mul _ _ _
      _ ≤ ∑ i : I, 27 * (2 * R + 2) * |(M i).det| := Finset.sum_le_sum (fun i _ => hF i)
      _ = _ := (Finset.mul_sum _ _ _).symm
  · intro i x hx
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hcover i x hx⟩

end

end Submission.Lib.K4AffineCubeSupport
