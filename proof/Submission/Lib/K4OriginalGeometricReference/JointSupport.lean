/-
Adapted from: here:o204
Original o204 sources and file-level provenance are recorded below.
-/
/- Original provenance: here:o204, session x0706, commit d013eb32;
   original file Submission/Obl/k4_uniform_sampled_isotropic_branches/JointSupport.lean. -/
import Submission.Lib.K4OriginalGeometricReference.AnisotropicSupport

/-!
The base mesh and native-signal mesh can be chosen independently. The
original anisotropic graph-box budget pays only actual base volumes, so
refining the base grid does not introduce an extra hidden-bin factor.
-/

namespace Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells

open Set

noncomputable section

def jointCode (baseMesh signalMesh : ℝ) (z : Fin 3 → ℝ) (w : ℝ) : Fin 4 → ℤ :=
  Fin.snoc (baseCode baseMesh z) ⌊w / signalMesh⌋

private theorem jointCode_scale {baseMesh signalMesh : ℝ}
    (hbase : 0 < baseMesh) (hsignal : 0 < signalMesh) (z : Fin 3 → ℝ) (w : ℝ) :
    pointCode baseMesh z ((baseMesh / signalMesh) * w) = jointCode baseMesh signalMesh z w := by
  unfold pointCode jointCode
  congr 1
  congr 1
  field_simp

/-- Actual rectangular graph entries have a joint support bound at
independent base and signal meshes. The SUM of exact anisotropic base
volumes is retained. -/
theorem rectangular_joint_family_cover
    {I X : Type*} [Fintype I]
    (Z : X → Fin 3 → ℝ) (signal : X → ℝ)
    (A : I → Set X) (c H : I → Fin 3 → ℝ)
    {R baseMesh signalMesh V : ℝ}
    (hR : 0 ≤ R) (hbase : 0 < baseMesh) (hsignal : 0 < signalMesh)
    (hresolve : ∀ i j, baseMesh ≤ H i j)
    (hbox : ∀ i x, x ∈ A i → ∀ j, |Z x j - c i j| ≤ H i j)
    (hosc : ∀ i x, x ∈ A i → ∀ y, y ∈ A i →
      baseCode baseMesh (Z x) = baseCode baseMesh (Z y) →
      |signal x - signal y| ≤ R * signalMesh)
    (hvolume : (∑ i, ∏ j, H i j) ≤ V) :
    ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ) * baseMesh ^ 3 ≤ 216 * (2 * R + 2) * V ∧
      ∀ i x, x ∈ A i → jointCode baseMesh signalMesh (Z x) (signal x) ∈ S := by
  have hscaled : ∀ i x, x ∈ A i → ∀ y, y ∈ A i →
      baseCode baseMesh (Z x) = baseCode baseMesh (Z y) →
      |(baseMesh / signalMesh) * signal x - (baseMesh / signalMesh) * signal y| ≤ R * baseMesh := by
    intro i x hx y hy hxy
    rw [← mul_sub, abs_mul, abs_of_pos (div_pos hbase hsignal)]
    calc
      _ ≤ (baseMesh / signalMesh) * (R * signalMesh) :=
        mul_le_mul_of_nonneg_left (hosc i x hx y hy hxy) (div_nonneg hbase.le hsignal.le)
      _ = _ := by field_simp
  obtain ⟨S, hS, hcover⟩ := rectangular_graph_family_cover Z
    (fun x => (baseMesh / signalMesh) * signal x) A c H hR hbase
    hresolve hbox hscaled hvolume
  exact ⟨S, hS, fun i x hx => by
    simpa only [jointCode_scale hbase hsignal] using hcover i x hx⟩

end

end Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
