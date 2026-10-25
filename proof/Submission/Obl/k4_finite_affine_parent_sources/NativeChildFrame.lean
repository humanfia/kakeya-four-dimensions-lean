-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.ModelEH1
import Submission.Obl.k4_finite_affine_parent_sources.Original

namespace Submission.Obl.k4_finite_affine_parent_sources

open Submission.Lib.K4XInterface

noncomputable section

namespace PFrame

def childMatrix (Φ : PFrame) (Q : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Φ.F.D⁻¹ * Q

def childCenter (Φ : PFrame) (c u : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  Matrix.toEuclideanLin Φ.F.D⁻¹ (c - Φ.F.c + Φ.F.t₀ • (u - Φ.F.u))

def childSpeed (Φ : PFrame) (u : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  Φ.F.q • Matrix.toEuclideanLin Φ.F.D⁻¹ (u - Φ.F.u)

lemma childMatrix_det_ne_zero (Φ : PFrame) (hD : Φ.F.D.det ≠ 0)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0) : (Φ.childMatrix Q).det ≠ 0 := by
  rw [childMatrix, Matrix.det_mul, det_inv_fin2]
  exact mul_ne_zero (inv_ne_zero hD) hQ

/-- The old child parallelogram is exactly its relative native
parallelogram, with the same slack and without changing the trajectory. -/
theorem child_frame_identity (Φ : PFrame) (hq : Φ.F.q ≠ 0) (hD : Φ.F.D.det ≠ 0)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (l : Trajectory) (t : ℝ) :
    Matrix.toEuclideanLin (Φ.childMatrix Q)⁻¹
      (gy (0, Φ.eb l) ((t - Φ.F.t₀) / Φ.F.q) - Φ.childCenter c u -
        ((t - Φ.F.t₀) / Φ.F.q) • Φ.childSpeed u) =
      Matrix.toEuclideanLin Q⁻¹ (gy l t - c - t • u) := by
  have hplane : gy (0, Φ.eb l) ((t - Φ.F.t₀) / Φ.F.q) =
      Matrix.toEuclideanLin Φ.F.D⁻¹ (gy l t - Φ.F.c - t • Φ.F.u) :=
    (Φ.toEuclideanLin_offset hq l t).symm
  have hoff : gy (0, Φ.eb l) ((t - Φ.F.t₀) / Φ.F.q) - Φ.childCenter c u -
      ((t - Φ.F.t₀) / Φ.F.q) • Φ.childSpeed u =
        Matrix.toEuclideanLin Φ.F.D⁻¹ (gy l t - c - t • u) := by
    rw [hplane]
    dsimp only [childCenter, childSpeed]
    rw [smul_smul, show (t - Φ.F.t₀) / Φ.F.q * Φ.F.q = t - Φ.F.t₀ by field_simp,
      ← map_smul, ← map_sub, ← map_sub]
    congr 1
    module
  rw [hoff, childMatrix, Matrix.mul_inv_rev, inv_inv_of_det_ne_zero Φ.F.D hD,
    Matrix.toLpLin_mul_same, LinearMap.comp_apply, toEuclideanLin_inv_cancel Φ.F.D hD]

/-- Whole-block old chart geometry gives the relative-frame hypothesis
used to produce the frozen tilted label rows. -/
theorem child_fit (Φ : PFrame) (hq : Φ.F.q ≠ 0) (hD : Φ.F.D.det ≠ 0)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (A : Set Trajectory) (I I' : Set ℝ) (κ : ℝ)
    (hI : ∀ t ∈ I', Φ.F.t₀ + Φ.F.q * t ∈ I)
    (hfit : ∀ l ∈ A, ∀ t ∈ I, ‖Matrix.toEuclideanLin Q⁻¹ (gy l t - c - t • u)‖ ≤ κ) :
    ∀ l ∈ A, ∀ t ∈ I', ‖Matrix.toEuclideanLin (Φ.childMatrix Q)⁻¹
      (gy (0, Φ.eb l) t - Φ.childCenter c u - t • Φ.childSpeed u)‖ ≤ κ := by
  intro l hl t ht
  have h := Φ.child_frame_identity hq hD Q c u l (Φ.F.t₀ + Φ.F.q * t)
  rw [Φ.tnorm_denorm hq] at h
  rw [h]
  exact hfit l hl _ (hI t ht)

end PFrame

end

end Submission.Obl.k4_finite_affine_parent_sources
