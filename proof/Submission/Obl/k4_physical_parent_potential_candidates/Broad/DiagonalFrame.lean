-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/DiagonalFrame.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.GridSeven
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.BaseCubes

/-!
# A diagonal frame for the old packet

The sampled exit works in a normalization `x ↦ c₁ + M₁ x` of the base. For the broad completion
we use a diagonal one, `u = diag(1/(2h), 1/D, 1/D) (z - z₀)`: the time scale is twice the block
length and the spatial scale `D` is chosen so that the packet's base region fits in `[0, 1/2]³`.
It has an explicit inverse, normalized lines move with time component `1/(2h)` and normalized
velocity `(2h/D) (l₃, l₄)`. When `z₀` and the scales times the grid side are integer multiples
of the observation mesh `p`, the grid cell of a normalized base point is a function of its
observation cube (`gridIdx_frame_eq`). Grid cells are then unions of whole observation cubes.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Broad

open Set MeasureTheory
open Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

/-- The scales of the diagonal frame: `2h` in time, `D` in space. -/
def frameScale (h D : ℝ) : Fin 3 → ℝ := ![2 * h, D, D]

/-- The diagonal frame matrix. -/
def frameMat (h D : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal fun i => (frameScale h D i)⁻¹

/-- The shift of the diagonal frame with corner `z₀`. -/
def frameShift (h D : ℝ) (z₀ : Fin 3 → ℝ) : Fin 3 → ℝ := fun i => -(z₀ i) / frameScale h D i

/-- The inverse matrix. -/
def frameMatInv (h D : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal (frameScale h D)

lemma frameScale_pos {h D : ℝ} (hh : 0 < h) (hD : 0 < D) (i : Fin 3) : 0 < frameScale h D i := by
  fin_cases i <;> simp [frameScale] <;> positivity

lemma frameMatInv_mul {h D : ℝ} (hh : 0 < h) (hD : 0 < D) :
    frameMatInv h D * frameMat h D = 1 := by
  rw [frameMatInv, frameMat, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact mul_inv_cancel₀ (frameScale_pos hh hD i).ne'

lemma frameShift_inv {h D : ℝ} (hh : 0 < h) (hD : 0 < D) (z₀ : Fin 3 → ℝ) :
    ∀ k, z₀ k = -∑ i : Fin 3, frameMatInv h D k i * frameShift h D z₀ i := by
  intro k
  rw [Finset.sum_eq_single k (fun i _ hik => by simp [frameMatInv, Matrix.diagonal_apply_ne _ hik.symm])
    (by simp)]
  simp only [frameMatInv, Matrix.diagonal_apply_eq, frameShift]
  have := (frameScale_pos hh hD k).ne'
  field_simp

lemma normalizedBase_frame (h D : ℝ) (z₀ : Fin 3 → ℝ) (B : ℝ) (x : Fin 4 → ℝ) (i : Fin 3) :
    normalizedBase (frameShift h D z₀) (frameMat h D) B x i =
      (x i.castSucc - z₀ i) / frameScale h D i := by
  fin_cases i <;>
    simp [normalizedBase, pointOfCoordinates, coordinateMap, frameShift, frameMat,
      Fin.sum_univ_three, Matrix.diagonal_apply] <;> ring

lemma graphPoint_castSucc_eq_basePoint (l : Line) (t : ℝ) (i : Fin 3) :
    graphPoint l t i.castSucc = basePoint (l, t) i := by
  fin_cases i <;> simp [graphPoint, basePoint]

lemma lineDir_frame_zero {h D : ℝ} (l : Line) : lineDir (frameMat h D) l 0 = (2 * h)⁻¹ := by
  simp [lineDir, frameMat, frameScale]

lemma lineVelocity_frame {h D : ℝ} (hh : 0 < h) (l : Line) :
    lineVelocity (frameMat h D) l = (2 * h / D) • (WithLp.toLp 2 ![l.2 3, l.2 4] :
      EuclideanSpace ℝ (Fin 2)) := by
  ext i
  fin_cases i <;> simp [lineVelocity, lineDir, frameMat, frameScale] <;> field_simp

/-- **Grid cells are unions of observation cubes.** -/
lemma gridIdx_frame_eq {h D p ℓ : ℝ} (hp : 0 < p) (g : Fin 3 → ℕ) (hg : ∀ i, 0 < g i)
    (hgL : ∀ i, frameScale h D i * ℓ = p * g i) (z₀ : Fin 3 → ℝ) (w : Fin 3 → ℤ)
    (hw : ∀ i, z₀ i = p * w i) (B : ℝ) (q : Ev) (i : Fin 3) :
    ⌊normalizedBase (frameShift h D z₀) (frameMat h D) B (graphPoint q.1 q.2) i / ℓ⌋ =
      (cubeIdx p q i - w i) / (g i : ℤ) := by
  have hgi : (0:ℝ) < g i := by exact_mod_cast hg i
  rw [normalizedBase_frame, graphPoint_castSucc_eq_basePoint]
  have hq : (q.1, q.2) = q := rfl
  rw [hq, div_div, hgL i, hw i]
  have : (basePoint q i - p * w i) / (p * g i) = (basePoint q i / p - w i) / (g i) := by
    field_simp
  rw [this, Int.floor_div_natCast, Int.floor_sub_intCast]
  rfl

end

end Submission.Obl.k4_physical_parent_potential_candidates.Broad
