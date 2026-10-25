-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativeFrameChange, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativeFrameChange.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativeFrameChange.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeFrameChange.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Frames
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NormalizedPosteriors
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.AffineStripTransfer
import Submission.Lib.K4XInterface.Charts

/-! Actual old/fine path frames transfer original velocity strip bounds
to the unit-base native sheet coordinates. Their inverse norm loses only
6*kappa^3*N^(2*delta0*L), with no dyadic time-ratio or format factor. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace

noncomputable def PathData.normalizedFrameOperator {W : ℕ} (p : PathData W)
    (b : Fin p.C) : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ((2 : ℝ) ^ p.T (p.lev b))⁻¹ • (Matrix.toEuclideanLin (p.Q b)⁻¹).toContinuousLinearMap

noncomputable def PathData.denormalizedFrameOperator {W : ℕ} (p : PathData W)
    (b : Fin p.C) : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (2 : ℝ) ^ p.T (p.lev b) • (Matrix.toEuclideanLin (p.Q b)).toContinuousLinearMap

noncomputable def PathData.cubeVelocityChange {W : ℕ} (p : PathData W)
    (old fine : Fin p.C) : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (6 * p.κ)⁻¹ • ((p.normalizedFrameOperator fine).comp (p.denormalizedFrameOperator old))

noncomputable def PathData.cubeVelocityChangeInv {W : ℕ} (p : PathData W)
    (old fine : Fin p.C) : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (6 * p.κ) • ((p.normalizedFrameOperator old).comp (p.denormalizedFrameOperator fine))

noncomputable def PathData.cubeVelocityShift {W : ℕ} (p : PathData W)
    (old fine : Fin p.C) : EuclideanSpace ℝ (Fin 2) :=
  (6 * p.κ)⁻¹ • p.normalizedFrameOperator fine (p.u old - p.u fine)

section Path

variable {W : ℕ} {p : PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {profile : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
  {Mp Dp : ℕ} {σ : ℝ}
  (hp : p.Valid Nk L ω ν E B profile κ₁ m s δ₀ Mp Dp σ)

include hp

theorem PathData.Valid.normalized_denormalized_frame_cancel (b : Fin p.C)
    (v : EuclideanSpace ℝ (Fin 2)) :
    p.normalizedFrameOperator b (p.denormalizedFrameOperator b v) = v := by
  have hq : (2 : ℝ) ^ p.T (p.lev b) ≠ 0 := by positivity
  change ((2 : ℝ) ^ p.T (p.lev b))⁻¹ • Matrix.toEuclideanLin (p.Q b)⁻¹
    ((2 : ℝ) ^ p.T (p.lev b) • Matrix.toEuclideanLin (p.Q b) v) = v
  rw [map_smul, smul_smul, inv_mul_cancel₀ hq, one_smul]
  rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hp.2.2.2.2.2.2.2 b).2.2.1)]
  simp

theorem PathData.Valid.denormalized_normalized_frame_cancel (b : Fin p.C)
    (v : EuclideanSpace ℝ (Fin 2)) :
    p.denormalizedFrameOperator b (p.normalizedFrameOperator b v) = v := by
  have hq : (2 : ℝ) ^ p.T (p.lev b) ≠ 0 := by positivity
  change (2 : ℝ) ^ p.T (p.lev b) • Matrix.toEuclideanLin (p.Q b)
    (((2 : ℝ) ^ p.T (p.lev b))⁻¹ • Matrix.toEuclideanLin (p.Q b)⁻¹ v) = v
  rw [map_smul, smul_smul, mul_inv_cancel₀ hq, one_smul]
  exact Submission.Lib.K4XInterface.toEuclideanLin_inv_cancel (p.Q b)
    (hp.2.2.2.2.2.2.2 b).2.2.1 v

theorem PathData.Valid.normalized_frame_operator_bound (hN : 1 ≤ Nk)
    (b : Fin p.C) (v : EuclideanSpace ℝ (Fin 2)) :
    ‖p.normalizedFrameOperator b v‖ ≤ p.κ * Nk ^ (2 * δ₀ * L) * ‖v‖ := by
  change ‖((2 : ℝ) ^ p.T (p.lev b))⁻¹ • Matrix.toEuclideanLin (p.Q b)⁻¹ v‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc
    _ ≤ ((2 : ℝ) ^ p.T (p.lev b))⁻¹ *
        ((∑ i, ∑ j, |(p.Q b)⁻¹ i j|) * ‖v‖) :=
      mul_le_mul_of_nonneg_left (matrix_action_norm_le_entry_sum _ _) (by positivity)
    _ = (((2 : ℝ) ^ p.T (p.lev b))⁻¹ * (∑ i, ∑ j, |(p.Q b)⁻¹ i j|)) * ‖v‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hp.normalized_inverse_bound hN b) (norm_nonneg _)

theorem PathData.Valid.denormalized_frame_operator_bound
    (b : Fin p.C) (v : EuclideanSpace ℝ (Fin 2)) :
    ‖p.denormalizedFrameOperator b v‖ ≤ p.κ * ‖v‖ := by
  have hsize : (∑ i, ∑ j, |p.Q b i j|) ≤ p.κ / (2 : ℝ) ^ p.T (p.lev b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.1
  have hq : (2 : ℝ) ^ p.T (p.lev b) ≠ 0 := by positivity
  change ‖(2 : ℝ) ^ p.T (p.lev b) • Matrix.toEuclideanLin (p.Q b) v‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc
    _ ≤ (2 : ℝ) ^ p.T (p.lev b) * ((∑ i, ∑ j, |p.Q b i j|) * ‖v‖) :=
      mul_le_mul_of_nonneg_left (matrix_action_norm_le_entry_sum _ _) (by positivity)
    _ ≤ (2 : ℝ) ^ p.T (p.lev b) * ((p.κ / (2 : ℝ) ^ p.T (p.lev b)) * ‖v‖) := by gcongr
    _ = _ := by field_simp

theorem PathData.Valid.cube_velocity_change_inverse (old fine : Fin p.C)
    (v : EuclideanSpace ℝ (Fin 2)) :
    p.cubeVelocityChange old fine (p.cubeVelocityChangeInv old fine v) = v := by
  have hc : 6 * p.κ ≠ 0 := by linarith [hp.1]
  change (6 * p.κ)⁻¹ • p.normalizedFrameOperator fine
    (p.denormalizedFrameOperator old ((6 * p.κ) • p.normalizedFrameOperator old
      (p.denormalizedFrameOperator fine v))) = v
  rw [map_smul, hp.denormalized_normalized_frame_cancel, map_smul, smul_smul,
    inv_mul_cancel₀ hc, one_smul, hp.normalized_denormalized_frame_cancel]

theorem PathData.Valid.cube_velocity_change_inv_bound (hN : 1 ≤ Nk)
    (old fine : Fin p.C) (v : EuclideanSpace ℝ (Fin 2)) :
    ‖p.cubeVelocityChangeInv old fine v‖ ≤ 6 * p.κ ^ 3 * Nk ^ (2 * δ₀ * L) * ‖v‖ := by
  have hκ : 0 ≤ p.κ := by linarith [hp.1]
  change ‖(6 * p.κ) • p.normalizedFrameOperator old (p.denormalizedFrameOperator fine v)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (show 0 < 6 * p.κ by linarith [hp.1])]
  calc
    _ ≤ (6 * p.κ) * (p.κ * Nk ^ (2 * δ₀ * L) * ‖p.denormalizedFrameOperator fine v‖) :=
      mul_le_mul_of_nonneg_left (hp.normalized_frame_operator_bound hN old _) (by linarith [hp.1])
    _ ≤ (6 * p.κ) * (p.κ * Nk ^ (2 * δ₀ * L) * (p.κ * ‖v‖)) := by
      gcongr
      exact hp.denormalized_frame_operator_bound fine v
    _ = _ := by ring

theorem PathData.Valid.cube_velocity_change_exact (old fine : Fin p.C)
    (x : (ℕ × (Fin 6 → ℝ)) × ℝ) :
    p.cubeVelocityChange old fine (p.normalizedVelocity old x) + p.cubeVelocityShift old fine =
      (6 * p.κ)⁻¹ • p.normalizedVelocity fine x := by
  change (6 * p.κ)⁻¹ • p.normalizedFrameOperator fine
      (p.denormalizedFrameOperator old (p.normalizedFrameOperator old (v x.1 - p.u old))) +
    (6 * p.κ)⁻¹ • p.normalizedFrameOperator fine (p.u old - p.u fine) =
      (6 * p.κ)⁻¹ • p.normalizedFrameOperator fine (v x.1 - p.u fine)
  rw [hp.denormalized_normalized_frame_cancel, ← smul_add, ← map_add]
  congr 2
  abel

/-- A strip in the ACTUAL unit-base fine velocity pulls back to a strip
of the specified original radius in the old normalized velocity. -/
theorem PathData.Valid.native_cube_velocity_strip_pullback (hN : 1 ≤ Nk)
    (old fine : Fin p.C) {width radius : ℝ} (hwidth : 0 ≤ width)
    (hscale : width * (6 * p.κ ^ 3 * Nk ^ (2 * δ₀ * L)) ≤ radius)
    (n center : EuclideanSpace ℝ (Fin 2)) (hn : ‖n‖ = 1) :
    ∃ normal : EuclideanSpace ℝ (Fin 2), ∃ offset : ℝ, ‖normal‖ = 1 ∧
      {x | |inner ℝ n ((6 * p.κ)⁻¹ • p.normalizedVelocity fine x - center)| ≤ width} ⊆
        {x | |inner ℝ (p.normalizedVelocity old x) normal - offset| ≤ radius} := by
  have hκ : 0 ≤ p.κ := by linarith [hp.1]
  obtain ⟨normal, offset, hnormal, hsub⟩ := affine_velocity_strip_pullback
    (p.cubeVelocityChange old fine) (p.cubeVelocityChangeInv old fine)
    (show 0 ≤ 6 * p.κ ^ 3 * Nk ^ (2 * δ₀ * L) by positivity)
    hwidth (hp.cube_velocity_change_inv_bound hN old fine)
    (hp.cube_velocity_change_inverse old fine) hscale n (p.cubeVelocityShift old fine) center hn
  refine ⟨normal, offset, hnormal, ?_⟩
  intro x hx
  apply hsub
  change |inner ℝ n (p.cubeVelocityChange old fine (p.normalizedVelocity old x) +
    p.cubeVelocityShift old fine - center)| ≤ width
  rw [hp.cube_velocity_change_exact old fine x]
  exact hx

end Path

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
