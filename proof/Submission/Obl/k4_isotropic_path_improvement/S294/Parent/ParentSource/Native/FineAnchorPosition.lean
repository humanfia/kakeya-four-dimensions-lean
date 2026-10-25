-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.FineAnchorPosition, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/FineAnchorPosition.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/FineAnchorPosition.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/FineAnchorPosition.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Frames
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripObservation

/-! A whole original fine assignment has a small old-frame position error
at a fixed fine-block time. This uses its full original chart fit. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped BigOperators

noncomputable def PathData.fineAnchorPosition {W : ℕ} (p : PathData W)
    (b f : Fin p.C) (t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  Matrix.toEuclideanLin (p.Q b)⁻¹ (p.c f + t • p.u f - p.c b - t • p.u b)

section Path

variable {W : ℕ} {p : PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {fprofile : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
  {Mp Dp : ℕ} {σ : ℝ}

theorem PathData.Valid.fine_anchor_position_bound
    (hp : p.Valid Nk L ω ν E B fprofile κ₁ m s δ₀ Mp Dp σ) (hN : 1 ≤ Nk)
    (b f : Fin p.C) (l : ℕ × (Fin 6 → ℝ)) (hl : l ∈ p.A f) (t : ℝ)
    (ht : t ∈ Icc ((p.j f : ℝ) / (2 : ℝ) ^ p.T (p.lev f))
      (((p.j f : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev f))) :
    ‖packetPosition (p.Q b) (p.c b) (p.u b) l t - p.fineAnchorPosition b f t‖ ≤
      p.κ ^ 3 * Nk ^ (2 * δ₀ * L) *
        ((2 : ℝ) ^ p.T (p.lev b) / (2 : ℝ) ^ p.T (p.lev f)) := by
  have hκ : 0 ≤ p.κ := by linarith [hp.1]
  rcases hp.2.2.2.2.2.2.2 f with ⟨_, _, hQf, _, _, hsize, _, _, _, _, _, hfit, _⟩
  have hphysical : ‖y l t - p.c f - t • p.u f‖ ≤
      p.κ ^ 2 * ((2 : ℝ) ^ p.T (p.lev f))⁻¹ :=
    physical_error_le_of_frame hQf hκ (by positivity)
      (by simpa only [div_eq_mul_inv] using hsize) (((hfit l hl).2.2 t ht).1)
  have hsumold : (∑ i, ∑ j, |(p.Q b)⁻¹ i j|) ≤
      (2 : ℝ) ^ p.T (p.lev b) * (p.κ * Nk ^ (2 * δ₀ * L)) := by
    have h := mul_le_mul_of_nonneg_left (hp.normalized_inverse_bound hN b)
      (by positivity : 0 ≤ (2 : ℝ) ^ p.T (p.lev b))
    simpa only [← mul_assoc,
      mul_inv_cancel₀ (by positivity : (2 : ℝ) ^ p.T (p.lev b) ≠ 0), one_mul] using h
  have herror : packetPosition (p.Q b) (p.c b) (p.u b) l t - p.fineAnchorPosition b f t =
      Matrix.toEuclideanLin (p.Q b)⁻¹ (y l t - p.c f - t • p.u f) := by
    change Matrix.toEuclideanLin (p.Q b)⁻¹ (y l t - p.c b - t • p.u b) -
      Matrix.toEuclideanLin (p.Q b)⁻¹ (p.c f + t • p.u f - p.c b - t • p.u b) = _
    rw [← map_sub]
    congr 1
    module
  rw [herror]
  calc
    _ ≤ (∑ i, ∑ j, |(p.Q b)⁻¹ i j|) * ‖y l t - p.c f - t • p.u f‖ :=
      matrix_action_norm_le_entry_sum _ _
    _ ≤ ((2 : ℝ) ^ p.T (p.lev b) * (p.κ * Nk ^ (2 * δ₀ * L))) *
        (p.κ ^ 2 * ((2 : ℝ) ^ p.T (p.lev f))⁻¹) :=
      mul_le_mul hsumold hphysical (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem PathData.Valid.fine_anchor_position_le_strip_radius
    (hp : p.Valid Nk L ω ν E B fprofile κ₁ m s δ₀ Mp Dp σ) (hN : 1 ≤ Nk)
    (b f : Fin p.C) (l : ℕ × (Fin 6 → ℝ)) (hl : l ∈ p.A f) (t : ℝ)
    (ht : t ∈ Icc ((p.j f : ℝ) / (2 : ℝ) ^ p.T (p.lev f))
      (((p.j f : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev f)))
    {radius : ℝ} (htime : Nk ^ (2 * δ₀ * L) *
      ((2 : ℝ) ^ p.T (p.lev b) / (2 : ℝ) ^ p.T (p.lev f)) ≤ radius) :
    ‖packetPosition (p.Q b) (p.c b) (p.u b) l t - p.fineAnchorPosition b f t‖ ≤
      p.κ ^ 3 * radius := by
  apply (hp.fine_anchor_position_bound hN b f l hl t ht).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left htime
    (pow_nonneg (by linarith [hp.1] : 0 ≤ p.κ) 3)

end Path

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
