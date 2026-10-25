-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripGeometryBudget, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripGeometryBudget.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripGeometryBudget.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripGeometryBudget.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripGeometryBudget.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripPhysical
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripAssignments
import Submission.Obl.k4_native_finite_terminal_atlas_lift.FrameComposition

/-! Numerical budgets for the physical strip charts. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Submission.Lib.K4VelocityStrips
open Submission.Obl.k4_native_finite_terminal_atlas_lift
open scoped BigOperators RealInnerProductSpace

theorem strip_center_velocity_norm {n : StripSpace} {s β : ℝ} (hn : ‖n‖ = 1) :
    ‖stripCenter n s β‖ + ‖stripVelocity n β‖ ≤ |s| + 2 * |β| := by
  simp only [stripCenter, stripVelocity, norm_smul, Real.norm_eq_abs, hn, mul_one]
  have h : |s - β / 2| ≤ |s| + |β| / 2 := by
    simpa [sub_eq_add_neg, abs_div] using abs_add_le s (-(β / 2))
  linarith [abs_nonneg β]

theorem physicalStrip_center_velocity_budget
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {c u n : StripSpace} {t₀ q s β H H' : ℝ}
    (hH : 1 ≤ H) (hH' : 1 ≤ H') (ht : |t₀| ≤ 1) (hq : |q⁻¹| ≤ H)
    (hcu : ‖c‖ + ‖u‖ ≤ H) (hQ : (∑ i : Fin 2, ∑ j : Fin 2, |Q i j|) ≤ H)
    (hn : ‖n‖ = 1) (hsβ : |s| + 2 * |β| ≤ H') :
    ‖physicalStripCenter Q c n t₀ q s β‖ + ‖physicalStripVelocity Q u n q β‖ ≤
      4 * H ^ 2 * H' := by
  have h := composite_center_velocity_bound hH hH' ht hq hcu
    ((strip_center_velocity_norm hn).trans hsβ) hQ
  simpa only [physicalStripCenter, physicalStripVelocity, compositeCenter, compositeVelocity,
    map_sub, map_smul, map_add, map_neg, sub_eq_add_neg, add_assoc] using h

/-- Entry and inverse-entry budgets multiply under physical composition. -/
theorem strip_composite_entry_budget
    {Q R : Matrix (Fin 2) (Fin 2) ℝ} {H H' : ℝ}
    (hQ : (∑ i : Fin 2, ∑ j : Fin 2, (|Q i j| + |Q⁻¹ i j|)) ≤ H)
    (hR : (∑ i : Fin 2, ∑ j : Fin 2, (|R i j| + |R⁻¹ i j|)) ≤ H') :
    (∑ i : Fin 2, ∑ j : Fin 2, (|(Q * R) i j| + |(Q * R)⁻¹ i j|)) ≤ H * H' := by
  simp only [Finset.sum_add_distrib] at hQ hR ⊢
  change frameSize Q + frameSize Q⁻¹ ≤ H at hQ
  change frameSize R + frameSize R⁻¹ ≤ H' at hR
  change frameSize (Q * R) + frameSize (Q * R)⁻¹ ≤ H * H'
  rw [Matrix.mul_inv_rev]
  calc
    _ ≤ frameSize Q * frameSize R + frameSize R⁻¹ * frameSize Q⁻¹ :=
      add_le_add (frameSize_mul _ _) (frameSize_mul _ _)
    _ ≤ (frameSize Q + frameSize Q⁻¹) * (frameSize R + frameSize R⁻¹) := by
      nlinarith [mul_nonneg (frameSize_nonneg Q) (frameSize_nonneg R⁻¹),
        mul_nonneg (frameSize_nonneg Q⁻¹) (frameSize_nonneg R)]
    _ ≤ H * H' := mul_le_mul hQ hR
      (add_nonneg (frameSize_nonneg _) (frameSize_nonneg _))
      ((add_nonneg (frameSize_nonneg _) (frameSize_nonneg _)).trans hQ)

theorem strip_physical_frame_entry_budget
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {K D r H : ℝ} {e n : StripSpace}
    (hK : 0 < K) (hD : 0 ≤ D) (hr : 0 < r)
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0)
    (hQ : (∑ i : Fin 2, ∑ j : Fin 2, (|Q i j| + |Q⁻¹ i j|)) ≤ H) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      (|(Q * stripLocalFrame K D r e n) i j| + |(Q * stripLocalFrame K D r e n)⁻¹ i j|)) ≤
        H * (2 * (K + (1 + D) * r + K⁻¹ + ((1 + D) * r)⁻¹)) :=
  strip_composite_entry_budget hQ (stripLocalFrame_entry_budget hK hD hr he hn hen)

/-- The frame size only incurs actual incoming and strip slack, so it can be
absorbed in any requested subpower output budget. -/
theorem strip_physical_frame_size_budget
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {K D r κ : ℝ} {T : ℕ} {e n : StripSpace}
    (hK : 0 < K) (hD : 0 ≤ D) (hr : 0 < r)
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1)
    (hQ : (∑ i : Fin 2, ∑ j : Fin 2, |Q i j|) ≤ κ / (2 : ℝ) ^ T) :
    (∑ i : Fin 2, ∑ j : Fin 2, |(Q * stripLocalFrame K D r e n) i j|) ≤
      (κ * (2 * (K + (1 + D) * r))) / (2 : ℝ) ^ T := by
  have hR : frameSize (stripLocalFrame K D r e n) ≤
      (2 * (K + (1 + D) * r)) / (2 : ℝ) ^ 0 := by
    simpa only [pow_zero, div_one, frameSize, stripLocalFrame] using
      Submission.Lib.K4FinitePlankAtlases.plankFrame_entries hK
        (show 0 < (1 + D) * r by positivity) he hn
  simpa only [Nat.add_zero, frameSize] using frameSize_mul_time (by positivity) hQ hR

def stripMidpointBinCount (κ r : ℝ) : ℕ := ⌈κ / r⌉₊

theorem stripMidpointBinCount_lower {κ r : ℝ} (hr : 0 < r) :
    κ ≤ (stripMidpointBinCount κ r : ℝ) * r := by
  exact (div_le_iff₀ hr).mp (Nat.le_ceil (κ / r))

theorem stripMidpointBinCount_upper {κ r : ℝ} (hκ : 0 ≤ κ) (hr : 0 < r) :
    (stripMidpointBinCount κ r : ℝ) * r ≤ κ + r := by
  have h := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (div_nonneg hκ hr.le)).le hr.le
  dsimp [stripMidpointBinCount]
  calc
    _ ≤ (κ / r + 1) * r := h
    _ = κ + r := by field_simp

theorem stripBinRange_center_budget {r : ℝ} {Z : ℕ} (hr : 0 ≤ r)
    {z : ℤ} (hz : z ∈ stripBinRange Z) : |(z : ℝ) * r| ≤ (Z : ℝ) * r := by
  have h : |(z : ℝ)| ≤ (Z : ℝ) := by
    rw [stripBinRange, Finset.mem_Icc] at hz
    rw [abs_le]
    constructor
    · exact_mod_cast hz.1
    · exact_mod_cast hz.2
  rw [abs_mul, abs_of_nonneg hr]
  exact mul_le_mul_of_nonneg_right h hr

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
