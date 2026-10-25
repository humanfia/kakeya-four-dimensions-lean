/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/NormalizedAssignments.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.BalancedNormalization
import Submission.Obl.k4_balanced_native_packet_transport.CPF.PacketCancellation

/-! Exact original assignment masses for children of the actual normalized
worlds. The selected incidence events do not enter the prior normalization. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF
namespace NormalizedAssignments

open MeasureTheory Set
open Submission.Obl.k4_dyadic_crop_affine_laws.Framework

abbrev SourceData := Submission.Obl.k4_remainder_pure_profile_normalization.Data
abbrev SourceAtlas := Submission.Obl.k4_remainder_pure_profile_normalization.Atlas

/-- The actual coefficient normalization, bundled with its accepted inverse
and measurability laws. -/
noncomputable def trajectoryEquiv {p : SourceData} {k : ℕ}
    (a : SourceAtlas p k) (b : Fin a.C) (hQ : (a.Q b).det ≠ 0) :
    Trajectory ≃ᵐ Trajectory where
  toFun := (a.system.frameOf b).normTraj
  invFun := (a.system.frameOf b).denormTraj
  left_inv := a.system.denormTraj_normTraj' b (isUnit_iff_ne_zero.mpr hQ)
  right_inv := a.system.normTraj_denormTraj b (isUnit_iff_ne_zero.mpr hQ)
  measurable_toFun :=
    Submission.Obl.k4_remainder_pure_profile_normalization.Normalization.ChartSystem.measurable_normTraj _
  measurable_invFun := (a.system.frameOf b).measurable_denormTraj

theorem normalized_prior_eq {p : SourceData} {k : ℕ}
    (a : SourceAtlas p k) (b : Fin a.C) (hQ : (a.Q b).det ≠ 0) :
    a.system.normPrior (p.ν k) b =
      conditionedPrior (p.ν k (a.γ b)) (a.A b) (trajectoryEquiv a b hQ) := rfl

/-- The full original child assignment is the parent's assignment intersected
with the preimage of the normalized child's full assignment. -/
def originalAssignment {p : SourceData} {k : ℕ} (a : SourceAtlas p k)
    (b : Fin a.C) (hQ : (a.Q b).det ≠ 0) (B : Set Trajectory) : Set Trajectory :=
  a.A b ∩ trajectoryEquiv a b hQ ⁻¹' B

theorem measurableSet_originalAssignment {p : SourceData} {k : ℕ}
    (a : SourceAtlas p k) (b : Fin a.C) (hQ : (a.Q b).det ≠ 0)
    (hA : MeasurableSet (a.A b)) (B : Set Trajectory) (hB : MeasurableSet B) :
    MeasurableSet (originalAssignment a b hQ B) :=
  hA.inter ((trajectoryEquiv a b hQ).measurable hB)

theorem normalized_assignment_mass {p : SourceData} {k : ℕ}
    (a : SourceAtlas p k) (b : Fin a.C) (hQ : (a.Q b).det ≠ 0)
    [IsFiniteMeasure (p.ν k (a.γ b))] (B : Set Trajectory) (hB : MeasurableSet B) :
    (a.system.normPrior (p.ν k) b B).toReal =
      (p.ν k (a.γ b) (originalAssignment a b hQ B)).toReal /
        (p.ν k (a.γ b) (a.A b)).toReal := by
  rw [normalized_prior_eq]
  exact PacketCancellation.conditional_assignment_mass _ _ _ _ hB

/-- Apply density cancellation directly to the actual normalized prior and
the actual composed spatial frame, with no additional mass identity assumed. -/
theorem original_assignment_balance {p : SourceData} {k : ℕ}
    (a : SourceAtlas p k) (b : Fin a.C) (hQ : (a.Q b).det ≠ 0)
    [IsFiniteMeasure (p.ν k (a.γ b))] (B : Set Trajectory) (hB : MeasurableSet B)
    (R : Frame) (hR : R.det ≠ 0) {N fL F₁ Fb α ε d depth : ℝ}
    (hN : 1 ≤ N) (ha : 0 < (p.ν k (a.γ b) (a.A b)).toReal)
    (hparent : N ^ (α - ε) ≤ |(a.Q b).det| / (p.ν k (a.γ b) (a.A b)).toReal ∧
      |(a.Q b).det| / (p.ν k (a.γ b) (a.A b)).toReal ≤ N ^ (α + ε))
    (hchild : N ^ (-Fb - ε) ≤ (a.system.normPrior (p.ν k) b B).toReal / |R.det| ∧
      (a.system.normPrior (p.ν k) b B).toReal / |R.det| ≤ N ^ (-Fb + ε))
    (hterminal : F₁ = fL - α)
    (hold : |fL - d| ≤ ε)
    (hrelative : |F₁ - Fb - d * (1 - depth)| ≤ ε) :
    N ^ (-d * depth - 4 * ε) ≤
        (p.ν k (a.γ b) (originalAssignment a b hQ B)).toReal / |(a.Q b * R).det| ∧
      (p.ν k (a.γ b) (originalAssignment a b hQ B)).toReal / |(a.Q b * R).det| ≤
        N ^ (-d * depth + 4 * ε) := by
  exact PacketCancellation.original_assignment_balance (p.ν k (a.γ b))
    (a.A b) (trajectoryEquiv a b hQ) B hB (a.Q b) R hN ha hQ hR
    hparent hchild hterminal hold hrelative

/-- Keep the fixed outer profile error separate from the arbitrarily small
inner calibration tolerance. This is the form used before the two-limit
diagonal in balanced packets. -/
theorem original_assignment_relative_band {p : SourceData} {k : ℕ}
    (a : SourceAtlas p k) (b : Fin a.C) (hQ : (a.Q b).det ≠ 0)
    [IsFiniteMeasure (p.ν k (a.γ b))] (B : Set Trajectory) (hB : MeasurableSet B)
    (R : Frame) (hR : R.det ≠ 0) {N fL F₁ Fb α ε err d depth : ℝ}
    (hN : 1 ≤ N) (ha : 0 < (p.ν k (a.γ b) (a.A b)).toReal)
    (hparent : N ^ (α - ε) ≤ |(a.Q b).det| / (p.ν k (a.γ b) (a.A b)).toReal ∧
      |(a.Q b).det| / (p.ν k (a.γ b) (a.A b)).toReal ≤ N ^ (α + ε))
    (hchild : N ^ (-Fb - ε) ≤ (a.system.normPrior (p.ν k) b B).toReal / |R.det| ∧
      (a.system.normPrior (p.ν k) b B).toReal / |R.det| ≤ N ^ (-Fb + ε))
    (hterminal : F₁ = fL - α)
    (hold : |fL - d| ≤ err)
    (hrelative : |F₁ - Fb - d * (1 - depth)| ≤ 2 * err) :
    N ^ (-d * depth - (3 * err + 2 * ε)) ≤
        (p.ν k (a.γ b) (originalAssignment a b hQ B)).toReal / |(a.Q b * R).det| ∧
      (p.ν k (a.γ b) (originalAssignment a b hQ B)).toReal / |(a.Q b * R).det| ≤
        N ^ (-d * depth + (3 * err + 2 * ε)) := by
  have hN₀ : 0 < N := by linarith
  have hdet : |(a.Q b * R).det| / |(a.Q b).det| = |R.det| := by
    rw [Matrix.det_mul, abs_mul, mul_div_cancel_left₀ _ (abs_ne_zero.mpr hQ)]
  have hchild' : N ^ (-Fb - ε) ≤
      ((p.ν k (a.γ b) (originalAssignment a b hQ B)).toReal /
        (p.ν k (a.γ b) (a.A b)).toReal) /
          (|(a.Q b * R).det| / |(a.Q b).det|) ∧
      ((p.ν k (a.γ b) (originalAssignment a b hQ B)).toReal /
        (p.ν k (a.γ b) (a.A b)).toReal) /
          (|(a.Q b * R).det| / |(a.Q b).det|) ≤ N ^ (-Fb + ε) := by
    simpa only [hdet, ← normalized_assignment_mass a b hQ B hB] using hchild
  have h := PacketCancellation.ratio_bounds hN₀ ha (abs_pos.mpr hQ)
    (abs_pos.mpr (by rw [Matrix.det_mul]; exact mul_ne_zero hQ hR))
    hparent hchild' hterminal
  have ho := abs_le.mp hold
  have hr := abs_le.mp hrelative
  constructor
  · exact (Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)).trans h.1
  · exact h.2.trans (Real.rpow_le_rpow_of_exponent_le hN (by nlinarith))

end NormalizedAssignments
end Submission.Obl.k4_balanced_native_packet_transport.CPF
