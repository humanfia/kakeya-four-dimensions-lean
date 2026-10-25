-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.OriginalScalarCoordinates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/OriginalScalarCoordinates.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 83ada3e49b5540f6b00606ae3df6268df68021ab,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/OriginalScalarCoordinates.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalNativeCoordinates
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AssignedGridGeometry

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory SourceGeometry
open Broad.Source

noncomputable section

def scalarPhysicalPoint (c : Fin 7 → ℝ) (t : ℝ) : Fin 4 → ℝ :=
  ![t, Jets2.zy c t 0, Jets2.zy c t 1, Jets2.zx c t]

section Path

variable {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

def Native.PathData.Valid.assignedScalarCoefficients (old : Fin p.C)
    (l : (hp.frozenPacket old).AssignedLine) : Fin 7 → ℝ :=
  (hp.frozenPacket old).scalarCoefficients l

include hp

/-- The independent canonical quadratic implementations give the same
actual signal coefficients. -/
theorem Native.PathData.Valid.frozenPacket_coefficients (old : Fin p.C) (l : Ln) :
    (hp.frozenPacket old).coefficients l = normalizedPacketCoefficients Nk p old l := by
  have hs (t : ℝ) : Submission.Lib.K4ProjectedGroups.sig (hp.frozenPacket old).test
      ((hp.frozenPacket old).line l).2 t = normalizedPacketCurve Nk p old l t := rfl
  ext j
  fin_cases j
  · exact hs 0
  · change Submission.Lib.K4ProjectedGroups.sc1 _ _ =
      -normalizedPacketCurve Nk p old l 1 + 4 * normalizedPacketCurve Nk p old l (1 / 2) -
        3 * normalizedPacketCurve Nk p old l 0
    simp only [Submission.Lib.K4ProjectedGroups.sc1, hs]
    ring
  · change Submission.Lib.K4ProjectedGroups.sc2 _ _ =
      2 * normalizedPacketCurve Nk p old l 1 - 4 * normalizedPacketCurve Nk p old l (1 / 2) +
        2 * normalizedPacketCurve Nk p old l 0
    simp only [Submission.Lib.K4ProjectedGroups.sc2, hs]
    ring

theorem Native.PathData.Valid.measurable_assignedScalarCoefficients (old : Fin p.C) :
    Measurable (hp.assignedScalarCoefficients old) :=
  (hp.frozenPacket old).measurable_scalarCoefficients.comp measurable_subtype_coe

theorem Native.PathData.Valid.assignedScalarCoefficients_bound (old : Fin p.C)
    (l : (hp.frozenPacket old).AssignedLine) (j : Fin 7) :
    |hp.assignedScalarCoefficients old l j| ≤ 17 * p.κ :=
  (hp.frozenPacket old).scalar_coefficients_bound l l.property j

/-- The scalar-normal world and the original MK4 source have exactly
the same spacetime point, in the order time, two base positions, height. -/
theorem Native.PathData.Valid.assigned_scalar_physical_point (old : Fin p.C)
    (z : (hp.frozenPacket old).AssignedLine × ℝ) :
    scalarPhysicalPoint (hp.assignedScalarCoefficients old z.1) z.2 =
      WithLp.ofLp (nativePhysicalCurve (normalizedPacketTest Nk p old)
        (normalizedPacketPosition p old z.1) (normalizedPacketVelocity p old z.1) z.2) := by
  let packet := hp.frozenPacket old
  unfold scalarPhysicalPoint Native.PathData.Valid.assignedScalarCoefficients
  rw [packet.scalar_x, packet.scalar_y]
  ext j
  fin_cases j
  · simp [nativePhysicalCurve, liftedVector, normalizedPacketPosition, normalizedPacketVelocity, xp]
  · simp [nativePhysicalCurve, liftedVector, normalizedPacketPosition, normalizedPacketVelocity, xp,
      Submission.Lib.K4XInterface.gy, Submission.Lib.K4XInterface.gx, packet, hp.frozenPacket_line]
  · simp [nativePhysicalCurve, liftedVector, normalizedPacketPosition, normalizedPacketVelocity, xp,
      Submission.Lib.K4XInterface.gy, Submission.Lib.K4XInterface.gx, packet, hp.frozenPacket_line]
  · change MvPolynomial.eval (xp (normalizedPacketLine p old z.1) z.2)
      (normalizedPacketTest Nk p old) = _
    rw [normalizedPacketMotion]
    rfl

theorem Native.PathData.Valid.assigned_scalar_row_identity (old : Fin p.C)
    (z : (hp.frozenPacket old).AssignedLine × ℝ) (row : Fin 3 → ℝ) :
    hp.assignedScalarCoefficients old z.1 1 +
        2 * hp.assignedScalarCoefficients old z.1 2 * z.2 -
      (row 0 + row 1 * hp.assignedScalarCoefficients old z.1 4 +
        row 2 * hp.assignedScalarCoefficients old z.1 6) =
    2 * normalizedPacketCoefficients Nk p old z.1 2 * z.2 +
        normalizedPacketCoefficients Nk p old z.1 1 -
      ∑ j : Fin 3, row j * normalizedPacketVelocity p old z.1 j.castSucc := by
  change (hp.frozenPacket old).coefficients z.1 1 +
      2 * (hp.frozenPacket old).coefficients z.1 2 * z.2 -
    (row 0 + row 1 * ((hp.frozenPacket old).line z.1).2 3 +
      row 2 * ((hp.frozenPacket old).line z.1).2 4) = _
  rw [hp.frozenPacket_coefficients]
  simp only [Fin.sum_univ_three]
  change _ = 2 * normalizedPacketCoefficients Nk p old z.1 2 * z.2 +
    normalizedPacketCoefficients Nk p old z.1 1 -
      (row 0 * 1 + row 1 * ((hp.frozenPacket old).line z.1).2 3 +
        row 2 * ((hp.frozenPacket old).line z.1).2 4)
  ring

/-- The row index of the actual source is the literal anisotropic grid
code of the scalar-normal spacetime point. -/
theorem Native.PathData.Valid.assigned_scalar_physical_code (old : Fin p.C)
    (baseMesh hidden : ℝ) (z : (hp.frozenPacket old).AssignedLine × ℝ) :
    hp.assignedFineCode old baseMesh hidden z = fun j =>
      ⌊scalarPhysicalPoint (hp.assignedScalarCoefficients old z.1) z.2 j /
        (if j = 3 then hidden else baseMesh)⌋ := by
  rw [hp.assigned_scalar_physical_point]
  exact hp.assigned_physical_code old baseMesh hidden z

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
