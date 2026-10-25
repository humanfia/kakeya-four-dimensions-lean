-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.PacketNativeLines, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/PacketNativeLines.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/PacketNativeLines.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 7287edefaa58;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/PacketNativeLines.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/PacketNativeLines.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PacketNativeMaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SpacetimeGradient

/-! # Actual affine lines in the local native comparison coordinates -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set
open Analytic k4_stable_native_signal_oscillation

noncomputable section

def packetCubeVelocity {W : ℕ} (p : Native.PathData W) (b : Fin p.C) (l : Line) :
    EuclideanSpace ℝ (Fin 2) :=
  (6 * p.κ)⁻¹ • v (normalizedPacketLine p b l)

theorem measurable_packetCubeVelocity {W : ℕ} (p : Native.PathData W) (b : Fin p.C) :
    Measurable (packetCubeVelocity p b) := by
  have hL := measurable_normalizedPacketLine p b
  have hc (j : Fin 6) : Measurable (fun l : Line => (normalizedPacketLine p b l).2 j) :=
    (measurable_pi_apply j).comp (measurable_snd.comp hL)
  have hV : Measurable (fun l : Line => v (normalizedPacketLine p b l)) := by
    unfold v
    apply (WithLp.measurable_toLp 2 _).comp
    apply measurable_pi_iff.mpr
    intro j
    fin_cases j
    · exact hc 3
    · exact hc 4
  exact hV.const_smul ((6 * p.κ)⁻¹)

def packetLocalCorePoint {W : ℕ} (Nk : ℝ) (B : Fin W → ℝ)
    (p : Native.PathData W) (b : Fin p.C) (K : ℝ) (R : ℕ)
    (c : EuclideanSpace ℝ (Fin 3)) (q : Event) : EuclideanSpace ℝ (Fin 3) :=
  (K ^ R) • (nativeBase (packetNativeCubePoint Nk B p b q) - c)

/-- Ordinary physical time parametrizes the ACTUAL local base line at
speed (1,V). The time conversion uses the original fine block length and
the comparison radius, with no derivative or independently chosen line. -/
theorem packetLocalCorePoint_line {W : ℕ} (Nk : ℝ) (B : Fin W → ℝ)
    (p : Native.PathData W) (b : Fin p.C) {K : ℝ} (hK : 0 < K) (R : ℕ)
    (hκ : p.κ ≠ 0) (c : EuclideanSpace ℝ (Fin 3)) (l : Line) (t τ : ℝ) :
    packetLocalCorePoint Nk B p b K R c
        (l, t + (((2 : ℝ) ^ p.T (p.lev b))⁻¹ * (K ^ R)⁻¹) * τ) =
      packetLocalCorePoint Nk B p b K R c (l, t) +
        τ • spacetimeDirection (packetCubeVelocity p b l) := by
  have hKR : K ^ R ≠ 0 := (pow_pos hK R).ne'
  have htwo : (2 : ℝ) ^ p.T (p.lev b) ≠ 0 := by positivity
  ext j
  fin_cases j <;>
    simp [packetLocalCorePoint, nativeBase, packetNativeCubePoint, nativeCubePoint,
      packetTime, nativeOldBaseFrame, spacetimeDirection, packetCubeVelocity, v, xp] <;>
    field_simp <;> ring

/-- The actual unit-base normalization makes EVERY assigned fine line's
planar speed at most one half, independent of all source formats. -/
theorem packetCubeVelocity_norm_le_half
    {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {weight : Fin W → ℝ}
    {ν : Fin W → Measure Line} {Ev : Fin W → Set Event} {B : Fin W → ℝ}
    {profile : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L weight ν Ev B profile κ₁ m s δ₀ Mp Dp σ)
    (b : Fin p.C) (l : Line) (hl : l ∈ p.A b) : ‖packetCubeVelocity p b l‖ ≤ 1 / 2 := by
  have hκ : 0 < p.κ := zero_lt_one.trans_le hp.1
  have hv : ‖v (normalizedPacketLine p b l)‖ ≤ 3 * p.κ := by
    have hh := (normalizedPacket_native_bounds hp b l hl 0 (by simp)).1
    linarith [norm_nonneg (y (normalizedPacketLine p b l) 0)]
  dsimp only [packetCubeVelocity]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (6 * p.κ)⁻¹)]
  calc
    _ ≤ (6 * p.κ)⁻¹ * (3 * p.κ) := mul_le_mul_of_nonneg_left hv (by positivity)
    _ = 1 / 2 := by field_simp; norm_num

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
