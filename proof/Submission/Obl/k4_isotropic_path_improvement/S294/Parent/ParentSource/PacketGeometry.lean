-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.PacketGeometry, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/PacketGeometry.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/PacketGeometry.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/PacketGeometry.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.NativeCapAssembly

/-! # Actual normalized native packet trajectories -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set

noncomputable section

def normalizedPacketLine {W : ℕ} (p : Native.PathData W) (b : Fin p.C) (l : Line) : Line :=
  (nativeOldBaseFrame p b).normTraj l

def normalizedPacketTest {W : ℕ} (Nk : ℝ) (p : Native.PathData W) (b : Fin p.C) :
    MvPolynomial (Fin 4) ℝ :=
  (nativeOldBaseFrame p b).normTest (δ Nk (p.r (p.lev b))) (p.R b)

def normalizedPacketPosition {W : ℕ} (p : Native.PathData W) (b : Fin p.C) (l : Line) :
    Fin 4 → ℝ := xp (normalizedPacketLine p b l) 0

def normalizedPacketVelocity {W : ℕ} (p : Native.PathData W) (b : Fin p.C) (l : Line) :
    Fin 4 → ℝ :=
  ![1, (normalizedPacketLine p b l).2 3, (normalizedPacketLine p b l).2 4,
    (normalizedPacketLine p b l).2 5]

theorem normalizedPacketVelocity_time {W : ℕ} (p : Native.PathData W)
    (b : Fin p.C) (l : Line) : normalizedPacketVelocity p b l 0 = 1 := rfl

/-- These are the position and velocity of the same normalized original
trajectory, rather than independent geometric witnesses. -/
theorem normalizedPacketMotion {W : ℕ} (p : Native.PathData W) (b : Fin p.C)
    (l : Line) (t : ℝ) :
    xp (normalizedPacketLine p b l) t =
      fun j => normalizedPacketPosition p b l j + t * normalizedPacketVelocity p b l j := by
  funext j
  fin_cases j <;> simp [normalizedPacketPosition, normalizedPacketVelocity, xp]

theorem measurable_normalizedPacketLine {W : ℕ} (p : Native.PathData W) (b : Fin p.C) :
    Measurable (normalizedPacketLine p b) :=
  Submission.Lib.K4ChartLifting.ChartSystem.measurable_normTraj _

section Path

variable {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Line} {E : Fin W → Set Event} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

theorem normalizedPacketTest_degree (b : Fin p.C) :
    (normalizedPacketTest Nk p b).totalDegree ≤ 2 := by
  rcases (hp.2.2.2.2.2.2.2 b).2.2 with ⟨_, _, _, _, hdeg, _⟩
  exact ((nativeOldBaseFrame p b).totalDegree_normTest_le _ _).trans hdeg

/-- Every original trajectory of the full old assignment has the native
unit-time geometry required by the physical graph construction. All losses
come from the actual path tolerance, independently of the format exponent. -/
theorem normalizedPacket_native_bounds (b : Fin p.C) (l : Line) (hl : l ∈ p.A b)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖y (normalizedPacketLine p b l) t‖ + ‖v (normalizedPacketLine p b l)‖ ≤ 3 * p.κ ∧
      |MvPolynomial.eval (xp (normalizedPacketLine p b l) t) (normalizedPacketTest Nk p b)| ≤ p.κ ∧
      |MvPolynomial.eval (xp (normalizedPacketLine p b l) t)
        (MvPolynomial.pderiv 3 (normalizedPacketTest Nk p b))| ≤
          p.κ * (B (p.γ b) / δ Nk (p.r (p.lev b))) ∧
      |MvPolynomial.eval (xp (normalizedPacketLine p b l) t)
        (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 (normalizedPacketTest Nk p b)))| ≤
          p.κ * (B (p.γ b) / δ Nk (p.r (p.lev b))) ^ 2 := by
  let F := nativeOldBaseFrame p b
  have hq : 0 < F.q := by change 0 < ((2 : ℝ) ^ p.T (p.lev b))⁻¹; positivity
  have hδ : 0 < δ Nk (p.r (p.lev b)) := by unfold δ; positivity
  rcases (hp.2.2.2.2.2.2.2 b).2.2 with
    ⟨hdet, _, _, _, _, _, _, _, _, hwhole, _, _⟩
  have hright : F.t₀ + F.q =
      ((p.j b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b) := by dsimp [F, nativeOldBaseFrame]; ring
  have htime (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) :
      F.t₀ + F.q * τ ∈ Icc ((p.j b : ℝ) / (2 : ℝ) ^ p.T (p.lev b))
        (((p.j b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)) := by
    change F.t₀ ≤ F.t₀ + F.q * τ ∧
      F.t₀ + F.q * τ ≤ ((p.j b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)
    rw [← hright]
    constructor <;> nlinarith [hτ.1, hτ.2]
  have hfit : ∀ τ ∈ Icc F.t₀ (F.t₀ + F.q),
      ‖Matrix.toEuclideanLin F.D⁻¹
        (Submission.Lib.K4ChartLifting.planarPoint l τ - F.c - τ • F.u)‖ ≤ p.κ := by
    intro τ hτ
    have hτ' : τ ∈ Icc ((p.j b : ℝ) / (2 : ℝ) ^ p.T (p.lev b))
        (((p.j b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)) := by
      refine ⟨hτ.1, ?_⟩
      rw [← hright]
      exact hτ.2
    exact ((hwhole l hl).2.2 τ hτ').1
  have hplan := Submission.Lib.K4ChartLifting.norm_planar_add_velocity_le
    (fun τ hτ => F.norm_planar_normTraj_le hq l hfit τ hτ) t ht
  obtain ⟨_, hval, hfirst, hsecond⟩ := (hwhole l hl).2.2 _ (htime t ht)
  have hnative := F.normTest_bounds hq.ne' (isUnit_iff_ne_zero.mpr hdet) hδ
    (p.R b) l t hval hfirst hsecond
  exact ⟨hplan, hnative⟩

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
