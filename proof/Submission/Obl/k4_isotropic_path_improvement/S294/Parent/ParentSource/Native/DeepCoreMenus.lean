-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.DeepCoreMenus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/DeepCoreMenus.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/DeepCoreMenus.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 7287edefaa58;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/DeepCoreMenus.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.DeepBaseMenus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PacketNativeCube
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.GoodCoreLists

/-! The actual unit-cube base of an intermediate native sheet is resolved
by a whole deeper original packet. Its nearby coded core centers therefore
have a bounded menu, with no total-center or inverse-grid-size factor. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Analytic

/-- The native coordinates used for the deep estimate agree with the
actual original packet base used in native sheet construction. -/
theorem PathData.native_base_coordinates_eq_packetBase {W : ℕ} (p : PathData W)
    (b : Fin p.C) (q : (ℕ × (Fin 6 → ℝ)) × ℝ) :
    WithLp.toLp 2 (p.nativeBaseCoordinates b q) = packetBase p b q := by
  ext j
  fin_cases j
  · rfl
  · simp [PathData.nativeBaseCoordinates, packetBase, nativeOldBaseFrame,
      Submission.Lib.K4ChartLifting.Frame.obsBase, packetPosition,
      Submission.Lib.K4XInterface.gy, Submission.Lib.K4XInterface.gx,
      Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.obs,
      Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.x,
      Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail,
      PiLp.add_apply, PiLp.smul_apply, Pi.smul_apply, smul_eq_mul]
  · simp [PathData.nativeBaseCoordinates, packetBase, nativeOldBaseFrame,
      Submission.Lib.K4ChartLifting.Frame.obsBase, packetPosition,
      Submission.Lib.K4XInterface.gy, Submission.Lib.K4XInterface.gx,
      Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.obs,
      Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.x,
      Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail,
      PiLp.add_apply, PiLp.smul_apply, Pi.smul_apply, smul_eq_mul]

section Path

variable {W : ℕ} {p : PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {profile : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
  {Mp Dp : ℕ} {σ : ℝ}

theorem PathData.Valid.deep_original_native_cube_box
    (hp : p.Valid Nk L ω ν E B profile κ₁ m s δ₀ Mp Dp σ) (hN : 1 ≤ Nk)
    (b f : Fin p.C) (hA : p.A f ⊆ p.A b) :
    ∃ anchor : Fin 3 → ℝ, ∀ x ∈ p.F f, ∀ j : Fin 3,
      |packetNativeCubePoint Nk B p b x j.castSucc - anchor j| ≤
        (1 + p.κ ^ 3 * Nk ^ (2 * δ₀ * L) + 2 * p.κ) *
          ((2 : ℝ) ^ p.T (p.lev b) / (2 : ℝ) ^ p.T (p.lev f)) := by
  obtain ⟨anchor, hanchor⟩ := hp.deep_original_base_box hN b f hA
  have hden : 0 < 6 * p.κ := by linarith [hp.1]
  have hdenOne : 1 ≤ 6 * p.κ := by linarith [hp.1]
  let cubeAnchor := nativeCubeBase (3 * p.κ) (WithLp.toLp 2 anchor)
  refine ⟨fun j => cubeAnchor j, ?_⟩
  intro x hx j
  have hcube := packetNativeCube_base_eq Nk B p b x
  rw [← p.native_base_coordinates_eq_packetBase b x] at hcube
  have hcoord := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z j) hcube
  change packetNativeCubePoint Nk B p b x j.castSucc =
    nativeCubeBase (3 * p.κ) (WithLp.toLp 2 (p.nativeBaseCoordinates b x)) j at hcoord
  rw [hcoord]
  have hcontract (t a : ℝ) : |(t + 3 * p.κ) / (6 * p.κ) -
      (a + 3 * p.κ) / (6 * p.κ)| ≤ |t - a| := by
    have hsub : (t + 3 * p.κ) - (a + 3 * p.κ) = t - a := by ring
    rw [← sub_div, hsub, abs_div, abs_of_pos hden]
    apply (div_le_iff₀ hden).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hdenOne (abs_nonneg (t - a))
  fin_cases j
  · exact hanchor x hx 0
  · change |(p.nativeBaseCoordinates b x 1 + 3 * p.κ) / (2 * (3 * p.κ)) -
        (anchor 1 + 3 * p.κ) / (2 * (3 * p.κ))| ≤ _
    simpa only [show 2 * (3 * p.κ) = 6 * p.κ by ring] using
      (hcontract (p.nativeBaseCoordinates b x 1) (anchor 1)).trans (hanchor x hx 1)
  · change |(p.nativeBaseCoordinates b x 2 + 3 * p.κ) / (2 * (3 * p.κ)) -
        (anchor 2 + 3 * p.κ) / (2 * (3 * p.κ))| ≤ _
    simpa only [show 2 * (3 * p.κ) = 6 * p.κ by ring] using
      (hcontract (p.nativeBaseCoordinates b x 2) (anchor 2)).trans (hanchor x hx 2)

/-- Coded intermediate native cores meeting one WHOLE deep original packet
have a menu independent of the total number of good centers. -/
theorem PathData.Valid.exists_deep_native_core_menu
    (hp : p.Valid Nk L ω ν E B profile κ₁ m s δ₀ Mp Dp σ) (hN : 1 ≤ Nk)
    (b f : Fin p.C) (hA : p.A f ⊆ p.A b)
    (center : (Fin 3 → ℤ) → EuclideanSpace ℝ (Fin 3))
    {mesh R : ℝ} (hmesh : 0 < mesh) (hR : 0 ≤ R)
    (hsmall : (1 + p.κ ^ 3 * Nk ^ (2 * δ₀ * L) + 2 * p.κ) *
      ((2 : ℝ) ^ p.T (p.lev b) / (2 : ℝ) ^ p.T (p.lev f)) ≤ mesh) :
    ∃ Menu : Finset (Fin 3 → ℤ), (Menu.card : ℝ) ≤ (4 * R + 6) ^ 3 ∧
      ∀ c : Fin 3 → ℤ, (∀ j, ⌊center c j / mesh⌋ = c j) →
        ∀ x ∈ p.F f,
          ‖WithLp.toLp 2 (fun j : Fin 3 => packetNativeCubePoint Nk B p b x j.castSucc) - center c‖ ≤
            R * mesh → c ∈ Menu := by
  obtain ⟨anchor, hanchor⟩ := hp.deep_original_native_cube_box hN b f hA
  obtain ⟨Menu, hcard, hcover⟩ := core_labels_over_resolved_base_box center hmesh hR anchor
  refine ⟨Menu, hcard, ?_⟩
  intro c hc x hx hnear
  exact hcover c hc _ (fun j => (hanchor x hx j).trans hsmall) hnear

/-- The actual quarter-core labels in NativeCoreEntryFamily use center
mesh radius/12 and have at most5832 choices per resolved deep packet. -/
theorem PathData.Valid.exists_deep_native_quarter_core_menu
    (hp : p.Valid Nk L ω ν E B profile κ₁ m s δ₀ Mp Dp σ) (hN : 1 ≤ Nk)
    (b f : Fin p.C) (hA : p.A f ⊆ p.A b)
    (center : (Fin 3 → ℤ) → EuclideanSpace ℝ (Fin 3))
    {K : ℝ} (hK : 0 < K) (R : ℕ)
    (hsmall : (1 + p.κ ^ 3 * Nk ^ (2 * δ₀ * L) + 2 * p.κ) *
      ((2 : ℝ) ^ p.T (p.lev b) / (2 : ℝ) ^ p.T (p.lev f)) ≤ (K ^ R)⁻¹ / 12) :
    ∃ Menu : Finset (Fin 3 → ℤ), (Menu.card : ℝ) ≤ 5832 ∧
      ∀ c : Fin 3 → ℤ, (∀ j, ⌊center c j / ((K ^ R)⁻¹ / 12)⌋ = c j) →
        ∀ x ∈ p.F f,
          ‖(K ^ R) • (WithLp.toLp 2 (fun j : Fin 3 =>
            packetNativeCubePoint Nk B p b x j.castSucc) - center c)‖ ≤ 1 / 4 → c ∈ Menu := by
  have hpR : 0 < K ^ R := pow_pos hK R
  obtain ⟨Menu, hcard, hcover⟩ := hp.exists_deep_native_core_menu hN b f hA center
    (show 0 < (K ^ R)⁻¹ / 12 by positivity) (show (0 : ℝ) ≤ 3 by norm_num) hsmall
  refine ⟨Menu, by norm_num at hcard ⊢; exact hcard, ?_⟩
  intro c hc x hx hnear
  apply hcover c hc x hx
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpR] at hnear
  have hcoeff : 3 * ((K ^ R)⁻¹ / 12) = (1 / 4 : ℝ) / (K ^ R) := by ring
  rw [hcoeff]
  exact (le_div_iff₀ hpR).mpr (by nlinarith)

end Path

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
