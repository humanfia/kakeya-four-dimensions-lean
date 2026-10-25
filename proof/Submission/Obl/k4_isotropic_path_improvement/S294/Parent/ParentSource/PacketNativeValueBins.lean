-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.PacketNativeValueBins, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/PacketNativeValueBins.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/PacketNativeValueBins.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/PacketNativeValueBins.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/PacketNativeValueBins.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PacketNativeCube
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.NativeCubeCurvature

/-! # Stable native equations from original fine-packet value bins -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set MvPolynomial
open Analytic k4_quadratic_atlas_normalization

noncomputable section

def packetNativeValueTest {W : ℕ} (Nk : ℝ) (B : Fin W → ℝ)
    (p : Native.PathData W) (b : Fin p.C) (center : ℝ) : Poly :=
  packetNativeCubeTest Nk B p b - C center

theorem packetNativeValueTest_pderiv {W : ℕ} (Nk : ℝ) (B : Fin W → ℝ)
    (p : Native.PathData W) (b : Fin p.C) (center : ℝ) :
    pderiv 3 (packetNativeValueTest Nk B p b center) =
      pderiv 3 (packetNativeCubeTest Nk B p b) := by
  simp [packetNativeValueTest]

theorem packetNativeValueTest_curvature {W : ℕ} (Nk : ℝ) (B : Fin W → ℝ)
    (p : Native.PathData W) (b : Fin p.C) (center : ℝ) :
    curvature (packetNativeValueTest Nk B p b center) 3 =
      curvature (packetNativeCubeTest Nk B p b) 3 := by
  simp [packetNativeValueTest, curvature]

/-- The degree and curvature bounds hold globally for the actual bin
equation, before restricting to any entry or choosing a branch. -/
theorem packetNativeValueTest_global_data
    {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Line} {E : Fin W → Set Event} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hNk : 0 < Nk) (b : Fin p.C) (hB : 0 < B (p.γ b))
    {K ε : ℝ} (hK : 2 ≤ K) (hκK : 3 * p.κ ≤ K)
    (hε : 0 < ε) (hεK : ε ≤ (K ^ 6)⁻¹) (center : ℝ) :
    (packetNativeValueTest Nk B p b center).totalDegree ≤ 2 ∧
      |curvature (packetNativeValueTest Nk B p b center) 3| ≤ K / ε ∧
      |curvature (packetNativeValueTest Nk B p b center) 3| ≤ (K ^ 5 * ε)⁻¹ := by
  have hcurv : |curvature (packetNativeValueTest Nk B p b center) 3| ≤ K := by
    rw [packetNativeValueTest_curvature]
    exact (packetNativeCube_curvature hp hNk b hB).trans hκK
  have hε1 : ε ≤ 1 := hεK.trans
    (inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith : 1 ≤ K)))
  refine ⟨(totalDegree_sub _ _).trans
    (max_le (packetNativeCubeTest_degree hp b) (by simp)), ?_,
      native_value_bin_small_curvature hK hε hεK hcurv⟩
  apply hcurv.trans
  apply (le_div_iff₀ hε).mpr
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hε1 (show 0 ≤ K by linarith)

/-- Every ORIGINAL source incidence in a sufficiently narrow value bin
supplies the exact unit-base, derivative and small-curvature hypotheses
of uniform branch preparation. No inherited posterior bound is used. -/
theorem packetNativeValueTest_source_data
    {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Line} {E : Fin W → Set Event} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hNk : 0 < Nk) (b : Fin p.C) (hB : 0 < B (p.γ b))
    {K ε : ℝ} (hK : 2 ≤ K) (hκK : 3 * p.κ ≤ K)
    (hε : 0 < ε) (hεK : ε ≤ (K ^ 6)⁻¹) (center : ℝ)
    {q : Event} (hq : q ∈ p.F b)
    (hbin : |eval (fun j => packetNativeCubePoint Nk B p b q j)
      (packetNativeCubeTest Nk B p b) - center| ≤ K * ε) :
    (packetNativeValueTest Nk B p b center).totalDegree ≤ 2 ∧
      |curvature (packetNativeValueTest Nk B p b center) 3| ≤ K / ε ∧
      |curvature (packetNativeValueTest Nk B p b center) 3| ≤ (K ^ 5 * ε)⁻¹ ∧
      (fun j : Fin 3 => packetNativeCubePoint Nk B p b q j.castSucc) ∈ Icc 0 1 ∧
      |eval (fun j => packetNativeCubePoint Nk B p b q j)
        (packetNativeValueTest Nk B p b center)| ≤ K * ε ∧
      K⁻¹ ≤ |eval (fun j => packetNativeCubePoint Nk B p b q j)
        (pderiv 3 (packetNativeValueTest Nk B p b center))| ∧
      |eval (fun j => packetNativeCubePoint Nk B p b q j)
        (pderiv 3 (packetNativeValueTest Nk B p b center))| ≤ K := by
  have hpoint := packetNativeCube_source_bounds hp b hB hq
  obtain ⟨hdeg, hcurv, hsmall⟩ := packetNativeValueTest_global_data hp hNk b hB hK hκK hε hεK center
  refine ⟨hdeg, hcurv, hsmall, hpoint.1, ?_, ?_, ?_⟩
  · simpa only [packetNativeValueTest, map_sub, eval_C] using hbin
  · rw [packetNativeValueTest_pderiv]
    exact (inv_anti₀ (show 0 < 3 * p.κ by linarith [hp.1]) hκK).trans hpoint.2.2.1
  · rw [packetNativeValueTest_pderiv]
    exact hpoint.2.2.2.1.trans hκK

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
