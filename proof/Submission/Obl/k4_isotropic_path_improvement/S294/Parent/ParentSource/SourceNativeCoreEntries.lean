-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.SourceNativeCoreEntries, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/SourceNativeCoreEntries.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/SourceNativeCoreEntries.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 7287edefaa58;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/SourceNativeCoreEntries.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/SourceNativeCoreEntries.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.NativeCoreEntries
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PacketNativeMaps

/-! # Coherent original core/sign entries for an actual fine value bin -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set MvPolynomial
open Analytic k4_stable_native_signal_oscillation

noncomputable section

/-- Every actual fine value entry with its original coded branch cover
has a measurable core/sign family, fixed F/f on each raw entry, exact
corrected-root matching and earlier heavy floors. All source tests and
measurability are derived from the SAME original path packet here.
The law μ keeps whatever FULL-prior scalar the preceding cover used. -/
theorem packet_value_native_core_entries
    {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {weight : Fin W → ℝ}
    {ν : Fin W → Measure Line} {Ev : Fin W → Set Event} {B : Fin W → ℝ}
    {profile : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L weight ν Ev B profile κ₁ m s δ₀ Mp Dp σ)
    (hNk : 0 < Nk) (b : Fin p.C) (hB : 0 < B (p.γ b))
    {K ε : ℝ} (hK : 2 ≤ K) (hκK : 3 * p.κ ≤ K)
    (hε : 0 < ε) (hεK : ε ≤ (K ^ 6)⁻¹) (center : ℝ)
    (μ : Measure Event) (G : Set Event) (hG : MeasurableSet G)
    (hsupp : ∀ᵐ z ∂μ, z ∈ G) (hGF : G ⊆ p.F b)
    (hbin : ∀ z ∈ G, |packetSignal Nk p b z - center| ≤ ε)
    {e R : ℕ}
    (hcover : NativeQuarterBranchCover e R K (packetNativeValueTest Nk B p b center) μ
      (fun z j => packetNativeCubePoint Nk B p b z j.castSucc)) (θ : ENNReal) :
    NativeCoreEntryFamily e R K (packetNativeValueTest Nk B p b center) μ
      (packetNativeCubePoint Nk B p b) G θ := by
  obtain ⟨hdeg, _, hsmall⟩ := packetNativeValueTest_global_data hp hNk b hB hK hκK hε hεK center
  have hε1 : ε ≤ 1 := hεK.trans
    (inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith : 1 ≤ K)))
  apply heavy_original_native_core_entries μ (packetNativeCubePoint Nk B p b)
    (measurable_packetNativeCubePoint Nk B p b) G hG hsupp
    (packetNativeValueTest Nk B p b center) hdeg hK hε hε1 hsmall ?_ hcover θ
  intro z hz
  have heval := (packetNativeCubePolynomial_original_values hp b hB (p.R b) z).1
  change eval (fun j => packetNativeCubePoint Nk B p b z j) (packetNativeCubeTest Nk B p b) =
    packetSignal Nk p b z at heval
  have hbin' : |eval (fun j => packetNativeCubePoint Nk B p b z j)
      (packetNativeCubeTest Nk B p b) - center| ≤ K * ε := by
    rw [heval]
    exact (hbin z hz).trans (le_mul_of_one_le_left hε.le (by linarith : 1 ≤ K))
  have hpoint := packetNativeValueTest_source_data hp hNk b hB hK hκK hε hεK center (hGF hz) hbin'
  exact ⟨hpoint.2.2.2.2.1, hpoint.2.2.2.2.2.1⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
