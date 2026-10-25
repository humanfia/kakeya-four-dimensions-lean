-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.PacketNativeMaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/PacketNativeMaps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/PacketNativeMaps.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 7287edefaa58;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/PacketNativeMaps.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/PacketNativeMaps.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PacketNativeValueBins

/-! # Actual measurable native points and their original corrected roots -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set MvPolynomial
open Analytic k4_stable_native_signal_oscillation k4_quadratic_atlas_normalization

noncomputable section

theorem measurable_packetNativeCubePoint {W : ℕ} (Nk : ℝ) (B : Fin W → ℝ)
    (p : Native.PathData W) (b : Fin p.C) : Measurable (packetNativeCubePoint Nk B p b) := by
  have hτ : Measurable (packetTime p b) := by unfold packetTime; fun_prop
  have hL : Measurable (fun q : Event => normalizedPacketLine p b q.1) :=
    (measurable_normalizedPacketLine p b).comp measurable_fst
  have hc (j : Fin 6) : Measurable (fun q : Event => (normalizedPacketLine p b q.1).2 j) :=
    (measurable_pi_apply j).comp (measurable_snd.comp hL)
  have hx : Measurable (fun q : Event => xp (normalizedPacketLine p b q.1) (packetTime p b q)) := by
    unfold xp
    apply measurable_pi_iff.mpr
    intro j
    fin_cases j
    · exact hτ
    · exact (hc 0).add (hτ.mul (hc 3))
    · exact (hc 1).add (hτ.mul (hc 4))
    · exact (hc 2).add (hτ.mul (hc 5))
  have hmap : Measurable (fun x : Fin 4 → ℝ => WithLp.toLp 2
      (nativeCubePoint (3 * p.κ) (B (p.γ b)) (δ Nk (p.r (p.lev b))) x)) := by
    apply (WithLp.measurable_toLp 2 _).comp
    apply measurable_pi_iff.mpr
    intro j
    fin_cases j <;> simp only [nativeCubePoint] <;> fun_prop
  exact hmap.comp hx

/-- Original packet and value-bin tests give the exact measurable
corrected root and its simplicity. Every old quadratic signal has the
scale-invariant K^14*epsilon prediction error in these SAME fine units. -/
theorem packetNativeValueTest_root_data
    {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {weight : Fin W → ℝ}
    {ν : Fin W → Measure Line} {Ev : Fin W → Set Event} {B : Fin W → ℝ}
    {profile : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L weight ν Ev B profile κ₁ m s δ₀ Mp Dp σ)
    (hNk : 0 < Nk) (b : Fin p.C) (hB : 0 < B (p.γ b))
    {K ε : ℝ} (hK : 2 ≤ K) (hκK : 3 * p.κ ≤ K)
    (hε : 0 < ε) (hεK : ε ≤ (K ^ 6)⁻¹) (center : ℝ)
    {q : Event} (hq : q ∈ p.F b) (hbin : |packetSignal Nk p b q - center| ≤ ε) :
    let P := packetNativeValueTest Nk B p b center
    let X := packetNativeCubePoint Nk B p b q
    value P (rootLift P X) = 0 ∧ value (pderiv 3 P) (rootLift P X) ≠ 0 ∧
      ∀ S : Poly, S.totalDegree ≤ 2 → |value (pderiv 3 S) X| ≤ K → |curvature S 3| ≤ K →
        |value S (rootLift P X) - value S X| ≤ K ^ 14 * ε := by
  dsimp only
  have hKp : 0 < K := by linarith
  have hvalue := (packetNativeCubePolynomial_original_values hp b hB (p.R b) q).1
  change eval (fun j => packetNativeCubePoint Nk B p b q j) (packetNativeCubeTest Nk B p b) =
    packetSignal Nk p b q at hvalue
  have hbin' : |eval (fun j => packetNativeCubePoint Nk B p b q j)
      (packetNativeCubeTest Nk B p b) - center| ≤ K * ε := by
    rw [hvalue]
    exact hbin.trans (le_mul_of_one_le_left hε.le (by linarith : 1 ≤ K))
  obtain ⟨hdeg, _, hsmall, _, hval, hlow, _⟩ := packetNativeValueTest_source_data hp hNk b hB
    hK hκK hε hεK center hq hbin'
  have hε1 : ε ≤ 1 := hεK.trans
    (inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith : 1 ≤ K)))
  have hroot := rootLift_spec (packetNativeValueTest Nk B p b center) 0 hdeg (by simp)
    hK hε hε1 hsmall (packetNativeCubePoint Nk B p b q) hval hlow
    (by simpa [value] using hKp.le) (by simpa [curvature] using hKp.le)
  refine ⟨hroot.1, hroot.2.1, ?_⟩
  intro S hS hS1 hS2
  exact (rootLift_spec (packetNativeValueTest Nk B p b center) S hdeg hS hK hε hε1 hsmall
    (packetNativeCubePoint Nk B p b q) hval hlow hS1 hS2).2.2

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
