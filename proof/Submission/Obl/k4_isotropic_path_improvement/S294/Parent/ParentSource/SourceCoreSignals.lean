-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.SourceCoreSignals, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/SourceCoreSignals.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/SourceCoreSignals.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 7287edefaa58;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/SourceCoreSignals.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/SourceCoreSignals.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.NativeCoreCoordinates
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PacketNativeMaps

/-! # Original old signals on the actual coherent fine core branch -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set MvPolynomial
open Analytic k4_stable_native_signal_oscillation k4_quadratic_atlas_normalization

noncomputable section

/-- The SAME fixed branch selected on an earlier original entry predicts
an ORIGINAL quadratic signal in local coordinates, in FINE signal units.
Only the actual old hidden derivative and curvature enter the estimate. -/
theorem packet_signal_core_prediction
    {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {weight : Fin W → ℝ}
    {ν : Fin W → Measure Line} {Ev : Fin W → Set Event} {B : Fin W → ℝ}
    {profile : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L weight ν Ev B profile κ₁ m s δ₀ Mp Dp σ)
    (hNk : 0 < Nk) (b : Fin p.C) (hB : 0 < B (p.γ b))
    {K ε : ℝ} (hK : 2 ≤ K) (hκK : 3 * p.κ ≤ K)
    (hε : 0 < ε) (hεK : ε ≤ (K ^ 6)⁻¹) (center : ℝ)
    {q : Event} (hq : q ∈ p.F b) (hbin : |packetSignal Nk p b q - center| ≤ ε)
    (R : ℕ) (c : EuclideanSpace ℝ (Fin 3)) (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hmatch : rootLift (packetNativeValueTest Nk B p b center) (packetNativeCubePoint Nk B p b q) 3 =
      f ((K ^ R) • (nativeBase (packetNativeCubePoint Nk B p b q) - c)))
    (S : Poly) (hS : S.totalDegree ≤ 2)
    (hfirst : |value (pderiv 3 (packetNativeCubePolynomial Nk B p b S))
      (packetNativeCubePoint Nk B p b q)| ≤ K)
    (hcurv : |curvature (packetNativeCubePolynomial Nk B p b S) 3| ≤ K) :
    let x := (K ^ R) • (nativeBase (packetNativeCubePoint Nk B p b q) - c)
    |eval (Fin.snoc (fun j => x j) (f x))
        (localNativePolynomial (fun j => c j) (K ^ R)⁻¹ (packetNativeCubePolynomial Nk B p b S)) -
      (δ Nk (p.r (p.lev b)))⁻¹ * eval (xp q.1 q.2) S| ≤ K ^ 14 * ε := by
  have hKp : 0 < K := by linarith
  have hroot := packetNativeValueTest_root_data hp hNk b hB hK hκK hε hεK center hq hbin
  have hpred := hroot.2.2 (packetNativeCubePolynomial Nk B p b S)
    ((packetNativeCubePolynomial_degree Nk B p b S).trans hS) hfirst hcurv
  have hlocal := local_core_signal_value_eq_rootLift (packetNativeValueTest Nk B p b center)
    (packetNativeCubePolynomial Nk B p b S) hKp R c (packetNativeCubePoint Nk B p b q) f hmatch
  have hactual := (packetNativeCubePolynomial_original_values hp b hB S q).1
  change value (packetNativeCubePolynomial Nk B p b S) (packetNativeCubePoint Nk B p b q) = _ at hactual
  dsimp only
  rw [hlocal, ← hactual]
  exact hpred

/-- Specialization to an ACTUAL earlier path test in the same world.
The old whole-block bounds and width order derive the two signal bounds;
no old coefficient or absolute-value envelope is supplied. -/
theorem path_old_signal_core_prediction
    {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {weight : Fin W → ℝ}
    {ν : Fin W → Measure Line} {Ev : Fin W → Set Event} {B : Fin W → ℝ}
    {profile : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L weight ν Ev B profile κ₁ m s δ₀ Mp Dp σ)
    (hNk : 0 < Nk) (a b : Fin p.C) (hB : 0 < B (p.γ b)) (hγ : p.γ b = p.γ a)
    (hwidth : δ Nk (p.r (p.lev b)) ≤ δ Nk (p.r (p.lev a)))
    {K ε : ℝ} (hK : 2 ≤ K) (hκK : 3 * p.κ ≤ K)
    (hε : 0 < ε) (hεK : ε ≤ (K ^ 6)⁻¹) (center : ℝ)
    {q : Event} (hq : q ∈ p.F b) (hqa : q ∈ p.F a)
    (hbin : |packetSignal Nk p b q - center| ≤ ε)
    (R : ℕ) (c : EuclideanSpace ℝ (Fin 3)) (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hmatch : rootLift (packetNativeValueTest Nk B p b center) (packetNativeCubePoint Nk B p b q) 3 =
      f ((K ^ R) • (nativeBase (packetNativeCubePoint Nk B p b q) - c))) :
    let x := (K ^ R) • (nativeBase (packetNativeCubePoint Nk B p b q) - c)
    |eval (Fin.snoc (fun j => x j) (f x))
        (localNativePolynomial (fun j => c j) (K ^ R)⁻¹ (packetNativeCubePolynomial Nk B p b (p.R a))) -
      (δ Nk (p.r (p.lev b)))⁻¹ * eval (xp q.1 q.2) (p.R a)| ≤ K ^ 14 * ε := by
  obtain ⟨hfirst, hcurv⟩ := packetNativeCube_old_signal_bounds hp a b hB hγ hwidth hqa
  have hκK' : p.κ ≤ K := by linarith [hp.1]
  have hR : (p.R a).totalDegree ≤ 2 := by
    rcases (hp.2.2.2.2.2.2.2 a).2.2 with ⟨_, _, _, _, hR, _⟩
    exact hR
  exact packet_signal_core_prediction hp hNk b hB hK hκK hε hεK center hq hbin R c f hmatch
    (p.R a) hR (hfirst.trans hκK') (hcurv.trans hκK')

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
