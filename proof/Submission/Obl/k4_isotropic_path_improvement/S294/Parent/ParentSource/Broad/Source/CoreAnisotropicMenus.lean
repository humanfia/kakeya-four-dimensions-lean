-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.CoreAnisotropicMenus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/CoreAnisotropicMenus.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/CoreAnisotropicMenus.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CoreEntryData
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CoreSourceCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceCoreValueVariation
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.AnisotropicDeepMenus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CoreOscillation

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Metric Native Analytic
open k4_stable_native_signal_oscillation
open scoped ENNReal

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H H₀ : Fin (d.W k) → Set Event} {mid m : ℕ} {K : ℝ} {q e R qcore : ℕ}
    (V : ValueBranchData d k p H mid K q e R)
    {u : T → ℝ} {τ ε : ℝ} (Q : PreparedAngularPath d k p m H₀ u τ)
    (hpure : Q.uniformPureBounds ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hpure hd hp

/-- Actual original value/core entries supply a physical menu after
arbitrary later selection inside a deeper whole packet. The cap and
norming mass come from the earlier raw core, whose branch is unchanged.
No mass floor on the later selected set is needed. -/
theorem CoreEntryData.exists_actual_deep_anisotropic_menu
    (hHE : ∀ w, H w ⊆ d.E k w) (hHbase : ∀ w, H w ⊆ Q.base w)
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k ^ (τ + ε) ≤ K) (hκK : 3 * p.κ ≤ K)
    (b : Fin p.C) (hb : p.lev b = mid)
    (hr : 0 ≤ p.r mid) (hrL : p.r mid ≤ d.L) (hB : 0 < d.B k (p.γ b))
    (a : Fin V.count)
    (C : CoreEntryData e R K (packetNativeValueTest (d.N k) (d.B k) p b (V.center a))
      (V.entryLaw b a) (packetNativeCubePoint (d.N k) (d.B k) p b) (V.outer b a)
      (ENNReal.ofReal ((K ^ qcore)⁻¹)))
    (i : ↥C.codes × Bool) (hi : (C.kept i).Nonempty)
    {D J : ℕ} (hD : 5186 ≤ D) (hjets : DenseJetBound D J)
    (old deep : Fin p.C) (hγ : p.γ b = p.γ old)
    (hwidth : δ (d.N k) (p.r (p.lev b)) ≤ δ (d.N k) (p.r (p.lev old)))
    (hFineOld : p.F b ⊆ p.F old)
    (hADeepFine : p.A deep ⊆ p.A b) (hADeepOld : p.A deep ⊆ p.A old)
    {baseMesh hidden : ℝ} (hbase : 0 < baseMesh) (hhidden : 0 < hidden)
    (hbaseSmall : p.deepBaseRadius (d.N k) d.L δ₀ old deep ≤ baseMesh)
    (hheightSmall :
      2 * (K ^ 14 * (K ^ 6)⁻¹ *
        (δ (d.N k) (p.r (p.lev b)) / δ (d.N k) (p.r (p.lev old)))) +
        ((K ^ (qcore + 7)) ^ J * (p.κ + K ^ 14 * (K ^ 6)⁻¹)) *
          (6 * K ^ R * p.deepBaseRadius (d.N k) d.L δ₀ b deep) ≤ hidden)
    (U : Set Event) (hUcore : U ⊆ C.raw i) (hUdeep : U ⊆ p.F deep) :
    ∃ Menu : Finset (Fin 4 → ℤ), (Menu.card : ℝ) ≤ 108 ∧
      ∀ z ∈ U, p.originalPhysicalCode (d.N k) old baseMesh hidden z ∈ Menu := by
  have hN : 1 ≤ d.N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hd.1 k)
  have hKpos : 0 < K := by linarith
  apply hp.exists_deep_original_anisotropic_menu hN old deep hADeepOld hbase hhidden hbaseSmall U hUdeep
  intro z hz z' hz'
  have hosc := CoreEntryData.actual_core_signal_oscillation V Q hpure hd hp
    hHE hHbase hK hmax hpower hκK b hb hr hrL hB a C i hi hD hjets old hγ hwidth hFineOld
    (6 * K ^ R * p.deepBaseRadius (d.N k) d.L δ₀ b deep) U hUcore
    (fun x hx y hy => hp.deep_original_core_diameter hN b deep hADeepFine hKpos.le R
      (C.center i.1.1) x (hUdeep hx) y (hUdeep hy)) z hz z' hz'
  simpa only [packetSignal, div_eq_mul_inv, mul_comm] using hosc.trans hheightSmall

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
