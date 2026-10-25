-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.CoreAncestorSignalMenus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/CoreAncestorSignalMenus.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
/- Adapted from this tree's CoreAnisotropicMenus.lean (ported from LOT
 o265, session x0943, commit2677a0404c1ed53d6c31d9fee7cfe07a1745d292).
 The ancestor test remains explicit and is read in independent child units. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CoreOscillation
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.UnshearedDeepMenus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AncestorSignalCoordinates
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.DeepPhysicalMenus

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Metric Native Analytic
open k4_stable_native_signal_oscillation
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
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

/-- Earlier actual raw-core floors and pure caps give an ancestor-signal
menu on every later subset of a whole deeper history. The base belongs to
an independently selected child, and the height is exactly R_root/aChild.
No floor on the later subset or gradient-renewal cut is imposed. -/
theorem CoreEntryData.exists_actual_deep_ancestor_signal_menu
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
    (root child deep : Fin p.C) (hγ : p.γ b = p.γ root)
    (hwidth : δ (d.N k) (p.r (p.lev b)) ≤ δ (d.N k) (p.r (p.lev root)))
    (hFineRoot : p.F b ⊆ p.F root) (hADeepFine : p.A deep ⊆ p.A b)
    {baseMesh hidden : ℝ} (hbase : 0 < baseMesh) (hhidden : 0 < hidden)
    (hbaseSmall : p.unshearedDeepRadius child deep ≤ baseMesh)
    (hheightSmall :
      (δ (d.N k) (p.r (p.lev root))/δ (d.N k) (p.r (p.lev child)))*
        (2 * (K ^ 14 * (K ^ 6)⁻¹ *
          (δ (d.N k) (p.r (p.lev b)) / δ (d.N k) (p.r (p.lev root)))) +
          ((K ^ (qcore + 7)) ^ J * (p.κ + K ^ 14 * (K ^ 6)⁻¹)) *
            (6 * K ^ R * p.deepBaseRadius (d.N k) d.L δ₀ b deep)) ≤ hidden)
    (U : Set Event) (hUcore : U ⊆ C.raw i) (hUdeep : U ⊆ p.F deep) :
    ∃ Menu : Finset (Fin 4 → ℤ), (Menu.card : ℝ) ≤ 108 ∧
      ∀ z ∈ U, jointCode baseMesh hidden (fun j => unshearedPacketBase p child z j)
        (physicalParentSignal (d.N k) p child (p.R root) z) ∈ Menu := by
  have hN : 1 ≤ d.N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hd.1 k)
  have hKpos : 0 < K := by linarith
  apply hp.exists_deep_unsheared_signal_menu child deep hbase hhidden hbaseSmall
    (physicalParentSignal (d.N k) p child (p.R root)) U hUdeep
  intro z hz z' hz'
  have hosc := CoreEntryData.actual_core_signal_oscillation V Q hpure hd hp
    hHE hHbase hK hmax hpower hκK b hb hr hrL hB a C i hi hD hjets root hγ hwidth hFineRoot
    (6 * K ^ R * p.deepBaseRadius (d.N k) d.L δ₀ b deep) U hUcore
    (fun x hx y hy => hp.deep_original_core_diameter hN b deep hADeepFine hKpos.le R
      (C.center i.1.1) x (hUdeep hx) y (hUdeep hy)) z hz z' hz'
  have hfactor : 0 ≤ δ (d.N k) (p.r (p.lev root))/δ (d.N k) (p.r (p.lev child)) := by
    unfold δ
    positivity
  rw [ancestor_signal_in_child_units (d.N k) p root child z,
    ancestor_signal_in_child_units (d.N k) p root child z', ←mul_sub, abs_mul,
    abs_of_nonneg hfactor]
  apply (mul_le_mul_of_nonneg_left ?_ hfactor).trans hheightSmall
  simpa only [packetSignal, div_eq_mul_inv, mul_comm] using hosc

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
