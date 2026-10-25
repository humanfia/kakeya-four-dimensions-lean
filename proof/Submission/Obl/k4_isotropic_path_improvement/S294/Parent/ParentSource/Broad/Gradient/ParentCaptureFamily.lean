-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.ParentCaptureFamily, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/ParentCaptureFamily.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 7f365adbfe16ac445495af8484302f0f8f899a28,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/ParentCaptureFamily.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.BadParentCoreMass
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ValueCoreRetention
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentSignalFacts

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Metric Native Analytic
open k4_stable_native_signal_oscillation

noncomputable section

abbrev ValueBranchData.ParentCaptureFamily
    {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H : Fin (d.W k) → Set Event} {mid : ℕ} {K : ℝ} {q e R : ℕ}
    (V : ValueBranchData d k p H mid K q e R) {coreFloor : ENNReal}
    (cores : V.CoreFamilies coreFloor) (floorPower : ℕ) (Kc width θrow : ℝ) (J qc : ℕ) :=
  (v : V.ActiveValue) → (ii : ↥(cores v).codes × Bool) →
    V.ParentCoreCertificate v.1.1 v.1.2 (cores v) ii floorPower Kc width θrow J qc

section Family

variable {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H : Fin (d.W k) → Set Event} {mid : ℕ} {K : ℝ} {q e R : ℕ}
    (V : ValueBranchData d k p H mid K q e R) {coreFloor : ENNReal}
    (cores : V.CoreFamilies coreFloor)
    {floorPower : ℕ} {Kc width θrow : ℝ} {J qc : ℕ}
    (certs : V.ParentCaptureFamily cores floorPower Kc width θrow J qc)

def ValueBranchData.ParentCaptureFamily.good
    (certs' : V.ParentCaptureFamily cores floorPower Kc width θrow J qc)
    (v : V.ActiveValue) (ii : ↥(cores v).codes × Bool) : Prop :=
  (certs' v ii).gradientGood

/- The union of good original core pieces is measurable. A later source
is restricted to this union, keeping the certificates' original laws. -/
open Classical in
def ValueBranchData.ParentCaptureFamily.goodPieces (w : Fin (d.W k)) : Set Event :=
  ⋃ v : V.ActiveValue, if p.γ v.1.1=w then
    ⋃ ii : ↥(cores v).codes × Bool, if ValueBranchData.ParentCaptureFamily.good V cores certs v ii then
      V.inner v.1.1 v.1.2∩(cores v).kept ii else ∅
    else ∅

open Classical in
def ValueBranchData.ParentCaptureFamily.capturedPieces (w : Fin (d.W k)) : Set Event :=
  ⋃ v : V.ActiveValue, if p.γ v.1.1=w then
    ⋃ ii : ↥(cores v).codes × Bool, if ¬ValueBranchData.ParentCaptureFamily.good V cores certs v ii then
      (V.inner v.1.1 v.1.2∩(cores v).kept ii)∩(certs v ii).capture else ∅
    else ∅

theorem ValueBranchData.ParentCaptureFamily.goodPieces_measurable (w : Fin (d.W k)) :
    MeasurableSet (ValueBranchData.ParentCaptureFamily.goodPieces V cores certs w) := by
  classical
  letI : Fintype V.ActiveValue := Fintype.ofFinite _
  apply MeasurableSet.iUnion
  intro v
  split_ifs
  · apply MeasurableSet.iUnion
    intro ii
    split_ifs
    · exact (V.measurable _ _).2.inter ((cores v).measurable ii).2
    · exact MeasurableSet.empty
  · exact MeasurableSet.empty

theorem ValueBranchData.ParentCaptureFamily.capturedPieces_measurable (w : Fin (d.W k)) :
    MeasurableSet (ValueBranchData.ParentCaptureFamily.capturedPieces V cores certs w) := by
  classical
  letI : Fintype V.ActiveValue := Fintype.ofFinite _
  apply MeasurableSet.iUnion
  intro v
  split_ifs
  · apply MeasurableSet.iUnion
    intro ii
    split_ifs
    · exact MeasurableSet.empty
    · apply ((V.measurable _ _).2.inter ((cores v).measurable ii).2).inter
      apply CoreStripCertificate.measurableSet_capture
      · exact (((measurable_nativeBase.comp
          (measurable_packetNativeCubePoint (d.N k) (d.B k) p v.1.1)).sub_const
            ((cores v).center ii.1.1)).const_smul (K^R))
      · exact (measurable_packetCubeVelocity p v.1.1).comp measurable_fst
  · exact MeasurableSet.empty

end Family

/-- All actual value/core/sign certificates are constructed simultaneously
from the original problem and pure source bounds, without broadness at
the tested depth or a supplied density on any core. -/
theorem ValueBranchData.exists_parent_capture_family
    {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H H₀ : Fin (d.W k) → Set Event} {mid m : ℕ} {K : ℝ} {q e R : ℕ}
    (V : ValueBranchData d k p H mid K q e R)
    {u : T → ℝ} {τ ε : ℝ} (Q : PreparedAngularPath d k p m H₀ u τ)
    (hpure : Q.uniformPureBounds ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w⊆d.E k w) (hHbase : ∀ w, H w⊆Q.base w)
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k^(τ+ε) ≤ K) (hκK : 3*p.κ ≤ K)
    {coreFloor : ENNReal} (cores : V.CoreFamilies coreFloor)
    (hr : 0 ≤ p.r mid) (hrL : p.r mid ≤ d.L)
    {D J : ℕ} (hD : 578 ≤ D) (hjets : ValueJetBound D J)
    (floorPower : ℕ) {Kc width θrow : ℝ} {qc : ℕ}
    (hKc : 2*K^(floorPower+7) ≤ Kc)
    (hwidth : 0 < width) (hwidthfloor : (Kc^qc)⁻¹ ≤ width)
    (hθrow : 0 < θrow) (hθrow1 : θrow ≤ 1) :
    Nonempty (V.ParentCaptureFamily cores floorPower Kc width θrow J qc) := by
  classical
  have hB (w : Fin (d.W k)) : 0 < d.B k w := (hd.parent_signal_data k w).1
  exact ⟨fun v ii => Classical.choice ((cores v).exists_parent_core_strip_certificate
    V Q hpure hd hp hHE hHbase hK hmax hpower hκK v.1.1 v.2.1 hr hrL (hB _)
    v.1.2 ii hD hjets floorPower hKc hwidth hwidthfloor hθrow hθrow1)⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
