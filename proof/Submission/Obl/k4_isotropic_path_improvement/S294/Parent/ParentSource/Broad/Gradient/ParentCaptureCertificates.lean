-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.ParentCaptureCertificates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/ParentCaptureCertificates.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 7f365adbfe16ac445495af8484302f0f8f899a28,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/ParentCaptureCertificates.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.ParentCaptureEntry

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Metric Native Analytic

noncomputable section

/-- Actual strip data and their original-law gradient/capture alternative.
The table is total, so it can be read on finite deep-packet menus later. -/
structure CoreStripCertificate {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Set Ω) (Z : Ω → EuclideanSpace ℝ (Fin 3))
    (V : Ω → EuclideanSpace ℝ (Fin 2)) (g : EuclideanSpace ℝ (Fin 3) → ℝ)
    (Kc : ℝ) (J qc : ℕ) (width B gradientBound loss : ℝ) where
  normal : (Fin 3 → ℤ) → EuclideanSpace ℝ (Fin 2)
  center : (Fin 3 → ℤ) → ℝ
  bounds : ∀ label, ‖normal label‖=1 ∧ |center label| ≤ B+width
  alternative : (∀ x∈closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
      ‖fderiv ℝ g x‖ ≤ gradientBound) ∨
    μ (S\⋃ label, (renewalCellCode Kc J (qc+1) ∘ Z) ⁻¹' {label}∩
      V ⁻¹' Submission.Lib.K4VelocityStrips.affineStrip (normal label) (center label) width) <
        ENNReal.ofReal loss

def CoreStripCertificate.capture {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {S : Set Ω} {Z : Ω → EuclideanSpace ℝ (Fin 3)}
    {V : Ω → EuclideanSpace ℝ (Fin 2)} {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    {Kc : ℝ} {J qc : ℕ} {width B gradientBound loss : ℝ}
    (C : CoreStripCertificate μ S Z V g Kc J qc width B gradientBound loss) : Set Ω :=
  ⋃ label, (renewalCellCode Kc J (qc+1) ∘ Z) ⁻¹' {label}∩
    V ⁻¹' Submission.Lib.K4VelocityStrips.affineStrip (C.normal label) (C.center label) width

theorem CoreStripCertificate.measurableSet_capture {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {S : Set Ω} {Z : Ω → EuclideanSpace ℝ (Fin 3)}
    {V : Ω → EuclideanSpace ℝ (Fin 2)} {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    {Kc : ℝ} {J qc : ℕ} {width B gradientBound loss : ℝ}
    (C : CoreStripCertificate μ S Z V g Kc J qc width B gradientBound loss)
    (hZ : Measurable Z) (hV : Measurable V) : MeasurableSet C.capture := by
  apply MeasurableSet.iUnion
  intro label
  exact (((measurable_renewalCellCode Kc J (qc+1)).comp hZ) (measurableSet_singleton label)).inter
    ((Submission.Lib.K4VelocityStrips.measurableSet_affineStrip _ _ _).preimage hV)

abbrev ValueBranchData.ParentCoreCertificate
    {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H : Fin (d.W k) → Set Event} {mid : ℕ} {K : ℝ} {q e R : ℕ}
    (V : ValueBranchData d k p H mid K q e R)
    (b : Fin p.C) (a : Fin V.count) {coreFloor : ENNReal}
    (C : CoreEntryData e R K (packetNativeValueTest (d.N k) (d.B k) p b (V.center a))
      (V.entryLaw b a) (packetNativeCubePoint (d.N k) (d.B k) p b) (V.outer b a) coreFloor)
    (ii : ↥C.codes × Bool) (floorPower : ℕ) (Kc width θrow : ℝ) (J qc : ℕ) :=
  let good := ParentSignal.goodLines (d.P k (p.γ b)) (d.K k) (d.B k (p.γ b))
  let Z := packetLocalCorePoint (d.N k) (d.B k) p b K R (C.center ii.1.1)
  let g := parentCorePrediction (d.N k) (d.B k) p b (d.P k (p.γ b)) K R
    (C.center ii.1.1) (C.sheet ii)
  let long := coreLongRows p b K R (C.raw ii∩Prod.fst ⁻¹' good) θrow
  let G := captureGradientCoeff (2*K^(floorPower+7)) width θrow J
  CoreStripCertificate (V.entryLaw b a) long Z (fun z : Event => packetCubeVelocity p b z.1) g
    Kc J qc width (1/2)
    (G*(K^14*(K^6)⁻¹*δ (d.N k) (p.r mid)+12*K*coreRowStep p b K R))
    ((K^floorPower)⁻¹/2)

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H H₀ : Fin (d.W k) → Set Event} {mid m : ℕ} {K : ℝ} {q e R : ℕ}
    (V : ValueBranchData d k p H mid K q e R)
    {u : T → ℝ} {τ ε : ℝ} (Q : PreparedAngularPath d k p m H₀ u τ)
    (hpure : Q.uniformPureBounds ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hpure hd hp

/-- Produce an actual total certificate even for empty raw cores. This
can be chosen simultaneously on every original value/core/sign label. -/
theorem CoreEntryData.exists_parent_core_strip_certificate
    (hHE : ∀ w, H w⊆d.E k w) (hHbase : ∀ w, H w⊆Q.base w)
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k^(τ+ε) ≤ K) (hκK : 3*p.κ ≤ K)
    (b : Fin p.C) (hb : p.lev b=mid)
    (hr : 0 ≤ p.r mid) (hrL : p.r mid ≤ d.L) (hB : 0 < d.B k (p.γ b))
    (a : Fin V.count) {coreFloor : ENNReal}
    (C : CoreEntryData e R K (packetNativeValueTest (d.N k) (d.B k) p b (V.center a))
      (V.entryLaw b a) (packetNativeCubePoint (d.N k) (d.B k) p b) (V.outer b a) coreFloor)
    (ii : ↥C.codes × Bool)
    {D J : ℕ} (hD : 578 ≤ D) (hjets : ValueJetBound D J)
    (floorPower : ℕ) {Kc width θrow : ℝ} {qc : ℕ}
    (hKc : 2*K^(floorPower+7) ≤ Kc)
    (hwidth : 0 < width) (hwidthfloor : (Kc^qc)⁻¹ ≤ width)
    (hθrow : 0 < θrow) (hθrow1 : θrow ≤ 1) :
    Nonempty (V.ParentCoreCertificate b a C ii floorPower Kc width θrow J qc) := by
  classical
  let n₀ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1,0]
  have hn₀ : ‖n₀‖=1 := by simp [n₀,EuclideanSpace.norm_eq,Fin.sum_univ_two]
  have hzero : |(0:ℝ)| ≤ 1/2+width := by rw [abs_zero]; linarith
  by_cases hii : (C.raw ii).Nonempty
  · obtain hgrad | ⟨normal,center,hbounds,_,hsmall⟩ := C.parent_gradient_or_strip_capture
      V Q hpure hd hp hHE hHbase hK hmax hpower hκK b hb hr hrL hB a ii hii
      hD hjets floorPower hKc hwidth hwidthfloor hθrow hθrow1
    · exact ⟨⟨(fun _ => n₀),(fun _ => 0),(fun _ => ⟨hn₀,hzero⟩),Or.inl hgrad⟩⟩
    · exact ⟨⟨normal,center,hbounds,Or.inr hsmall⟩⟩
  · refine ⟨⟨(fun _ => n₀),(fun _ => 0),(fun _ => ⟨hn₀,hzero⟩),Or.inr ?_⟩⟩
    have hempty : C.raw ii=∅ := not_nonempty_iff_eq_empty.mp hii
    change V.entryLaw b a ((coreLongRows p b K R (C.raw ii∩_) θrow)\_) < _
    simp only [hempty,empty_inter,coreLongRows,empty_sdiff,measure_empty]
    apply ENNReal.ofReal_pos.mpr
    have hKp : 0 < K := by linarith
    positivity

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
