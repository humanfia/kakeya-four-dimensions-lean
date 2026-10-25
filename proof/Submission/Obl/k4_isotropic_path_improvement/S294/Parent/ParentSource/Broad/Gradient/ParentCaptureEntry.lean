-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.ParentCaptureEntry, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/ParentCaptureEntry.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit af69463910936c02b3e287e9153c4781be3e7639,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/ParentCaptureEntry.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.LongRowStripCapture
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.ParentEntry
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.OriginalParentInputs

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Metric Native Analytic
open k4_stable_native_signal_oscillation

noncomputable section

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

/-- On one genuine ORIGINAL core, the physical parent prediction is either
controlled on the whole comparison ball, or its actual long rows are
captured by explicit unit strips up to a prescribed original floor.
The parent jets, motion, analytic presentation, directional tests and
base cap are all produced internally. There is no broadness premise,
no old parent packet and no supplied cell or entry density. -/
theorem CoreEntryData.parent_gradient_or_strip_capture
    (hHE : ∀ w, H w⊆d.E k w) (hHbase : ∀ w, H w⊆Q.base w)
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k^(τ+ε) ≤ K) (hκK : 3*p.κ ≤ K)
    (b : Fin p.C) (hb : p.lev b=mid)
    (hr : 0 ≤ p.r mid) (hrL : p.r mid ≤ d.L) (hB : 0 < d.B k (p.γ b))
    (a : Fin V.count) {coreFloor : ENNReal}
    (C : CoreEntryData e R K (packetNativeValueTest (d.N k) (d.B k) p b (V.center a))
      (V.entryLaw b a) (packetNativeCubePoint (d.N k) (d.B k) p b) (V.outer b a) coreFloor)
    (ii : ↥C.codes × Bool) (hii : (C.raw ii).Nonempty)
    {D J : ℕ} (hD : 578 ≤ D) (hjets : ValueJetBound D J)
    (floorPower : ℕ) {Kc width θrow : ℝ} {qc : ℕ}
    (hKc : 2*K^(floorPower+7) ≤ Kc)
    (hwidth : 0 < width) (hwidthfloor : (Kc^qc)⁻¹ ≤ width)
    (hθrow : 0 < θrow) (hθrow1 : θrow ≤ 1) :
    let good := ParentSignal.goodLines (d.P k (p.γ b)) (d.K k) (d.B k (p.γ b))
    let Z := packetLocalCorePoint (d.N k) (d.B k) p b K R (C.center ii.1.1)
    let g := parentCorePrediction (d.N k) (d.B k) p b (d.P k (p.γ b)) K R
      (C.center ii.1.1) (C.sheet ii)
    let long := coreLongRows p b K R (C.raw ii∩Prod.fst ⁻¹' good) θrow
    let G := captureGradientCoeff (2*K^(floorPower+7)) width θrow J
    (∀ x∈closedBall (0 : Base) 2, ‖fderiv ℝ g x‖ ≤
      G*(K^14*(K^6)⁻¹*δ (d.N k) (p.r mid)+12*K*coreRowStep p b K R)) ∨
    ∃ (normal : (Fin 3 → ℤ) → EuclideanSpace ℝ (Fin 2)) (center : (Fin 3 → ℤ) → ℝ),
      (∀ i, ‖normal i‖=1 ∧ |center i| ≤ 1/2+width) ∧
      MeasurableSet (⋃ i, (renewalCellCode Kc J (qc+1) ∘ Z) ⁻¹' {i}∩
        (fun z : Event => packetCubeVelocity p b z.1) ⁻¹'
          Submission.Lib.K4VelocityStrips.affineStrip (normal i) (center i) width) ∧
      V.entryLaw b a (long\⋃ i, (renewalCellCode Kc J (qc+1) ∘ Z) ⁻¹' {i}∩
        (fun z : Event => packetCubeVelocity p b z.1) ⁻¹'
          Submission.Lib.K4VelocityStrips.affineStrip (normal i) (center i) width) <
          ENNReal.ofReal ((K^floorPower)⁻¹/2) := by
  classical
  have hKtwo : 2 ≤ K := by linarith
  have hKp : 0 < K := by linarith
  have hN : 1 ≤ d.N k := by linarith [hd.1 k]
  have hNp : 0 < d.N k := zero_lt_one.trans_le hN
  have hDK : d.K k ≤ K := (le_max_right p.κ (d.K k)).trans hmax
  let P := d.P k (p.γ b)
  let good := ParentSignal.goodLines P (d.K k) (d.B k (p.γ b))
  let U := C.raw ii∩Prod.fst ⁻¹' good
  let long := coreLongRows p b K R U θrow
  let Z := packetLocalCorePoint (d.N k) (d.B k) p b K R (C.center ii.1.1)
  let vel := fun z : Event => packetCubeVelocity p b z.1
  let g := parentCorePrediction (d.N k) (d.B k) p b P K R (C.center ii.1.1) (C.sheet ii)
  let A := 2*K^(floorPower+7)
  let fit := K^14*(K^6)⁻¹*δ (d.N k) (p.r mid)+12*K*coreRowStep p b K R
  have hUsub : U⊆d.E k (p.γ b) := fun z hz =>
    hHE _ ((V.subset b a).2 ((C.subset ii).2 hz.1)).1
  obtain ⟨hP,hgoodm,_,hparentJets,hmotion⟩ := original_parent_source_inputs hd k (p.γ b) hDK U hUsub
  have hUm : MeasurableSet U := (C.measurable ii).1.inter (hgoodm.preimage measurable_fst)
  have hlongm : MeasurableSet long := measurableSet_coreLongRows p b K R hUm θrow
  have hZ : Measurable Z :=
    (((measurable_nativeBase.comp (measurable_packetNativeCubePoint (d.N k) (d.B k) p b)).sub_const
      (C.center ii.1.1)).const_smul (K^R))
  have hvel : Measurable vel := (measurable_packetCubeVelocity p b).comp measurable_fst
  have hU (z) (hz : z∈U) : CoreIncidence (d.N k) (d.B k) p b b K (K^6)⁻¹ R
      (V.center a) (C.center ii.1.1) (C.sheet ii) z := by
    have hzV := (C.subset ii).2 hz.1
    have hzF := ((V.subset b a).2 hzV).2
    have hc := C.points ii z hz.1
    exact ⟨hzF,hzF,V.value b a z hzV,hc.1,hc.2.2⟩
  have hjet (z) (hz : z∈U) := hparentJets z hz hz.2
  have hmove (z) (hz : z∈U) (z') (hz' : z'∈U) (hl : z'.1=z.1) :=
    hmotion z hz z' hz' hz.2 hl
  have hbranch := C.branch ii hii
  have hanalytic : CorePredictionAnalytic g := parentCorePrediction_analytic
    (d.N k) (d.B k) p b P hP K R (V.center a) (C.center ii.1.1) (nativeCoreSign ii.2)
    (C.extension ii) (C.sheet ii) hbranch
  have hA : 2 ≤ A := by
    have hh := one_le_pow₀ (by linarith : 1 ≤ K) (n := floorPower+7)
    dsimp [A]
    linarith
  have hKc2 : 2 ≤ Kc := hA.trans hKc
  have hcore (z) (hz : z∈long) : ‖Z z‖ ≤ 1/4 := (C.points ii z hz.1.1).1
  have hspeed (z) (hz : z∈long) : ‖vel z‖ ≤ 1/2 :=
    packetCubeVelocity_norm_le_half hp b z.1 (coreIncidence_line_old (hU z hz.1) hp).2.2
  have hfit : 0 ≤ fit := by dsimp [fit,coreRowStep,δ]; positivity
  have hcap (S : Set Base) (hS : MeasurableSet S) :
      ((V.entryLaw b a).restrict long) (Z ⁻¹' S) ≤ ENNReal.ofReal (K^7)*volume S := by
    have hmap := V.entryLaw_core_cap Q hpure hd hp hHE hHbase hK hmax hpower b hb hr hrL a
      long (C.center ii.1.1)
    rw [←Measure.map_apply hZ hS]
    simpa only [Measure.smul_apply,smul_eq_mul] using (Measure.le_iff.mp hmap S hS)
  have hrows (z) (hz : z∈long) : ∃ T : Set ℝ, ∃ intercept : ℝ,
      MeasurableSet T ∧ ENNReal.ofReal θrow ≤ volume T ∧
      (∀ t∈T, ‖Z z+t • spacetimeDirection (vel z)‖ ≤ 1/4) ∧
      ∀ t∈T, |g (Z z+t • spacetimeDirection (vel z))-intercept| ≤ fit := by
    refine ⟨coreRowTimes p b K R U z,MvPolynomial.eval (xp z.1 z.2) P,
      measurableSet_coreRowTimes p b K R hUm z,hz.2,?_,?_⟩
    · intro t ht
      exact (parent_core_row_fit hp hNp b b hB P hP
        (by rw [hb]; exact physical_parent_fine_width_le_one hN hr) hKtwo hκK
        (by positivity) le_rfl (V.center a) R (C.center ii.1.1) (C.sheet ii) U hU
        (by positivity : 0 ≤ 24*K) hjet hmove z hz.1 t ht).1
    · intro t ht
      have hh := (parent_core_row_fit hp hNp b b hB P hP
        (by rw [hb]; exact physical_parent_fine_width_le_one hN hr) hKtwo hκK
        (by positivity) le_rfl (V.center a) R (C.center ii.1.1) (C.sheet ii) U hU
        (by positivity : 0 ≤ 24*K) hjet hmove z hz.1 t ht).2
      rw [hb] at hh
      exact hh.trans_eq (by dsimp [fit]; ring)
  have hh := original_long_rows_gradient_or_strip_capture hjets hD
    ((V.entryLaw b a).restrict long) Z hZ vel hvel long hlongm g hanalytic
    hKc2 hA hKc (by positivity : 0 < K^7) hwidth hwidthfloor
    (by norm_num : 0 ≤ (1/2:ℝ)) (by linarith : (1/2:ℝ) ≤ Kc)
    hθrow hθrow1 hfit hcore hspeed hcap hrows
  rcases hh with hgrad | ⟨normal,center,hbounds,hm,hcapture⟩
  · left
    intro x hx
    exact hgrad x hx
  · right
    refine ⟨normal,center,hbounds,hm,?_⟩
    rw [Measure.restrict_apply' hlongm,inter_eq_left.mpr sdiff_subset] at hcapture
    apply hcapture.trans_eq
    congr 1
    dsimp [A]
    rw [pow_add]
    field_simp

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
