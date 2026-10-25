-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.BadParentCoreMass, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/BadParentCoreMass.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 7f365adbfe16ac445495af8484302f0f8f899a28,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/BadParentCoreMass.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.ParentCaptureCertificates
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.CoreGradientSource

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Metric Native Analytic
open scoped ENNReal

noncomputable section

def CoreStripCertificate.gradientGood {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {S : Set Ω} {Z : Ω → EuclideanSpace ℝ (Fin 3)}
    {V : Ω → EuclideanSpace ℝ (Fin 2)} {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    {Kc : ℝ} {J qc : ℕ} {width B gradientBound loss : ℝ}
    (_C : CoreStripCertificate μ S Z V g Kc J qc width B gradientBound loss) : Prop :=
  ∀ x∈closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2, ‖fderiv ℝ g x‖ ≤ gradientBound

/-- On a bad actual core, all uncaptured original points cost only short
rows plus the certificate's prescribed ORIGINAL floor. Multiplying back
by the full original assignment and clock removes the entry normalization. -/
theorem CoreEntryData.uncaptured_bad_parent_core_mass_le
    {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H : Fin (d.W k) → Set Event} {mid : ℕ} {K : ℝ} {q e R : ℕ}
    (V : ValueBranchData d k p H mid K q e R) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (hK : 0 < K) (b : Fin p.C) (hb : p.lev b=mid) (a : Fin V.count)
    {coreFloor : ENNReal}
    (C : CoreEntryData e R K (packetNativeValueTest (d.N k) (d.B k) p b (V.center a))
      (V.entryLaw b a) (packetNativeCubePoint (d.N k) (d.B k) p b) (V.outer b a) coreFloor)
    (ii : ↥C.codes × Bool) {floorPower J qc : ℕ} {Kc width θrow : ℝ}
    (hθrow : 0 ≤ θrow)
    (cert : V.ParentCoreCertificate b a C ii floorPower Kc width θrow J qc)
    (hbad : ¬cert.gradientGood) :
    let good := ParentSignal.goodLines (d.P k (p.γ b)) (d.K k) (d.B k (p.γ b))
    ((d.ν k (p.γ b)).prod volume) (((V.inner b a∩C.kept ii)∩Prod.fst ⁻¹' good)\cert.capture) ≤
      (ENNReal.ofReal (θrow*(K^R)⁻¹)+ENNReal.ofReal ((K^floorPower)⁻¹/2))*
        (d.ν k (p.γ b) (p.A b)*ENNReal.ofReal (((2:ℝ)^p.T mid)⁻¹)) := by
  classical
  letI : IsProbabilityMeasure (d.ν k (p.γ b)) := (hd.weights k).2.2 _
  let μ : Measure Event := (d.ν k (p.γ b)).prod volume
  let good := ParentSignal.goodLines (d.P k (p.γ b)) (d.K k) (d.B k (p.γ b))
  let U := C.raw ii∩Prod.fst ⁻¹' good
  let long := coreLongRows p b K R U θrow
  let reference := d.ν k (p.γ b) (p.A b)*ENNReal.ofReal (((2:ℝ)^p.T mid)⁻¹)
  have hUm : MeasurableSet U := (C.measurable ii).1.inter
    ((ParentSignal.measurableSet_goodLines _ _ _).preimage measurable_fst)
  have hsubF : U⊆p.F b := fun z hz => ((V.subset b a).2 ((C.subset ii).2 hz.1)).2
  have hN : 0 < d.N k := (by norm_num : (0:ℝ) < 2).trans_le (hd.1 k)
  have href0 : reference ≠ 0 := mul_ne_zero (hp.assignment_mass_pos hN b).ne'
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hreftop : reference ≠ ⊤ := ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  have hsmall : V.entryLaw b a (long\cert.capture) ≤ ENNReal.ofReal ((K^floorPower)⁻¹/2) :=
    (cert.alternative.resolve_left hbad).le
  have hconv : μ (long\cert.capture)=reference*V.entryLaw b a (long\cert.capture) := by
    rw [V.entryLaw_apply_of_subset b a (fun z hz => (C.subset ii).2 hz.1.1.1)]
    change _=reference*(reference⁻¹*_)
    rw [←mul_assoc,ENNReal.mul_inv_cancel href0 hreftop,one_mul]
  have hlong : μ (long\cert.capture) ≤ ENNReal.ofReal ((K^floorPower)⁻¹/2)*reference := by
    rw [hconv,mul_comm _ reference]
    exact mul_le_mul' le_rfl hsmall
  obtain ⟨-, -, hch⟩ := hp.2.2.2.2.2.2.2 b
  obtain ⟨_, _, _, _, _, _, hAm, _, _, _, hF, -⟩ := hch
  have hshort : μ (U\long) ≤ ENNReal.ofReal (θrow*coreRowStep p b K R)*d.ν k (p.γ b) (p.A b) := by
    have heq : U\long=U∩{z | rowVolume U (coreRowStep p b K R) z < ENNReal.ofReal θrow} := by
      ext z
      simp only [long,coreLongRows,mem_sdiff,mem_inter_iff,mem_ofPred_eq,not_and,not_le]
      tauto
    rw [heq]
    exact short_rows_mass_le (d.ν k (p.γ b)) hAm hUm (fun z hz => (hF z (hsubF hz)).2.1)
      (by unfold coreRowStep; positivity)
  have hstep : ENNReal.ofReal (θrow*coreRowStep p b K R)*d.ν k (p.γ b) (p.A b)=
      ENNReal.ofReal (θrow*(K^R)⁻¹)*reference := by
    dsimp only [reference,coreRowStep]
    rw [hb,show θrow*(((2:ℝ)^p.T mid)⁻¹*(K^R)⁻¹)=
      (θrow*(K^R)⁻¹)*((2:ℝ)^p.T mid)⁻¹ by ring,
      ENNReal.ofReal_mul (by positivity : 0 ≤ θrow*(K^R)⁻¹)]
    ring
  have hcover : U\cert.capture⊆(U\long)∪(long\cert.capture) := by
    intro z hz
    by_cases hl : z∈long
    · exact Or.inr ⟨hl,hz.2⟩
    · exact Or.inl ⟨hz.1,hl⟩
  calc
    _ ≤ μ (U\cert.capture) := by
      apply measure_mono
      intro z hz
      exact ⟨⟨(C.subset ii).1 hz.1.1.2,hz.1.2⟩,hz.2⟩
    _ ≤ μ ((U\long)∪(long\cert.capture)) := measure_mono hcover
    _ ≤ μ (U\long)+μ (long\cert.capture) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (θrow*(K^R)⁻¹)*reference+
        ENNReal.ofReal ((K^floorPower)⁻¹/2)*reference := by
      rw [←hstep]
      exact add_le_add hshort hlong
    _ = _ := by ring

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
