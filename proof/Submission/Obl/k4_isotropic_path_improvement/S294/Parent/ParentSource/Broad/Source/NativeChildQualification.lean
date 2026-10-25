-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.NativeChildQualification, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/NativeChildQualification.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalChildLabels
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.NativeQualification

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native
open Qualification.Jets2
open scoped ENNReal

noncomputable section

local instance (C : ℕ) : MeasurableSpace (Option (Fin C)) := ⊤
local instance (C : ℕ) : MeasurableSingletonClass (Option (Fin C)) := ⟨fun _ => trivial⟩

/-- Duration in the original Lebesgue time includes exactly the original
root clock length, for any measurable set of normalized witness times. -/
theorem Native.PathData.original_clock_time_measure {W : ℕ} (p : PathData W)
    (root : Fin p.C) (line : Ln) {times : Set ℝ} (htimes : MeasurableSet times) :
    volume ((fun t : ℝ => packetTime p root (line,t)) ⁻¹' times)=
      ENNReal.ofReal (((2 : ℝ)^p.T (p.lev root))⁻¹)*volume times := by
  let t₀ := (p.j root : ℝ)/(2 : ℝ)^p.T (p.lev root)
  let h := ((2 : ℝ)^p.T (p.lev root))⁻¹
  have hh : 0 < h := by dsimp [h]; positivity
  have he : (fun t : ℝ => packetTime p root (line,t))=
      ((Submission.Obl.k4_balanced_native_packet_transport.CPF.timeChartEquiv t₀ h hh.ne').symm : ℝ → ℝ) := by
    funext t
    rw [Submission.Obl.k4_balanced_native_packet_transport.CPF.timeChartEquiv_symm_apply]
    dsimp [packetTime,nativeOldBaseFrame,t₀,h]
    ring
  have hmap := Submission.Obl.k4_balanced_native_packet_transport.CPF.map_timeChartEquiv_symm t₀ h hh
  have happly := congrArg (fun μ : Measure ℝ => μ times) hmap
  rw [Measure.map_apply (MeasurableEquiv.measurable _) htimes,
    Measure.smul_apply,smul_eq_mul] at happly
  simpa only [←he] using happly

section Path

variable {W : ℕ} {p : PathData W} {N L κ₁ δ₀ σ : ℝ}
    {m Mp Dp : ℕ} {s : ℕ → ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ} {f : ℝ → ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (root : Fin p.C) (level : ℕ) (hlevel : p.lev root ≤ level) (hlast : level ≤ m-1)
    (source : Set Ev) (hsource : source⊆p.F root)
    (hterminal : ∀ z∈source, ∃ terminal : Fin p.C,
      p.lev terminal=m-1 ∧ p.γ terminal=p.γ root ∧ z∈p.F terminal)

include hp hlevel hlast hsource hterminal

/-- A qualified incidence and every same-label witness belong to one
actual true child, under the unchanged original indexed line. -/
theorem Native.PathData.Valid.nativeQualified_original_child
    {z : Ev} (hz : z∈p.childClockReference root level source)
    {G : Ev → Fin 3 → ℝ} {M T : ℕ} {Kq error duration : ℝ}
    (hq : NativeQualified (p.childClockReference root level source)
      (p.childClockLabel root level (p.γ root)) G M T Kq error duration z) :
    ∃ b : Fin p.C, b∈p.trueDescendants root level ∧
      p.childClockPoint root z∈source∩p.F b ∧
      NativeQualified (p.childClockPoint root ⁻¹' (source∩p.F b))
        (p.childClockLabel root level (p.γ root)) G M T Kq error duration z := by
  obtain ⟨b,hb,hlab,hpoint⟩ := hp.childClockReference_spec root level hlevel hlast source hsource hterminal hz
  obtain ⟨Q,hdeg,hcoeff,hfit,hduration⟩ := hq
  refine ⟨b,hb,hpoint,Q,hdeg,hcoeff,hfit,hduration.trans (measure_mono ?_)⟩
  rintro t ⟨ht,htr,htlab,htfit⟩
  obtain ⟨b',hb',hlab',hpoint'⟩ :=
    hp.childClockReference_spec root level hlevel hlast source hsource hterminal htr
  have hbb : b'=b := Option.some.inj (hlab'.symm.trans (htlab.trans hlab))
  subst b'
  exact ⟨ht,hpoint',htlab,htfit⟩

/-- Grid qualification retains its exact grid polynomial and restores
every witness to the same actual child's original source. -/
theorem Native.PathData.Valid.nativeGridQualified_original_child
    {z : Ev} (hz : z∈p.childClockReference root level source)
    {G : Ev → Fin 3 → ℝ} {M T : ℕ} {mesh error duration : ℝ} {bound : ℤ}
    (hq : NativeGridQualified (p.childClockReference root level source)
      (p.childClockLabel root level (p.γ root)) G M T mesh bound error duration z) :
    ∃ b : Fin p.C, b∈p.trueDescendants root level ∧
      p.childClockPoint root z∈source∩p.F b ∧
      NativeGridQualified (p.childClockPoint root ⁻¹' (source∩p.F b))
        (p.childClockLabel root level (p.γ root)) G M T mesh bound error duration z := by
  obtain ⟨b,hb,hlab,hpoint⟩ := hp.childClockReference_spec root level hlevel hlast source hsource hterminal hz
  obtain ⟨a,hcoeff,hfit,hduration⟩ := hq
  refine ⟨b,hb,hpoint,a,hcoeff,hfit,hduration.trans (measure_mono ?_)⟩
  rintro t ⟨ht,htr,htlab,htfit⟩
  obtain ⟨b',hb',hlab',hpoint'⟩ :=
    hp.childClockReference_spec root level hlevel hlast source hsource hterminal htr
  have hbb : b'=b := Option.some.inj (hlab'.symm.trans (htlab.trans hlab))
  subst b'
  exact ⟨ht,hpoint',htlab,htfit⟩

/-- Restore the qualification duration to ordinary original time, in
one actual child's ORIGINAL counted source. No row-clock or posterior
normalization is substituted for that reference. -/
theorem Native.PathData.Valid.nativeQualified_original_duration
    (hsourceMeas : MeasurableSet source)
    {z : Ev} (hz : z∈p.childClockReference root level source)
    {G : Ev → Fin 3 → ℝ} (hG : Measurable G) {M T : ℕ} {Kq error duration : ℝ}
    (hq : NativeQualified (p.childClockReference root level source)
      (p.childClockLabel root level (p.γ root)) G M T Kq error duration z) :
    ∃ b : Fin p.C, b∈p.trueDescendants root level ∧
      p.childClockPoint root z∈source∩p.F b ∧
      ∃ Q : Fin 3 → Polynomial ℝ, (∀ j, (Q j).natDegree ≤ M) ∧
        (∀ j n, |(Q j).coeff n| ≤ Kq) ∧ (∀ j, |G z j-(Q j).eval z.2| ≤ error) ∧
        ENNReal.ofReal ((((2 : ℝ)^p.T (p.lev root))⁻¹)*duration) ≤
          volume {t : ℝ | (z.1,t)∈source∩p.F b ∧
            ∀ j, |G (z.1,packetTime p root (z.1,t)) j-
              (Q j).eval (packetTime p root (z.1,t))| ≤ error} := by
  obtain ⟨b,hb,hpoint,Q,hdeg,hcoeff,hfit,hduration⟩ :=
    hp.nativeQualified_original_child root level hlevel hlast source hsource hterminal hz hq
  let times : Set ℝ := {t | p.childClockPoint root (z.1,t)∈source∩p.F b ∧
    ∀ j, |G (z.1,t) j-(Q j).eval t| ≤ error}
  have hFb : MeasurableSet (p.F b) := (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have htimes : MeasurableSet times := by
    have h1 : Measurable (fun t : ℝ => p.childClockPoint root (z.1,t)) :=
      (p.childClockPoint_measurable root).comp (measurable_const.prodMk measurable_id)
    apply ((hsourceMeas.inter hFb).preimage h1).inter
    have hi (j : Fin 3) : MeasurableSet {t : ℝ | |G (z.1,t) j-(Q j).eval t| ≤ error} :=
      measurableSet_le
        ((((measurable_pi_apply j).comp hG).comp (measurable_const.prodMk measurable_id)).sub
          (Q j).continuous.measurable).abs measurable_const
    have heq : ({t : ℝ | ∀ j, |G (z.1,t) j-(Q j).eval t| ≤ error} : Set ℝ)=
        ⋂ j : Fin 3, {t : ℝ | |G (z.1,t) j-(Q j).eval t| ≤ error} := by
      ext t
      simp only [mem_iInter,mem_ofPred_eq]
    change MeasurableSet ({t : ℝ | ∀ j, |G (z.1,t) j-(Q j).eval t| ≤ error} : Set ℝ)
    rw [heq]
    exact MeasurableSet.iInter hi
  have htimeMass : ENNReal.ofReal duration ≤ volume times :=
    hduration.trans (measure_mono (fun t ht => ⟨ht.2.1,ht.2.2.2⟩))
  have hraw : (fun t : ℝ => packetTime p root (z.1,t)) ⁻¹' times=
      {t : ℝ | (z.1,t)∈source∩p.F b ∧
        ∀ j, |G (z.1,packetTime p root (z.1,t)) j-
          (Q j).eval (packetTime p root (z.1,t))| ≤ error} := by
    ext t
    simp only [mem_preimage,times,mem_ofPred_eq]
    rw [p.childClockPoint_packetTime root (z.1,t)]
  refine ⟨b,hb,hpoint,Q,hdeg,hcoeff,hfit,?_⟩
  calc
    _ = ENNReal.ofReal (((2 : ℝ)^p.T (p.lev root))⁻¹)*ENNReal.ofReal duration :=
      ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal (((2 : ℝ)^p.T (p.lev root))⁻¹)*volume times :=
      mul_le_mul' le_rfl htimeMass
    _ = _ := by rw [←p.original_clock_time_measure root z.1 htimes,hraw]

end Path
end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
