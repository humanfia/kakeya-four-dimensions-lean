-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.ChildFailureQualification, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Clauses
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalChildRowQualification
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ReindexedQualWitness
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.SelectedPacketLaw

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open scoped ENNReal
open Parent.ParentSource Parent.ParentSource.Native Parent.Qualification.Jets2

noncomputable section

local instance (C : ℕ) : MeasurableSpace (Option (Fin C)) := ⊤
local instance (C : ℕ) : MeasurableSingletonClass (Option (Fin C)) := ⟨fun _ => trivial⟩

section Path

variable {W : ℕ} {p : PathData W} {N L κ₁ δ₀ σ : ℝ}
    {m Mp Dp : ℕ} {s : ℕ → ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ} {f : ℝ → ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

/-- A small ORIGINAL-law native failure ratio gives the exact final
qualification exception, including later Nat-state readout. Residual
regularization is used only in the total failure proof; the source and
its statewise breadth are not restricted to native-good points. -/
theorem child_qual_clauses_of_original_native_failure_ratio
    (root : Fin p.C) (level : ℕ) (hlevel : p.lev root ≤ level) (hlast : level ≤ m-1)
    (source : Set Ev) (hsource : source⊆p.F root)
    (hterminal : ∀ z∈source, ∃ terminal : Fin p.C,
      p.lev terminal=m-1 ∧ p.γ terminal=p.γ root ∧ z∈p.F terminal)
    (hsourceMeas : MeasurableSet source)
    (S : Set Ev) (hSref : S⊆p.childReference root level source)
    {Code : Type*} (st : Ev → Code) (Gs : Code → Fin 3 → ℝ)
    (hG : Measurable (Gs ∘ st))
    (child : Fin p.C) (hchildLevel : p.lev child=level) (hchildWorld : p.γ child=p.γ root)
    (hSchild : S⊆p.F child)
    (st' : Ev → ℕ) (G' : ℕ → Fin 3 → ℝ)
    (M T : ℕ) (mesh error duration aA q K theta : ℝ) (bound : ℤ)
    (hreadout : ∀ z∈source∩p.F child,
      G' (st' z)=fun i => (aA/q)*Gs (st z) i)
    (hmesh : 0 ≤ mesh) (hbound : 0 ≤ bound) (hscale : 0 ≤ aA/q)
    (hcoeff : Parent.QualificationClock.coefficientCost M*(mesh*bound) ≤ K)
    (herror : error ≤ theta)
    (hduration : 1/K ≤ duration/((((2:ℝ)^p.T (p.lev child))⁻¹)/
      (((2:ℝ)^p.T (p.lev root))⁻¹)))
    (ν₀ : Measure Ln)
    (hfailure : ((ν₀.prod volume).restrict S)
      {w | ¬NativeGridQualified (p.childClockReference root level source)
        (p.childClockLabel root level (p.γ root))
        (Gs ∘ (st ∘ p.childClockPoint root)) M T mesh bound error duration
        ((hp.frozenPacket root).timeChange w)}≤
      (1/10000:ENNReal)*((ν₀.prod volume).restrict S) univ) :
    QualClauses M K theta aA q (p.j child) (((2:ℝ)^p.T (p.lev child))⁻¹)
      ν₀ S (source∩p.F child)
      {w | ¬NativeGridQualified (p.childClockReference root level source)
        (p.childClockLabel root level (p.γ root))
        (Gs ∘ (st ∘ p.childClockPoint root)) M T mesh bound error duration
        ((hp.frozenPacket root).timeChange w)} st' G'  := by
  let goodClock := {z | NativeGridQualified (p.childClockReference root level source)
    (p.childClockLabel root level (p.γ root)) (Gs ∘ (st ∘ p.childClockPoint root))
    M T mesh bound error duration z}
  let bad := (hp.frozenPacket root).timeChange ⁻¹' goodClockᶜ
  have href : MeasurableSet (p.childClockReference root level source) :=
    p.childClockReference_measurable root level hsourceMeas
  have hrow : Measurable (Gs ∘ (st ∘ p.childClockPoint root)) := by
    simpa only [Function.comp_assoc] using hG.comp (p.childClockPoint_measurable root)
  have hgood : MeasurableSet goodClock := measurableSet_nativeGridQualified href
    (hp.childClockLabel_measurable root level _) ((to_countable _).measurableSet)
    hrow M T mesh bound error duration
  have hbad : MeasurableSet bad := hgood.compl.preimage (hp.frozenPacket root).timeChange.measurable
  have hpoint (w : Ev) : p.childClockPoint root ((hp.frozenPacket root).timeChange w)=w := by
    rw [hp.childClockPoint_eq_timeChange_symm]
    exact MeasurableEquiv.symm_apply_apply _ w
  refine ⟨hbad,?_,hfailure⟩
  rintro w ⟨hw,hnot⟩
  change w∈bad
  by_contra hn
  have hq : NativeGridQualified (p.childClockReference root level source)
      (p.childClockLabel root level (p.γ root))
      (Gs ∘ (st ∘ p.childClockPoint root)) M T mesh bound error duration
      ((hp.frozenPacket root).timeChange w) := by
    exact not_not.mp hn
  have hz : (hp.frozenPacket root).timeChange w∈p.childClockReference root level source := by
    change p.childClockPoint root ((hp.frozenPacket root).timeChange w)∈p.childReference root level source
    rw [hpoint]
    exact hSref hw
  have hwq := hp.original_child_row_qualified root level hlevel hlast source hsource hterminal
    hsourceMeas st Gs hG child hchildLevel hchildWorld hz
    (by simpa only [hpoint] using hSchild hw) hmesh hbound hscale hcoeff herror hduration hq
  have hqualified : Parent.Cartesian.QualWitness (source∩p.F child) st
      (fun k i => (aA/q)*Gs k i) ((p.j child:ℝ)/(2:ℝ)^p.T (p.lev child))
      (((2:ℝ)^p.T (p.lev child))⁻¹) M (K*(aA/q)) ((aA/q)*theta) (1/K) w := by
    simpa only [hpoint] using hwq
  have hfinal := Parent.Qualification.qualWitness_of_readout_eq_on_reference
    (st:=st) (st':=st') (row:=fun k i => (aA/q)*Gs k i) (row':=G')
    hreadout ⟨(hSref hw).1.1,hSchild hw⟩ hqualified
  apply hnot
  simpa only [Submission.Obl.k4_physical_row_packet_potential.Cartesian.QualWitness,div_eq_mul_inv] using hfinal

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
