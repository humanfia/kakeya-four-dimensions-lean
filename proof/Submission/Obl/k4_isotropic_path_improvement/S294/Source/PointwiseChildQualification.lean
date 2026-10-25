-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.PointwiseChildQualification, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Clauses
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalChildRowQualification
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ReindexedQualWitness
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.SelectedPacketLaw

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource Parent.ParentSource.Native Parent.Qualification.Jets2

noncomputable section

section Path

variable {W : ℕ} {p : PathData W} {N L κ₁ δ₀ σ : ℝ}
    {m Mp Dp : ℕ} {s : ℕ → ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ} {f : ℝ → ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

/-- Remove native failures before selecting a child. Every later subset
of that good source satisfies the literal final qualification clause,
with empty exception. A later state coding keeps the same witnesses
through its readout identity on the fixed row reference. -/
theorem pointwise_child_qual_clauses
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
    (hqualified : ∀ z∈(hp.frozenPacket root).selectedEvent S,
      NativeGridQualified (p.childClockReference root level source)
        (p.childClockLabel root level (p.γ root))
        (Gs ∘ (st ∘ p.childClockPoint root)) M T mesh bound error duration z)
    (ν₀ : Measure Ln) :
    QualClauses M K theta aA q (p.j child) (((2:ℝ)^p.T (p.lev child))⁻¹)
      ν₀ S (source∩p.F child) ∅ st' G' := by
  have hpoint (w : Ev) : p.childClockPoint root ((hp.frozenPacket root).timeChange w)=w := by
    rw [hp.childClockPoint_eq_timeChange_symm]
    exact MeasurableEquiv.symm_apply_apply _ w
  have hgood (w : Ev) (hw : w∈S) :
      Parent.Cartesian.QualWitness (source∩p.F child) st
        (fun k i => (aA/q)*Gs k i)
        ((p.j child : ℝ)/(2:ℝ)^p.T (p.lev child))
        (((2:ℝ)^p.T (p.lev child))⁻¹) M (K*(aA/q)) ((aA/q)*theta) (1/K) w := by
    have hz : (hp.frozenPacket root).timeChange w∈p.childClockReference root level source := by
      change p.childClockPoint root ((hp.frozenPacket root).timeChange w)∈p.childReference root level source
      rw [hpoint]
      exact hSref hw
    have hq := hp.original_child_row_qualified root level hlevel hlast source hsource hterminal
      hsourceMeas st Gs hG child hchildLevel hchildWorld hz
      (by simpa only [hpoint] using hSchild hw) hmesh hbound hscale hcoeff herror hduration
      (hqualified _ ⟨w,hw,rfl⟩)
    simpa only [hpoint] using hq
  refine ⟨MeasurableSet.empty,?_,?_⟩
  · rintro w ⟨hw,hnot⟩
    have href : w∈source∩p.F child := ⟨(hSref hw).1.1,hSchild hw⟩
    have hq := Parent.Qualification.qualWitness_of_readout_eq_on_reference
      (st:=st) (st':=st') (row:=fun k i => (aA/q)*Gs k i) (row':=G')
      hreadout href (hgood w hw)
    apply (hnot ?_).elim
    simpa only [Submission.Obl.k4_physical_row_packet_potential.Cartesian.QualWitness,
      div_eq_mul_inv] using hq
  · simp

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
