-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.OriginalChildRowQualification, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.NativeChildCartesianQualification
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ScaledQualWitness
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Cartesian.MeasurableQualification

/-! The qualification rows on one actual original child, in original
signal units. Native discovery is performed in the ancestor clock;
neither the witness trajectory nor its original reference is changed. -/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native
open Qualification.Jets2

noncomputable section

section Path

variable {W : ℕ} {p : PathData W} {N L κ₁ δ₀ σ : ℝ}
    {m Mp Dp : ℕ} {s : ℕ → ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ} {f : ℝ → ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

/-- A true descendant retains its original world. -/
theorem Native.PathData.Valid.trueDescendants_world (root child : Fin p.C)
    (level : ℕ) (hchild : child∈p.trueDescendants root level) :
    p.γ child=p.γ root := by
  obtain ⟨_,ha⟩ := (Finset.mem_filter.mp hchild).2
  obtain ⟨_,hw,_⟩ := Broad.iterate_par_spec hp.toOriginal
    (p.lev child-p.lev root) child (Nat.sub_le _ _)
  change p.γ (p.par^[p.lev child-p.lev root] child)=p.γ child at hw
  simpa only [ha] using hw.symm

/-- The existential child produced by native qualification is the
specified original child whenever that child contains the occurrence.
The endpoint cut makes the identification literal. -/
theorem Native.PathData.Valid.cartesianQualified_fixed_child_of_grid
    (root : Fin p.C) (level : ℕ) (hlevel : p.lev root ≤ level) (hlast : level ≤ m-1)
    (source : Set Ev) (hsource : source⊆p.F root)
    (hterminal : ∀ z∈source, ∃ terminal : Fin p.C,
      p.lev terminal=m-1 ∧ p.γ terminal=p.γ root ∧ z∈p.F terminal)
    (hsourceMeas : MeasurableSet source)
    {Code : Type*} (st : Ev → Code) (Gs : Code → Fin 3 → ℝ)
    (hG : Measurable (Gs ∘ st))
    (child : Fin p.C) (hchildLevel : p.lev child=level) (hchildWorld : p.γ child=p.γ root)
    {z : Ev} (hz : z∈p.childClockReference root level source)
    (hzchild : p.childClockPoint root z∈p.F child)
    {M T : ℕ} {mesh error duration : ℝ} {bound : ℤ}
    (hmesh : 0 ≤ mesh) (hbound : 0 ≤ bound)
    (hq : NativeGridQualified (p.childClockReference root level source)
      (p.childClockLabel root level (p.γ root))
      (Gs ∘ (st ∘ p.childClockPoint root)) M T mesh bound error duration z) :
    Cartesian.QualWitness (source∩p.F child) st Gs
      ((p.j child : ℝ)/(2:ℝ)^p.T (p.lev child))
      (((2:ℝ)^p.T (p.lev child))⁻¹) M
      (QualificationClock.coefficientCost M*(mesh*bound)) error
      (duration/((((2:ℝ)^p.T (p.lev child))⁻¹)/
        (((2:ℝ)^p.T (p.lev root))⁻¹))) (p.childClockPoint root z) := by
  obtain ⟨child',hchild',hpoint,hqualified⟩ :=
    hp.cartesianQualified_original_child_of_grid root level hlevel hlast source hsource hterminal
      hsourceMeas st Gs hG hz hmesh hbound hq
  have hchildLevel' := (Finset.mem_filter.mp hchild').2.1
  have hchildWorld' := hp.trueDescendants_world root child' level hchild'
  have haway : p.childClockPoint root z∉p.oldEndpoints child := by
    simpa only [Native.PathData.oldEndpoints,Native.PathData.levelEndpoints,hchildLevel] using hz.2
  have heq := hp.eq_of_common_nonendpoint child child'
    (hchildLevel'.trans hchildLevel.symm) (hchildWorld'.trans hchildWorld.symm)
    hzchild hpoint.2 haway
  subst child'
  exact hqualified

/-- The final relative-row qualification clause on an actual child.
Its polynomial is in the CHILD block time, and `scale` is the original
signal factor `a_ancestor/h_ancestor`. All three budgets are explicit. -/
theorem Native.PathData.Valid.original_child_row_qualified
    (root : Fin p.C) (level : ℕ) (hlevel : p.lev root ≤ level) (hlast : level ≤ m-1)
    (source : Set Ev) (hsource : source⊆p.F root)
    (hterminal : ∀ z∈source, ∃ terminal : Fin p.C,
      p.lev terminal=m-1 ∧ p.γ terminal=p.γ root ∧ z∈p.F terminal)
    (hsourceMeas : MeasurableSet source)
    {Code : Type*} (st : Ev → Code) (Gs : Code → Fin 3 → ℝ)
    (hG : Measurable (Gs ∘ st))
    (child : Fin p.C) (hchildLevel : p.lev child=level) (hchildWorld : p.γ child=p.γ root)
    {z : Ev} (hz : z∈p.childClockReference root level source)
    (hzchild : p.childClockPoint root z∈p.F child)
    {M T : ℕ} {mesh error duration scale K theta : ℝ} {bound : ℤ}
    (hmesh : 0 ≤ mesh) (hbound : 0 ≤ bound) (hscale : 0 ≤ scale)
    (hcoeff : QualificationClock.coefficientCost M*(mesh*bound) ≤ K)
    (herror : error ≤ theta)
    (hduration : 1/K ≤ duration/((((2:ℝ)^p.T (p.lev child))⁻¹)/
      (((2:ℝ)^p.T (p.lev root))⁻¹)))
    (hq : NativeGridQualified (p.childClockReference root level source)
      (p.childClockLabel root level (p.γ root))
      (Gs ∘ (st ∘ p.childClockPoint root)) M T mesh bound error duration z) :
    Cartesian.QualWitness (source∩p.F child) st (fun k i => scale*Gs k i)
      ((p.j child : ℝ)/(2:ℝ)^p.T (p.lev child))
      (((2:ℝ)^p.T (p.lev child))⁻¹) M (K*scale) (scale*theta) (1/K)
      (p.childClockPoint root z) := by
  have hqualified := hp.cartesianQualified_fixed_child_of_grid root level hlevel hlast
    source hsource hterminal hsourceMeas st Gs hG child hchildLevel hchildWorld
    hz hzchild hmesh hbound hq
  have hs : Cartesian.QualWitness (source∩p.F child) st (fun k i => scale*Gs k i)
      ((p.j child : ℝ)/(2:ℝ)^p.T (p.lev child))
      (((2:ℝ)^p.T (p.lev child))⁻¹) M
      (scale*(QualificationClock.coefficientCost M*(mesh*bound))) (scale*error)
      (duration/((((2:ℝ)^p.T (p.lev child))⁻¹)/
        (((2:ℝ)^p.T (p.lev root))⁻¹))) (p.childClockPoint root z) :=
    Qualification.scaled_qualWitness hscale hqualified
  exact hs.mono (by nlinarith only [mul_le_mul_of_nonneg_left hcoeff hscale])
    (mul_le_mul_of_nonneg_left herror hscale) hduration

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
