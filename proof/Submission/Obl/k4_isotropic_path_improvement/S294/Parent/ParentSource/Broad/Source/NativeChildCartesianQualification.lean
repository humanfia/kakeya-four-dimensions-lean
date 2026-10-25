-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.NativeChildCartesianQualification, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/NativeChildCartesianQualification.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.NativeChildQualification
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.AncestorQualification

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native
open Qualification.Jets2

noncomputable section

/-- The actual inverse root clock is the affine clock used by the
Cartesian qualification transport. The original line index is unchanged. -/
theorem Native.PathData.childClockPoint_eq_fromAncestor {W : ℕ} (p : PathData W)
    (root : Fin p.C) :
    p.childClockPoint root = AncestorQualification.fromAncestor
      ((p.j root : ℝ)/(2:ℝ)^p.T (p.lev root))
      (((2:ℝ)^p.T (p.lev root))⁻¹) := by
  funext z
  apply Prod.ext
  · rfl
  · dsimp only [childClockPoint,AncestorQualification.fromAncestor]
    ring

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

/-- Qualification in the root clock yields a Cartesian witness on one
actual original child. Every witness stays in that child's original
counted source. Its duration is divided by the exact relative block
length, with only a degree-dependent coefficient cost. -/
theorem Native.PathData.Valid.cartesianQualified_original_child
    (hsourceMeas : MeasurableSet source)
    {Code : Type*} (st : Ev → Code) (Gs : Code → Fin 3 → ℝ)
    (hG : Measurable (Gs ∘ st))
    {z : Ev} (hz : z∈p.childClockReference root level source)
    {M T : ℕ} {Kq error duration : ℝ} (hKq : 0 ≤ Kq)
    (hq : NativeQualified (p.childClockReference root level source)
      (p.childClockLabel root level (p.γ root))
      (Gs ∘ (st ∘ p.childClockPoint root)) M T Kq error duration z) :
    ∃ b : Fin p.C, b∈p.trueDescendants root level ∧
      p.childClockPoint root z∈source∩p.F b ∧
      Cartesian.QualWitness (source∩p.F b) st Gs
        ((p.j b : ℝ)/(2:ℝ)^p.T (p.lev b))
        (((2:ℝ)^p.T (p.lev b))⁻¹) M
        (QualificationClock.coefficientCost M*Kq) error
        (duration/((((2:ℝ)^p.T (p.lev b))⁻¹)/
          (((2:ℝ)^p.T (p.lev root))⁻¹))) (p.childClockPoint root z) := by
  obtain ⟨b,hb,hpoint,hqb⟩ :=
    hp.nativeQualified_original_child root level hlevel hlast source hsource hterminal hz hq
  obtain ⟨hl,hancestor⟩ := (Finset.mem_filter.mp hb).2
  have hCylinder : p.fullCylinder b⊆p.fullCylinder root := by
    simpa only [hancestor] using
      hp.iterate_par_fullCylinder (p.lev b-p.lev root) b (Nat.sub_le _ _)
  have hzA := (hp.counted_subset_fullCylinder b hpoint.2).1
  let tA : ℝ := (p.j root : ℝ)/(2:ℝ)^p.T (p.lev root)
  let hA : ℝ := ((2:ℝ)^p.T (p.lev root))⁻¹
  let t0 : ℝ := (p.j b : ℝ)/(2:ℝ)^p.T (p.lev b)
  let h : ℝ := ((2:ℝ)^p.T (p.lev b))⁻¹
  have hhA : 0 < hA := by dsimp [hA]; positivity
  have hh : 0 < h := by dsimp [h]; positivity
  have hleft : tA ≤ t0 := by
    have ht : (z.1,t0)∈p.fullCylinder b := by
      refine ⟨hzA,le_rfl,?_⟩
      dsimp [t0]
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    exact (hCylinder ht).2.1
  have hright : t0+h ≤ tA+hA := by
    have ht : (z.1,t0+h)∈p.fullCylinder b := by
      refine ⟨hzA,by linarith only [hh.le],?_⟩
      dsimp [t0,h]
      apply le_of_eq
      ring
    have ht' := (hCylinder ht).2.2
    have he : (((p.j root : ℝ)+1)/(2:ℝ)^p.T (p.lev root))=tA+hA := by
      dsimp [tA,hA]
      ring
    rwa [he] at ht'
  have hFb : MeasurableSet (p.F b) := (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hclock : p.childClockPoint root = AncestorQualification.fromAncestor tA hA :=
    p.childClockPoint_eq_fromAncestor root
  have hback : ((p.childClockPoint root z).1,
      ((p.childClockPoint root z).2-tA)/hA)=z := by
    rw [hclock]
    apply Prod.ext
    · rfl
    · dsimp only [AncestorQualification.fromAncestor]
      field_simp
      ring
  have hqb' : NativeQualified (AncestorQualification.event tA hA (source∩p.F b))
      (p.childClockLabel root level (p.γ root))
      (Gs ∘ (st ∘ AncestorQualification.fromAncestor tA hA))
      M T Kq error duration
      ((p.childClockPoint root z).1,((p.childClockPoint root z).2-tA)/hA) := by
    rw [hback]
    simpa only [AncestorQualification.event,←hclock] using hqb
  refine ⟨b,hb,hpoint,?_⟩
  exact AncestorQualification.qualWitness_of_native_in_ancestor
    (source∩p.F b) (hsourceMeas.inter hFb) st Gs hG
    (p.childClockLabel root level (p.γ root)) hhA hh
    (by linarith only [hleft,hright]) hleft (by linarith only [hright,hh.le]) hKq
    (fun t ht _ => by
      have ht' := (hp.counted_subset_fullCylinder b ht.2).2
      refine ⟨ht'.1,?_⟩
      have he : (((p.j b : ℝ)+1)/(2:ℝ)^p.T (p.lev b))=t0+h := by
        dsimp [t0,h]
        ring
      simpa only [he] using ht'.2) hqb'

/-- The finite-grid qualification supplied by the original-world failure
bound has the same actual-child Cartesian witness. No polynomial grid
or witness time is chosen from a new conditional law. -/
theorem Native.PathData.Valid.cartesianQualified_original_child_of_grid
    (hsourceMeas : MeasurableSet source)
    {Code : Type*} (st : Ev → Code) (Gs : Code → Fin 3 → ℝ)
    (hG : Measurable (Gs ∘ st))
    {z : Ev} (hz : z∈p.childClockReference root level source)
    {M T : ℕ} {mesh error duration : ℝ} {bound : ℤ}
    (hmesh : 0 ≤ mesh) (hbound : 0 ≤ bound)
    (hq : NativeGridQualified (p.childClockReference root level source)
      (p.childClockLabel root level (p.γ root))
      (Gs ∘ (st ∘ p.childClockPoint root)) M T mesh bound error duration z) :
    ∃ b : Fin p.C, b∈p.trueDescendants root level ∧
      p.childClockPoint root z∈source∩p.F b ∧
      Cartesian.QualWitness (source∩p.F b) st Gs
        ((p.j b : ℝ)/(2:ℝ)^p.T (p.lev b))
        (((2:ℝ)^p.T (p.lev b))⁻¹) M
        (QualificationClock.coefficientCost M*(mesh*bound)) error
        (duration/((((2:ℝ)^p.T (p.lev b))⁻¹)/
          (((2:ℝ)^p.T (p.lev root))⁻¹))) (p.childClockPoint root z) := by
  exact hp.cartesianQualified_original_child root level hlevel hlast source hsource hterminal
    hsourceMeas st Gs hG hz (mul_nonneg hmesh (by exact_mod_cast hbound))
    (nativeQualified_of_nativeGridQualified hmesh hq)

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
