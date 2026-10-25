-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.AncestorRecordChildRatios, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.AncestorRecordRatioStates

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData PreparedAngularPath PaletteFamily velocityPalette labelledVelocityPalette)
open Parent.OriginalVelocityPalette
open scoped ENNReal

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A : ℝ} {θ : ENNReal}
    {F : PaletteFamily Q i stop a A θ}
    {root : Fin p.C} {E : Set Ev}
    {Krecord baseRef hiddenRef finePv paletteRatio cut frontRadius fraction χ finest dimension Kcap : ℝ}
    (data : OriginalAncestorRecordSource F root E Krecord baseRef hiddenRef finePv paletteRatio
      cut frontRadius fraction χ finest dimension Kcap)
    (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hd hp


/-- Every current original-record event ratio survives restricting to
a later child, because that child is a union of complete original
histories. The reference record law remains the same original law. -/
theorem OriginalAncestorRecordSource.record_ratio_on_child
    (hEbase : E⊆Q.base (p.γ root))
    (child : Fin p.C) (hworld : p.γ child=p.γ root) (hchild : p.lev child ≤ stop)
    (B : Set Ev) (cap : ENNReal)
    (hcaps : ∀ rec, (((d.ν k (p.γ root)).prod volume).restrict data.kept)
      (data.piece rec∩B) ≤ cap*(((d.ν k (p.γ root)).prod volume).restrict data.kept) (data.piece rec))
    (rec) :
    (((d.ν k (p.γ root)).prod volume).restrict (data.kept∩p.F child)) (data.piece rec∩B) ≤
      cap*(((d.ν k (p.γ root)).prod volume).restrict (data.kept∩p.F child)) (data.piece rec) := by
  let raw := (d.ν k (p.γ root)).prod (volume : Measure ℝ)
  let mu := raw.restrict data.kept
  have hloc := F.record_child_localization hp root child hworld hchild
    (fun rec => rec.1) data.piece (fun rec z hz => (data.subset rec hz).2)
    (fun rec z hz => hEbase (data.subset rec hz).1)
  obtain ⟨_hfloor,hratios⟩ := hloc.2 mu
    (fun rec => ENNReal.ofReal cut*raw (F.fineOriginalEvent root rec.1.1 univ)) data.floor
  have hmChild : MeasurableSet (p.F child) :=
    (hp.2.2.2.2.2.2.2 child).2.2.2.2.2.2.2.2.2.1
  have hlaw : mu.restrict (p.F child)=raw.restrict (data.kept∩p.F child) := by
    change (raw.restrict data.kept).restrict (p.F child)=raw.restrict (data.kept∩p.F child)
    rw [Measure.restrict_restrict hmChild,inter_comm]
  have h := hratios B cap hcaps rec
  rw [hlaw] at h
  exact h

/-- The original all-D fine palette ceiling on every child's record
reservoir. The probability reference is fixed at the ancestor before
all child choices; no palette is conditioned on the current law. -/
theorem OriginalAncestorRecordSource.child_record_palette_cap
    (hEbase : E⊆Q.base (p.γ root))
    (child : Fin p.C) (hworld : p.γ child=p.γ root) (hchild : p.lev child ≤ stop)
    (D : Set (ℤ×ℤ)) (hD : MeasurableSet D) (rec) :
    (((d.ν k (p.γ root)).prod volume).restrict (data.kept∩p.F child))
      (data.piece rec∩{z | velocityPalette finePv (Parent.v z.1)∈D}) ≤
      (ENNReal.ofReal ((8*paletteRatio)/cut)*
        ((Q.coarseLaw (p.lev root) (F.code root)).map (labelledVelocityPalette finePv)) D)*
          (((d.ν k (p.γ root)).prod volume).restrict (data.kept∩p.F child)) (data.piece rec) := by
  apply OriginalAncestorRecordSource.record_ratio_on_child data hd hp hEbase child hworld hchild _ _ ?_ rec
  intro r
  have hset : data.piece r∩{z | velocityPalette finePv (Parent.v z.1)∈D}=
      {z | z∈data.piece r ∧ velocityPalette finePv (Parent.v z.1)∈D} := by
    ext z
    simp only [mem_inter_iff,mem_ofPred_eq]
  rw [hset]
  simpa only [mul_assoc,mul_comm,mul_left_comm,Parent.v,Parent.ParentSource.v] using data.palette r D hD

/-- Scaled normalized pencil strips on the exact child record law,
from the same genuine whole-history floors and narrow-state exclusion. -/
theorem OriginalAncestorRecordSource.child_record_normalized_strip_cap
    (hHE : ∀ w, H w⊆d.E k w)
    (hH : ∀ w, H w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (hactive : F.active root) (hEbase : E⊆Q.base (p.γ root))
    (child : Fin p.C) (hworld : p.γ child=p.γ root) (hchild : p.lev child ≤ stop)
    (hcut : 0 < cut) (hfr : 0 ≤ fraction)
    (radius : ℝ) (hwidth : (6*p.κ)*radius ≤ frontRadius)
    (normal center : EuclideanSpace ℝ (Fin 2)) (hnormal : ‖normal‖=1) (rec) :
    (((d.ν k (p.γ root)).prod volume).restrict (data.kept∩p.F child))
      (data.piece rec∩{z |
        |Inner.inner ℝ normal ((6*p.κ)⁻¹ • p.normalizedVelocity root z-center)| ≤ radius}) ≤
      ENNReal.ofReal ((8*fraction)/cut)*
        (((d.ν k (p.γ root)).prod volume).restrict (data.kept∩p.F child)) (data.piece rec) := by
  classical
  apply OriginalAncestorRecordSource.record_ratio_on_child data hd hp hEbase child hworld hchild _ _ ?_ rec
  intro r
  have hf : p.lev r.1.1=stop :=
    (Finset.mem_filter.mp (F.retained_original_fine_spec root r.1).1).2.1
  have hw : p.γ r.1.1=p.γ root :=
    (Finset.mem_filter.mp (F.retained_original_fine_spec root r.1).1).2.2.1
  by_cases hne : (data.piece r).Nonempty
  · exact F.current_record_scaled_normalized_strip_cap hd hp hHE hH root r.1.1 hactive hf hw hfr
      (data.wide r hne) (F.retained_original_fine_spec root r.1).2
      (((d.ν k (p.γ root)).prod volume).restrict data.kept) Measure.restrict_le_self (data.piece r)
      (fun z hz => (data.subset r hz).2) cut hcut (data.floor r) radius hwidth normal center hnormal
  · have hempty : data.piece r=∅ := Set.not_nonempty_iff_eq_empty.mp hne
    apply (measure_mono inter_subset_left).trans
    simp only [hempty,measure_empty,mul_zero,le_refl]

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
