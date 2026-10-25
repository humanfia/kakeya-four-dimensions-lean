-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.GlobalAncestorRecordSource, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalAncestorRecordSource

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native
open scoped ENNReal BigOperators

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A : ℝ} {θ : ENNReal}
    (F : PaletteFamily Q i stop a A θ) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hd hp

/-- A genuine record source on each active ancestor yields ONE original
surviving family. Every ancestor's actual retained law is exactly that
global family's slice, including all of its record floors and all later
child/query numerator estimates. No other root's cut alters that law. -/
theorem Native.PaletteFamily.assemble_original_ancestor_record_sources
    (E : Fin (d.W k) → Set Ev) (hE : ∀ w, MeasurableSet (E w))
    (hbase : ∀ w, E w⊆Q.base w)
    {K baseRef hiddenRef pv paletteRatio cut frontRadius fraction χ finest dimension Kcap : ℝ}
    (hsources : ∀ root, F.active root → Nonempty (OriginalAncestorRecordSource F root
      (E (p.γ root)∩p.F root) K baseRef hiddenRef pv paletteRatio cut frontRadius fraction
        χ finest dimension Kcap)) :
    ∃ (sources : (root : Fin p.C) → F.active root → OriginalAncestorRecordSource F root
        (E (p.γ root)∩p.F root) K baseRef hiddenRef pv paletteRatio cut frontRadius fraction
          χ finest dimension Kcap)
      (keep : Fin (d.W k) → Set Ev),
      (∀ w, MeasurableSet (keep w) ∧ keep w⊆E w) ∧
      (∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (E w\keep w)) ≤
        ENNReal.ofReal cut*(⌈K^12⌉₊:ENNReal) ∧
      ∀ root (hroot : F.active root),
        keep (p.γ root)∩p.F root=(sources root hroot).kept := by
  classical
  let sources := fun root (hroot : F.active root) => Classical.choice (hsources root hroot)
  let G := fun root => if hroot : F.active root then (sources root hroot).kept else univ
  have hG (root : Fin p.C) (hroot : F.active root) : MeasurableSet (G root) := by
    simpa only [G,dif_pos hroot] using (sources root hroot).kept_measurable
  have hcut (root : Fin p.C) (hroot : F.active root) :
      ((d.ν k (p.γ root)).prod volume) ((E (p.γ root)∩p.F root)\G root) ≤
        (ENNReal.ofReal cut*(⌈K^12⌉₊:ENNReal))*
          ((d.ν k (p.γ root)).prod volume) {z | (p.γ root,z)∈F.U root} := by
    simpa only [G,dif_pos hroot] using (sources root hroot).loss
  obtain ⟨keep,hkeep,hloss,hslices⟩ := F.assemble_original_root_palette_cuts hd hp
    E hE hbase G hG (ENNReal.ofReal cut*(⌈K^12⌉₊:ENNReal)) hcut
  refine ⟨sources,keep,hkeep,hloss,?_⟩
  intro root hroot
  rw [hslices root hroot]
  simpa only [G,dif_pos hroot] using
    (inter_eq_right.mpr (sources root hroot).kept_subset)

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
