-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeRootMetadata, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalPreStateData
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestorOriginalFloors
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.OriginalRootFromData
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalPaletteVector
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.CommonDyadicVelocityReference

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData)
open Parent.Qualification
open Parent.Qualification.PhysicalModel
open Parent.Qualification.PhysicalModel.NativeAncestor

noncomputable section

section Path

variable {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)

/-- The actual data left by native preparation BEFORE child states.
Each root keeps one fixed original velocity reference and full-prior
floors/actual derivative tables, with no row or qualification oracle. -/
structure NativeRootMetadata (roots : Set (Fin p.C)) (E : Fin (d.W k) → Set Ev)
    (Vmax finePv : ℝ) (scales : OriginalRootScales) (pairPalette : Fin p.C → Measure (ℤ×ℤ)) where
  palette : Fin p.C → Measure (Fin 2 → ℝ)
  reference : ∀ a∈roots, Jets2.CommonDyadicVelocityReference finePv scales.paletteFinest
    (fun b => ((pairPalette a).map Parent.OriginalVelocityPalette.palettePairVector) {b}) (palette a)
  pre : ∀ a∈roots, Jets2.OriginalPreStateData ((hp.frozenPacket a).prior (d.ν k (p.γ a)))
    (coefficientTable (d.N k) p a Vmax) ((hp.frozenPacket a).selectedEvent (E (p.γ a)∩p.F a))
    (palette a) scales.dimension scales.floorExponent scales.floorStart scales.floorCount
    (fun i : Fin scales.regLength => scales.regLevel i.val) scales.KL

/-- Every later source restriction preserves all original metadata,
including the exact reference used by the final P5 state palettes. -/
def NativeRootMetadata.restrict {roots : Set (Fin p.C)} {E : Fin (d.W k) → Set Ev}
    {Vmax finePv : ℝ} {scales : OriginalRootScales} {pairPalette : Fin p.C → Measure (ℤ×ℤ)}
    (data : NativeRootMetadata hp roots E Vmax finePv scales pairPalette)
    {E' : Fin (d.W k) → Set Ev} (hsub : ∀ w, E' w⊆E w) :
    NativeRootMetadata hp roots E' Vmax finePv scales pairPalette where
  palette := data.palette
  reference := data.reference
  pre := fun a ha => (data.pre a ha).restrict (image_mono (fun z hz => ⟨hsub _ hz.1,hz.2⟩))

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
