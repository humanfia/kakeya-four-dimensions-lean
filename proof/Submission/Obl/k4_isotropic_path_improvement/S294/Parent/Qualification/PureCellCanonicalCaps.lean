-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PureCellCanonicalCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.CurrentOriginalFloorCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.CanonicalCellIncidenceCaps

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- Current pure-cell numerators give the canonical coefficient-world
caps needed by native qualification and incidence parameter palettes.
Only bounded original coefficients, unit time and geometric resolution
are used; the original external velocity weights are unchanged. -/
theorem canonical_cell_cap_of_current_pure_cells {Λ : Type*} [MeasurableSpace Λ]
    (μ : Measure (Λ × ℝ)) (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (E : Set (Λ × ℝ)) (hE : MeasurableSet E)
    {δ ρ s H C dimension : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1)
    (hδs : δ ≤ s) (hδp : δ ≤ ρ*s) (hH : 1 ≤ H) (hC : 0 ≤ C) (hd : 0 ≤ dimension)
    (hsmall : 3*(H+ρ)*δ ≤ ρ*s)
    (ht : ∀ z∈E, z.2∈Icc (0:ℝ) 1)
    (hcoeff : ∀ z∈E, ∀ i, |c z.1 i| ≤ H)
    (weight : (Fin 2 → ℤ) → ENNReal) (hweight : ∀ v, weight v≠∞)
    (hpure : ∀ w : ℝ, δ ≤ w → w ≤ 1 → ∀ (b : Fin 3 → ℤ) (j : ℤ) (v : Fin 2 → ℤ),
      (μ.restrict E) {z | originalBaseCode c δ z=b ∧ ⌊zx (c z.1) z.2/w⌋=j ∧
        parameterCode (ρ*s) (zv (c z.1))=v} ≤ 
          ENNReal.ofReal (C*δ^3*w^dimension)*weight v) :
    ∀ world cell v,
      (μ.restrict E) {z | parameterCode ρ (c z.1)=world ∧ canonicalZoomCell c ρ s z=cell ∧
        parameterCode (ρ*s) (zv (c z.1))=v} ≤ 
          ENNReal.ofReal ((151200*(12*H+3)*C*(3:ℝ)^dimension)*s*(ρ*s)^((2:ℝ)+dimension))*weight v := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hδ1 : δ ≤ 1 := hδs.trans hs1
  have hp : 0 < ρ*s := mul_pos hρ hs
  have hbound : ∀ᵐ z ∂μ.restrict E, |zx (c z.1) z.2| ≤ 3*H :=
    (ae_restrict_mem hE).mono (fun z hz => abs_zx_le (hcoeff z hz) (ht z hz))
  let Crect := 37800*(12*H+3)*C*(3:ℝ)^dimension
  have hCrect : 0 ≤ Crect := by dsimp only [Crect]; positivity
  have hrect (τ : ℝ) (Y : Fin 3 → ℝ) (v : Fin 2 → ℤ) :
      μ {z | z∈E ∧ z.2∈Icc τ (τ+δ) ∧
        (∀ i : Fin 3, zpos (c z.1) z.2 i.succ∈Icc (Y i) (Y i+3*(ρ*s))) ∧
        parameterCode (ρ*s) (zv (c z.1))=v} ≤ 
        ENNReal.ofReal (Crect*δ*(ρ*s)^2*(ρ*s)^dimension)*weight v := by
    have h := all_height_rectangle_caps_of_pure_cells (μ.restrict E)
      (originalBaseCoordinates c) (fun z => zx (c z.1) z.2)
      (fun z => parameterCode (ρ*s) (zv (c z.1))) v
      hδ le_rfl hδ1 (by positivity : 0 ≤ 3*H) hC hd (weight v) (hweight v) hbound
      (fun w hw hw1 b j => hpure w hw hw1 b j v)
      τ ![Y 1,Y 2] (Y 0) (3*(ρ*s)) (3*(ρ*s)) (by linarith) (by linarith)
    rw [Measure.restrict_apply' hE] at h
    have hset : {z : Λ × ℝ | z∈E ∧ z.2∈Icc τ (τ+δ) ∧
        (∀ i : Fin 3, zpos (c z.1) z.2 i.succ∈Icc (Y i) (Y i+3*(ρ*s))) ∧
        parameterCode (ρ*s) (zv (c z.1))=v}=
      {z | originalBaseCoordinates c z 0∈Icc τ (τ+δ) ∧
        (∀ i : Fin 2, originalBaseCoordinates c z i.succ∈
          Icc (![Y 1,Y 2] i) (![Y 1,Y 2] i+3*(ρ*s))) ∧
        zx (c z.1) z.2∈Icc (Y 0) (Y 0+3*(ρ*s)) ∧
        parameterCode (ρ*s) (zv (c z.1))=v}∩E := by
      ext z
      simp only [mem_inter_iff,mem_ofPred_eq]
      constructor
      · rintro ⟨hz,ht,hpos,hv⟩
        refine ⟨⟨ht,?_,hpos 0,hv⟩,hz⟩
        intro i
        fin_cases i
        · exact hpos 1
        · exact hpos 2
      · rintro ⟨⟨ht,hy,hx,hv⟩,hz⟩
        refine ⟨hz,ht,?_,hv⟩
        intro i
        fin_cases i
        · exact hx
        · exact hy 0
        · exact hy 1
    rw [hset]
    apply h.trans_eq
    congr 2
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hp.le]
    dsimp only [Crect]
    ring
  have h := canonical_cell_incidence_palette_cap μ c hc E hρ hs hδ hδs hH hCrect
    (Real.rpow_nonneg hp.le dimension) hsmall ht
    (fun z hz => ⟨hcoeff z hz 1,hcoeff z hz 2,hcoeff z hz 4,hcoeff z hz 6⟩)
    weight hrect
  intro world cell v
  apply (h world cell v).trans_eq
  congr 2
  rw [Real.rpow_add hp,Real.rpow_two]
  dsimp only [Crect]
  ring

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
