-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.SimultaneousIncidenceParameterPalettes, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/SimultaneousIncidenceParameterPalettes.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalIncidenceParameterPalettes

/-! # Prepare both parameter-palette levels with one original entry cut -/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section

/-- One current-law restriction constructs both original-state coarse
worlds and all fine canonical-cell parameter palettes. -/
theorem prepare_simultaneous_incidence_parameter_palettes {Λ σ : Type*}
    [MeasurableSpace Λ] [Fintype σ]
    (μ : Measure (Λ × ℝ)) (ν : Measure Λ)
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (E : Set (Λ × ℝ)) (hE : MeasurableSet E)
    {b ρ H amplitude0 K0 C0 cut0 : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hρ : 0 < ρ) (hH : 0 ≤ H)
    (hamp0 : 0 < amplitude0) (hK0 : 0 < K0) (hC0 : 0 ≤ C0) (hcut0 : 0 < cut0)
    (n0 : ℕ) (hρdyadic : ρ=dyadicParameterWidth n0)
    (n : σ → ℕ) (amplitude K C cut : σ → ℝ)
    (hamp : ∀ i, 0 < amplitude i) (hK : ∀ i, 0 < K i)
    (hC : ∀ i, 0 ≤ C i) (hcut : ∀ i, 0 < cut i)
    (ht : ∀ z∈E, z.2∈Icc (0 : ℝ) 1)
    (hjets : ∀ z∈E, |c z.1 1|≤H ∧ |c z.1 2|≤H ∧ |c z.1 4|≤H ∧ |c z.1 6|≤H)
    (hsmall : (2+3*(H+1))*b ≤ ρ)
    (hfinite0 : ((fun z : Λ × ℝ => parameterCode ρ (c z.1)) '' E).Finite)
    (hfinite : ∀ i, ((fun z : Λ × ℝ =>
      parameterCode (ρ*dyadicParameterWidth (n i)) (c z.1)) '' E).Finite)
    (weight0 : (Fin 2 → ℤ) → ENNReal) (hweight0 : ∀ v, weight0 v ≠ ∞)
    (weight : σ → (Fin 2 → ℤ) → ENNReal) (hweight : ∀ i v, weight i v ≠ ∞)
    (hfloor0 : ∀ z∈E,
      ENNReal.ofReal (ρ^2*amplitude0/K0)*weight0 (parameterCode ρ (zv (c z.1))) ≤
        ν {l | parameterCode ρ (c l)=parameterCode ρ (c z.1)})
    (hfloor : ∀ i z, z∈E →
      ENNReal.ofReal ((ρ*dyadicParameterWidth (n i))^2*amplitude i/K i)*
        weight i (parameterCode (ρ*dyadicParameterWidth (n i)) (zv (c z.1))) ≤
      ν {l | parameterCode (ρ*dyadicParameterWidth (n i)) (c l)=
        parameterCode (ρ*dyadicParameterWidth (n i)) (c z.1)})
    (hcap0 : ∀ world cell v,
      (μ.restrict E) {z | parameterCode 1 (c z.1)=world ∧
        canonicalZoomCell c 1 ρ z=cell ∧ parameterCode ρ (zv (c z.1))=v} ≤
      ENNReal.ofReal (C0*ρ*ρ^2*amplitude0)*weight0 v)
    (hcap : ∀ i world cell v,
      (μ.restrict E) {z | parameterCode ρ (c z.1)=world ∧
        canonicalZoomCell c ρ (dyadicParameterWidth (n i)) z=cell ∧
        parameterCode (ρ*dyadicParameterWidth (n i)) (zv (c z.1))=v} ≤
      ENNReal.ofReal (C i*dyadicParameterWidth (n i)*
        (ρ*dyadicParameterWidth (n i))^2*amplitude i)*weight i v) :
    ∃ R : Set (Λ × ℝ), MeasurableSet R ∧ R ⊆ E ∧
      μ (E \ R) ≤ (ENNReal.ofReal (cut0*zoomBlockVisitConstant)+
        ∑ i, ENNReal.ofReal (cut i*zoomBlockVisitConstant))*ν univ ∧
      ∃ (blocks : ((Fin 4 → ℤ) × (Fin 2 → ℤ)) → Finset (Fin 7 → ℤ))
        (palettes : σ → (((Fin 7 → ℤ) × (Fin 4 → ℤ)) × (Fin 2 → ℤ)) → Finset (Fin 7 → ℤ)),
        (∀ key, ((blocks key).card : ℝ) ≤ 256*(12*H+4)^7*(C0*K0/cut0)) ∧
        (∀ i key, ((palettes i key).card : ℝ) ≤ C i*K i/cut i) ∧
        (∀ z∈R, parameterCode ρ (c z.1) ∈
          blocks (originalFineState c b z,parameterCode ρ (zv (c z.1)))) ∧
        ∀ i z, z∈R → parameterCode (ρ*dyadicParameterWidth (n i)) (c z.1) ∈
          palettes i ((parameterCode ρ (c z.1),
            canonicalZoomCell c ρ (dyadicParameterWidth (n i)) z),
            parameterCode (ρ*dyadicParameterWidth (n i)) (zv (c z.1))) := by
  let root : Option σ → ℝ := fun q => match q with | none => 1 | some _ => ρ
  let levels : Option σ → ℕ := fun q => match q with | none => n0 | some i => n i
  let amps : Option σ → ℝ := fun q => match q with | none => amplitude0 | some i => amplitude i
  let Ks : Option σ → ℝ := fun q => match q with | none => K0 | some i => K i
  let Cs : Option σ → ℝ := fun q => match q with | none => C0 | some i => C i
  let cuts : Option σ → ℝ := fun q => match q with | none => cut0 | some i => cut i
  let weights : Option σ → (Fin 2 → ℤ) → ENNReal :=
    fun q => match q with | none => weight0 | some i => weight i
  have hroot (q) : 0 < root q := by cases q <;> simp only [root] <;> positivity
  have hamps (q) : 0 < amps q := by
    cases q with
    | none => exact hamp0
    | some i => exact hamp i
  have hKs (q) : 0 < Ks q := by
    cases q with
    | none => exact hK0
    | some i => exact hK i
  have hCs (q) : 0 ≤ Cs q := by
    cases q with
    | none => exact hC0
    | some i => exact hC i
  have hcuts (q) : 0 < cuts q := by
    cases q with
    | none => exact hcut0
    | some i => exact hcut i
  have hwtop (q) v : weights q v ≠ ∞ := by
    cases q with
    | none => exact hweight0 v
    | some i => exact hweight i v
  have hfin (q) : ((fun z : Λ × ℝ =>
      parameterCode (root q*dyadicParameterWidth (levels q)) (c z.1)) '' E).Finite := by
    cases q with
    | none => simpa only [root,levels,one_mul,← hρdyadic] using hfinite0
    | some i => exact hfinite i
  have hfl (q) z (hz : z∈E) :
      ENNReal.ofReal ((root q*dyadicParameterWidth (levels q))^2*amps q/Ks q)*
        weights q (parameterCode (root q*dyadicParameterWidth (levels q)) (zv (c z.1))) ≤
      ν {l | parameterCode (root q*dyadicParameterWidth (levels q)) (c l)=
        parameterCode (root q*dyadicParameterWidth (levels q)) (c z.1)} := by
    cases q with
    | none => simpa only [root,levels,amps,Ks,weights,one_mul,← hρdyadic] using hfloor0 z hz
    | some i => exact hfloor i z hz
  have hcp (q) world cell v :
      (μ.restrict E) {z | parameterCode (root q) (c z.1)=world ∧
        canonicalZoomCell c (root q) (dyadicParameterWidth (levels q)) z=cell ∧
        parameterCode (root q*dyadicParameterWidth (levels q)) (zv (c z.1))=v} ≤
      ENNReal.ofReal (Cs q*dyadicParameterWidth (levels q)*
        (root q*dyadicParameterWidth (levels q))^2*amps q)*weights q v := by
    cases q with
    | none => simpa only [root,levels,amps,Cs,weights,one_mul,← hρdyadic] using hcap0 world cell v
    | some i => exact hcap i world cell v
  obtain ⟨R,hR,hsub,hloss,pal,hpal,hknown⟩ := prepare_incidence_parameter_palettes
    μ ν c hc E hE ht root amps Ks Cs cuts levels hroot hamps hKs hCs hcuts hfin weights hwtop hfl hcp
  have hpal0 (key) : ((pal none key).card : ℝ) ≤ C0*K0/cut0 := hpal none key
  have hknown0 (z) (hz : z∈R) : parameterCode ρ (c z.1) ∈
      pal none ((parameterCode 1 (c z.1),canonicalZoomCell c 1 ρ z),
        parameterCode ρ (zv (c z.1))) := by
    simpa only [root,levels,one_mul,← hρdyadic] using hknown none z hz
  obtain ⟨blocks,hblocks,hblocksKnown⟩ := original_state_parameter_palettes_from_unit_cells c R
    hb hb1 hρ hH (by positivity : 0 ≤ C0*K0/cut0)
    (fun z hz => ht z (hsub hz)) (fun z hz => hjets z (hsub hz)) hsmall
    (pal none) hpal0 hknown0
  refine ⟨R,hR,hsub,?_,blocks,(fun i => pal (some i)),hblocks,?_,hblocksKnown,?_⟩
  · simpa [cuts] using hloss
  · intro i key
    exact hpal (some i) key
  · intro i z hz
    exact hknown (some i) z hz

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
