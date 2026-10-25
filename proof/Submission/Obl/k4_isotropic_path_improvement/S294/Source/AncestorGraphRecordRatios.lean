-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.AncestorGraphRecordRatios, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.AncestorCapsFromChildren
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.ChildRecordRatioStates

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData PreparedAngularPath)
open scoped ENNReal BigOperators

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    (Q : PreparedAngularPath d k p m H u τ)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hp

/-- All three current graph ratios aggregate along the actual disjoint
child cover with the same coefficients and original palette. -/
theorem graph_record_ratios_of_fine_packet_ratios
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (root : Fin p.C) (level : ℕ) (hlevel : p.lev root ≤ level) (hlevelm : level < m)
    (E : Set Ev) (hE : MeasurableSet E) (hbase : E ⊆ Q.base (p.γ root))
    {graphMesh finePv radius stripWidth : ℝ} {stripCoeff paletteCoeff : ENNReal}
    (palette : Measure (ℤ×ℤ))
    (hchildren : ∀ b∈originalFinePackets p root level,
      GraphRecordRatios p (d.N k) root graphMesh finePv radius stripWidth stripCoeff paletteCoeff
        ((d.ν k (p.γ root)).prod volume) (E∩p.F b) palette) :
    GraphRecordRatios p (d.N k) root graphMesh finePv radius stripWidth stripCoeff paletteCoeff
      ((d.ν k (p.γ root)).prod volume) (E∩p.F root) palette := by
  let code := clockParentCode p root (Parent.SignalGraph.ancestorSignal (d.N k) p root) graphMesh
  have hcode : Measurable code := measurable_clockParentCode p root _ graphMesh
  refine ⟨?_,?_,?_⟩
  · intro label normal center hnormal
    apply ancestor_code_cap_of_child_caps Q hp hH root level hlevel hlevelm E hE hbase code hcode
      {z | |Inner.inner ℝ normal ((6*p.κ)⁻¹ • p.normalizedVelocity root z-center)| ≤ radius}
      stripCoeff ?_ label
    intro b hb cd
    exact (hchildren b hb).1 cd normal center hnormal
  · intro label normal offset hnormal
    apply ancestor_code_cap_of_child_caps Q hp hH root level hlevel hlevelm E hE hbase code hcode
      {z | |Inner.inner ℝ normal (Parent.v z.1)-offset| ≤ stripWidth} stripCoeff ?_ label
    intro b hb cd
    exact (hchildren b hb).2.1 cd normal offset hnormal
  · intro label D hD
    have hcap := ancestor_code_cap_of_child_caps Q hp hH root level hlevel hlevelm E hE hbase
      code hcode {z | Native.velocityPalette finePv (Parent.v z.1)∈D}
      (paletteCoeff*palette D) (fun b hb cd => by
        have hh := (hchildren b hb).2.2 cd D hD
        simpa only [code,mem_ofPred_eq,mul_assoc,mul_left_comm,mul_comm] using hh) label
    simpa only [code,mem_ofPred_eq,mul_assoc,mul_left_comm,mul_comm] using hcap

/-- The literal child-indexed ratios of state preparation give the
ancestor's current ratios. Empty child slices require no ancestor
identity; a nonempty slice identifies par^[c] b with the root by actual
prepared packet uniqueness. There is no child-count or mass factor. -/
theorem ancestor_graph_record_ratios_of_child_ratios
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (selectedRoot : Set (Fin p.C)) (root : Fin p.C) (hroot : root∈selectedRoot)
    (c : ℕ) (hlevelm : p.lev root+c < m)
    (E : Fin (d.W k) → Set Ev) (hE : ∀ w, MeasurableSet (E w))
    (hbase : ∀ w, E w ⊆ Q.base w)
    {graphMesh finePv radius stripWidth : ℝ} {stripCoeff paletteCoeff : ENNReal}
    (palette : Fin p.C → Measure (ℤ×ℤ))
    (hchildren : ∀ b, p.lev b=p.lev root+c → p.par^[c] b∈selectedRoot →
      GraphRecordRatios p (d.N k) (p.par^[c] b) graphMesh finePv radius stripWidth stripCoeff
        paletteCoeff ((d.ν k (p.γ b)).prod volume) (E (p.γ b)∩p.F b) (palette (p.par^[c] b))) :
    GraphRecordRatios p (d.N k) root graphMesh finePv radius stripWidth stripCoeff paletteCoeff
      ((d.ν k (p.γ root)).prod volume) (E (p.γ root)∩p.F root) (palette root) := by
  classical
  apply graph_record_ratios_of_fine_packet_ratios Q hp hH root (p.lev root+c)
    (by omega) hlevelm (E (p.γ root)) (hE _) (hbase _) (palette root)
  intro b hb
  obtain ⟨hlev,hγ,hFsub⟩ := (Finset.mem_filter.mp hb).2
  by_cases hempty : E (p.γ root)∩p.F b=∅
  · simp [GraphRecordRatios,hempty]
  · obtain ⟨z,hz⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    have hc : c ≤ p.lev b := by omega
    obtain ⟨hancLev,hancγ,hancF⟩ := Broad.iterate_par_spec hp.toOriginal c b hc
    change p.lev (p.par^[c] b)=p.lev b-c at hancLev
    change p.γ (p.par^[c] b)=p.γ b at hancγ
    change p.F b ⊆ p.F (p.par^[c] b) at hancF
    have heq : root=p.par^[c] b := Q.base_packet_unique (p.γ root) z (hbase _ hz.1)
      root (p.par^[c] b) (by omega) rfl (hancγ.trans hγ) (hFsub hz.2) (hancF hz.2)
    have hh := hchildren b hlev (by rw [←heq]; exact hroot)
    simpa only [←heq,hγ] using hh

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
