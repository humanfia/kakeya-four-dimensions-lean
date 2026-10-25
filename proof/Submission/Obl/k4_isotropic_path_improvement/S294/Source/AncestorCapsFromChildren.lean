-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.AncestorCapsFromChildren, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PreparedAncestry

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

/-- Child-dependent state preparation gives the SAME ancestor graph-code
ratio after summing all its actual children at one level. Prepared
uniqueness and the true original ancestry supply a disjoint cover; no
number of children or reciprocal mass factor is lost. The event B is
arbitrary, so this applies to every normalized pencil strip together. -/
theorem ancestor_code_cap_of_child_caps
    (hH : ∀ w, H w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (root : Fin p.C) (childLevel : ℕ)
    (hlevel : p.lev root ≤ childLevel) (hchildLevel : childLevel < m)
    (E : Set Ev) (hE : MeasurableSet E) (hbase : E⊆Q.base (p.γ root))
    (code : Ev → Fin 4 → ℤ) (hcode : Measurable code)
    (B : Set Ev) (cap : ENNReal)
    (hchildren : ∀ b∈originalFinePackets p root childLevel, ∀ label,
      (((d.ν k (p.γ root)).prod volume).restrict (E∩p.F b))
          {z | code z=label ∧ z∈B} ≤
        cap*(((d.ν k (p.γ root)).prod volume).restrict (E∩p.F b)) {z | code z=label}) :
    ∀ label,
      (((d.ν k (p.γ root)).prod volume).restrict (E∩p.F root))
          {z | code z=label ∧ z∈B} ≤
        cap*(((d.ν k (p.γ root)).prod volume).restrict (E∩p.F root)) {z | code z=label} := by
  classical
  intro label
  let raw := (d.ν k (p.γ root)).prod (volume : Measure ℝ)
  let Children := ↥(originalFinePackets p root childLevel)
  let source := (E∩p.F root)∩code ⁻¹' {label}
  let piece := fun b : Children => (E∩p.F b.1)∩code ⁻¹' {label}
  have hF (b) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hsource : MeasurableSet source := (hE.inter (hF root)).inter
    (hcode (measurableSet_singleton label))
  have hm (b : Children) : MeasurableSet (piece b) := (hE.inter (hF b.1)).inter
    (hcode (measurableSet_singleton label))
  have hspec (b : Children) :
      p.lev b.1=childLevel ∧ p.γ b.1=p.γ root ∧ p.F b.1⊆p.F root :=
    (Finset.mem_filter.mp b.2).2
  have hcover : source=⋃ b : Children, piece b := by
    ext z
    constructor
    · rintro ⟨⟨hzE,hzroot⟩,hzcode⟩
      obtain ⟨b,hblev,hbworld,hzb⟩ := hp.covered_at_level H childLevel (by omega) hH (p.γ root)
        (Q.base_subset _ (hbase hzE))
      have hb : b∈originalFinePackets p root childLevel :=
        Q.mem_original_fine_packets hp root b childLevel hlevel hblev hbworld
          z (hbase hzE) hzroot hzb
      exact mem_iUnion.mpr ⟨⟨b,hb⟩,⟨hzE,hzb⟩,hzcode⟩
    · intro hz
      obtain ⟨b,hzb⟩ := mem_iUnion.mp hz
      exact ⟨⟨hzb.1.1,(hspec b).2.2 hzb.1.2⟩,hzb.2⟩
  have hdj : Pairwise (fun b b' : Children => Disjoint (piece b) (piece b')) := by
    intro b b' hne
    apply Set.disjoint_left.mpr
    rintro z ⟨⟨hzE,hzb⟩,_⟩ ⟨⟨_,hzb'⟩,_⟩
    apply hne
    apply Subtype.ext
    exact Q.base_packet_unique (p.γ root) z (hbase hzE) b.1 b'.1
      ((hspec b).1.trans (hspec b').1.symm) (hspec b).2.1 (hspec b').2.1 hzb hzb'
  have hlocal (b : Children) : raw (piece b∩B) ≤ cap*raw (piece b) := by
    have h := hchildren b.1 b.2 label
    simp only [Measure.restrict_apply' (hE.inter (hF b.1))] at h
    have hnum : piece b∩B={z | code z=label ∧ z∈B}∩(E∩p.F b.1) := by
      ext z
      simp only [piece,mem_inter_iff,mem_preimage,mem_singleton_iff,mem_ofPred_eq]
      tauto
    have hden : piece b={z | code z=label}∩(E∩p.F b.1) := by
      ext z
      simp only [piece,mem_inter_iff,mem_preimage,mem_singleton_iff,mem_ofPred_eq]
      tauto
    rw [hnum,hden]
    exact h
  have htotal : raw (source∩B) ≤ cap*raw source := by
    calc
      _ = (raw.restrict B) source := (Measure.restrict_apply hsource).symm
      _ = ∑ b : Children, (raw.restrict B) (piece b) := by
        rw [hcover,measure_iUnion hdj hm,tsum_fintype]
      _ = ∑ b : Children, raw (piece b∩B) :=
        Finset.sum_congr rfl (fun b _ => Measure.restrict_apply (hm b))
      _ ≤ ∑ b : Children, cap*raw (piece b) := Finset.sum_le_sum (fun b _ => hlocal b)
      _ = cap*(∑ b : Children, raw (piece b)) := (Finset.mul_sum _ _ _).symm
      _ = cap*raw source := by rw [hcover,measure_iUnion hdj hm,tsum_fintype]
  simp only [Measure.restrict_apply' (hE.inter (hF root))]
  have hnum : source∩B={z | code z=label ∧ z∈B}∩(E∩p.F root) := by
    ext z
    simp only [source,mem_inter_iff,mem_preimage,mem_singleton_iff,mem_ofPred_eq]
    tauto
  have hden : source={z | code z=label}∩(E∩p.F root) := by
    ext z
    simp only [source,mem_inter_iff,mem_preimage,mem_singleton_iff,mem_ofPred_eq]
    tauto
  rw [hnum,hden] at htotal
  exact htotal

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
