-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.WholeChildFailurePruning, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.WholeBlockFailurePruning
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

/-- The actual prepared path removes whole children with excessive
qualification failure. Prepared uniqueness supplies disjointness at the
chosen level; all original worlds share one weighted failure budget.
Every positive-mass surviving child retains its EXACT original source,
so its state clauses and row reference remain available unchanged. -/
theorem discard_failure_heavy_children
    (selected : Set (Fin p.C)) (level : ℕ) (hlevel : ∀ b∈selected, p.lev b=level)
    (E bad : Fin (d.W k) → Set Ev) (hE : ∀ w, MeasurableSet (E w))
    (hbad : ∀ w, MeasurableSet (bad w)) (hbase : ∀ w, E w⊆Q.base w)
    (ratio : ENNReal) (hratio0 : ratio≠0) (hratioTop : ratio≠⊤) :
    ∃ keep : Fin (d.W k) → Set Ev,
      (∀ w, MeasurableSet (keep w) ∧ keep w⊆E w) ∧
      (∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (E w\keep w)) ≤
        ratio⁻¹*(∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (E w∩bad w)) ∧
      (∀ b∈selected, keep (p.γ b)∩p.F b=∅ ∨
        keep (p.γ b)∩p.F b=E (p.γ b)∩p.F b ∧
          ((d.ν k (p.γ b)).prod volume) ((keep (p.γ b)∩p.F b)∩bad (p.γ b)) ≤
            ratio*((d.ν k (p.γ b)).prod volume) (keep (p.γ b)∩p.F b)) ∧
      ∀ b∈selected, ((d.ν k (p.γ b)).prod volume) (keep (p.γ b)∩p.F b)≠0 →
        keep (p.γ b)∩p.F b=E (p.γ b)∩p.F b ∧
          ((d.ν k (p.γ b)).prod volume) ((keep (p.γ b)∩p.F b)∩bad (p.γ b)) ≤
            ratio*((d.ν k (p.γ b)).prod volume) (keep (p.γ b)∩p.F b) := by
  classical
  let indices := fun w => Finset.univ.filter (fun b => b∈selected ∧ p.γ b=w)
  have hF (b) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hindices (w) (b) : b∈indices w ↔ b∈selected ∧ p.γ b=w := by
    simp only [indices,Finset.mem_filter,Finset.mem_univ,true_and]
  have hdisjoint (w) : ∀ b∈indices w, ∀ b'∈indices w, b≠b' →
      Disjoint (E w∩p.F b) (E w∩p.F b') := by
    intro b hb b' hb' hne
    obtain ⟨hs,hw⟩ := (hindices w b).mp hb
    obtain ⟨hs',hw'⟩ := (hindices w b').mp hb'
    apply Set.disjoint_left.mpr
    rintro z ⟨hzE,hzb⟩ ⟨_,hzb'⟩
    exact hne (Q.base_packet_unique w z (hbase w hzE) b b'
      ((hlevel b hs).trans (hlevel b' hs').symm) hw hw' hzb hzb')
  have hlocal (w) := Parent.Qualification.exists_whole_block_small_failure_source
    ((d.ν k w).prod (volume : Measure ℝ)) (E w) (bad w) (hE w) (hbad w)
    p.F (indices w) (fun b _ => hF b) (hdisjoint w) ratio hratio0 hratioTop
  choose keep hkeep hsub hloss hslices using hlocal
  have hslices' (b) (hb : b∈selected) :
      keep (p.γ b)∩p.F b=∅ ∨
        keep (p.γ b)∩p.F b=E (p.γ b)∩p.F b ∧
          ((d.ν k (p.γ b)).prod volume) ((keep (p.γ b)∩p.F b)∩bad (p.γ b)) ≤
            ratio*((d.ν k (p.γ b)).prod volume) (keep (p.γ b)∩p.F b) :=
    hslices (p.γ b) b ((hindices (p.γ b) b).mpr ⟨hb,rfl⟩)
  refine ⟨keep,(fun w => ⟨hkeep w,hsub w⟩),?_,hslices',?_⟩
  · calc
      _ ≤ ∑ w, ENNReal.ofReal (d.ω k w)*
          (ratio⁻¹*((d.ν k w).prod volume) (E w∩bad w)) :=
        Finset.sum_le_sum (fun w _ => mul_le_mul' le_rfl (hloss w))
      _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ac_rfl)
  · intro b hb hpos
    obtain hzero | hgood := hslices' b hb
    · exact (hpos (by rw [hzero,measure_empty])).elim
    · exact hgood

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
